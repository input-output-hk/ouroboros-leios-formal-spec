## Linear Leios

<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Config
open import Leios.FFD
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.SpecStructure

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import CategoricalCrypto hiding (id; _∘_; eval)
open import CategoricalCrypto.Channel.Selection

open import Data.List.Properties
open import Data.Maybe.Properties

open import Prelude.STS.GenPremises

module Leios.Linear (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params) where
```
-->

This document is a specification of Linear Leios. It removes
concurrency at the transaction level by producing one (large) EB for
every Praos block.

In addition to the expected paramaters, we assume a two functions:

- `splitTxs`: produces a pair of a list of transactions that can be
  included in an RB and a list of transactions that can be included in
  an EB
- `validityCheckTime`: the time it takes to validate a given EB (in slots)

### Upkeep

A node that never produces a block even though it could is not
supposed to be an honest node, and we prevent that by tracking whether
a node has checked if it can make a block in a particular slot.
`LeiosState` contains a set of `SlotUpkeep` and we ensure that this
set contains all elements before we can advance to the next slot,
resetting this field to the empty set.

`CertCheck` records that the node has checked the voting functionality
for a certificate before producing its RB: it is added either by the
query (`Base₃`) or by `Base₂` when there is no EB to certify, and the
RB-submitting answer rule `Cert₁` requires it.

```agda
data SlotUpkeep : Type where
  Base CertCheck EB-Role VT-Role : SlotUpkeep
```
<!--
```agda
unquoteDecl DecEq-SlotUpkeep = derive-DecEq ((quote SlotUpkeep , DecEq-SlotUpkeep) ∷ [])

open import Leios.Protocol (⋯) SlotUpkeep ⊥ public
open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD

private variable s s'   : LeiosState
                 ffds'  : FFD.State
                 π      : VrfPf
                 ks ks' : K.State
                 msgs   : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 i      : FFDAbstract.Input ffdAbstract
                 eb     : EndorserBlock
                 ebs    : List EndorserBlock
                 rbs    : List RankingBlock
                 txs    : List Tx
                 V      : VTy
                 SD     : StakeDistr
                 pks    : List PubKey
                 cert   : EBCert
                 c      : Maybe EBCert
                 r      : EBRef
```
-->

### Block/Vote production

We now define the rules for block production given by the relation `_↝_`. These are split in two:

1. Positive rules, when we do need to create a block.
2. Negative rules, when we cannot create a block.

The purpose of the negative rules is to properly adjust the upkeep if
we cannot make a block.

Note that `_↝_`, starting with an empty upkeep can always make exactly
three steps corresponding to the three types of Leios specific blocks.

```agda
toProposeEB : LeiosState → VrfPf → Maybe EndorserBlock
toProposeEB s π = let open LeiosState s in case proj₂ (splitTxs ToPropose) of λ where
  [] → nothing
  _ → just $ mkEB slot id π sk-EB ToPropose

getCurrentEBHash : LeiosState → Maybe EBRef
getCurrentEBHash s = let open LeiosState s in
  RankingBlock.announcedEB currentRB

isEquivocated : LeiosState → EndorserBlock → Type
isEquivocated s eb = Any (areEquivocated eb) (toSet (LeiosState.EBs s))
```
The EB whose certificate the node would embed in the RB: the EB announced by
the current chain tip, old enough for the votes on it to have diffused.
```agda
certRequest : LeiosState → Maybe EndorserBlock
certRequest s = let open LeiosState s in
  find (λ eb → ¿ just (hash eb) ≡ getCurrentEBHash s
             × slotNumber eb + 3 * Lhdr + Lvote + Ldiff ≤ slot ¿) EBs

mkRB : LeiosState → VrfPf → Maybe EBCert → RankingBlock
mkRB s π mc = let open LeiosState s in record
  { announcedEB = hash <$> toProposeEB s π
  ; txsOrEbCert = case mc of λ where
      (just c) → inj₂ c
      nothing  → inj₁ (proj₁ (splitTxs ToPropose))
  }

{- A positive answer to a certificate query must certify the requested EB;
   a negative answer trivially matches any request. -}
data AnswerMatches : Maybe EBCert → EBRef → Type where
  matches-just    : ∀ {c r} → getEBHash c ≡ r → AnswerMatches (just c) r
  matches-nothing : ∀ {r} → AnswerMatches nothing r

instance
  Dec-AnswerMatches : ∀ {c r} → AnswerMatches c r ⁇
  Dec-AnswerMatches {c = just c} {r} .dec with getEBHash c ≟ r
  ... | yes p = yes (matches-just p)
  ... | no ¬p = no λ where (matches-just q) → ¬p q
  Dec-AnswerMatches {c = nothing} .dec = yes matches-nothing

rememberVote : LeiosState → EndorserBlock → LeiosState
rememberVote s@(record { VotedEBs = vebs }) eb =
  record s { VotedEBs = hash eb ∷ vebs }
```
The output of a block-production step: either a message for the FFD
functionality (announcing a block) or a vote cast to the voting functionality.
```agda
data _↝_ : LeiosState → LeiosState × (FFDAbstract.Input ffdAbstract ⊎ Vote) → Type where
```
#### Positive rules

In this specification, we don't want to peek behind the base chain
abstraction. This means that we assume instead that the `canProduceEB`
predicate is satisfied if and only if we can make an RB. In that case,
we send out an EB with the transactions currently stored in the
mempool.

```agda
  EB-Role : let open LeiosState s in
          ∙ toProposeEB s π ≡ just eb
          ∙ canProduceEB slot sk-EB (stake s) π
          ───────────────────────────────────────────────────────
          s ↝ (addUpkeep s EB-Role
              , inj₁ (Send (ebHeader eb) nothing))
```
```agda
  VT-Role : ∀ {ebHash slot'}
          → let open LeiosState s
          in
          ∙ getCurrentEBHash s ≡ just ebHash
          ∙ find (λ (_ , eb') → hash eb' ≟ ebHash) EBs' ≡ just (slot' , eb)
          ∙ hash eb ∉ VotedEBs
          ∙ ¬ isEquivocated s eb
          ∙ isValid s (inj₁ (ebHeader eb))
          ∙ slot' ≤ slotNumber eb + Lhdr
          ∙ slotNumber eb + 3 * Lhdr ≤ slot
          ∙ slot ≡ slotNumber eb + (3 * Lhdr ⊔ validityCheckTime eb)
          ∙ validityCheckTime eb ≤ 3 * Lhdr + Lvote
          ∙ EndorserBlockOSig.txs eb ≢ []
          ∙ needsUpkeep VT-Role
          ∙ canProduceV (slotNumber eb) sk-VT (stake s)
          ───────────────────────────────────────────────────────
          s ↝ (rememberVote (addUpkeep s VT-Role) eb
              , inj₂ (vote sk-VT (hash eb)))
```
Predicate needed for slot transition. Special care needs to be taken when starting from
genesis.
```agda
allDone : LeiosState → Type
allDone record { Upkeep = u } = VT-Role ∈ˡ u × EB-Role ∈ˡ u × Base ∈ˡ u × CertCheck ∈ˡ u
```
### Linear Leios transitions
The relation describing the transition given input and state

```agda
open Types params
open BaseAbstract B'

data _-⟦_/_⟧⇀_ : MachineType ((FFD ⊗₀ BaseIO) ⊗₀ VotingC) (IO ⊗₀ Adv) LeiosState where
```
#### Network and Ledger
```agda
  Slot₁ : let open LeiosState s in
        ∙ allDone s
        ──────────────────────────────────────────────────────────────────
        s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ FFD-OUT msgs / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ FTCH-LDG ⟧⇀
          let s' = s ↑ L.filter (isValid? s) msgs
          in record s'
               { slot   = suc slot
               ; Upkeep = []
               }

  Slot₂ : let open LeiosState s in
        ───────────────────────────────────────────────────────────────────
        s -⟦ ((L⊗ ϵ) ⊗R) ⊗R ↑ᵢ BASE-LDG rbs / nothing ⟧⇀ record s { RBs = rbs }
```
```agda
  Ftch : let open LeiosState s in
       ───────────────────────────────────────────────────────────────────────────
       s -⟦ L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FetchLdgI / just $ L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ FetchLdgO Ledger ⟧⇀ s
```
#### Base chain

Note: Submitted data to the base chain is only taken into account
      if the party submitting is the block producer on the base chain
      for the given slot
```agda
  Base₁   :
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ SubmitTxs txs / nothing ⟧⇀ record s { ToPropose = txs }

  Base₂   : let open LeiosState s in
          ∙ needsUpkeep Base
          ∙ needsUpkeep CertCheck
          ∙ certRequest s ≡ nothing
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s π nothing) ⟧⇀
            addUpkeep (addUpkeep s CertCheck) Base
```
If the chain tip announces an EB whose voting window has passed, the node
instead queries the voting functionality for a certificate before it submits:
the `Base` upkeep stays open until the answer arrives.
```agda
  Base₃   : let open LeiosState s in
          ∙ needsUpkeep CertCheck
          ∙ certRequest s ≡ just eb
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ (L⊗ ϵ) ⊗R ↑ₒ QUERY (hash eb) ⟧⇀
            record (addUpkeep s CertCheck) { PendingQuery = just (hash eb) }
```
#### Voting
```agda
  Vote₁ : ∀ {v} →
         ∙ s ↝ (s' , inj₂ v)
         ────────────────────────────────────────────────────────────
         s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ (L⊗ ϵ) ⊗R ↑ₒ CAST v ⟧⇀ s'

```
The answer to a certificate query: a positive answer embeds the certificate
in the submitted RB, a negative one falls back to submitting transactions.
The answer is correlated with the request recorded in `PendingQuery`: the
rule only accepts an answer while a query is outstanding, a positive answer
must certify the requested EB, and the request is cleared on submission.
```agda
  Cert₁ : let open LeiosState s in
        ∙ needsUpkeep Base
        ∙ CertCheck ∈ˡ Upkeep
        ∙ PendingQuery ≡ just r
        ∙ AnswerMatches c r
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ CERT c / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s π c) ⟧⇀
          record (addUpkeep s Base) { PendingQuery = nothing }
```
#### Protocol rules
```agda
  Roles₁ :
         ∙ s ↝ (s' , inj₁ i)
         ────────────────────────────────────────────────────────────
         s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ ((ϵ ⊗R) ⊗R) ⊗R ↑ₒ FFD-IN i ⟧⇀ s'

  Roles₂ : ∀ {u} → let open LeiosState in
         ∙ ¬ (∃[ s'×i ] (s ↝ s'×i × Upkeep (addUpkeep s u) ≡ Upkeep (proj₁ s'×i)))
         ∙ needsUpkeep s u
         ∙ u ≢ Base
         ∙ u ≢ CertCheck
         ──────────────────────────────────────────────────
         s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / nothing ⟧⇀ addUpkeep s u
```
<!--
```agda
LinearLeios : Machine ((FFD ⊗₀ BaseIO) ⊗₀ VotingC) (IO ⊗₀ Adv)
LinearLeios .Machine.State = LeiosState
LinearLeios .Machine.stepRel = _-⟦_/_⟧⇀_

instance
  Dec-isValid : ∀ {s x} → isValid s x ⁇
  Dec-isValid {s} {x} = ⁇ isValid? s x

unquoteDecl EB-Role-premises = genPremises EB-Role-premises (quote _↝_.EB-Role)
unquoteDecl VT-Role-premises = genPremises VT-Role-premises (quote _↝_.VT-Role)

unquoteDecl Slot₁-premises = genPremises Slot₁-premises (quote Slot₁)
unquoteDecl Slot₂-premises = genPremises Slot₂-premises (quote Slot₂)
unquoteDecl Base₁-premises = genPremises Base₁-premises (quote Base₁)
unquoteDecl Base₂-premises = genPremises Base₂-premises (quote Base₂)
unquoteDecl Base₃-premises = genPremises Base₃-premises (quote Base₃)
unquoteDecl Cert₁-premises = genPremises Cert₁-premises (quote Cert₁)

just≢nothing : ∀ {ℓ} {A : Type ℓ} {x} → (Maybe A ∋ just x) ≡ nothing → ⊥
just≢nothing = λ ()

nothing≢just : ∀ {ℓ} {A : Type ℓ} {x} → nothing ≡ (Maybe A ∋ just x) → ⊥
nothing≢just = λ ()

P : EBRef → ℕ × EndorserBlock → Type
P h (_ , eb) = hash eb ≡ h

P? : (h : EBRef) → ((s , eb) : ℕ × EndorserBlock) → Dec (P h (s , eb))
P? h (_ , eb) = hash eb ≟ h

not-found : LeiosState → EBRef → Type
not-found s k = find (P? k) (LeiosState.EBs' s) ≡ nothing

subst' : ∀ {s ebHash ebHash₁ slot' slot'' eb eb₁}
  → getCurrentEBHash s ≡ just ebHash₁
  → find (λ (_ , eb') → hash eb' ≟ ebHash₁) (LeiosState.EBs' s) ≡ just (slot'' , eb₁)
  → getCurrentEBHash s ≡ just ebHash
  → find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) ≡ just (slot' , eb)
  → (eb₁ , ebHash₁ , slot'') ≡ (eb , ebHash , slot')
subst' {s} {ebHash = ebHash} {eb = eb} eq₁₁ eq₁₂ eq₂₁ eq₂₂
  with getCurrentEBHash s | eq₁₁ | eq₂₁
... | _ | refl | refl
  with find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) | eq₁₂ | eq₂₂
... | _ | refl | refl = refl

Base≢EB-Role : SlotUpkeep.Base ≢ SlotUpkeep.EB-Role
Base≢EB-Role = λ ()

Base≢VT-Role : SlotUpkeep.Base ≢ SlotUpkeep.VT-Role
Base≢VT-Role = λ ()

CertCheck≢EB-Role : SlotUpkeep.CertCheck ≢ SlotUpkeep.EB-Role
CertCheck≢EB-Role = λ ()

CertCheck≢VT-Role : SlotUpkeep.CertCheck ≢ SlotUpkeep.VT-Role
CertCheck≢VT-Role = λ ()

π-unique : ∀ {s π} → canProduceEB (LeiosState.slot s) sk-EB (stake s) π → π ≡ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))
π-unique (_ , refl) = refl

instance

  Dec-↝ : ∀ {s u} → (∃[ s'×i ] (s ↝ s'×i × (u ∷ LeiosState.Upkeep s) ≡ LeiosState.Upkeep (proj₁ s'×i))) ⁇
  Dec-↝ {s} {EB-Role} .dec
    with toProposeEB s (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s))) in eq₁
  ... | nothing = no λ where
    (_ , EB-Role {π = π} (p , a) , b) →
      case (π ≟ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))) of λ
        { (yes q) → nothing≢just (trans (sym eq₁) (subst (λ x → toProposeEB s x ≡ just _) q p)) ;
          (no ¬q) → contradiction (π-unique {s} {π} a) ¬q
        }
  ... | just eb
    with ¿ canProduceEB (LeiosState.slot s) sk-EB (stake s) _ ¿
  ... | yes q = yes (_ , EB-Role (eq₁ , q) , refl)
  ... | no ¬q = no λ where
    (_ , EB-Role {π = π} (a , q) , b) →
      case (π ≟ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))) of λ
        { (yes r) → ¬q (subst (λ x → canProduceEB (LeiosState.slot s) sk-EB (stake s) x) r q) ;
          (no ¬r) → contradiction (π-unique {s} {π} q) ¬r
        }
  Dec-↝ {s} {VT-Role} .dec
    with getCurrentEBHash s in eq₂
  ... | nothing = no λ where (_ , VT-Role (p , _) , _) → nothing≢just (trans (sym eq₂) p)
  ... | just ebHash
    with find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) in eq₃
  ... | nothing = no λ where
    (_ , VT-Role (x , y , _) , _) →
      let ji = just-injective (trans (sym x) eq₂)
      in just≢nothing $ trans (sym y) (subst (not-found s) (sym ji) eq₃)
  ... | just (slot' , eb)
    with ¿ VT-Role-premises {s} {eb} {ebHash} {slot'} .proj₁ ¿
  ... | yes p = yes ((rememberVote (addUpkeep s VT-Role) eb , inj₂ (vote sk-VT (hash eb))) ,
                      VT-Role p , refl)
  ... | no ¬p = no λ where (_ , VT-Role (x , y , p) , _) → ¬p $ subst
                             (λ where (eb , ebHash , slot) → VT-Role-premises {s} {eb} {ebHash} {slot} .proj₁)
                             (subst' {s} x y eq₂ eq₃) (x , y , p)
  Dec-↝ {s} {Base} .dec = no λ where
    (_ , EB-Role _ , x) → Base≢EB-Role (∷-injectiveˡ (trans x refl))
    (_ , VT-Role _ , x) → Base≢VT-Role (∷-injectiveˡ (trans x refl))
  Dec-↝ {s} {CertCheck} .dec = no λ where
    (_ , EB-Role _ , x) → CertCheck≢EB-Role (∷-injectiveˡ (trans x refl))
    (_ , VT-Role _ , x) → CertCheck≢VT-Role (∷-injectiveˡ (trans x refl))

unquoteDecl Roles₂-premises = genPremises Roles₂-premises (quote Roles₂)
```
-->
