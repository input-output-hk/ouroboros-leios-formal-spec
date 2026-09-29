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
- `isValidityChecked`: whether validation of a given EB has completed by a
  given slot

### Upkeep

A node that never produces a block even though it could is not
supposed to be an honest node, and we prevent that by tracking whether
a node has checked if it can make a block in a particular slot.
`LeiosState` contains a set of `SlotUpkeep` and we ensure that this
set contains all elements before we can advance to the next slot,
resetting this field to the empty set.

`CertCheck` records that the node has checked the voting functionality
for a certificate before producing its RB.
```agda
data SlotUpkeep : Type where
  Base CertCheck EB-Role VT-Role : SlotUpkeep
```
<!--
```agda
unquoteDecl DecEq-SlotUpkeep = derive-DecEq ((quote SlotUpkeep , DecEq-SlotUpkeep) ∷ [])

open import Leios.Protocol (⋯) SlotUpkeep ⊥ public
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD

private variable s s' : LeiosState
                 π     : VrfPf
                 msgs  : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 i     : FFDAbstract.Input ffdAbstract
                 eb    : EndorserBlock
                 rbs   : List RankingBlock
                 txs   : List Tx
                 c     : Maybe EBCert
                 r     : EBRef
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

mkRB : LeiosState → Maybe EBCert → RankingBlock
mkRB s mc = let open LeiosState s in record
  { announcedEB = proposedEB
  ; txsOrEbCert = case mc of λ where
      (just c) → inj₂ c
      nothing  → inj₁ (proj₁ (splitTxs ToPropose))
  }
```
A positive answer to a certificate query must certify the requested EB;
a negative answer trivially matches any request.
```agda
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
rememberVote s@(record { VotedEBs = vebs }) eb = record s { VotedEBs = hash eb ∷ vebs }

-- Record the EB this party is diffusing, so that `Base₂` announces the block
-- that actually went out rather than recomputing a candidate from `ToPropose`.
rememberProposal : LeiosState → EndorserBlock → LeiosState
rememberProposal s eb = record s { proposedEB = just (hash eb) }
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
          ∙ needsUpkeep EB-Role
          ───────────────────────────────────────────────────────
          s ↝ (rememberProposal (addUpkeep s EB-Role) eb
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
          ∙ slot ≤ slotNumber eb + 3 * Lhdr + Lvote
          ∙ isValidityChecked slot eb
          ∙ EndorserBlockOSig.txs eb ≢ []
          ∙ needsUpkeep VT-Role
          ∙ inVotingCommittee params (stake s)
          -- Only a pool with a registered voting key may sign
          ∙ id ∈ˡ L.map poolID PubKeys
          ───────────────────────────────────────────────────────
          s ↝ (rememberVote (addUpkeep s VT-Role) eb
              , inj₂ (vote sk-VT (hash currentRB)))
```
Predicate needed for slot transition. Special care needs to be taken when starting from
genesis.
```agda
allDone : LeiosState → Type
allDone record { Upkeep = u } = VT-Role ∈ˡ u × EB-Role ∈ˡ u × Base ∈ˡ u × CertCheck ∈ˡ u
```
Voting happens within a window: it opens `3 * Lhdr` slots after the announcing
RB's slot (the equivocation-detection period) and closes `Lvote` slots later.
`voteDeadline` is the last slot at which the current EB may still be voted on;
when there is no current EB (or it has not been received yet) the deadline is `0`,
so the deferral rule `Roles₃` below is vacuously inapplicable and abstention is
governed solely by `Roles₂`.
```agda
voteDeadline : LeiosState → ℕ
voteDeadline s = let open LeiosState s in
  case getCurrentEBHash s of λ where
    nothing       → 0
    (just ebHash) → case find (λ (_ , eb') → hash eb' ≟ ebHash) EBs' of λ where
      nothing         → 0
      (just (_ , eb)) → slotNumber eb + 3 * Lhdr + Lvote
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
               { slot       = suc slot
               ; Upkeep     = []
               ; proposedEB = nothing
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

`Base₂` announces the EB recorded by `EB-Role`, not a candidate recomputed
from `ToPropose`. The premise `hasUpkeep EB-Role` makes the party settle its
EB role for the slot first, either by producing (which sets `proposedEB`) or
by declining through `Roles₂`; without it a `Base₂` step scheduled early in
the slot would announce `nothing` and strand the EB the party goes on to
diffuse. `Base₃` carries the same premise, so that the RB eventually
submitted by `Cert₁` or `Cert₂` announces the settled EB too: those rules
only fire once a query is outstanding, which only `Base₃` makes it.
```agda
  Base₁   :
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ SubmitTxs txs / nothing ⟧⇀ record s { ToPropose = txs }

  Base₂   : let open LeiosState s in
          ∙ needsUpkeep Base
          ∙ needsUpkeep CertCheck
          ∙ hasUpkeep EB-Role
          ∙ certRequest s ≡ nothing
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s nothing) ⟧⇀
            addUpkeep (addUpkeep s CertCheck) Base
```
If the chain tip announces an EB whose voting window has passed, the node
instead queries the voting functionality for a certificate before it submits:
the `Base` upkeep stays open until the answer arrives.
```agda
  Base₃   : let open LeiosState s in
          ∙ needsUpkeep CertCheck
          ∙ hasUpkeep EB-Role
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
The answer is correlated with the request recorded in `PendingQuery`: the
rule only accepts an answer while a query is outstanding, a positive answer
must certify the requested EB, and the request is cleared on submission.

Since the chain tip may change between query and answer (`Slot₂` has no
premises), the rule also re-validates the request at submission time: the
pending query must still be for the EB the *current* tip calls for, so a
stale answer cannot be embedded. This re-validation, combined with
`needsUpkeep CertCheck` in `Base₂` and `Base₃` (each fires only once per
slot), would otherwise leave `Base` stuck open forever if the tip changes
between query and answer: `Cert₁` refuses the stale answer, `Base₂` requires
`certRequest s ≡ nothing`, and `Base₃` can no longer fire since `CertCheck`
upkeep is already spent. Two further rules make every `CERT` answer lead
somewhere:

- `Cert₂`: the tip no longer calls for a certificate at all
  (`certRequest s ≡ nothing`). The stale answer is discarded and the RB is
  submitted without a certificate, discharging `Base` — mirroring `Base₂`'s
  action.
- `Cert₃`: the tip now calls for a certificate on a *different* EB than the
  one queried. The stale answer is discarded and a fresh query is issued for
  the new EB; `Base` stays open until that query is answered.
```agda
  Cert₁ : let open LeiosState s in
        ∙ needsUpkeep Base
        ∙ CertCheck ∈ˡ Upkeep
        ∙ certRequest s ≡ just eb
        ∙ PendingQuery ≡ just (hash eb)
        ∙ AnswerMatches c (hash eb)
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ CERT c / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s c) ⟧⇀
          record (addUpkeep s Base) { PendingQuery = nothing }

  Cert₂ : let open LeiosState s in
        ∙ needsUpkeep Base
        ∙ CertCheck ∈ˡ Upkeep
        ∙ certRequest s ≡ nothing
        ∙ PendingQuery ≡ just r
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ CERT c / just $ ((L⊗ ϵ) ⊗R) ⊗R ↑ₒ SUBMIT (mkRB s nothing) ⟧⇀
          record (addUpkeep s Base) { PendingQuery = nothing }

  Cert₃ : let open LeiosState s in
        ∙ needsUpkeep Base
        ∙ CertCheck ∈ˡ Upkeep
        ∙ certRequest s ≡ just eb
        ∙ PendingQuery ≡ just r
        ∙ hash eb ≢ r
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ CERT c / just $ (L⊗ ϵ) ⊗R ↑ₒ QUERY (hash eb) ⟧⇀
          record s { PendingQuery = just (hash eb) }
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
Deferral of the VT-Role: abstaining from voting is permitted while the
current EB's voting window is still open, even when a positive VT-Role
step could fire. Together with `Roles₂` this yields bounded liveness:
at the deadline slot neither `Roles₃` (window closes) nor `Roles₂` (a vote can still fire)
applies, so a vote must be cast by then.
```agda
  Roles₃ : let open LeiosState s in
         ∙ slot < voteDeadline s
         ∙ needsUpkeep VT-Role
         ──────────────────────────────────────────────────
         s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / nothing ⟧⇀ addUpkeep s VT-Role
```
<!--
```agda
LinearLeios : Machine ((FFD ⊗₀ BaseIO) ⊗₀ VotingC) (IO ⊗₀ Adv)
LinearLeios .Machine.State = LeiosState
LinearLeios .Machine.stepRel = _-⟦_/_⟧⇀_

instance
  Dec-isValid : ∀ {s x} → isValid s x ⁇
  Dec-isValid {s} {x} = ⁇ isValid? s x

  Dec-isValidityChecked : ∀ {n eb} → isValidityChecked n eb ⁇
  Dec-isValidityChecked {n} {eb} = ⁇ isValidityChecked? n eb

unquoteDecl EB-Role-premises = genPremises EB-Role-premises (quote _↝_.EB-Role)
unquoteDecl VT-Role-premises = genPremises VT-Role-premises (quote _↝_.VT-Role)

unquoteDecl Slot₁-premises = genPremises Slot₁-premises (quote Slot₁)
unquoteDecl Slot₂-premises = genPremises Slot₂-premises (quote Slot₂)
unquoteDecl Base₁-premises = genPremises Base₁-premises (quote Base₁)
unquoteDecl Base₂-premises = genPremises Base₂-premises (quote Base₂)
unquoteDecl Base₃-premises = genPremises Base₃-premises (quote Base₃)
unquoteDecl Cert₁-premises = genPremises Cert₁-premises (quote Cert₁)
unquoteDecl Cert₂-premises = genPremises Cert₂-premises (quote Cert₂)
unquoteDecl Cert₃-premises = genPremises Cert₃-premises (quote Cert₃)

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

π-unique : ∀ {s π} → canProduceEB (LeiosState.slot s) sk-EB (stake s) π → π ≡ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))
π-unique (_ , refl) = refl

instance

  Dec-↝ : ∀ {s u} → (∃[ s'×i ] (s ↝ s'×i × (u ∷ LeiosState.Upkeep s) ≡ LeiosState.Upkeep (proj₁ s'×i))) ⁇
  Dec-↝ {s} {EB-Role} .dec
    with toProposeEB s (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s))) in eq₁
  ... | nothing = no λ where
    (_ , EB-Role {π = π} (p , a , _) , b) →
      case (π ≟ (proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s)))) of λ
        { (yes q) → nothing≢just (trans (sym eq₁) (subst (λ x → toProposeEB s x ≡ just _) q p)) ;
          (no ¬q) → contradiction (π-unique {s} {π} a) ¬q
        }
  ... | just eb
    with ¿ canProduceEB (LeiosState.slot s) sk-EB (stake s) _ ¿
       | ¿ LeiosState.needsUpkeep s SlotUpkeep.EB-Role ¿
  ... | yes q | yes u = yes (_ , EB-Role (eq₁ , q , u) , refl)
  ... | yes _ | no ¬u = no λ where
    (_ , EB-Role (_ , _ , u) , _) → ¬u u
  ... | no ¬q | _ = no λ where
    (_ , EB-Role {π = π} (a , q , _) , b) →
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
  ... | yes p = yes ((rememberVote (addUpkeep s VT-Role) eb , inj₂ (vote sk-VT (hash (LeiosState.currentRB s)))) ,
                      VT-Role p , refl)
  ... | no ¬p = no λ where (_ , VT-Role (x , y , p) , _) → ¬p $ subst
                             (λ where (eb , ebHash , slot) → VT-Role-premises {s} {eb} {ebHash} {slot} .proj₁)
                             (subst' {s} x y eq₂ eq₃) (x , y , p)
  Dec-↝ {u = Base} .dec = no λ where
    (_ , EB-Role _ , ())
    (_ , VT-Role _ , ())
  Dec-↝ {u = CertCheck} .dec = no λ where
    (_ , EB-Role _ , ())
    (_ , VT-Role _ , ())

unquoteDecl Roles₂-premises = genPremises Roles₂-premises (quote Roles₂)
unquoteDecl Roles₃-premises = genPremises Roles₃-premises (quote Roles₃)
```
-->
