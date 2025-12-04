## Linear Leios

<!--
```agda
{-# OPTIONS --safe --no-require-unique-meta-solutions #-}
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Channel.Selection

module Leios.Linear (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (Lhdr Lvote Ldiff : ℕ)
  (splitTxs : List Tx → List Tx × List Tx)
  (validityCheckTime : EndorserBlock → ℕ) where
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

```agda
data SlotUpkeep : Type where
  Base EB-Role VT-Role : SlotUpkeep
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
                 bs'    : B.State
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

rememberVote : LeiosState → EndorserBlock → LeiosState
rememberVote s@(record { VotedEBs = vebs }) eb = record s { VotedEBs = hash eb ∷ vebs }

data _↝_ : LeiosState → LeiosState × FFDAbstract.Input ffdAbstract → Type where
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
          s ↝ (addUpkeep s EB-Role , Send (ebHeader eb) nothing)
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
          s ↝ ( rememberVote (addUpkeep s VT-Role) eb
              , Send (vtHeader [ vote sk-VT (hash eb) ]) nothing)
```
Predicate needed for slot transition. Special care needs to be taken when starting from
genesis.
```agda
allDone : LeiosState → Type
allDone record { Upkeep = u } = VT-Role ∈ˡ u × EB-Role ∈ˡ u × Base ∈ˡ u
```
### Linear Leios transitions
The relation describing the transition given input and state

#### Initialization
```agda
open Types params

data _⊢_ : VTy → LeiosState → Type where
  Init :
       ∙ ks K.-⟦ K.INIT pk-EB pk-VT / K.PUBKEYS pks ⟧⇀ ks'
       ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs'
       ────────────────────────────────────────────────────────────────
       V ⊢ initLeiosState V SD pks
```
```agda
data _-⟦_/_⟧⇀_ : MachineType (FFD ⊗ BaseC) (IO ⊗ Adv) LeiosState where
```
#### Network and Ledger
```agda
  Slot₁ : let open LeiosState s in
        ∙ allDone s
        ──────────────────────────────────────────────────────────────────
        s -⟦ (ϵ ⊗R) ⊗R ↑ᵢ FFD-OUT msgs / just $ (L⊗ ϵ) ⊗R ↑ₒ FTCH-LDG ⟧⇀
          let s' = s ↑ L.filter (isValid? s) msgs
          in record s'
               { slot   = suc slot
               ; Upkeep = []
               }

  Slot₂ : let open LeiosState s in
        ───────────────────────────────────────────────────────────────────
        s -⟦ (L⊗ ϵ) ⊗R ↑ᵢ BASE-LDG rbs / nothing ⟧⇀ record s { RBs = rbs }
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
```
```agda
  Base₂   : let open LeiosState s
                currentCertEB = find (λ (eb , _) →
                  ¿ just (hash eb) ≡ getCurrentEBHash s
                  × slotNumber eb + 3 * Lhdr + Lvote + Ldiff ≤ slot ¿) ebsWithCert
                rb = record
                       { txs = proj₁ (splitTxs ToPropose)
                       ; announcedEB = hash <$> toProposeEB s π
                       ; ebCert = proj₂ <$> currentCertEB }
          in
          ∙ needsUpkeep Base
          ───────────────────────────────────────────────────────────────────────────
          s -⟦ (ϵ ⊗R) ⊗R ↑ᵢ SLOT / just $ (L⊗ ϵ) ⊗R ↑ₒ SUBMIT rb ⟧⇀ addUpkeep s Base
```
#### Protocol rules
```agda
  Roles₁ :
         ∙ s ↝ (s' , i)
         ────────────────────────────────────────────────────────────
         s -⟦ (ϵ ⊗R) ⊗R ↑ᵢ SLOT / just $ (ϵ ⊗R) ⊗R ↑ₒ FFD-IN i ⟧⇀ s'

  Roles₂ : ∀ {u} → let open LeiosState in
         ∙ ¬ (∃[ s'×i ] (s ↝ s'×i × Upkeep (addUpkeep s u) ≡ Upkeep (proj₁ s'×i)))
         ∙ needsUpkeep s u
         ∙ u ≢ Base
         ──────────────────────────────────────────────────
         s -⟦ (ϵ ⊗R) ⊗R ↑ᵢ SLOT / nothing ⟧⇀ addUpkeep s u
```
<!--
```agda
ShortLeios : Machine (FFD ⊗ BaseC) (IO ⊗ Adv)
ShortLeios .Machine.State = LeiosState
ShortLeios .Machine.stepRel = _-⟦_/_⟧⇀_

record IsBlockchain {A B} (Block : Type) (m : Machine A B) : Type where
  open Channel
  open Machine m renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
  field getCurrentChainI : B .outType
        getCurrentChainO : B .inType → Maybe (List Block)
        correctness : ∀ {s} → ∃[ o ] ∃[ bs ]
          s -⟦ L⊗ ϵ ↑ᵢ getCurrentChainI / just (L⊗ ϵ ↑ₒ o) ⟧ᵐ⇀ s
          -- asking for the chain probably shouldn't update the state
          × getCurrentChainO o ≡ just bs

module _ {A} {B} (m : Machine A B) where
  module m = Machine m
  open m using () renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
  open Channel (A ⊗ B ᵀ)

  data Trace : m.State → Type where
    [] : ∀ {s} → Trace s
    ⟨_,_,_⟩∷_ : ∀ {s} → (i : inType) → (o : Maybe outType)
      → (Σ[ s' ∈ m.State ] (s -⟦ i / o ⟧ᵐ⇀ s')) → Trace s → Trace s

  finalState : ∀ {s} → Trace s → m.State
  finalState {s} [] = s
  finalState (⟨ i , o , x ⟩∷ _) = proj₁ x

  record ComputationalMachine : Type where
    field compute : inType → m.State → Maybe (outType × State)
          -- correctness
          -- TODO: use Computational22

module _
  (numberOfParties : ℕ) (IO Adv : Channel)
  (Node : Machine Network (IO ⊗ Adv))
  (nodesF : (k : Fin numberOfParties) → Machine Network (IO ⊗ Adv))
  (Computational-Nodes : ∀ {k} → ComputationalMachine (nodesF k))
  (IsBlockchain-Node : ∀ {k} → IsBlockchain Block (nodesF k))
  (honestNodes : ℙ (Fin numberOfParties))
  (honest-Node : ∀ {p} → p ∈ honestNodes → nodesF p ≡ Node)
  (p : Fin numberOfParties) (honest-p : p ∈ honestNodes)
  where
  open import Network.BasicBroadcast numberOfParties NetworkMessage as BB
    using () renaming (Network to Net)

  nodes : Machine (⨂_ {n = numberOfParties} (const Network)) ((⨂_ {n = numberOfParties} (const IO)) ⊗ (⨂_ {n = numberOfParties} (const Adv)))
  nodes = ⨂ᴷ nodesF

  network : Machine I ((⨂_ {n = numberOfParties} (const IO)) ⊗ (BB.A ⊗ (⨂_ {n = numberOfParties} (const Adv))))
  network = nodes ∘ᴷ {!Net!}

  module network = Machine network

  getChain : network.State → Fin numberOfParties → Maybe (List Block)
  getChain s p = case compute (L⊗ ϵ ↑ᵢ getCurrentChainI) {!!} of λ where -- extract the right state
      (just (x , _)) → maybe getCurrentChainO nothing {!!} -- project x onto the right channel
      nothing → nothing
    where
      open ComputationalMachine (Computational-Nodes {p})
      open IsBlockchain (IsBlockchain-Node {p})

  -- similar to `getChain`
  getCurrentSlot : network.State → Fin numberOfParties → Maybe ℕ
  getCurrentSlot = {!!}

  safety : Type
  safety = Σ[ Δ ∈ ℕ ] ∀ (init : network.State) {chain} {s₁ s₂} → getChain init p ≡ just chain
    -- for all traces that reach `Δ` slots into the future
    →  ∀ (tr : Trace network init)
    →  let final = finalState network tr
    in getCurrentSlot init  p ≡ just s₁
    →  getCurrentSlot final p ≡ just s₂
    →  s₂ ≥ s₁ + Δ
    -- all honest nodes have `chain` as a prefix
    →  ∀ {p' : Fin numberOfParties} → p' ∈ honestNodes
    →  ∃[ chain' ] getChain init p ≡ just (chain ++ chain')

open import Prelude.STS.GenPremises

instance
  Dec-isValid : ∀ {s x} → isValid s x ⁇
  Dec-isValid {s} {x} = ⁇ isValid? s x

unquoteDecl EB-Role-premises = genPremises EB-Role-premises (quote _↝_.EB-Role)
unquoteDecl VT-Role-premises = genPremises VT-Role-premises (quote _↝_.VT-Role)

unquoteDecl Slot₁-premises = genPremises Slot₁-premises (quote Slot₁)
unquoteDecl Slot₂-premises = genPremises Slot₂-premises (quote Slot₂)
unquoteDecl Base₁-premises = genPremises Base₁-premises (quote Base₁)
unquoteDecl Base₂-premises = genPremises Base₂-premises (quote Base₂)

just≢nothing : ∀ {ℓ} {A : Type ℓ} {x} → (Maybe A ∋ just x) ≡ nothing → ⊥
just≢nothing = λ ()

nothing≢just : ∀ {ℓ} {A : Type ℓ} {x} → nothing ≡ (Maybe A ∋ just x) → ⊥
nothing≢just = λ ()

open import Data.List.Properties
open import Data.Maybe.Properties
open import Data.Product.Properties

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
  ... | yes p = yes ((rememberVote (addUpkeep s VT-Role) eb , Send (vtHeader [ vote sk-VT (hash eb) ]) nothing) ,
                      VT-Role p , refl)
  ... | no ¬p = no λ where (_ , VT-Role (x , y , p) , _) → ¬p $ subst
                             (λ where (eb , ebHash , slot) → VT-Role-premises {s} {eb} {ebHash} {slot} .proj₁)
                             (subst' {s} x y eq₂ eq₃) (x , y , p)
  Dec-↝ {s} {Base} .dec = no λ where
    (_ , EB-Role _ , x) → Base≢EB-Role (∷-injectiveˡ (trans x refl))
    (_ , VT-Role _ , x) → Base≢VT-Role (∷-injectiveˡ (trans x refl))

unquoteDecl Roles₂-premises = genPremises Roles₂-premises (quote Roles₂)
```
-->
