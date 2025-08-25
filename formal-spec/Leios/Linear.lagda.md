## Linear Leios

<!--
```agda
-- {-# OPTIONS --safe #-}
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import CategoricalCrypto hiding (id; _∘_)

open import Data.Maybe.Properties
open import Data.Product.Properties

module Leios.Linear (⋯ : SpecStructure 1)
  (let open SpecStructure ⋯ renaming (isVoteCertified to isVoteCertified'))
  (params : Params)
  (Lvote Ldiff : ℕ) where
```
-->

This document is a specification of Linear Leios. It removes
concurrency at the transaction level by producing one (large) EB for
every Praos block.

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

unquoteDecl DecEq-SlotUpkeep = derive-DecEq ((quote SlotUpkeep , DecEq-SlotUpkeep) ∷ [])
```
<!--
```agda
open import Leios.Protocol (⋯) SlotUpkeep ⊥ public

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD
```
```agda
isVoteCertified : LeiosState → EndorserBlock → Type
isVoteCertified s eb = isVoteCertified' (LeiosState.votingState s) (0F , eb)
```
```agda
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
toProposeEB s π = let open LeiosState s in case ToPropose of λ where
  []      → nothing
  (_ ∷ _) → just $ mkEB slot id π sk-IB ToPropose [] []

getCurrentEBHash : LeiosState → Maybe EBRef
getCurrentEBHash s = let open LeiosState s in
  RankingBlock.announcedEB currentRB

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
          ∙ toProposeEB s (lotteryPf eb) ≡ just eb
          ∙ canProduceEB slot sk-EB (stake s) (lotteryPf eb)
          ─────────────────────────────────────────────────────────────────────────
          s ↝ (addUpkeep s EB-Role , Send (ebHeader eb) nothing)
```
```agda
  VT-Role : ∀ {ebHash slot'} → let open LeiosState s in
          ∙ getCurrentEBHash s ≡ just ebHash
          ∙ find (λ (_ , eb') → hash eb' ≟ ebHash) EBs' ≡ just (slot' , eb)
--          ∙ isValid s (inj₁ (ebHeader eb))
          ∙ slot' ≤ slotNumber eb + Lvote
          ∙ needsUpkeep VT-Role
          ∙ canProduceV slot sk-VT (stake s)
          ─────────────────────────────────────────────────────────────────────────
          s ↝ (addUpkeep s VT-Role , Send (vtHeader [ vote sk-VT ebHash ]) nothing)
```
Predicate needed for slot transition.
```agda
allDone : LeiosState → Type
allDone record { Upkeep = u } = u ≡ᵉ fromList (EB-Role ∷ Base ∷ [])
```
### Linear Leios transitions
The relation describing the transition given input and state
#### Initialization
```agda
open Types params

data _⊢_ : VTy → LeiosState → Type where
  Init :
       ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-VT / K.PUBKEYS pks ⟧⇀ ks'
       ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs' -- TODO: replace this line
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
        ────────────────────────────────────────────────────────────────────────────────────
        s -⟦ honestOutputI (rcvˡ (-, FFD-OUT msgs)) / honestInputO' (sndʳ (-, FTCH-LDG)) ⟧⇀ record s
            { slot         = suc slot
            ; Upkeep       = ∅
            } ↑ L.filter (isValid? s) msgs

  Slot₂ : let open LeiosState s in
        ──────────────────────────────────────────────────────────────────────────────
        s -⟦ honestOutputI (rcvʳ (-, BASE-LDG rbs)) / nothing ⟧⇀ record s { RBs = rbs }
```
```agda
  Ftch : let open LeiosState s in
       ─────────────────────────────────────────────────────────────────────────────────────
       s -⟦ honestInputI (-, FetchLdgI) / honestOutputO' (-, FetchLdgO Ledger) ⟧⇀ s
```
#### Base chain

Note: Submitted data to the base chain is only taken into account
      if the party submitting is the block producer on the base chain
      for the given slot
```agda
  Base₁   :
          ──────────────────────────────────────────────────────────────────────────────
          s -⟦ honestInputI (-, SubmitTxs txs) / nothing ⟧⇀ record s { ToPropose = txs }
```
```agda
  Base₂   : let open LeiosState s
                currentCertEB = find (λ (eb , _) → ¿ just (hash eb) ≡ getCurrentEBHash s × slotNumber eb + Lvote + Ldiff ≤ slot ¿) (ebsWithCert fzero)
                rb = record
                       { txs = [] -- TODO: we don't have block sizes ATM, so for the moment we put all transactions here
                       ; announcedEB = hash <$> toProposeEB s π
                       ; ebCert = proj₂ <$> currentCertEB }
          in
          ∙ needsUpkeep Base
          ───────────────────────────────────────────────────────────────────────────────────
          s -⟦ honestOutputI (rcvˡ (-, SLOT)) / honestInputO' (sndʳ (-, SUBMIT rb)) ⟧⇀
            addUpkeep s Base
```
#### Protocol rules
```agda
  Roles₁ :
         ∙ s ↝ (s' , i)
         ──────────────────────────────────────────────────────────────────────────────
         s -⟦ honestOutputI (rcvˡ (-, SLOT)) / honestInputO' (sndˡ (-, FFD-IN i)) ⟧⇀ s'

{-
  Roles₂ :
         ∙ s ↝ (s' , nothing)
         ───────────────────────────────────────────────────
         s -⟦ honestOutputI (rcvˡ (-, SLOT)) / nothing ⟧⇀ s'
-}

  Roles₃ : ∀ {x u} → let open LeiosState s in
         ∙ ¬ (s ↝ (addUpkeep s u , x))
         ∙ needsUpkeep u
         ∙ u ≢ Base
         ───────────────────────────────────────────────────
         s -⟦ honestOutputI (rcvˡ (-, SLOT)) / nothing ⟧⇀ addUpkeep s u
```
<!--
```agda
ShortLeios : Machine (FFD ⊗ BaseC) (IO ⊗ Adv)
ShortLeios .Machine.State = LeiosState
ShortLeios .Machine.stepRel = _-⟦_/_⟧⇀_

open import GenPremises

{-
instance
  Dec-isValid : ∀ {s x} → isValid s x ⁇
  Dec-isValid {s} {x} .dec = isValid? s x
-}

unquoteDecl EB-Role-premises = genPremises EB-Role-premises (quote _↝_.EB-Role)
unquoteDecl VT-Role-premises = genPremises VT-Role-premises (quote _↝_.VT-Role)

unquoteDecl Slot₁-premises = genPremises Slot₁-premises (quote Slot₁)
unquoteDecl Slot₂-premises = genPremises Slot₂-premises (quote Slot₂)
unquoteDecl Base₁-premises = genPremises Base₁-premises (quote Base₁)
unquoteDecl Base₂-premises = genPremises Base₂-premises (quote Base₂)

just≢nothing : ∀ {ℓ} {A : Type ℓ} {x} → (Maybe A ∋ just x) ≡ nothing → ⊥
just≢nothing = λ ()

P : EBRef → ℕ × EndorserBlock → Type
P h (_ , eb) = hash eb ≡ h

P? : (h : EBRef) → ((s , eb) : ℕ × EndorserBlock) → Dec (P h (s , eb))
P? h (_ , eb) = hash eb ≟ h

found : LeiosState → EndorserBlock → ℕ → EBRef → Type
found s eb slot' k = find (P? k) (LeiosState.EBs' s) ≡ just (slot' , eb)

not-found : LeiosState → EBRef → Type
not-found s k = find (P? k) (LeiosState.EBs' s) ≡ nothing

open import Data.List.Properties

open Equivalence
open import Axiom.Set.Properties th

singleton-injective : ∀ {X : Type} {u₁ u₂ : X} → ❴ u₁ ❵ ≡ ❴ u₂ ❵ → u₁ ≡ u₂
singleton-injective {X} {u₁} {u₂} eq =
  let s = subst (u₁ ∈ˢ_) eq $ to ∈-singleton refl
  in from ∈-singleton s
  where
    open import Axiom.Set using (Theory)
    open Theory th renaming (_∈_ to _∈ˢ_) using ()

≡→≡ᵉ : ∀ {X : Type} → {A B : ℙ X} → A ≡ B → A ≡ᵉ B
≡→≡ᵉ refl = (λ z → z) , (λ z → z)

postulate
  ∪-injective'' : ∀ {X : Type} {l : ℙ X} {u₁ u₂ : X} → l ∪ ❴ u₁ ❵ ≡ᵉ l ∪ ❴ u₂ ❵ → u₁ ≡ u₂
-- ∪-injective'' {X} {l} {u₁} {u₂} x = {!!}

addUpkeep-injective' : ∀ {u₁ u₂}
  → addUpkeep s u₁ ≡ addUpkeep s u₂
  → (LeiosState.Upkeep s) ∪ ❴ u₁ ❵ ≡ᵉ (LeiosState.Upkeep s) ∪ ❴ u₂ ❵
addUpkeep-injective' = ≡→≡ᵉ ∘ cong LeiosState.Upkeep

addUpkeep-injective : ∀ {u₁ u₂} → addUpkeep s u₁ ≡ addUpkeep s u₂ → u₁ ≡ u₂
addUpkeep-injective = ∪-injective'' ∘ addUpkeep-injective'

s'≢addUpkeep-Base : ∀ {o} → s ↝ (s' , o) → s' ≢ addUpkeep s Base
s'≢addUpkeep-Base (EB-Role (_ , _)) = EB-Role≢Base ∘ addUpkeep-injective
  where
    EB-Role≢Base : EB-Role ≢ Base
    EB-Role≢Base = λ ()
s'≢addUpkeep-Base (VT-Role (_ , _)) = VT-Role≢Base ∘ addUpkeep-injective
  where
    VT-Role≢Base : VT-Role ≢ Base
    VT-Role≢Base = λ ()

VT-Role≢EB-Role : SlotUpkeep.VT-Role ≢ SlotUpkeep.EB-Role
VT-Role≢EB-Role = λ ()

vtHeader→s'≢addUpkeep-EB-Role : ∀ {s} {s'} {vts}
  → s ↝ (s' , Send (vtHeader vts) nothing)
  → s' ≢ addUpkeep s EB-Role
vtHeader→s'≢addUpkeep-EB-Role (VT-Role (_ , _)) = VT-Role≢EB-Role ∘ addUpkeep-injective

ebHeader→s'≡addUpkeep-EB-Role :
    s ↝ (s' , Send (ebHeader eb) nothing)
  → s' ≡ addUpkeep s EB-Role
ebHeader→s'≡addUpkeep-EB-Role (EB-Role (_ , _)) = refl

instance
  Dec-↝ : ∀ {s u o} → (s ↝ (addUpkeep s u , o)) ⁇
  Dec-↝ {s} {u} {Send (ibHeader _) nothing} .dec = no λ ()
  Dec-↝ {s} {EB-Role} {Send (ebHeader _) nothing} .dec
    with ¿ EB-Role-premises .proj₁ ¿
  ... | yes p = yes (EB-Role p)
  ... | no ¬p = no λ where
    (EB-Role p) → ¬p p
  Dec-↝ {s} {u} {Send (vtHeader []) nothing} .dec = no λ ()
  Dec-↝ {s} {VT-Role} {Send (vtHeader (vt ∷ [])) nothing} .dec
    with getCurrentEBHash s in eq₁
  ... | nothing = no λ where
    (VT-Role (x , _ , _ , _ , _)) → just≢nothing $ trans (sym x) eq₁
  ... | just h
    with find (λ (_ , eb') → hash eb' ≟ h) (LeiosState.EBs' s) in eq₂
  ... | nothing = no λ where
    (VT-Role (x , y , _ , _ , _)) →
      let ji = just-injective (trans (sym x) eq₁)
      in just≢nothing $ trans (sym y) (subst (not-found s) (sym ji) eq₂)
  ... | just (slot' , eb)
    with ¿ slot' ≤ slotNumber eb + Lvote ¿
  ... | no ¬p
      = no λ where
           (VT-Role {s} {ebHash = ebHash} (x , y , z , _ , _)) →
              let ji = just-injective (trans (sym x) eq₁)
                  js = subst (found s eb slot') (sym ji) eq₂
                  (x₁ , x₂) = ,-injective (just-injective (trans (sym y) js))
              in ¬p $ subst₂ (λ a b → a ≤ slotNumber b + Lvote) x₁ x₂ z
  ... | yes a
    with ¿ LeiosState.needsUpkeep s VT-Role ¿
  ... | no ¬p = no λ where
    (VT-Role (_ , _ , _ , p , _)) → ¬p p
  ... | yes b
    with ¿ canProduceV (LeiosState.slot s) sk-VT (stake s) ¿
  ... | no ¬p = no λ where
    (VT-Role (a , b , _ , _ , p)) → ¬p p
  ... | yes c
    with vt ≟ vote sk-VT h
  ... | no ¬q = no λ where
    (VT-Role {s} {ebHash} (x , _ , _ , _ , _)) →
      let ji = just-injective (trans (sym x) eq₁)
      in ¬q $ cong (vote sk-VT) ji
  ... | yes q rewrite q = yes (VT-Role (eq₁ , eq₂ , a , b , c))
  Dec-↝ {s} {Base} {Send (ebHeader _) nothing} .dec = no (flip s'≢addUpkeep-Base refl)
  Dec-↝ {s} {Base} {Send (vtHeader (_ ∷ _)) nothing} .dec = no (flip s'≢addUpkeep-Base refl)
  Dec-↝ {s} {EB-Role} {Send (vtHeader _) nothing} .dec = no (flip vtHeader→s'≢addUpkeep-EB-Role refl)
  Dec-↝ {s} {VT-Role} {Send (ebHeader _) nothing} .dec = no (VT-Role≢EB-Role ∘ addUpkeep-injective ∘ ebHeader→s'≡addUpkeep-EB-Role)
  Dec-↝ {s} {VT-Role} {Send (vtHeader (_ ∷ _ ∷ _)) nothing} .dec = no λ ()
  Dec-↝ {s} {u} {Send x (just y)} .dec = no λ ()
  Dec-↝ {s} {u} {Fetch} .dec = no λ ()

unquoteDecl Roles₃-premises = genPremises Roles₃-premises (quote Roles₃)
```
--!>
