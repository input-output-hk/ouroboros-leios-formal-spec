## Linear Leios Trace Verifier

```agda
open import Leios.Prelude hiding (id; _>>=_; return; _⊗_)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Channel.Selection

open import Data.List.Properties
open import Data.Maybe.Properties
open import Data.Product.Properties

module Leios.Linear.Trace.Verifier (params : Params) where

-- TODO: Use module parameters, do not depend on `Leios.Defaults`
-- SpecStructure is not a module parameter, as the type for VrfPf needs to be known
open import Leios.Defaults params using (d-SpecStructure; isb; hpe) public
open SpecStructure d-SpecStructure hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified) public

module Defaults
  (Lhdr Lvote Ldiff : ℕ)
  (splitTxs : List Tx → List Tx × List Tx)
  (validityCheckTime : EndorserBlock → ℕ)
  where

  open import Leios.Linear d-SpecStructure params Lhdr Lvote Ldiff splitTxs validityCheckTime public
  open FFD hiding (_-⟦_/_⟧⇀_)
  open GenFFD
  open Types params

  -- An `Action` provides input to the relational semantics
  data Action : Type where
    EB-Role-Action    : ℕ → EndorserBlock → Action
    VT-Role-Action    : ℕ → EndorserBlock → ℕ → Action
    Ftch-Action       : ℕ → Action
    Slot₁-Action      : ℕ → Action
    Slot₂-Action      : ℕ → Action
    Base₁-Action      : ℕ → Action
    Base₂-Action      : ℕ → Action
    No-EB-Role-Action : ℕ → Action
    No-VT-Role-Action : ℕ → Action

  -- A `TestTrace` is a list of actions togther with channels related to the other functionalities
  TestTrace = List (Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In))

  private variable
    s s′ : LeiosState
    σ    : Action
    σs   : TestTrace
    ib   : InputBlock
    eb   : EndorserBlock
    ebs  : List EndorserBlock
    vt   : List Vote
    i    : FFDT Out ⊎ BaseT Out ⊎ IOT In
    o    : FFDT In

  getAction : ∀ {i o} → s -⟦ i / o ⟧⇀ s′ → Action
  getAction (Slot₁ {s} _)                                      = Slot₁-Action (LeiosState.slot s)
  getAction (Slot₂ {s})                                        = Slot₂-Action (LeiosState.slot s)
  getAction (Ftch {s})                                         = Ftch-Action (LeiosState.slot s)
  getAction (Base₁ {s})                                        = Base₁-Action (LeiosState.slot s)
  getAction (Base₂ {s} _)                                      = Base₂-Action (LeiosState.slot s)
  getAction (Roles₁ (EB-Role {s} {eb = eb} _))                 = EB-Role-Action (LeiosState.slot s) eb
  getAction (Roles₁ (VT-Role {s} {eb = eb} {slot' = slot'} _)) = VT-Role-Action (LeiosState.slot s) eb slot'
  getAction (Roles₂ {u = Base} (_ , _ , x))                    = ⊥-elim (x refl) -- Roles₂ excludes the `Base` role
  getAction (Roles₂ {s} {u = EB-Role} _)                       = No-EB-Role-Action (LeiosState.slot s)
  getAction (Roles₂ {s} {u = VT-Role} _)                       = No-VT-Role-Action (LeiosState.slot s)

  getSlot : Action → ℕ
  getSlot (EB-Role-Action x _)   = x
  getSlot (VT-Role-Action x _ _) = x
  getSlot (No-EB-Role-Action x)  = x
  getSlot (No-VT-Role-Action x)  = x
  getSlot (Ftch-Action x)        = x
  getSlot (Slot₁-Action x)       = x
  getSlot (Slot₂-Action x)       = x
  getSlot (Base₁-Action x)       = x
  getSlot (Base₂-Action x)       = x

  -- NOTE: this goes backwards, from the current state to the initial state
  data _—→_ : LeiosState → LeiosState → Type where

    ActionStep : ∀ {s i o s′} →
      ∙ s -⟦ i / o ⟧⇀ s′
        ───────────────────
        s′ —→ s

  open import Prelude.Closures _—→_

  toRcvType : FFDT Out ⊎ BaseT Out ⊎ IOT In → Channel.inType ((FFD ⊗ BaseC) ⊗ ((IO ⊗ Adv) ᵀ))
  toRcvType (inj₁ i) = (ϵ ⊗R) ⊗R ↑ᵢ i
  toRcvType (inj₂ (inj₁ i)) = (L⊗ ϵ) ⊗R ↑ᵢ i
  toRcvType (inj₂ (inj₂ i)) = L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ i

  infix 0 _≈_ _≈¹_

  data _≈¹_ : Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In) → s′ —→ s → Type where

    FromAction :
      ∀ i {s′ o}
        → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
        → (getAction σ , i) ≈¹ ActionStep σ

  data ValidStep (es : Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In)) (s : LeiosState) : Type where
    Valid : (tr : s′ —→ s) → es ≈¹ tr → ValidStep es s

  data _≈_ : TestTrace → s′ —↠ s → Type where

    FromAction :
      ∀ i {σs s′ s₀ o} {tr : s —↠ s₀}
        → σs ≈ tr
        → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
        → (getAction σ , i) ∷ σs ≈ s′ —→⟨ ActionStep σ ⟩ tr

    Done : [] ≈ s ∎

  data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
    Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s

  getNewState : ∀ {es s} → ValidTrace es s → LeiosState
  getNewState (Valid {s′ = s} _ _) = s

  -- Errors that occur when verifying a step
  data Err-verifyStep (σ : Action) (i : FFDT Out ⊎ BaseT Out ⊎ IOT In) (s : LeiosState) : Type where
    Err-Slot : getSlot σ ≢ LeiosState.slot s → Err-verifyStep σ i s
    Err-EB-Role-premises : ∀ {π} → ¬ (
      toProposeEB s π ≡ just eb ×
      canProduceEB (LeiosState.slot s) sk-EB (stake s) π) →
      Err-verifyStep σ i s
    Err-VT-Role-premises : ∀ {ebHash slot'} → let open LeiosState s in ¬ (
      getCurrentEBHash s ≡ just ebHash ×
      find (λ (_ , eb') → hash eb' ≟ ebHash) EBs' ≡ just (slot' , eb) ×
      hash eb ∉ VotedEBs ×
      ¬ isEquivocated s eb ×
      isValid s (inj₁ (ebHeader eb)) ×
      slot' ≤ slotNumber eb + Lhdr ×
      slotNumber eb + 3 * Lhdr ≤ slot ×
      slot ≡ slotNumber eb + validityCheckTime eb ×
      validityCheckTime eb ≤ 3 * Lhdr + Lvote ×
      EndorserBlockOSig.txs eb ≢ [] ×
      needsUpkeep VT-Role ×
      canProduceV (slotNumber eb) sk-VT (stake s)) →
      Err-verifyStep σ i s
    Err-AllDone : ¬ (allDone s) → Err-verifyStep σ i s
    Err-BaseUpkeep : ¬ (LeiosState.needsUpkeep s Base) → Err-verifyStep σ i s
    Err-Invalid : Err-verifyStep σ i s -- TODO: drop generic constructor

  -- Errors when verifying a trace
  data Err-verifyTrace : TestTrace → LeiosState → Type where
    Err-StepOk : Err-verifyTrace σs s → Err-verifyTrace ((σ , i) ∷ σs) s
    Err-Step   : Err-verifyStep σ i s′ → Err-verifyTrace ((σ , i) ∷ σs) s

  Ok' : ∀ {s i o s′} → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
      → Result (Err-verifyStep (getAction σ) i s) (ValidStep (getAction σ , i) s)
  Ok' a = Ok (Valid _ (FromAction _ a))

```
<!--
```agda
  -- TODO: Move code related to Roles₂-promises into a separate module `Leios.Linear.Premises`
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

  instance
    Dec-↝ : ∀ {s u} → (∃[ s'×i ] (s ↝ s'×i × (u ∷ LeiosState.Upkeep s) ≡ LeiosState.Upkeep (proj₁ s'×i))) ⁇
    Dec-↝ {s} {EB-Role} .dec
      with toProposeEB s _ in eq₁
    ... | nothing = no λ where (_ , EB-Role (p , _) , _) → nothing≢just (trans (sym eq₁) p)
    ... | just eb
      with ¿ canProduceEB (LeiosState.slot s) sk-EB (stake s) _ ¿
    ... | yes q = yes (_ , EB-Role (eq₁ , q) , refl)
    ... | no ¬q = no λ where (_ , EB-Role (_ , q) , _) → ¬q q
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

  open import Prelude.STS.GenPremises
  unquoteDecl Roles₂-premises = genPremises Roles₂-premises (quote Roles₂)
```
-->
```agda
  verifyStep' : (a : Action) →
    (i : FFDT Out ⊎ BaseT Out ⊎ IOT In) →
    (s : LeiosState) → getSlot a ≡ LeiosState.slot s →
    Result (Err-verifyStep a i s) (ValidStep (a , i) s)
  verifyStep' (EB-Role-Action n ebs) (inj₁ SLOT) s refl
    with ¿ EB-Role-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Roles₁ (EB-Role p))
  ... | no ¬p = Err (Err-EB-Role-premises ¬p)
  verifyStep' (EB-Role-Action _ _) (inj₁ FTCH) _ _        = Err Err-Invalid
  verifyStep' (EB-Role-Action _ _) (inj₁ (FFD-OUT _)) _ _ = Err Err-Invalid
  verifyStep' (EB-Role-Action _ _) (inj₂ _) _ _           = Err Err-Invalid
  verifyStep' (VT-Role-Action _ eb slot') (inj₁ SLOT) s refl
    with ¿ VT-Role-premises {s = s} {eb = eb} {ebHash = hash eb} {slot' = slot'} .proj₁ ¿
  ... | yes p = Ok' (Roles₁ (VT-Role {ebHash = hash eb} {slot' = slot'} p))
  ... | no ¬p = Err (Err-VT-Role-premises ¬p)
  verifyStep' (VT-Role-Action _ _ _) (inj₁ FTCH) _ _        = Err Err-Invalid
  verifyStep' (VT-Role-Action _ _ _) (inj₁ (FFD-OUT _)) _ _ = Err Err-Invalid
  verifyStep' (VT-Role-Action _ _ _) (inj₂ _) _ _           = Err Err-Invalid

  -- This has a different IO pattern, not sure if we want to model that here
  -- For now we'll just fail
  verifyStep' (Ftch-Action _) _ _ _ = Err Err-Invalid

  verifyStep' (Slot₁-Action _) (inj₁ SLOT) _ _ = Err Err-Invalid
  verifyStep' (Slot₁-Action _) (inj₁ FTCH) _ _ = Err Err-Invalid
  verifyStep' (Slot₁-Action _) (inj₁ (FFD-OUT msgs)) s refl
    with ¿ Slot₁-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Slot₁ {s = s} {msgs = msgs} p)
  ... | no ¬p = Err (Err-AllDone ¬p)
  verifyStep' (Slot₁-Action _) (inj₂ _) _ _        = Err Err-Invalid
  verifyStep' (Slot₂-Action _) (inj₁ _) _ _        = Err Err-Invalid
  verifyStep' (Slot₂-Action _) (inj₂ (inj₂ _)) _ _ = Err Err-Invalid
  verifyStep' (Slot₂-Action _) (inj₂ (inj₁ (BASE-LDG rbs))) s refl = Ok' Slot₂

  -- Different IO pattern again
  verifyStep' (Base₁-Action _) (inj₁ _) _ _                = Err Err-Invalid
  verifyStep' (Base₁-Action _) (inj₂ (inj₁ _)) _ _         = Err Err-Invalid
  verifyStep' (Base₁-Action _) (inj₂ (inj₂ FetchLdgI)) _ _ = Err Err-Invalid
  verifyStep' (Base₁-Action _) (inj₂ (inj₂ (SubmitTxs _))) _ refl = Ok' Base₁
  verifyStep' (Base₂-Action _) (inj₁ SLOT) s refl
    with ¿ Base₂-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Base₂ p)
  ... | no ¬p = Err (Err-BaseUpkeep ¬p)
  verifyStep' (Base₂-Action _) (inj₁ FTCH) _ _        = Err Err-Invalid
  verifyStep' (Base₂-Action _) (inj₁ (FFD-OUT _)) _ _ = Err Err-Invalid
  verifyStep' (Base₂-Action _) (inj₂ _) _ _           = Err Err-Invalid
  verifyStep' (No-EB-Role-Action _) (inj₁ SLOT) s refl
    with ¿ Roles₂-premises {s = s} {u = EB-Role} .proj₁ ¿
  ... | yes p = Ok' (Roles₂ p)
  ... | no ¬p = Err Err-Invalid -- FIXME: specific error message
  verifyStep' (No-EB-Role-Action _) (inj₁ FTCH) _ _        = Err Err-Invalid
  verifyStep' (No-EB-Role-Action _) (inj₁ (FFD-OUT _)) _ _ = Err Err-Invalid
  verifyStep' (No-EB-Role-Action _) (inj₂ _) _ _           = Err Err-Invalid
  verifyStep' (No-VT-Role-Action _) (inj₁ SLOT) s refl
    with ¿ Roles₂-premises {s = s} {u = VT-Role} .proj₁ ¿
  ... | yes p = Ok' (Roles₂ p)
  ... | no ¬p = Err Err-Invalid -- FIXME: specific error message
  verifyStep' (No-VT-Role-Action _) (inj₁ FTCH) _ _        = Err Err-Invalid
  verifyStep' (No-VT-Role-Action _) (inj₁ (FFD-OUT _)) _ _ = Err Err-Invalid
  verifyStep' (No-VT-Role-Action _) (inj₂ _) _ _           = Err Err-Invalid

  verifyStep : (a : Action) → (i : FFDT Out ⊎ BaseT Out ⊎ IOT In) → (s : LeiosState) → Result (Err-verifyStep a i s) (ValidStep (a , i) s)
  verifyStep a i s = case getSlot a ≟ LeiosState.slot s of λ where
    (yes p) → verifyStep' a i s p
    (no ¬p) → Err (Err-Slot λ p → ⊥-elim (¬p p))

  verifyTrace : ∀ (σs : TestTrace) → (s : LeiosState) → Result (Err-verifyTrace σs s) (ValidTrace σs s)
  verifyTrace [] s = Ok (Valid (s ∎) Done)
  verifyTrace ((a , i) ∷ σs) s = do
    σs ← mapErr Err-StepOk (verifyTrace σs s)
    x  ← mapErr Err-Step (verifyStep a i (getNewState σs))
    return (σs Valid∷ʳ x)
    where
      open Monad-Result
      _Valid∷ʳ_ : ∀ {e es s} → (σs : ValidTrace es s) → ValidStep e (getNewState σs) → ValidTrace (e ∷ es) s
      Valid tr x Valid∷ʳ Valid (ActionStep as) (FromAction a _) = Valid (_ —→⟨ ActionStep as ⟩ tr) (FromAction a x as)
```
