open import Leios.Prelude hiding (id; _>>=_; return)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_)

module Leios.Linear.Trace.Verifier (params : Params) where

-- SpecStructure is not a module parameter, as the type for VrfPf needs to be known
open import Leios.Defaults params using (isb; hpe; d-SpecStructure) public
open SpecStructure d-SpecStructure hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified) public

module Defaults
  (Lhdr Lvote Ldiff : ℕ)
  (splitTxs : List Tx → List Tx × List Tx)
  (validityCheckTime : EndorserBlock → ℕ)
  where

  open import Leios.Linear d-SpecStructure params Lhdr Lvote Ldiff splitTxs validityCheckTime public
  open GenFFD
  open Types params

  data Action : Type where
    EB-Role-Action    : ℕ → EndorserBlock → Action
    VT-Role-Action    : ℕ → EndorserBlock → Action
    Ftch-Action       : ℕ → Action
    Slot₁-Action      : ℕ → Action
    Slot₂-Action      : ℕ → Action
    Base₁-Action      : ℕ → Action
    Base₂-Action      : ℕ → Action
    No-EB-Role-Action : ℕ → Action
    No-VT-Role-Action : ℕ → Action

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

  open LeiosState

  getAction : ∀ {i o} → s -⟦ i / o ⟧⇀ s′ → Action
  getAction (Slot₁ {s} _)                      = Slot₁-Action (slot s)
  getAction (Slot₂ {s})                        = Slot₂-Action (slot s)
  getAction (Ftch {s})                         = Ftch-Action (slot s)
  getAction (Base₁ {s})                        = Base₁-Action (slot s)
  getAction (Base₂ {s} _)                      = Base₂-Action (slot s)
  getAction (Roles₁ (VT-Role {s} {eb = eb} _)) = VT-Role-Action (slot s) eb
  getAction (Roles₁ (EB-Role {s} {eb = eb} _)) = EB-Role-Action (slot s) eb
  getAction (Roles₂ {u = Base} (_ , x))        = ⊥-elim (x refl)
  getAction (Roles₂ {s} {u = EB-Role} _)       = No-EB-Role-Action (slot s)
  getAction (Roles₂ {s} {u = VT-Role} _)       = No-VT-Role-Action (slot s)

  getSlot : Action → ℕ
  getSlot (EB-Role-Action x _) = x
  getSlot (VT-Role-Action x _) = x
  getSlot (No-EB-Role-Action x) = x
  getSlot (No-VT-Role-Action x) = x
  getSlot (Ftch-Action x) = x
  getSlot (Slot₁-Action x) = x
  getSlot (Slot₂-Action x) = x
  getSlot (Base₁-Action x) = x
  getSlot (Base₂-Action x) = x


  data Err-verifyAction (σ : Action) (i : FFDT Out ⊎ BaseT Out ⊎ IOT In) (s : LeiosState) : Type where
    E-Err-Slot : getSlot σ ≢ slot s → Err-verifyAction σ i s
    E-Err-CanProduceIB : (∀ π → ¬ canProduceIB (slot s) sk-IB (stake s) π) → Err-verifyAction σ i s
    dummyErr : Err-verifyAction σ i s

  -- NOTE: this goes backwards, from the current state to the initial state
  data _—→_ : LeiosState → LeiosState → Type where

    ActionStep : ∀ {s i o s′} →
      ∙ s -⟦ i / o ⟧⇀ s′
        ───────────────────
        s′ —→ s

  open import Prelude.Closures _—→_

  infix 0 _≈_ _≈¹_

  data _≈¹_ : Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In) → s′ —→ s → Type where

    FromAction¹ :
      ∀ i {s′ o}
        → (σ : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
        → (getAction σ , inj₁ i) ≈¹ ActionStep σ

    FromAction² :
      ∀ i {s′ o}
        → (σ : s -⟦ honestOutputI (rcvʳ (-, i)) / o ⟧⇀ s′)
        → (getAction σ , inj₂ (inj₁ i)) ≈¹ ActionStep σ

    FromAction³ :
      ∀ i {s′ o}
        → (σ : s -⟦ honestInputI (-, i) / o ⟧⇀ s′)
        → (getAction σ , inj₂ (inj₂ i)) ≈¹ ActionStep σ

  data ValidStep (es : Action × (FFDT Out ⊎ BaseT Out ⊎ IOT In)) (s : LeiosState) : Type where
    Valid : (tr : s′ —→ s) → es ≈¹ tr → ValidStep es s

  data _≈_ : TestTrace → s′ —↠ s → Type where

    FromAction-FFD :
      ∀ i {σs s′ s₀ o} {tr : s —↠ s₀}
        → σs ≈ tr
        → (σ : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
        → (getAction σ , inj₁ i) ∷ σs ≈ s′ —→⟨ ActionStep σ ⟩ tr

    FromAction-Base :
      ∀ i {σs s′ s₀ o} {tr : s —↠ s₀}
        → σs ≈ tr
        → (σ : s -⟦ honestOutputI (rcvʳ (-, i)) / o ⟧⇀ s′)
        → (getAction σ , inj₂ (inj₁ i)) ∷ σs ≈ s′ —→⟨ ActionStep σ ⟩ tr

    FromAction-IO :
      ∀ i {σs s′ s₀ o} {tr : s —↠ s₀}
        → σs ≈ tr
        → (σ : s -⟦ honestInputI (-, i) / o ⟧⇀ s′)
        → (getAction σ , inj₂ (inj₂ i)) ∷ σs ≈ s′ —→⟨ ActionStep σ ⟩ tr

    Done : [] ≈ s ∎

  data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
    Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s

  getNewState : ∀ {es s} → ValidTrace es s → LeiosState
  getNewState (Valid {s′ = s} _ _) = s

  data Err-verifyTrace : TestTrace → LeiosState → Type where
    Err-StepOk   : Err-verifyTrace σs s → Err-verifyTrace ((σ , i) ∷ σs) s
    Err-Action   : Err-verifyAction σ i s′ → Err-verifyTrace ((σ , i) ∷ σs) s

  Ok' : ∀ {s i o s′} → (σ : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
      → Result (Err-verifyAction (getAction σ) (inj₁ i) s) (ValidStep (getAction σ , inj₁ i) s)
  Ok' a = Ok (Valid _ (FromAction¹ _ a))

  Ok'' : ∀ {s i o s′} → (σ : s -⟦ honestOutputI (rcvʳ (-, i)) / o ⟧⇀ s′)
      → Result (Err-verifyAction (getAction σ) (inj₂ (inj₁ i)) s) (ValidStep (getAction σ , inj₂ (inj₁ i)) s)
  Ok'' a = Ok (Valid _ (FromAction² _ a))

  Ok''' : ∀ {s i o s′} → (σ : s -⟦ honestInputI (-, i) / o ⟧⇀ s′)
    → Result (Err-verifyAction (getAction σ) (inj₂ (inj₂ i)) s) (ValidStep (getAction σ , inj₂ (inj₂ i)) s)
  Ok''' a = Ok (Valid _ (FromAction³ _ a))

  open import Relation.Nullary.Negation

  verifyStep' : (a : Action) → (i : FFDT Out ⊎ BaseT Out ⊎ IOT In) → (s : LeiosState) → getSlot a ≡ slot s
              → Result (Err-verifyAction a i s) (ValidStep (a , i) s)
  verifyStep' (EB-Role-Action n ebs) (inj₁ SLOT) s refl with ¿ EB-Role-premises {s = s} .proj₁ ¿
  ... | yes h = Ok' (Roles₁ (EB-Role h))
  ... | _ = Err dummyErr
  verifyStep' (EB-Role-Action _ _) (inj₁ FTCH) _ _ = Err dummyErr
  verifyStep' (EB-Role-Action _ _) (inj₁ (FFD-OUT _)) _ _ = Err dummyErr
  verifyStep' (VT-Role-Action n eb) (inj₁ SLOT) s refl with ¿ VT-Role-premises {s = s} {ebHash = hash eb} .proj₁ ¿
  ... | yes h = Ok' (Roles₁ (VT-Role {slot' = n} h))
  ... | no ¬h = Err dummyErr
  verifyStep' (VT-Role-Action _ _) (inj₁ FTCH) _ _ = Err dummyErr
  verifyStep' (VT-Role-Action _ _) (inj₁ (FFD-OUT eb)) _ _ = Err dummyErr

  -- This has a different IO pattern, not sure if we want to model that here
  -- For now we'll just fail
  verifyStep' (Ftch-Action n) _ _ _ = Err dummyErr

  verifyStep' (Slot₁-Action n) (inj₁ SLOT) _ _ = Err dummyErr
  verifyStep' (Slot₁-Action n) (inj₁ FTCH) _ _ = Err dummyErr
  verifyStep' (Slot₁-Action n) (inj₁ (FFD-OUT msgs)) s refl with ¿ Slot₁-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Slot₁ p)
  ... | no _ = Err dummyErr
  verifyStep' (Slot₂-Action n) (inj₁ _) _ _ = Err dummyErr
  verifyStep' (Slot₂-Action n) (inj₂ (inj₁ (BASE-LDG rbs))) s refl = Ok'' Slot₂

  -- Different IO pattern again
  verifyStep' (Base₁-Action n) (inj₂ (inj₂ (SubmitTxs txs))) s refl = Ok''' Base₁
  verifyStep' (Base₂-Action n) (inj₁ SLOT) s refl with ¿ Base₂-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Base₂ p)
  ... | no _ = Err dummyErr
  verifyStep' (Base₂-Action n) _ s refl = Err dummyErr
  verifyStep' (No-EB-Role-Action n) (inj₁ SLOT) s refl
    with ¿ needsUpkeep s EB-Role × (∀ π → ¬ canProduceEB (slot s) (EB , tt) (stake s) π) ¿
  ... | yes p = Ok' (Roles₂ {s' = addUpkeep s EB-Role} {u = EB-Role} ((No-EB-Role p , λ () )))
  ... | no ¬p = Err dummyErr
  verifyStep' (No-EB-Role-Action n) _ s refl = Err dummyErr
  verifyStep' (No-VT-Role-Action n) (inj₁ SLOT) s refl
    with ¿ No-VT-Role-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Roles₂ {s' = addUpkeep s VT-Role} {u = VT-Role} (No-VT-Role p , λ ()))
  ... | no ¬p = Err dummyErr
  verifyStep' (No-VT-Role-Action n) _ s refl = Err dummyErr
  verifyStep' (EB-Role-Action .(slot s) x) (inj₂ y) s refl = Err dummyErr
  verifyStep' (VT-Role-Action .(slot s) x) (inj₂ y) s refl = Err dummyErr
  verifyStep' (Slot₁-Action x₁) (inj₂ y) s x = Err dummyErr
  verifyStep' (Base₁-Action .(slot s)) (inj₁ x) s refl = Err dummyErr
  verifyStep' (Base₁-Action .(slot s)) (inj₂ y) s refl = Err dummyErr
  verifyStep' (Slot₂-Action .(slot s)) (inj₂ (inj₂ y)) s refl = Err dummyErr

  verifyStep : (a : Action) → (i : FFDT Out ⊎ BaseT Out ⊎ IOT In) → (s : LeiosState) → Result (Err-verifyAction a i s) (ValidStep (a , i) s)
  verifyStep a i s = case getSlot a ≟ slot s of λ where
    (yes p) → verifyStep' a i s p
    (no ¬p) → Err (E-Err-Slot λ p → ⊥-elim (¬p p))

  verifyTrace : ∀ (σs : TestTrace) → (s : LeiosState) → Result (Err-verifyTrace σs s) (ValidTrace σs s)
  verifyTrace [] s = Ok (Valid (s ∎) Done)
  verifyTrace ((a , i) ∷ σs) s = do
    σs ← mapErr Err-StepOk (verifyTrace σs s)
    x  ← mapErr Err-Action (verifyStep a i (getNewState σs))
    return (σs Valid∷ʳ x)
    where
      open Monad-Result
      _Valid∷ʳ_ : ∀ {e es s} → (σs : ValidTrace es s) → ValidStep e (getNewState σs) → ValidTrace (e ∷ es) s
      Valid tr x Valid∷ʳ Valid (ActionStep as) (FromAction¹ a _) = Valid (_ —→⟨ ActionStep as ⟩ tr) (FromAction-FFD a x as)
      Valid tr x Valid∷ʳ Valid (ActionStep as) (FromAction² a _) = Valid (_ —→⟨ ActionStep as ⟩ tr) (FromAction-Base a x as)
      Valid tr x Valid∷ʳ Valid (ActionStep as) (FromAction³ a _) = Valid (_ —→⟨ ActionStep as ⟩ tr) (FromAction-IO a x as)
