open import Leios.Prelude hiding (id; _>>=_; return)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_)

open import Data.List.Properties
open import Data.Maybe.Properties
open import Data.Product.Properties

module Leios.Linear.Trace.Verifier (params : Params) where

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
  getAction (Roles₁ (VT-Role {s} {eb = eb} {slot' = slot'} _)) = VT-Role-Action (slot s) eb slot'
  getAction (Roles₁ (EB-Role {s} {eb = eb} _)) = EB-Role-Action (slot s) eb
  getAction (Roles₂ {u = Base} (_ , _ , x))    = ⊥-elim (x refl)
  getAction (Roles₂ {s} {u = EB-Role} _)       = No-EB-Role-Action (slot s)
  getAction (Roles₂ {s} {u = VT-Role} _)       = No-VT-Role-Action (slot s)

  getSlot : Action → ℕ
  getSlot (EB-Role-Action x _) = x
  getSlot (VT-Role-Action x _ _) = x
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

  just≢nothing : ∀ {ℓ} {A : Type ℓ} {x} → (Maybe A ∋ just x) ≡ nothing → ⊥
  just≢nothing = λ ()

  nothing≢just : ∀ {ℓ} {A : Type ℓ} {x} → nothing ≡ (Maybe A ∋ just x) → ⊥
  nothing≢just = λ ()

  P : EBRef → ℕ × EndorserBlock → Type
  P h (_ , eb) = hash eb ≡ h

  P? : (h : EBRef) → ((s , eb) : ℕ × EndorserBlock) → Dec (P h (s , eb))
  P? h (_ , eb) = hash eb ≟ h

  found : LeiosState → EndorserBlock → ℕ → EBRef → Type
  found s eb slot' k = find (P? k) (LeiosState.EBs' s) ≡ just (slot' , eb)

  not-found : LeiosState → EBRef → Type
  not-found s k = find (P? k) (LeiosState.EBs' s) ≡ nothing

  subst' : ∀ {s ebHash ebHash₁ slot' slot'' eb eb₁}
    → getCurrentEBHash s ≡ just ebHash₁
    → find (λ (_ , eb') → hash eb' ≟ ebHash₁) (LeiosState.EBs' s) ≡ just (slot'' , eb₁)
    → getCurrentEBHash s ≡ just ebHash
    → find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) ≡ just (slot' , eb)
    → slot'' ≡ slot' × eb₁ ≡ eb
  subst' {s} {slot' = slot'} {eb = eb} x y eq₂ eq₃ =
    let ji = just-injective (trans (sym x) eq₂)
        js = subst (found s eb slot') (sym ji) eq₃
    in ,-injective (just-injective (trans (sym y) js))

  Base≢EB-Role : SlotUpkeep.Base ≢ SlotUpkeep.EB-Role
  Base≢EB-Role = λ ()

  Base≢VT-Role : SlotUpkeep.Base ≢ SlotUpkeep.VT-Role
  Base≢VT-Role = λ ()

  instance
    Dec-↝ : ∀ {s} {u : SlotUpkeep} → (∃[ s'×i ] (s ↝ s'×i × (u ∷ LeiosState.Upkeep s) ≡ LeiosState.Upkeep (proj₁ s'×i))) ⁇
    Dec-↝ {s} {EB-Role} .dec
      with toProposeEB s _ in eq₁
    ... | nothing = no λ where
      (_ , EB-Role (p , _) , _) → nothing≢just (trans (sym eq₁) p)
    ... | just eb
      with ¿ canProduceEB (LeiosState.slot s) sk-EB (stake s) _ ¿
    ... | yes q = yes ((_ , _) , EB-Role (eq₁ , q) , refl)
    ... | no ¬q = no λ where
      (_ , EB-Role (_ , q) , _) → ¬q q
    Dec-↝ {s} {VT-Role} .dec
      with getCurrentEBHash s in eq₂
    ... | nothing = no λ where
      (_ , VT-Role (p , _) , _) → nothing≢just (trans (sym eq₂) p)
    ... | just ebHash
      with find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) in eq₃
    ... | nothing = no λ where
      (_ , VT-Role (x , y , _) , _) →
        let ji = just-injective (trans (sym x) eq₂)
        in just≢nothing $ trans (sym y) (subst (not-found s) (sym ji) eq₃)
    ... | just (slot' , eb)
      with ¿ hash eb ∉ (LeiosState.VotedEBs s) ¿
    ... | no ¬p = no λ where
      (_ , VT-Role (x , y , p , _) , _) → ¬p $ subst (λ b → hash (EndorserBlock ∋ b) ∉ LeiosState.VotedEBs s) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes p
      with ¿ ¬ isEquivocated s eb ¿
    ... | no ¬a = no λ where
      (_ , VT-Role (x , y , _ , p , _) , _) → ¬a $ subst (λ b → ¬ isEquivocated s b) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes a
      with isValid? s (inj₁ (ebHeader eb))
    ... | no ¬b = no λ where
      (_ , VT-Role (x , y , _ , _ , p , _) , _) → ¬b $ subst (λ b → isValid s (inj₁ (ebHeader b))) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes b
      with ¿ slot' ≤ slotNumber eb + Lhdr ¿
    ... | no ¬c = no λ where
      (_ , VT-Role (x , y , _ , _ , _ , p , _ ) , _) → let (x₁ , x₂) = subst' {s} x y eq₂ eq₃ in ¬c $ subst₂ (λ a b → a ≤ slotNumber b + Lhdr) x₁ x₂ p
    ... | yes c
      with ¿ slotNumber eb + 3 * Lhdr ≤ LeiosState.slot s ¿
    ... | no ¬d = no λ where
      (_ , VT-Role (x , y , _ , _ , _ , _ , p , _) , _) → ¬d $ subst (λ b → slotNumber b + 3 * Lhdr ≤ LeiosState.slot s) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes d
      with ¿ LeiosState.slot s ≡ slotNumber eb + validityCheckTime eb ¿
    ... | no ¬e = no λ where
      (_ , VT-Role (x , y , _ , _ , _ , _ , _ , p , _) , _) → ¬e $ subst (λ b → LeiosState.slot s ≡ slotNumber b + validityCheckTime b) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes e
      with ¿ validityCheckTime eb ≤ 3 * Lhdr + Lvote ¿
    ... | no ¬f = no λ where
      (_ , VT-Role (x , y , _ , _ , _ , _ , _ , _ , p , _) , _) → ¬f $ subst (λ b → validityCheckTime b ≤ 3 * Lhdr + Lvote) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes f
      with ¿ EndorserBlockOSig.txs eb ≢ [] ¿
    ... | no ¬g = no λ where
      (_ , VT-Role (x , y , _ , _ , _ , _ , _ , _ , _ , p , _ ) , _) → ¬g $ subst (λ b → EndorserBlockOSig.txs b ≢ []) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes g
      with ¿ needsUpkeep s VT-Role ¿
    ... | no ¬h = no λ where
      (_ , VT-Role (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , p , _) , _) → ¬h p
    ... | yes h
      with ¿ canProduceV (slotNumber eb) sk-VT (stake s) ¿
    ... | no ¬i = no λ where
      (_ , VT-Role (x , y , _ , _ , _ , _ , _ , _ , _ , _ , _ , p) , refl) → ¬i $ subst (λ b → canProduceV (slotNumber b) sk-VT (stake s)) (proj₂ $ subst' {s} x y eq₂ eq₃) p
    ... | yes i = yes ((rememberVote (addUpkeep s VT-Role) eb , Send (vtHeader [ vote sk-VT (hash eb) ]) nothing) ,
                       (VT-Role ((eq₂ , eq₃ , p , a , b , c , d , e , f , g , h , i))), refl)
    Dec-↝ {s} {Base} .dec = no λ where
      (_ , EB-Role _ , x) → Base≢EB-Role (∷-injectiveˡ (trans x refl))
      (_ , VT-Role _ , x) → Base≢VT-Role (∷-injectiveˡ (trans x refl))

  open import Prelude.STS.GenPremises
  unquoteDecl Roles₂-premises = genPremises Roles₂-premises (quote Roles₂)

  verifyStep' : (a : Action) → (i : FFDT Out ⊎ BaseT Out ⊎ IOT In) → (s : LeiosState) → getSlot a ≡ slot s
              → Result (Err-verifyAction a i s) (ValidStep (a , i) s)
  verifyStep' (EB-Role-Action n ebs) (inj₁ SLOT) s refl
    with ¿ EB-Role-premises {s = s} .proj₁ ¿
  ... | yes h = Ok' (Roles₁ (EB-Role h))
  ... | _ = Err dummyErr
  verifyStep' (EB-Role-Action _ _) (inj₁ FTCH) _ _ = Err dummyErr
  verifyStep' (EB-Role-Action _ _) (inj₁ (FFD-OUT _)) _ _ = Err dummyErr
  verifyStep' (VT-Role-Action .(slot s) eb slot') (inj₁ SLOT) s refl
    with ¿ VT-Role-premises {s = s} {eb = eb} {ebHash = hash eb} {slot' = slot'} .proj₁ ¿
       | isValid? s (inj₁ (ebHeader eb)) -- TODO:  why not covered above?
  ... | yes (x , x₁ , x₂ , x₃ , x₄ , x₅ , x₆ , x₇ , x₈ , x₉ , x₁₀) | yes h = Ok' (Roles₁ (VT-Role {ebHash = hash eb} {slot' = slot'} ((x , x₁ , x₂ , x₃ , h , x₄ , x₅ , x₆ , x₇ , x₈ , x₉ , x₁₀))))
  ... | yes (x , x₁ , x₂ , x₃ , x₄ , x₅ , x₆ , x₇ , x₈ , x₉ , x₁₀) | no _ = Err dummyErr
  ... | no ¬h | _ = Err dummyErr
  verifyStep' (VT-Role-Action _ _ _) (inj₁ FTCH) _ _ = Err dummyErr
  verifyStep' (VT-Role-Action _ _ _) (inj₁ (FFD-OUT _)) _ _ = Err dummyErr
  verifyStep' (VT-Role-Action _ _ _) (inj₂ _) _ refl = Err dummyErr

  -- This has a different IO pattern, not sure if we want to model that here
  -- For now we'll just fail
  verifyStep' (Ftch-Action n) _ _ _ = Err dummyErr

  verifyStep' (Slot₁-Action n) (inj₁ SLOT) _ _ = Err dummyErr
  verifyStep' (Slot₁-Action n) (inj₁ FTCH) _ _ = Err dummyErr
  verifyStep' (Slot₁-Action n) (inj₁ (FFD-OUT msgs)) s refl with ¿ Slot₁-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Slot₁ {s = s} {msgs = msgs} p)
  ... | no _ = Err dummyErr
  verifyStep' (Slot₂-Action n) (inj₁ _) _ _ = Err dummyErr
  verifyStep' (Slot₂-Action n) (inj₂ (inj₁ (BASE-LDG rbs))) s refl = Ok'' (Slot₂ {s = s} {rbs = rbs})
  verifyStep' (Slot₂-Action n) (inj₂ (inj₂ y)) s refl = Err dummyErr

  -- Different IO pattern again
  verifyStep' (Base₁-Action n) (inj₂ (inj₂ (SubmitTxs txs))) s refl = Ok''' Base₁
  verifyStep' (Base₂-Action n) (inj₁ SLOT) s refl with ¿ Base₂-premises {s = s} .proj₁ ¿
  ... | yes p = Ok' (Base₂ p)
  ... | no _ = Err dummyErr
  verifyStep' (Base₂-Action n) _ s refl = Err dummyErr
  verifyStep' (No-EB-Role-Action n) (inj₁ SLOT) s refl
    with ¿ Roles₂-premises {s = s} {u = EB-Role} .proj₁ ¿
  ... | yes p = Ok' (Roles₂ p)
  ... | no ¬p = Err dummyErr
  verifyStep' (No-EB-Role-Action n) _ s refl = Err dummyErr
  verifyStep' (No-VT-Role-Action n) (inj₁ SLOT) s refl
    with ¿ Roles₂-premises {s = s} {u = VT-Role} .proj₁ ¿
  ... | yes p = Ok' (Roles₂ p)
  ... | no ¬p = Err dummyErr
  verifyStep' (No-VT-Role-Action n) _ s refl = Err dummyErr
  verifyStep' (EB-Role-Action .(slot s) x) (inj₂ y) s refl = Err dummyErr
  verifyStep' (Slot₁-Action x₁) (inj₂ y) s x = Err dummyErr
  verifyStep' (Base₁-Action .(slot s)) (inj₁ x) s refl = Err dummyErr
  verifyStep' (Base₁-Action .(slot s)) (inj₂ y) s refl = Err dummyErr

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
