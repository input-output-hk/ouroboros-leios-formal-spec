open import Leios.Prelude hiding (id; _>>=_; return)
open import Leios.Config

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_)

-- TODO: SpecStructure as parameter
module Leios.Short.Trace.Verifier (params : Params) (let open Params params) where

open import Leios.Defaults params
  using (isb; hpe; hhs; htx; SendIB; FFDBuffers; Dec-SimpleFFD; sortition)
  renaming (d-SpecStructure to traceSpecStructure) public

open import Leios.SpecStructure using (SpecStructure)
open SpecStructure traceSpecStructure hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified) public

open import Leios.Short traceSpecStructure params public
open GenFFD

open Types params

data Action : Type where
  IB-Role-Action    : ℕ → Action
  EB-Role-Action    : ℕ → List IBRef → List EndorserBlock → Action
  VT-Role-Action    : ℕ → Action
  No-IB-Role-Action : ℕ → Action
  No-EB-Role-Action : ℕ → Action
  No-VT-Role-Action : ℕ → Action
  Ftch-Action       : ℕ → Action
  Slot-Action       : ℕ → Action
  Base₁-Action      : ℕ → Action
  Base₂a-Action     : ℕ → EndorserBlock → Action
  Base₂b-Action     : ℕ → Action

TestTrace = List (Action × FFDT Out)

private variable
  s s′ : LeiosState
  α    : Action
  αs   : TestTrace
  ib   : InputBlock
  eb   : EndorserBlock
  ebs  : List EndorserBlock
  vt   : List Vote
  i    : FFDT Out
  o    : FFDT In

open LeiosState
open FFDBuffers

getLabel : ∀ {i o} → s -⟦ i / o ⟧⇀ s′ → Action
getLabel (Slot₁ {s} _)                        = Slot-Action (slot s)
getLabel (Slot₂ {s})                          = Slot-Action (slot s)
getLabel (Ftch {s})                           = Ftch-Action (slot s)
getLabel (Base₁ {s})                          = Base₁-Action (slot s)
getLabel (Base₂a {s} {eb} (_ , _))            = Base₂a-Action (slot s) eb
getLabel (Base₂b {s} (_ , _))                 = Base₂b-Action (slot s)
getLabel (Roles₁ (IB-Role {s} _))             = IB-Role-Action (slot s)
getLabel (Roles₁ (EB-Role {s} {ebs} (_ , _ , _ , _))) =
  let ibs = L.filter (IBSelection? s Late-IB-Inclusion) (IBs s)
      LI  = map getIBRef ibs
  in EB-Role-Action (slot s) LI ebs
getLabel (Roles₁ (VT-Role {s} (_ , _)))       = VT-Role-Action (slot s)
getLabel (Roles₂ (No-IB-Role {s} (_ , _)))    = No-IB-Role-Action (slot s)
getLabel (Roles₂ (No-EB-Role {s} (_ , _)))    = No-EB-Role-Action (slot s)
getLabel (Roles₂ (No-VT-Role {s} (_ , _)))    = No-VT-Role-Action (slot s)

getSlot : Action → ℕ
getSlot (IB-Role-Action x) = x
getSlot (EB-Role-Action x _ _) = x
getSlot (VT-Role-Action x) = x
getSlot (No-IB-Role-Action x) = x
getSlot (No-EB-Role-Action x) = x
getSlot (No-VT-Role-Action x) = x
getSlot (Ftch-Action x) = x
getSlot (Slot-Action x) = x
getSlot (Base₁-Action x) = x
getSlot (Base₂a-Action x _) = x
getSlot (Base₂b-Action x) = x

data Err-verifyAction (α : Action) (i : FFDT Out) (s : LeiosState) : Type where
  E-Err-Slot : getSlot α ≢ slot s → Err-verifyAction α i s
  E-Err-CanProduceIB : (∀ π → ¬ canProduceIB (slot s) sk-IB (stake s) π) → Err-verifyAction α i s
  dummyErr : Err-verifyAction α i s

-- NOTE: this goes backwards, from the current state to the initial state
data _—→_ : LeiosState → LeiosState → Type where

  ActionStep : ∀ {s i o s′} →
    ∙ s -⟦ i / o ⟧⇀ s′
      ───────────────────
      s′ —→ s

open import Prelude.Closures _—→_

infix 0 _≈_ _≈¹_

data _≈¹_ : Action × FFDT Out → s′ —→ s → Type where

  FromAction¹ :
    ∀ i {s′ o}
      → (α : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
      → (getLabel α , i) ≈¹ ActionStep α

data ValidStep (es : Action × FFDT Out) (s : LeiosState) : Type where
  Valid : (tr : s′ —→ s) → es ≈¹ tr → ValidStep es s

data _≈_ : TestTrace → s′ —↠ s → Type where

  FromAction :
    ∀ i {αs s′ s₀ o} {tr : s —↠ s₀}
      → αs ≈ tr
      → (α : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
      → (getLabel α , i) ∷ αs ≈ s′ —→⟨ ActionStep α ⟩ tr

  Done : [] ≈ s ∎

data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
  Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s

getNewState : ∀ {es s} → ValidTrace es s → LeiosState
getNewState (Valid {s′ = s} _ _) = s

data Err-verifyTrace : TestTrace → LeiosState → Type where
  Err-StepOk   : Err-verifyTrace αs s → Err-verifyTrace ((α , i) ∷ αs) s
  Err-Action   : Err-verifyAction α i s′ → Err-verifyTrace ((α , i) ∷ αs) s

Ok' : ∀ {s i o s′} → (α : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
    → Result (Err-verifyAction (getLabel α) i s) (ValidStep (getLabel α , i) s)
Ok' a = Ok (Valid _ (FromAction¹ _ a))

-- We need the SpecStructure in context when generating Base₂a-premises
open import Prelude.STS.GenPremises
unquoteDecl Base₂a-premises = genPremises Base₂a-premises (quote Base₂a)

verifyStep' : (a : Action) → (i : FFDT Out) → (s : LeiosState) → getSlot a ≡ slot s
            → Result (Err-verifyAction a i s) (ValidStep (a , i) s)

verifyStep' (IB-Role-Action n) FFDT.SLOT s refl with ¿ IB-Role-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Roles₁ (IB-Role p))
... | no ¬p = Err (E-Err-CanProduceIB λ _ → ¬p)
verifyStep' (IB-Role-Action _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (IB-Role-Action _) (FFDT.FFD-OUT _) _ _ = Err dummyErr

verifyStep' (EB-Role-Action n ibs ebs) FFDT.SLOT s refl with ¿ EB-Role-premises {s = s} .proj₁ ¿
    | ibs ≟  map getIBRef (L.filter (IBSelection? s Late-IB-Inclusion) (IBs s))
... | yes h | yes q rewrite q = Ok' (Roles₁ (EB-Role h))
... | _ | _ = Err dummyErr
verifyStep' (EB-Role-Action _ _ _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (EB-Role-Action _ _ _) (FFDT.FFD-OUT _) _ _ = Err dummyErr

verifyStep' (VT-Role-Action n) FFDT.SLOT s refl with ¿ VT-Role-premises {s = s} .proj₁ ¿
... | yes h = Ok' (Roles₁ (VT-Role h))
... | no ¬h = Err dummyErr
verifyStep' (VT-Role-Action _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (VT-Role-Action _) (FFDT.FFD-OUT _) _ _ = Err dummyErr

verifyStep' (No-IB-Role-Action n) FFDT.SLOT s refl
  with ¿ No-IB-Role-premises {s = s} .proj₁ × (∀ π → ¬ canProduceIB (slot s) (IB , tt) (stake s) π) ¿
... | yes (p , p₁) = Ok' (Roles₂ (No-IB-Role (p , p₁)))
... | no ¬p = Err dummyErr
verifyStep' (No-IB-Role-Action _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (No-IB-Role-Action _) (FFDT.FFD-OUT _) _ _ = Err dummyErr

verifyStep' (No-EB-Role-Action n) FFDT.SLOT s refl
  with ¿ No-EB-Role-premises {s = s} .proj₁ × (∀ π → ¬ canProduceEB (slot s) (EB , tt) (stake s) π) ¿
... | yes (p , p₁) = Ok' (Roles₂ (No-EB-Role (p , p₁)))
... | no ¬p = Err dummyErr
verifyStep' (No-EB-Role-Action _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (No-EB-Role-Action _) (FFDT.FFD-OUT _) _ _ = Err dummyErr

verifyStep' (No-VT-Role-Action n) FFDT.SLOT s refl with ¿ No-VT-Role-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Roles₂ (No-VT-Role p))
... | no ¬p = Err dummyErr
verifyStep' (No-VT-Role-Action _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (No-VT-Role-Action _) (FFDT.FFD-OUT _) _ _ = Err dummyErr

-- This has a different IO pattern, not sure if we want to model that here
-- For now we'll just fail
verifyStep' (Ftch-Action n) _ _ _ = Err dummyErr

verifyStep' (Slot-Action n) FFDT.SLOT _ _ = Err dummyErr
verifyStep' (Slot-Action n) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (Slot-Action n) (FFDT.FFD-OUT msgs) s refl with ¿ Slot₁-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Slot₁ {msgs = msgs} p)
... | no _ = Err dummyErr

-- Different IO pattern again
verifyStep' (Base₁-Action n) _ s refl = Err dummyErr
verifyStep' (Base₂a-Action n _) FFDT.SLOT s refl
  with (RankingBlock.ebCert (currentRB s))
... | nothing = Err dummyErr
... | just cert
  with ¿ Base₂a-premises {s = s} {cert = cert} .proj₁ ¿
... | yes p = Ok' (Base₂a p)
... | no _ = Err dummyErr
verifyStep' (Base₂a-Action n _) _ s refl = Err dummyErr
verifyStep' (Base₂b-Action n) FFDT.SLOT s refl with ¿ Base₂b-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Base₂b p)
... | no _ = Err dummyErr
verifyStep' (Base₂b-Action n) _ s refl = Err dummyErr

verifyStep : (a : Action) → (i : FFDT Out) → (s : LeiosState) → Result (Err-verifyAction a i s) (ValidStep (a , i) s)
verifyStep a i s = case getSlot a ≟ slot s of λ where
  (yes p) → verifyStep' a i s p
  (no ¬p) → Err (E-Err-Slot λ p → ⊥-elim (¬p p))

verifyTrace : ∀ (αs : TestTrace) → (s : LeiosState) → Result (Err-verifyTrace αs s) (ValidTrace αs s)
verifyTrace [] s = Ok (Valid (s ∎) Done)
verifyTrace ((a , i) ∷ αs) s = do
  αs ← mapErr Err-StepOk (verifyTrace αs s)
  x  ← mapErr Err-Action (verifyStep a i (getNewState αs))
  return (αs Valid∷ʳ x)
  where
    open Monad-Result
    _Valid∷ʳ_ : ∀ {e es s} → (αs : ValidTrace es s) → ValidStep e (getNewState αs) → ValidTrace (e ∷ es) s
    Valid tr x Valid∷ʳ Valid (ActionStep as) (FromAction¹ a _) =
      Valid (_ —→⟨ ActionStep as ⟩ tr) (FromAction a x as)
