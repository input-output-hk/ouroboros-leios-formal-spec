open import Leios.Prelude hiding (id; _>>=_; return)
open import Leios.Config

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_)

-- TODO: SpecStructure as parameter
module Leios.Linear.Trace.Verifier (params : Params) (Lvote Ldiff : ℕ) where

open import Leios.Defaults params
  using (isb; hpe; hhs; htx; SendIB; FFDBuffers; Dec-SimpleFFD; sortition)
  renaming (d-SpecStructure to traceSpecStructure) public

open import Leios.SpecStructure using (SpecStructure)
open SpecStructure traceSpecStructure hiding (Hashable-IBHeader; Hashable-EndorserBlock; isVoteCertified) public

open import Leios.Linear traceSpecStructure params Lvote Ldiff public
open GenFFD

open Types params

data Action : Type where
  EB-Role-Action    : ℕ → EndorserBlock → Action
  VT-Role-Action    : ℕ → EndorserBlock → Action
  Ftch-Action       : ℕ → Action
  Slot-Action       : ℕ → Action
  Base₁-Action      : ℕ → Action
  Base₂-Action      : ℕ → Action
  No-EB-Role-Action : ℕ → Action

TestTrace = List (Action × FFDT Out)

private variable
  s s′ : LeiosState
  σ    : Action
  σs   : TestTrace
  ib   : InputBlock
  eb   : EndorserBlock
  ebs  : List EndorserBlock
  vt   : List Vote
  i    : FFDT Out
  o    : FFDT In

open LeiosState
open FFDBuffers

getAction : ∀ {i o} → s -⟦ i / o ⟧⇀ s′ → Action
getAction (Slot₁ {s} _)                      = Slot-Action (slot s)
getAction (Slot₂ {s})                        = Slot-Action (slot s)
getAction (Ftch {s})                         = Ftch-Action (slot s)
getAction (Base₁ {s})                        = Base₁-Action (slot s)
getAction (Base₂ {s} _)                      = Base₂-Action (slot s)
getAction (Roles₁ (VT-Role {s} {eb = eb} _)) = VT-Role-Action (slot s) eb
getAction (Roles₁ (EB-Role {s} {eb = eb} _)) = EB-Role-Action (slot s) eb
getAction (Roles₃ {u = Base} (_ , _ , x))    = ⊥-elim (x refl)
getAction (Roles₃ {s} {u = EB-Role} _)       = No-EB-Role-Action (slot s)

getSlot : Action → ℕ
getSlot (EB-Role-Action x _) = x
getSlot (VT-Role-Action x _) = x
getSlot (No-EB-Role-Action x) = x
getSlot (Ftch-Action x) = x
getSlot (Slot-Action x) = x
getSlot (Base₁-Action x) = x
getSlot (Base₂-Action x) = x


data Err-verifyAction (σ : Action) (i : FFDT Out) (s : LeiosState) : Type where
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

data _≈¹_ : Action × FFDT Out → s′ —→ s → Type where

  FromAction¹ :
    ∀ i {s′ o}
      → (σ : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
      → (getAction σ , i) ≈¹ ActionStep σ

data ValidStep (es : Action × FFDT Out) (s : LeiosState) : Type where
  Valid : (tr : s′ —→ s) → es ≈¹ tr → ValidStep es s

data _≈_ : TestTrace → s′ —↠ s → Type where

  FromAction :
    ∀ i {σs s′ s₀ o} {tr : s —↠ s₀}
      → σs ≈ tr
      → (σ : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
      → (getAction σ , i) ∷ σs ≈ s′ —→⟨ ActionStep σ ⟩ tr

  Done : [] ≈ s ∎

data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
  Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s

getNewState : ∀ {es s} → ValidTrace es s → LeiosState
getNewState (Valid {s′ = s} _ _) = s

data Err-verifyTrace : TestTrace → LeiosState → Type where
  Err-StepOk   : Err-verifyTrace σs s → Err-verifyTrace ((σ , i) ∷ σs) s
  Err-Action   : Err-verifyAction σ i s′ → Err-verifyTrace ((σ , i) ∷ σs) s

Ok' : ∀ {s i o s′} → (σ : s -⟦ honestOutputI (rcvˡ (-, i)) / o ⟧⇀ s′)
    → Result (Err-verifyAction (getAction σ) i s) (ValidStep (getAction σ , i) s)
Ok' a = Ok (Valid _ (FromAction¹ _ a))

verifyStep' : (a : Action) → (i : FFDT Out) → (s : LeiosState) → getSlot a ≡ slot s
            → Result (Err-verifyAction a i s) (ValidStep (a , i) s)
verifyStep' (EB-Role-Action n ebs) FFDT.SLOT s refl with ¿ EB-Role-premises {s = s} .proj₁ ¿
... | yes h = Ok' (Roles₁ (EB-Role h))
... | _ = Err dummyErr
verifyStep' (EB-Role-Action _ _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (EB-Role-Action _ _) (FFDT.FFD-OUT _) _ _ = Err dummyErr
verifyStep' (VT-Role-Action n eb) SLOT s refl with ¿ VT-Role-premises {s = s} .proj₁ ¿
... | yes h = Ok' (Roles₁ (VT-Role {ebHash = hash eb} {slot' = n} h))
... | no ¬h = Err dummyErr
verifyStep' (VT-Role-Action _ _) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (VT-Role-Action _ _) (FFDT.FFD-OUT eb) _ _ = Err dummyErr

-- This has a different IO pattern, not sure if we want to model that here
-- For now we'll just fail
verifyStep' (Ftch-Action n) _ _ _ = Err dummyErr

verifyStep' (Slot-Action n) FFDT.SLOT _ _ = Err dummyErr
verifyStep' (Slot-Action n) FFDT.FTCH _ _ = Err dummyErr
verifyStep' (Slot-Action n) (FFDT.FFD-OUT msgs) s refl with ¿ Slot₁-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Slot₁ p)
... | no _ = Err dummyErr

-- Different IO pattern again
verifyStep' (Base₁-Action n) _ s refl = Err dummyErr
verifyStep' (Base₂-Action n) _ s refl = Err dummyErr
{-
verifyStep' (Base₂a-Action n _) FFDT.SLOT s refl with ¿ Base₂a-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Base₂a p)
... | no _ = Err dummyErr
verifyStep' (Base₂a-Action n _) _ s refl = Err dummyErr
verifyStep' (Base₂b-Action n) FFDT.SLOT s refl with ¿ Base₂b-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Base₂b p)
... | no _ = Err dummyErr
verifyStep' (Base₂b-Action n) _ s refl = Err dummyErr
-}

verifyStep' (No-EB-Role-Action n) _ s refl = Err dummyErr

verifyStep : (a : Action) → (i : FFDT Out) → (s : LeiosState) → Result (Err-verifyAction a i s) (ValidStep (a , i) s)
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
    Valid tr x Valid∷ʳ Valid (ActionStep as) (FromAction¹ a _) =
      Valid (_ —→⟨ ActionStep as ⟩ tr) (FromAction a x as)
