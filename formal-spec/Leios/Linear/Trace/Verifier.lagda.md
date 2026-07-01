## Linear Leios Trace Verifier
<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _>>=_; return; _⊗_)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_; eval)
open import CategoricalCrypto.Channel.Selection

open import Data.List.Properties
open import Data.Maybe.Properties
open import Data.Product.Properties
```
-->
```agda
module Leios.Linear.Trace.Verifier (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params)
  where

open import Leios.Linear ⋯ params public
open FFD hiding (_-⟦_/_⟧⇀_)
open GenFFD
open Types params
open BaseAbstract B'
```
An `Action` provides input to the relational semantics
```agda
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
```
A `TestTrace` is a list of actions togther with channels related to the other functionalities
```agda
TestTrace = List (Action × (FFDT Out ⊎ BaseIOF In ⊎ IOT In))
```
```agda
private variable
  s s′ : LeiosState
  σ    : Action
  σs   : TestTrace
  eb   : EndorserBlock
  ebs  : List EndorserBlock
  vt   : List Vote
  i    : FFDT Out ⊎ BaseIOF In ⊎ IOT In
  o    : FFDT In
```
```agda
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
```
```agda
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
```
NOTE: this goes backwards, from the current state to the initial state
```agda
data _—→_ : LeiosState → LeiosState → Type where

  ActionStep : ∀ {s i o s′} →
    ∙ s -⟦ i / o ⟧⇀ s′
      ───────────────────
      s′ —→ s

open import Prelude.Closures _—→_
```
```agda
toRcvType : FFDT Out ⊎ BaseIOF In ⊎ IOT In → Channel.inType ((FFD ⊗₀ BaseIO) ⊗₀ ((IO ⊗₀ Adv) ᵀ))
toRcvType (inj₁ i) = (ϵ ⊗R) ⊗R ↑ᵢ i
toRcvType (inj₂ (inj₁ i)) = (L⊗ ϵ) ⊗R ↑ᵢ i
toRcvType (inj₂ (inj₂ i)) = L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ i
```
```agda
infix 0 _≈_ _≈¹_

data _≈¹_ : Action × (FFDT Out ⊎ BaseIOF In ⊎ IOT In) → s′ —→ s → Type where

  FromAction :
    ∀ i {s′ o}
      → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
      → (getAction σ , i) ≈¹ ActionStep σ

data ValidStep (es : Action × (FFDT Out ⊎ BaseIOF In ⊎ IOT In)) (s : LeiosState) : Type where
  Valid : (tr : s′ —→ s) → es ≈¹ tr → ValidStep es s
```
```agda
data _≈_ : TestTrace → s′ —↠ s → Type where

  FromAction :
    ∀ i {σs s′ s₀ o} {tr : s —↠ s₀}
      → σs ≈ tr
      → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
      → (getAction σ , i) ∷ σs ≈ s′ —→⟨ ActionStep σ ⟩ tr

  Done : [] ≈ s ∎

data ValidTrace (es : TestTrace) (s : LeiosState) : Type where
  Valid : (tr : s′ —↠ s) → es ≈ tr → ValidTrace es s
```
### Error handling
Errors that occur when verifying a step
```agda
getNewState : ∀ {es s} → ValidTrace es s → LeiosState
getNewState (Valid {s′ = s} _ _) = s
```
Ideally an `Err-InputMismatch`/`Err-Unsupported` would carry `¬ ValidStep (σ , i) s`. That is
however not provable here: the transition's input index is `toRcvType i`, and `toRcvType`
routes through the channel-selection `app`, an opaque record projection Agda cannot invert. So
we instead witness the mismatch at the level of the *input-channel selector*: every transition
rule reads one specific input constructor, and an action/input pairing is rejected exactly when
the constructor supplied differs from the one the action's rule consumes.
```agda
data InputC : Type where
  cSLOT cFTCH cFFD-OUT           : InputC  -- FFDT Out
  cBASE-LDG cSTAKE cEMPTY cbSLOT : InputC  -- BaseIOF In
  cSubmitTxs cFetchLdgI          : InputC  -- IOT In
  cUnreachable                   : InputC  -- no representable input (Ftch's output-typed pattern)

inputC : FFDT Out ⊎ BaseIOF In ⊎ IOT In → InputC
inputC (inj₁ SLOT)                 = cSLOT
inputC (inj₁ FTCH)                 = cFTCH
inputC (inj₁ (FFD-OUT _))          = cFFD-OUT
inputC (inj₂ (inj₁ (BASE-LDG _)))  = cBASE-LDG
inputC (inj₂ (inj₁ (STAKE _)))     = cSTAKE
inputC (inj₂ (inj₁ EMPTY))         = cEMPTY
inputC (inj₂ (inj₁ (SLOT _)))      = cbSLOT
inputC (inj₂ (inj₂ (SubmitTxs _))) = cSubmitTxs
inputC (inj₂ (inj₂ FetchLdgI))     = cFetchLdgI

-- The input constructor each action's transition rule consumes.
expectedInput : Action → InputC
expectedInput (EB-Role-Action _ _)   = cSLOT
expectedInput (VT-Role-Action _ _ _) = cSLOT
expectedInput (No-EB-Role-Action _)  = cSLOT
expectedInput (No-VT-Role-Action _)  = cSLOT
expectedInput (Base₂-Action _)       = cSLOT
expectedInput (Slot₁-Action _)       = cFFD-OUT
expectedInput (Slot₂-Action _)       = cBASE-LDG
expectedInput (Base₁-Action _)       = cSubmitTxs
expectedInput (Ftch-Action _)        = cUnreachable

data Err-verifyStep (σ : Action) (i : FFDT Out ⊎ BaseIOF In ⊎ IOT In) (s : LeiosState) : Type where
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
    slot ≡ slotNumber eb + (3 * Lhdr ⊔ validityCheckTime eb) ×
    validityCheckTime eb ≤ 3 * Lhdr + Lvote ×
    EndorserBlockOSig.txs eb ≢ [] ×
    needsUpkeep VT-Role ×
    canProduceV (slotNumber eb) sk-VT (stake s)) →
    Err-verifyStep σ i s
  Err-AllDone : ¬ (allDone s) → Err-verifyStep σ i s
  Err-BaseUpkeep : ¬ (LeiosState.needsUpkeep s Base) → Err-verifyStep σ i s
  Err-Roles₂-premises : ∀ {u} → ¬ (Roles₂-premises {s = s} {u = u} .proj₁) → Err-verifyStep σ i s
  Err-InputMismatch : inputC i ≢ expectedInput σ → Err-verifyStep σ i s -- the input channel does not match the action
  Err-Unsupported : inputC i ≢ expectedInput σ → Err-verifyStep σ i s   -- the action's IO pattern is not modelled by the verifier
```
Errors when verifying a trace
```agda
data Err-verifyTrace : TestTrace → LeiosState → Type where
  Err-StepOk : Err-verifyTrace σs s → Err-verifyTrace ((σ , i) ∷ σs) s
  Err-Step   : Err-verifyStep σ i s′ → Err-verifyTrace ((σ , i) ∷ σs) s
```
```agda
Ok' : ∀ {s i o s′} → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
    → Result (Err-verifyStep (getAction σ) i s) (ValidStep (getAction σ , i) s)
Ok' a = Ok (Valid _ (FromAction _ a))
```
Reusable witnesses for the mismatching input families (payloads are irrelevant):
```agda
inj₂≢SLOT : ∀ y → inputC (inj₂ y) ≢ cSLOT
inj₂≢SLOT (inj₁ (BASE-LDG _))  ()
inj₂≢SLOT (inj₁ (STAKE _))     ()
inj₂≢SLOT (inj₁ EMPTY)         ()
inj₂≢SLOT (inj₁ (SLOT _))      ()
inj₂≢SLOT (inj₂ (SubmitTxs _)) ()
inj₂≢SLOT (inj₂ FetchLdgI)     ()

inj₂≢FFD-OUT : ∀ y → inputC (inj₂ y) ≢ cFFD-OUT
inj₂≢FFD-OUT (inj₁ (BASE-LDG _))  ()
inj₂≢FFD-OUT (inj₁ (STAKE _))     ()
inj₂≢FFD-OUT (inj₁ EMPTY)         ()
inj₂≢FFD-OUT (inj₁ (SLOT _))      ()
inj₂≢FFD-OUT (inj₂ (SubmitTxs _)) ()
inj₂≢FFD-OUT (inj₂ FetchLdgI)     ()

inj₁≢BASE-LDG : ∀ x → inputC (inj₁ x) ≢ cBASE-LDG
inj₁≢BASE-LDG SLOT        ()
inj₁≢BASE-LDG FTCH        ()
inj₁≢BASE-LDG (FFD-OUT _) ()

inj₁≢SubmitTxs : ∀ x → inputC (inj₁ x) ≢ cSubmitTxs
inj₁≢SubmitTxs SLOT        ()
inj₁≢SubmitTxs FTCH        ()
inj₁≢SubmitTxs (FFD-OUT _) ()

inj₂inj₁≢SubmitTxs : ∀ y → inputC (inj₂ (inj₁ y)) ≢ cSubmitTxs
inj₂inj₁≢SubmitTxs (BASE-LDG _) ()
inj₂inj₁≢SubmitTxs (STAKE _)    ()
inj₂inj₁≢SubmitTxs EMPTY        ()
inj₂inj₁≢SubmitTxs (SLOT _)     ()

≢Unreachable : ∀ i → inputC i ≢ cUnreachable
≢Unreachable (inj₁ SLOT)                 ()
≢Unreachable (inj₁ FTCH)                 ()
≢Unreachable (inj₁ (FFD-OUT _))          ()
≢Unreachable (inj₂ (inj₁ (BASE-LDG _)))  ()
≢Unreachable (inj₂ (inj₁ (STAKE _)))     ()
≢Unreachable (inj₂ (inj₁ EMPTY))         ()
≢Unreachable (inj₂ (inj₁ (SLOT _)))      ()
≢Unreachable (inj₂ (inj₂ (SubmitTxs _))) ()
≢Unreachable (inj₂ (inj₂ FetchLdgI))     ()
```
```agda
verifyStep' : (a : Action) →
  (i : FFDT Out ⊎ BaseIOF In ⊎ IOT In) →
  (s : LeiosState) → getSlot a ≡ LeiosState.slot s →
  Result (Err-verifyStep a i s) (ValidStep (a , i) s)
verifyStep' (EB-Role-Action n ebs) (inj₁ SLOT) s refl
  with ¿ EB-Role-premises {s = s} {π = proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s))} .proj₁ ¿
... | yes p = Ok' (Roles₁ (EB-Role p))
... | no ¬p = Err (Err-EB-Role-premises ¬p)
verifyStep' (EB-Role-Action _ _) (inj₁ FTCH) _ _        = Err (Err-InputMismatch λ ())
verifyStep' (EB-Role-Action _ _) (inj₁ (FFD-OUT _)) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (EB-Role-Action _ _) (inj₂ y) _ _           = Err (Err-InputMismatch (inj₂≢SLOT y))
verifyStep' (VT-Role-Action _ eb slot') (inj₁ SLOT) s refl
  with ¿ VT-Role-premises {s = s} {eb = eb} {ebHash = hash eb} {slot' = slot'} .proj₁ ¿
... | yes p = Ok' (Roles₁ (VT-Role {ebHash = hash eb} {slot' = slot'} p))
... | no ¬p = Err (Err-VT-Role-premises ¬p)
verifyStep' (VT-Role-Action _ _ _) (inj₁ FTCH) _ _        = Err (Err-InputMismatch λ ())
verifyStep' (VT-Role-Action _ _ _) (inj₁ (FFD-OUT _)) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (VT-Role-Action _ _ _) (inj₂ y) _ _           = Err (Err-InputMismatch (inj₂≢SLOT y))

-- The `Ftch` transition uses a different IO pattern (an output-typed channel), so it is never
-- reachable through `toRcvType`; hence no representable input produces a `Ftch-Action` step.
verifyStep' (Ftch-Action _) i _ _ = Err (Err-Unsupported (≢Unreachable i))

verifyStep' (Slot₁-Action _) (inj₁ SLOT) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (Slot₁-Action _) (inj₁ FTCH) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (Slot₁-Action _) (inj₁ (FFD-OUT msgs)) s refl
  with ¿ Slot₁-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Slot₁ {s = s} {msgs = msgs} p)
... | no ¬p = Err (Err-AllDone ¬p)
verifyStep' (Slot₁-Action _) (inj₂ y) _ _ = Err (Err-InputMismatch (inj₂≢FFD-OUT y))
verifyStep' (Slot₂-Action _) (inj₁ x) _ _ = Err (Err-InputMismatch (inj₁≢BASE-LDG x))
verifyStep' (Slot₂-Action _) (inj₂ (inj₁ (BASE-LDG rbs))) s refl = Ok' Slot₂
verifyStep' (Slot₂-Action _) (inj₂ (inj₁ (STAKE _))) _ _        = Err (Err-InputMismatch λ ())
verifyStep' (Slot₂-Action _) (inj₂ (inj₁ EMPTY)) _ _            = Err (Err-InputMismatch λ ())
verifyStep' (Slot₂-Action _) (inj₂ (inj₁ (SLOT _))) _ _         = Err (Err-InputMismatch λ ())
verifyStep' (Slot₂-Action _) (inj₂ (inj₂ (SubmitTxs _))) _ _    = Err (Err-InputMismatch λ ())
verifyStep' (Slot₂-Action _) (inj₂ (inj₂ FetchLdgI)) _ _        = Err (Err-InputMismatch λ ())

verifyStep' (Base₁-Action _) (inj₁ x) _ _                = Err (Err-InputMismatch (inj₁≢SubmitTxs x))
verifyStep' (Base₁-Action _) (inj₂ (inj₁ y)) _ _         = Err (Err-InputMismatch (inj₂inj₁≢SubmitTxs y))
verifyStep' (Base₁-Action _) (inj₂ (inj₂ FetchLdgI)) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (Base₁-Action _) (inj₂ (inj₂ (SubmitTxs _))) _ refl = Ok' Base₁
verifyStep' (Base₂-Action _) (inj₁ SLOT) s refl
  with ¿ Base₂-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Base₂ {π = proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s))} p)
... | no ¬p = Err (Err-BaseUpkeep ¬p)
verifyStep' (Base₂-Action _) (inj₁ FTCH) _ _        = Err (Err-InputMismatch λ ())
verifyStep' (Base₂-Action _) (inj₁ (FFD-OUT _)) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (Base₂-Action _) (inj₂ y) _ _           = Err (Err-InputMismatch (inj₂≢SLOT y))
verifyStep' (No-EB-Role-Action _) (inj₁ SLOT) s refl
  with ¿ Roles₂-premises {s = s} {u = EB-Role} .proj₁ ¿
... | yes p = Ok' (Roles₂ p)
... | no ¬p = Err (Err-Roles₂-premises ¬p)
verifyStep' (No-EB-Role-Action _) (inj₁ FTCH) _ _        = Err (Err-InputMismatch λ ())
verifyStep' (No-EB-Role-Action _) (inj₁ (FFD-OUT _)) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (No-EB-Role-Action _) (inj₂ y) _ _           = Err (Err-InputMismatch (inj₂≢SLOT y))
verifyStep' (No-VT-Role-Action _) (inj₁ SLOT) s refl
  with ¿ Roles₂-premises {s = s} {u = VT-Role} .proj₁ ¿
... | yes p = Ok' (Roles₂ p)
... | no ¬p = Err (Err-Roles₂-premises ¬p)
verifyStep' (No-VT-Role-Action _) (inj₁ FTCH) _ _        = Err (Err-InputMismatch λ ())
verifyStep' (No-VT-Role-Action _) (inj₁ (FFD-OUT _)) _ _ = Err (Err-InputMismatch λ ())
verifyStep' (No-VT-Role-Action _) (inj₂ y) _ _           = Err (Err-InputMismatch (inj₂≢SLOT y))
```
```agda
verifyStep : (a : Action) → (i : FFDT Out ⊎ BaseIOF In ⊎ IOT In) → (s : LeiosState) → Result (Err-verifyStep a i s) (ValidStep (a , i) s)
verifyStep a i s = case getSlot a ≟ LeiosState.slot s of λ where
  (yes p) → verifyStep' a i s p
  (no ¬p) → Err (Err-Slot λ p → ⊥-elim (¬p p))
```
```agda
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
#### Error handling
```agda
open import Prelude.Errors
open import Text.Printf

actionName : Action → String
actionName (EB-Role-Action _ _)   = "EB-Role-Action"
actionName (VT-Role-Action _ _ _) = "VT-Role-Action"
actionName (Ftch-Action _)        = "Ftch-Action"
actionName (Slot₁-Action _)       = "Slot₁-Action"
actionName (Slot₂-Action _)       = "Slot₂-Action"
actionName (Base₁-Action _)       = "Base₁-Action"
actionName (Base₂-Action _)       = "Base₂-Action"
actionName (No-EB-Role-Action _)  = "No-EB-Role-Action"
actionName (No-VT-Role-Action _)  = "No-VT-Role-Action"

module _
  ⦃ Show-Hash : Show Hash ⦄
  where

  instance
    iErr-verifyStep : ∀ {s} → IsError (λ σ  → Err-verifyStep σ i s)
    iErr-verifyStep {i} {s} .errorMsg {EB-Role-Action _ _} (Err-Slot _)   = printf "%u : Err-Slot / EB-Role-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {VT-Role-Action _ _ _} (Err-Slot _) = printf "%u : Err-Slot / VT-Role-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {Ftch-Action _} (Err-Slot _)        = printf "%u : Err-Slot / Ftch-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {Slot₁-Action _} (Err-Slot _)       = printf "%u : Err-Slot / Slot₁-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {Slot₂-Action _} (Err-Slot _)       = printf "%u : Err-Slot / Slot₂-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {Base₁-Action _} (Err-Slot _)       = printf "%u : Err-Slot / Base₁-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {Base₂-Action _} (Err-Slot _)       = printf "%u : Err-Slot / Base₂-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {No-EB-Role-Action _} (Err-Slot _)  = printf "%u : Err-Slot / No-EB-Role-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {No-VT-Role-Action _} (Err-Slot _)  = printf "%u : Err-Slot / No-VT-Role-Action" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg (Err-EB-Role-premises _)            = printf "%u : Err-EB-Role-premises" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg (Err-AllDone _)                     = printf "%u : Err-AllDone" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg (Err-BaseUpkeep _)                  = printf "%u : Err-BaseUpkeep" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg (Err-Roles₂-premises _)             = printf "%u : Err-Roles₂-premises: no applicable role step to skip" (LeiosState.slot s)
    iErr-verifyStep {i} {s} .errorMsg {a} (Err-InputMismatch _)           = printf "%u : Err-InputMismatch: input channel does not match action %s" (LeiosState.slot s) (actionName a)
    iErr-verifyStep {i} {s} .errorMsg {a} (Err-Unsupported _)             = printf "%u : Err-Unsupported: IO pattern of action %s not modelled" (LeiosState.slot s) (actionName a)
    iErr-verifyStep {i} {s} .errorMsg (Err-VT-Role-premises {eb = eb} {ebHash = ebHash} {slot' = slot'} _)
      with ¿ getCurrentEBHash s ≡ just ebHash ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Current EB hash does not match" (LeiosState.slot s)
    ... | yes p
      with ¿ find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) ≡ just (slot' , eb) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Hashes mismatch, ebHash=%s" (LeiosState.slot s) (show ebHash)
    ... | yes p
      with ¿ hash eb ∉ (LeiosState.VotedEBs s) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Already voted" (LeiosState.slot s)
    ... | yes p
      with ¿ ¬ isEquivocated s eb ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Is equivocated" (LeiosState.slot s)
    ... | yes p
      with ¿ isValid s (inj₁ (ebHeader eb)) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Not valid" (LeiosState.slot s)
    ... | yes p
      with ¿ slot' ≤ slotNumber eb + Lhdr ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: ¬ (slot' ≤ slotNumber eb + Lhdr)" (LeiosState.slot s)
    ... | yes p
      with ¿ slotNumber eb + 3 * Lhdr ≤ (LeiosState.slot s) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: ¬ (slotNumber eb + 3 * Lhdr ≤ (LeiosState.slot s))" (LeiosState.slot s)
    ... | yes p
      with ¿ (LeiosState.slot s) ≡ slotNumber eb + validityCheckTime eb ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: ¬ ((LeiosState.slot s) ≡ slotNumber eb + validityCheckTime eb)" (LeiosState.slot s)
    ... | yes p
      with ¿ validityCheckTime eb ≤ 3 * Lhdr + Lvote ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: ¬ (validityCheckTime eb ≤ 3 * Lhdr + Lvote)" (LeiosState.slot s)
    ... | yes p
      with ¿ EndorserBlockOSig.txs eb ≢ [] ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: No transactions in EB" (LeiosState.slot s)
    ... | yes p
      with ¿ LeiosState.needsUpkeep s VT-Role ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: VT-Role already done" (LeiosState.slot s)
    ... | yes p
      with ¿ canProduceV (slotNumber eb) sk-VT (stake s) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Can not produce vote" (LeiosState.slot s)
    ... | yes p = printf "%u : Impossible!" (LeiosState.slot s)

    iErr-verifyTrace : ∀ {s} → IsError (λ t → Err-verifyTrace t s)
    iErr-verifyTrace .errorMsg (Err-StepOk x) = errorMsg x
    iErr-verifyTrace .errorMsg (Err-Step x)   = errorMsg x
```
