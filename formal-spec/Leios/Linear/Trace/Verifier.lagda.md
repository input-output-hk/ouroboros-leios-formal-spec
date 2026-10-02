## Linear Leios Trace Verifier
<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _>>=_; return; _⊗_)
open import Leios.Config
open import Leios.SpecStructure

open import Prelude.Result
open import CategoricalCrypto hiding (id; _∘_; eval)
open import CategoricalCrypto.Channel.Selection

open import Data.Maybe.Properties
```
-->
```agda
module Leios.Linear.Trace.Verifier (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params)
  where

open import Leios.Linear ⋯ params public
open GenFFD
open Types params
open BaseAbstract B'
```
An `Action` names the rule a trace step is expected to take, tagged with its slot.
```agda
data Action : Type where
  EB-Role-Action    : ℕ → EndorserBlock → Action
  VT-Role-Action    : ℕ → EndorserBlock → ℕ → Action
  Cert₁-Action      : ℕ → Action
  Cert₂-Action      : ℕ → Action
  Cert₃-Action      : ℕ → Action
  Fetch-Action      : ℕ → Action
  Slot-Action       : ℕ → Action
  Chain-Action      : ℕ → Action
  Mempool-Action    : ℕ → Action
  Base₁-Action      : ℕ → Action
  Base₂-Action      : ℕ → Action
  No-EB-Role-Action : ℕ → Action
  No-VT-Role-Action : ℕ → Action
```
A `TestTrace` pairs each action with the input its step consumes.
```agda
TestInput = FFDT Out ⊎ BaseIOF In ⊎ IOT In ⊎ VotingT In

TestTrace = List (Action × TestInput)
```
```agda
private variable
  s s′ : LeiosState
  σ    : Action
  σs   : TestTrace
  eb   : EndorserBlock
  i    : TestInput
```
```agda
getAction : ∀ {i o} → s -⟦ i / o ⟧⇀ s′ → Action
getAction (Slot {s} _)                                       = Slot-Action (LeiosState.slot s)
getAction (Chain {s})                                        = Chain-Action (LeiosState.slot s)
getAction (Fetch {s})                                        = Fetch-Action (LeiosState.slot s)
getAction (Mempool {s})                                      = Mempool-Action (LeiosState.slot s)
getAction (Base₁ {s} _)                                      = Base₁-Action (LeiosState.slot s)
getAction (Base₂ {s} _)                                      = Base₂-Action (LeiosState.slot s)
getAction (Cert₁ {s} _)                                      = Cert₁-Action (LeiosState.slot s)
getAction (Cert₂ {s} _)                                      = Cert₂-Action (LeiosState.slot s)
getAction (Cert₃ {s} _)                                      = Cert₃-Action (LeiosState.slot s)
getAction (EB-Role {s} {eb = eb} _)                          = EB-Role-Action (LeiosState.slot s) eb
getAction (No-EB-Role {s} _)                                 = No-EB-Role-Action (LeiosState.slot s)
getAction (VT-Role {s} {eb = eb} {slot' = slot'} _)          = VT-Role-Action (LeiosState.slot s) eb slot'
getAction (No-VT-Role {s} _)                                 = No-VT-Role-Action (LeiosState.slot s)
getAction (VT-Defer {s} _)                                   = No-VT-Role-Action (LeiosState.slot s)
```
```agda
getSlot : Action → ℕ
getSlot (EB-Role-Action x _)   = x
getSlot (VT-Role-Action x _ _) = x
getSlot (Cert₁-Action x)       = x
getSlot (Cert₂-Action x)       = x
getSlot (Cert₃-Action x)       = x
getSlot (No-EB-Role-Action x)  = x
getSlot (No-VT-Role-Action x)  = x
getSlot (Fetch-Action x)       = x
getSlot (Slot-Action x)        = x
getSlot (Chain-Action x)       = x
getSlot (Mempool-Action x)     = x
getSlot (Base₁-Action x)       = x
getSlot (Base₂-Action x)       = x
```
`_—→_` runs backwards, from the later state to the earlier one.
```agda
data _—→_ : LeiosState → LeiosState → Type where

  ActionStep : ∀ {s i o s′} →
    ∙ s -⟦ i / o ⟧⇀ s′
      ───────────────────
      s′ —→ s

open import Prelude.Closures _—→_
```
```agda
toRcvType : TestInput → Channel.inType (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ ((IO ⊗₀ Adv) ᵀ))
toRcvType (inj₁ i) = ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ i
toRcvType (inj₂ (inj₁ i)) = ((L⊗ ϵ) ⊗R) ⊗R ↑ᵢ i
toRcvType (inj₂ (inj₂ (inj₁ i))) = L⊗ (ϵ ᵗ¹ ⊗R) ᵗ¹ ↑ᵢ i
toRcvType (inj₂ (inj₂ (inj₂ i))) = (L⊗ ϵ) ⊗R ↑ᵢ i
```
```agda
infix 0 _≈_ _≈¹_

data _≈¹_ : Action × TestInput → s′ —→ s → Type where

  FromAction :
    ∀ i {s′ o}
      → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
      → (getAction σ , i) ≈¹ ActionStep σ

data ValidStep (es : Action × TestInput) (s : LeiosState) : Type where
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
```agda
getNewState : ∀ {es s} → ValidTrace es s → LeiosState
getNewState (Valid {s′ = s} _ _) = s
```
`Err-InputMismatch` carries the real refutation `¬ ValidStep (σ , i) s`.  Deriving it requires
inverting the transition's input index `toRcvType i`, whose channel selections are `opaque` in
categorical-crypto; the lemmas below therefore sit in an `opaque unfolding _⊗₀_` block, where
the selections reduce to constructor form and Agda can dismiss the impossible transition
rules.  The refutation is mediated by the *input-channel selector*: `input-sound` proves that
every derivable step consumes the input constructor its action's rule expects, so a selector
mismatch refutes the step.

The premise-less `Fetch` rule reads its input through an output-typed channel selection, which
nevertheless coincides with `toRcvType (inj₂ (inj₂ (inj₁ FetchLdgI)))` once the selections reduce;
`Fetch-step` witnesses this inside the unfolding block, letting `verifyStep'` accept the pairing.
```agda
data InputC : Type where
  cSLOT cFTCH cFFD-OUT           : InputC
  cBASE-LDG cSTAKE cEMPTY cbSLOT : InputC
  cSubmitTxs cFetchLdgI          : InputC
  cCERT                          : InputC

inputC : TestInput → InputC
inputC (inj₁ SLOT)                        = cSLOT
inputC (inj₁ FTCH)                        = cFTCH
inputC (inj₁ (FFD-OUT _))                 = cFFD-OUT
inputC (inj₂ (inj₁ (BASE-LDG _)))         = cBASE-LDG
inputC (inj₂ (inj₁ (STAKE _)))            = cSTAKE
inputC (inj₂ (inj₁ EMPTY))                = cEMPTY
inputC (inj₂ (inj₁ (SLOT _)))             = cbSLOT
inputC (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) = cSubmitTxs
inputC (inj₂ (inj₂ (inj₁ FetchLdgI)))     = cFetchLdgI
inputC (inj₂ (inj₂ (inj₂ (CERT _))))      = cCERT

expectedInput : Action → InputC
expectedInput (EB-Role-Action _ _)   = cSLOT
expectedInput (VT-Role-Action _ _ _) = cSLOT
expectedInput (No-EB-Role-Action _)  = cSLOT
expectedInput (No-VT-Role-Action _)  = cSLOT
expectedInput (Base₁-Action _)       = cSLOT
expectedInput (Base₂-Action _)       = cSLOT
expectedInput (Slot-Action _)        = cFFD-OUT
expectedInput (Chain-Action _)       = cBASE-LDG
expectedInput (Mempool-Action _)     = cSubmitTxs
expectedInput (Fetch-Action _)       = cFetchLdgI
expectedInput (Cert₁-Action _)       = cCERT
expectedInput (Cert₂-Action _)       = cCERT
expectedInput (Cert₃-Action _)       = cCERT

opaque
  unfolding _⊗₀_

  input-sound : ∀ (i : TestInput) {s s′ o}
                (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
              → inputC i ≡ expectedInput (getAction σ)
  input-sound (inj₁ SLOT) (Base₁ _)                       = refl
  input-sound (inj₁ SLOT) (Base₂ _)                       = refl
  input-sound (inj₁ SLOT) (EB-Role _)                     = refl
  input-sound (inj₁ SLOT) (No-EB-Role _)                  = refl
  input-sound (inj₁ SLOT) (VT-Role _)                     = refl
  input-sound (inj₁ SLOT) (No-VT-Role _)                  = refl
  input-sound (inj₁ SLOT) (VT-Defer _)                    = refl
  input-sound (inj₁ FTCH) ()
  input-sound (inj₁ (FFD-OUT _)) (Slot _)                 = refl
  input-sound (inj₂ (inj₁ (BASE-LDG _))) Chain            = refl
  input-sound (inj₂ (inj₁ (STAKE _))) ()
  input-sound (inj₂ (inj₁ EMPTY)) ()
  input-sound (inj₂ (inj₁ (SLOT _))) ()
  input-sound (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) Mempool  = refl
  input-sound (inj₂ (inj₂ (inj₁ FetchLdgI))) Fetch        = refl
  input-sound (inj₂ (inj₂ (inj₂ (CERT _)))) (Cert₁ _)     = refl
  input-sound (inj₂ (inj₂ (inj₂ (CERT _)))) (Cert₂ _)     = refl
  input-sound (inj₂ (inj₂ (inj₂ (CERT _)))) (Cert₃ _)     = refl

  input-mismatch : ∀ {a i s} → inputC i ≢ expectedInput a → ¬ ValidStep (a , i) s
  input-mismatch neq (Valid _ (FromAction i σ)) = neq (input-sound i σ)

  Fetch-step : ∀ {s} → ValidStep (Fetch-Action (LeiosState.slot s) , inj₂ (inj₂ (inj₁ FetchLdgI))) s
  Fetch-step = Valid _ (FromAction (inj₂ (inj₂ (inj₁ FetchLdgI))) Fetch)

data Err-verifyStep (σ : Action) (i : TestInput) (s : LeiosState) : Type where
  Err-Slot : getSlot σ ≢ LeiosState.slot s → Err-verifyStep σ i s
  Err-EB-Role-premises : ∀ {π} → ¬ (EB-Role-premises {s = s} {π = π} {eb = eb} .proj₁) → Err-verifyStep σ i s
  Err-No-EB-Role-premises : ¬ (No-EB-Role-premises {s = s} .proj₁) → Err-verifyStep σ i s
  Err-VT-Role-premises : ∀ {ebHash slot'}
    → ¬ (VT-Role-premises {s = s} {eb = eb} {ebHash = ebHash} {slot' = slot'} .proj₁) → Err-verifyStep σ i s
  Err-No-VT-Role-premises : ¬ (No-VT-Role-premises {s = s} .proj₁) → ¬ (VT-Defer-premises {s = s} .proj₁)
    → Err-verifyStep σ i s
  Err-AllDone : ¬ (allDone s) → Err-verifyStep σ i s
  Err-Cert₁-premises : ∀ {c} → (∀ {eb} → ¬ (Cert₁-premises {s = s} {eb = eb} {c = c} .proj₁)) → Err-verifyStep σ i s
  Err-Cert₂-premises : (∀ {r} → ¬ (Cert₂-premises {s = s} {r = r} .proj₁)) → Err-verifyStep σ i s
  Err-Cert₃-premises : (∀ {eb r} → ¬ (Cert₃-premises {s = s} {eb = eb} {r = r} .proj₁)) → Err-verifyStep σ i s
  Err-Base₁-premises : ¬ (Base₁-premises {s = s} .proj₁) → Err-verifyStep σ i s
  Err-Base₂-premises : (∀ {eb} → ¬ (Base₂-premises {s = s} {eb = eb} .proj₁)) → Err-verifyStep σ i s
  Err-InputMismatch : ¬ ValidStep (σ , i) s → Err-verifyStep σ i s
data Err-verifyTrace : TestTrace → LeiosState → Type where
  Err-StepOk : Err-verifyTrace σs s → Err-verifyTrace ((σ , i) ∷ σs) s
  Err-Step   : Err-verifyStep σ i s′ → Err-verifyTrace ((σ , i) ∷ σs) s
```
```agda
Ok' : ∀ {s i o s′} → (σ : s -⟦ toRcvType i / o ⟧⇀ s′)
    → Result (Err-verifyStep (getAction σ) i s) (ValidStep (getAction σ , i) s)
Ok' a = Ok (Valid _ (FromAction _ a))

Mismatch : ∀ {a i s} → inputC i ≢ expectedInput a
         → Result (Err-verifyStep a i s) (ValidStep (a , i) s)
Mismatch neq = Err (Err-InputMismatch (input-mismatch neq))
inj₂≢SLOT : ∀ y → inputC (inj₂ y) ≢ cSLOT
inj₂≢SLOT (inj₁ (BASE-LDG _))         ()
inj₂≢SLOT (inj₁ (STAKE _))            ()
inj₂≢SLOT (inj₁ EMPTY)                ()
inj₂≢SLOT (inj₁ (SLOT _))             ()
inj₂≢SLOT (inj₂ (inj₁ (SubmitTxs _))) ()
inj₂≢SLOT (inj₂ (inj₁ FetchLdgI))     ()
inj₂≢SLOT (inj₂ (inj₂ (CERT _)))      ()

inj₂≢FFD-OUT : ∀ y → inputC (inj₂ y) ≢ cFFD-OUT
inj₂≢FFD-OUT (inj₁ (BASE-LDG _))         ()
inj₂≢FFD-OUT (inj₁ (STAKE _))            ()
inj₂≢FFD-OUT (inj₁ EMPTY)                ()
inj₂≢FFD-OUT (inj₁ (SLOT _))             ()
inj₂≢FFD-OUT (inj₂ (inj₁ (SubmitTxs _))) ()
inj₂≢FFD-OUT (inj₂ (inj₁ FetchLdgI))     ()
inj₂≢FFD-OUT (inj₂ (inj₂ (CERT _)))      ()

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

inj₁≢FetchLdgI : ∀ x → inputC (inj₁ x) ≢ cFetchLdgI
inj₁≢FetchLdgI SLOT        ()
inj₁≢FetchLdgI FTCH        ()
inj₁≢FetchLdgI (FFD-OUT _) ()

inj₂inj₁≢FetchLdgI : ∀ y → inputC (inj₂ (inj₁ y)) ≢ cFetchLdgI
inj₂inj₁≢FetchLdgI (BASE-LDG _) ()
inj₂inj₁≢FetchLdgI (STAKE _)    ()
inj₂inj₁≢FetchLdgI EMPTY        ()
inj₂inj₁≢FetchLdgI (SLOT _)     ()

inj₁≢CERT : ∀ x → inputC (inj₁ x) ≢ cCERT
inj₁≢CERT SLOT        ()
inj₁≢CERT FTCH        ()
inj₁≢CERT (FFD-OUT _) ()

inj₂inj₁≢CERT : ∀ y → inputC (inj₂ (inj₁ y)) ≢ cCERT
inj₂inj₁≢CERT (BASE-LDG _) ()
inj₂inj₁≢CERT (STAKE _)    ()
inj₂inj₁≢CERT EMPTY        ()
inj₂inj₁≢CERT (SLOT _)     ()
```
```agda
verifyStep' : (a : Action) →
  (i : TestInput) →
  (s : LeiosState) → getSlot a ≡ LeiosState.slot s →
  Result (Err-verifyStep a i s) (ValidStep (a , i) s)
verifyStep' (EB-Role-Action _ _) (inj₁ SLOT) s refl
  with ¿ EB-Role-premises {s = s} {π = proj₂ $ eval sk-EB (genEBInput (LeiosState.slot s))} .proj₁ ¿
... | yes p = Ok' (EB-Role p)
... | no ¬p = Err (Err-EB-Role-premises ¬p)
verifyStep' (EB-Role-Action _ _) (inj₁ FTCH) _ _        = Mismatch λ ()
verifyStep' (EB-Role-Action _ _) (inj₁ (FFD-OUT _)) _ _ = Mismatch λ ()
verifyStep' (EB-Role-Action _ _) (inj₂ y) _ _           = Mismatch (inj₂≢SLOT y)
verifyStep' (VT-Role-Action _ eb slot') (inj₁ SLOT) s refl
  with ¿ VT-Role-premises {s = s} {eb = eb} {ebHash = hash eb} {slot' = slot'} .proj₁ ¿
... | yes p = Ok' (VT-Role {ebHash = hash eb} {slot' = slot'} p)
... | no ¬p = Err (Err-VT-Role-premises ¬p)
verifyStep' (VT-Role-Action _ _ _) (inj₁ FTCH) _ _        = Mismatch λ ()
verifyStep' (VT-Role-Action _ _ _) (inj₁ (FFD-OUT _)) _ _ = Mismatch λ ()
verifyStep' (VT-Role-Action _ _ _) (inj₂ y) _ _           = Mismatch (inj₂≢SLOT y)

verifyStep' (Cert₁-Action _) (inj₁ x) _ _                           = Mismatch (inj₁≢CERT x)
verifyStep' (Cert₁-Action _) (inj₂ (inj₁ y)) _ _                    = Mismatch (inj₂inj₁≢CERT y)
verifyStep' (Cert₁-Action _) (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) _ _ = Mismatch λ ()
verifyStep' (Cert₁-Action _) (inj₂ (inj₂ (inj₁ FetchLdgI))) _ _     = Mismatch λ ()
verifyStep' (Cert₁-Action _) (inj₂ (inj₂ (inj₂ (CERT c)))) s refl
  with certRequest s in eq
... | nothing = Err (Err-Cert₁-premises {c = c} λ (_ , _ , creq , _) → just≢nothing (trans (sym creq) eq))
... | just eb
  with ¿ Cert₁-premises {s = s} {eb = eb} {c = c} .proj₁ ¿
... | yes p = Ok' (Cert₁ p)
... | no ¬p = Err (Err-Cert₁-premises λ p@(_ , _ , creq , _) →
                ¬p (subst (λ e → Cert₁-premises {s = s} {eb = e} {c = c} .proj₁) (just-injective (trans (sym creq) eq)) p))

verifyStep' (Cert₂-Action _) (inj₁ x) _ _                           = Mismatch (inj₁≢CERT x)
verifyStep' (Cert₂-Action _) (inj₂ (inj₁ y)) _ _                    = Mismatch (inj₂inj₁≢CERT y)
verifyStep' (Cert₂-Action _) (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) _ _ = Mismatch λ ()
verifyStep' (Cert₂-Action _) (inj₂ (inj₂ (inj₁ FetchLdgI))) _ _     = Mismatch λ ()
verifyStep' (Cert₂-Action _) (inj₂ (inj₂ (inj₂ (CERT c)))) s refl
  with LeiosState.PendingQuery s in peq
... | nothing = Err (Err-Cert₂-premises λ (_ , _ , _ , pq) → just≢nothing (trans (sym pq) peq))
... | just r
  with ¿ Cert₂-premises {s = s} {r = r} .proj₁ ¿
... | yes p = Ok' (Cert₂ p)
... | no ¬p = Err (Err-Cert₂-premises λ (upk , chk , creq , _) → ¬p (upk , chk , creq , peq))

verifyStep' (Cert₃-Action _) (inj₁ x) _ _                           = Mismatch (inj₁≢CERT x)
verifyStep' (Cert₃-Action _) (inj₂ (inj₁ y)) _ _                    = Mismatch (inj₂inj₁≢CERT y)
verifyStep' (Cert₃-Action _) (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) _ _ = Mismatch λ ()
verifyStep' (Cert₃-Action _) (inj₂ (inj₂ (inj₁ FetchLdgI))) _ _     = Mismatch λ ()
verifyStep' (Cert₃-Action _) (inj₂ (inj₂ (inj₂ (CERT c)))) s refl
  with certRequest s in eq | LeiosState.PendingQuery s in peq
... | nothing | _       = Err (Err-Cert₃-premises λ (_ , _ , creq , _) → just≢nothing (trans (sym creq) eq))
... | just _  | nothing = Err (Err-Cert₃-premises λ (_ , _ , _ , pq , _) → just≢nothing (trans (sym pq) peq))
... | just eb | just r
  with ¿ Cert₃-premises {s = s} {eb = eb} {r = r} .proj₁ ¿
... | yes p = Ok' (Cert₃ p)
... | no ¬p = Err (Err-Cert₃-premises λ p@(_ , _ , creq , pq , _) →
                ¬p (subst₂ (λ e r' → Cert₃-premises {s = s} {eb = e} {r = r'} .proj₁)
                      (just-injective (trans (sym creq) eq)) (just-injective (trans (sym pq) peq)) p))

verifyStep' (Fetch-Action _) (inj₁ x) _ _                           = Mismatch (inj₁≢FetchLdgI x)
verifyStep' (Fetch-Action _) (inj₂ (inj₁ y)) _ _                    = Mismatch (inj₂inj₁≢FetchLdgI y)
verifyStep' (Fetch-Action _) (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) _ _ = Mismatch λ ()
verifyStep' (Fetch-Action _) (inj₂ (inj₂ (inj₁ FetchLdgI))) _ refl  = Ok Fetch-step
verifyStep' (Fetch-Action _) (inj₂ (inj₂ (inj₂ (CERT _)))) _ _      = Mismatch λ ()

verifyStep' (Slot-Action _) (inj₁ SLOT) _ _ = Mismatch λ ()
verifyStep' (Slot-Action _) (inj₁ FTCH) _ _ = Mismatch λ ()
verifyStep' (Slot-Action _) (inj₁ (FFD-OUT msgs)) s refl
  with ¿ Slot-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Slot {s = s} {msgs = msgs} p)
... | no ¬p = Err (Err-AllDone ¬p)
verifyStep' (Slot-Action _) (inj₂ y) _ _ = Mismatch (inj₂≢FFD-OUT y)
verifyStep' (Chain-Action _) (inj₁ x) _ _ = Mismatch (inj₁≢BASE-LDG x)
verifyStep' (Chain-Action _) (inj₂ (inj₁ (BASE-LDG _))) _ refl         = Ok' Chain
verifyStep' (Chain-Action _) (inj₂ (inj₁ (STAKE _))) _ _               = Mismatch λ ()
verifyStep' (Chain-Action _) (inj₂ (inj₁ EMPTY)) _ _                   = Mismatch λ ()
verifyStep' (Chain-Action _) (inj₂ (inj₁ (SLOT _))) _ _                = Mismatch λ ()
verifyStep' (Chain-Action _) (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) _ _    = Mismatch λ ()
verifyStep' (Chain-Action _) (inj₂ (inj₂ (inj₁ FetchLdgI))) _ _        = Mismatch λ ()
verifyStep' (Chain-Action _) (inj₂ (inj₂ (inj₂ (CERT _)))) _ _         = Mismatch λ ()

verifyStep' (Mempool-Action _) (inj₁ x) _ _                              = Mismatch (inj₁≢SubmitTxs x)
verifyStep' (Mempool-Action _) (inj₂ (inj₁ y)) _ _                       = Mismatch (inj₂inj₁≢SubmitTxs y)
verifyStep' (Mempool-Action _) (inj₂ (inj₂ (inj₁ FetchLdgI))) _ _        = Mismatch λ ()
verifyStep' (Mempool-Action _) (inj₂ (inj₂ (inj₁ (SubmitTxs _)))) _ refl = Ok' Mempool
verifyStep' (Mempool-Action _) (inj₂ (inj₂ (inj₂ (CERT _)))) _ _         = Mismatch λ ()
verifyStep' (Base₁-Action _) (inj₁ SLOT) s refl
  with ¿ Base₁-premises {s = s} .proj₁ ¿
... | yes p = Ok' (Base₁ p)
... | no ¬p = Err (Err-Base₁-premises ¬p)
verifyStep' (Base₁-Action _) (inj₁ FTCH) _ _        = Mismatch λ ()
verifyStep' (Base₁-Action _) (inj₁ (FFD-OUT _)) _ _ = Mismatch λ ()
verifyStep' (Base₁-Action _) (inj₂ y) _ _           = Mismatch (inj₂≢SLOT y)
verifyStep' (Base₂-Action _) (inj₁ SLOT) s refl
  with certRequest s in eq
... | nothing = Err (Err-Base₂-premises λ { (_ , _ , q) → just≢nothing (trans (sym q) eq) })
... | just eb
  with ¿ Base₂-premises {s = s} {eb = eb} .proj₁ ¿
... | yes p = Ok' (Base₂ p)
... | no ¬p = Err (Err-Base₂-premises λ (p , u , _) → ¬p (p , u , eq))
verifyStep' (Base₂-Action _) (inj₁ FTCH) _ _        = Mismatch λ ()
verifyStep' (Base₂-Action _) (inj₁ (FFD-OUT _)) _ _ = Mismatch λ ()
verifyStep' (Base₂-Action _) (inj₂ y) _ _           = Mismatch (inj₂≢SLOT y)
verifyStep' (No-EB-Role-Action _) (inj₁ SLOT) s refl
  with ¿ No-EB-Role-premises {s = s} .proj₁ ¿
... | yes p = Ok' (No-EB-Role p)
... | no ¬p = Err (Err-No-EB-Role-premises ¬p)
verifyStep' (No-EB-Role-Action _) (inj₁ FTCH) _ _        = Mismatch λ ()
verifyStep' (No-EB-Role-Action _) (inj₁ (FFD-OUT _)) _ _ = Mismatch λ ()
verifyStep' (No-EB-Role-Action _) (inj₂ y) _ _           = Mismatch (inj₂≢SLOT y)
verifyStep' (No-VT-Role-Action _) (inj₁ SLOT) s refl
  with ¿ No-VT-Role-premises {s = s} .proj₁ ¿ | ¿ VT-Defer-premises {s = s} .proj₁ ¿
... | yes p | _     = Ok' (No-VT-Role p)
... | no _  | yes q = Ok' (VT-Defer q)
... | no ¬p | no ¬q = Err (Err-No-VT-Role-premises ¬p ¬q)
verifyStep' (No-VT-Role-Action _) (inj₁ FTCH) _ _        = Mismatch λ ()
verifyStep' (No-VT-Role-Action _) (inj₁ (FFD-OUT _)) _ _ = Mismatch λ ()
verifyStep' (No-VT-Role-Action _) (inj₂ y) _ _           = Mismatch (inj₂≢SLOT y)
```
```agda
verifyStep : (a : Action) → (i : TestInput) → (s : LeiosState) → Result (Err-verifyStep a i s) (ValidStep (a , i) s)
verifyStep a i s = case getSlot a ≟ LeiosState.slot s of λ where
  (yes p) → verifyStep' a i s p
  (no ¬p) → Err (Err-Slot ¬p)
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
#### Error messages
```agda
open import Prelude.Errors
open import Text.Printf

actionName : Action → String
actionName (EB-Role-Action _ _)   = "EB-Role-Action"
actionName (VT-Role-Action _ _ _) = "VT-Role-Action"
actionName (Cert₁-Action _)       = "Cert₁-Action"
actionName (Cert₂-Action _)       = "Cert₂-Action"
actionName (Cert₃-Action _)       = "Cert₃-Action"
actionName (Fetch-Action _)       = "Fetch-Action"
actionName (Slot-Action _)        = "Slot-Action"
actionName (Chain-Action _)       = "Chain-Action"
actionName (Mempool-Action _)     = "Mempool-Action"
actionName (Base₁-Action _)       = "Base₁-Action"
actionName (Base₂-Action _)       = "Base₂-Action"
actionName (No-EB-Role-Action _)  = "No-EB-Role-Action"
actionName (No-VT-Role-Action _)  = "No-VT-Role-Action"

module _
  ⦃ Show-Hash : Show Hash ⦄
  where

  instance
    iErr-verifyStep : ∀ {s} → IsError (λ σ  → Err-verifyStep σ i s)
    iErr-verifyStep {s = s} .errorMsg {a} (Err-Slot _)                    = printf "%u : Err-Slot / %s" (LeiosState.slot s) (actionName a)
    iErr-verifyStep {s = s} .errorMsg (Err-EB-Role-premises _)            = printf "%u : Err-EB-Role-premises" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-AllDone _)                     = printf "%u : Err-AllDone" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-Cert₁-premises _)              = printf "%u : Err-Cert₁-premises: Base upkeep spent, no certificate query made this slot, the tip calls for no certificate, the pending query is not for the current tip, or the answer does not certify it" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-Cert₂-premises _)              = printf "%u : Err-Cert₂-premises: Base upkeep spent, no certificate query made this slot, the tip still calls for a certificate, or no query is pending" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-Cert₃-premises _)              = printf "%u : Err-Cert₃-premises: Base upkeep spent, no certificate query made this slot, the tip calls for no certificate, no query is pending, or the pending query is already for the current tip" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-Base₁-premises _)              = printf "%u : Err-Base₁-premises: Base or CertCheck upkeep spent, EB role not yet settled, or the tip calls for a certificate" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-Base₂-premises _)              = printf "%u : Err-Base₂-premises: CertCheck upkeep spent, EB role not yet settled, or the tip calls for no certificate" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-No-EB-Role-premises _)         = printf "%u : Err-No-EB-Role-premises: EB role already settled, or an EB can be produced" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg (Err-No-VT-Role-premises _ _)       = printf "%u : Err-No-VT-Role-premises: VT role already settled, or a vote can be cast and the voting window has closed" (LeiosState.slot s)
    iErr-verifyStep {s = s} .errorMsg {a} (Err-InputMismatch _)           = printf "%u : Err-InputMismatch: input channel does not match action %s" (LeiosState.slot s) (actionName a)
    iErr-verifyStep {s = s} .errorMsg (Err-VT-Role-premises {eb = eb} {ebHash = ebHash} {slot' = slot'} _)
      with ¿ getCurrentEBHash s ≡ just ebHash ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Current EB hash does not match" (LeiosState.slot s)
    ... | yes p
      with ¿ find (λ (_ , eb') → hash eb' ≟ ebHash) (LeiosState.EBs' s) ≡ just (slot' , eb) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Hashes mismatch, ebHash=%s" (LeiosState.slot s) (show ebHash)
    ... | yes p
      with ¿ hash eb ∉ LeiosState.VotedEBs s ¿
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
      with ¿ slotNumber eb + 3 * Lhdr ≤ LeiosState.slot s ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: ¬ (slotNumber eb + 3 * Lhdr ≤ (LeiosState.slot s))" (LeiosState.slot s)
    ... | yes p
      with ¿ LeiosState.slot s ≤ slotNumber eb + 3 * Lhdr + Lvote ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: ¬ ((LeiosState.slot s) ≤ slotNumber eb + 3 * Lhdr + Lvote)" (LeiosState.slot s)
    ... | yes p
      with ¿ isValidityChecked (LeiosState.slot s) eb ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: EB validation not completed (isValidityChecked)" (LeiosState.slot s)
    ... | yes p
      with ¿ EndorserBlockOSig.txs eb ≢ [] ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: No transactions in EB" (LeiosState.slot s)
    ... | yes p
      with ¿ LeiosState.needsUpkeep s VT-Role ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: VT-Role already done" (LeiosState.slot s)
    ... | yes p
      with ¿ inVotingCommittee params (stake s) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: Not in the voting committee" (LeiosState.slot s)
    ... | yes p
      with ¿ id ∈ˡ L.map poolID (LeiosState.PubKeys s) ¿
    ... | no ¬p = printf "%u : Err-VT-Role-premises: No registered voting key (keyless committee seat)" (LeiosState.slot s)
    ... | yes p = printf "%u : Impossible!" (LeiosState.slot s)

    iErr-verifyTrace : ∀ {s} → IsError (λ t → Err-verifyTrace t s)
    iErr-verifyTrace .errorMsg (Err-StepOk x) = errorMsg x
    iErr-verifyTrace .errorMsg (Err-Step x)   = errorMsg x
```
