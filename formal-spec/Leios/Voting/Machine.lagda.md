## The Leios voting scheme as a composable state machine

This module recasts the ideal and real voting functionalities as
`CategoricalCrypto` machines, so that voting becomes a *composable*
object in the same category as the rest of the Leios network models.

The functionalities are morphisms `Machine I C`: the machine has no proper input
channel (`I`) and exposes a channel `C` on which parties *cast* votes.
<!--
```agda
{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

open import Leios.Prelude hiding (_⊗_; module Any)
open import CategoricalCrypto

import Leios.Voting.Ideal
import Leios.Voting.Real
```
-->

```agda
module Leios.Voting.Machine
  (Party      : Type)
  (EBRef      : Type)
  (honest     : Party → Type) ⦃ _ : honest ⁇¹ ⦄
  (Validated  : Party → EBRef → Type)
  (threshold  : ℕ)
  where

module Ideal = Leios.Voting.Ideal Party EBRef honest Validated threshold
open Ideal using (IdealState; ⟨_⟩)
open Ideal.IdealState using (voteLog)
```

### Channels

An honest party casts a vote on the honest channel; the adversary casts
on its own channel.

```agda
data HonestT : Mode → Type where
  CastH : Party → EBRef → HonestT Out

data AdvT : Mode → Type where
  CastA : Party → EBRef → AdvT Out

Hon Adv : Channel
Hon = simpleChannel HonestT
Adv = simpleChannel AdvT
```

### The ideal functionality

```agda
data WithState_receive_return_newState_ : MachineType I (Hon ⊗₀ Adv) IdealState where

  CastHonest : ∀ {st p eb} → honest p → Validated p eb
             → WithState st
               receive L⊗ (ϵ ⊗R) ᵗ² ↑ₒ CastH p eb
               return nothing
               newState ⟨ (p , eb) ∷ voteLog st ⟩

  CastAdv    : ∀ {st p eb} → ¬ honest p
             → WithState st
               receive L⊗ (L⊗ ϵ) ᵗ² ↑ₒ CastA p eb
               return nothing
               newState ⟨ (p , eb) ∷ voteLog st ⟩

IdealFunctionality : Machine I (Hon ⊗₀ Adv)
IdealFunctionality .Machine.State   = IdealState
IdealFunctionality .Machine.stepRel = WithState_receive_return_newState_
```

### The machine coincides with `Ideal.Step`

Every machine step is an `Ideal.Step` and vice versa, so all results about the
ideal transition system transfer to the machine.

```agda
machine⇒step : ∀ {st i o st'}
             → WithState st receive i return o newState st' → Ideal.Step st st'
machine⇒step (CastHonest hp val) = Ideal.CastHonest hp val
machine⇒step (CastAdv ¬hp)       = Ideal.CastAdv ¬hp

step⇒machine : ∀ {st st'} → Ideal.Step st st'
             → ∃[ i ] WithState st receive i return nothing newState st'
step⇒machine (Ideal.CastHonest hp val) = -, CastHonest hp val
step⇒machine (Ideal.CastAdv ¬hp)       = -, CastAdv ¬hp
```

In particular well-formedness is an invariant of the machine,
i.e. every recorded honest vote is backed by a validation.
The certificate correctness property holds in every state reachable from `init`.

```agda
wf-invariant : Invariant IdealFunctionality Ideal.WF
wf-invariant _ _ []                  wf = wf
wf-invariant _ _ (tr ∷ʳ⟨ _ , _ , stp ⟩) wf =
  Ideal.wf-step (wf-invariant _ _ tr wf) (machine⇒step stp)

cert-correctᴹ : ∀ {st eb}
  → Trace IdealFunctionality Ideal.init st
  → (corrupt : List Party)
  → (∀ {p} → Ideal.Voted p eb st → ¬ honest p → p ∈ˡ corrupt)
  → length corrupt N.< threshold
  → Ideal.Certified st eb
  → ∃[ p ] (honest p × Validated p eb)
cert-correctᴹ tr = Ideal.cert-correct (wf-invariant _ _ tr Ideal.wf-init)
```

### The real functionality as a machine

The real scheme needs the concrete vote type; parameters are as in
`Leios.Voting.Real`. There is a single channel: anyone — honest or not — casts an
unauthenticated `Vote`.

```agda
module RealMachine
  (Vote  : Type)
  (voter : Vote → Party)
  (forEB : Vote → EBRef)
  (Valid : Vote → Type) ⦃ _ : Valid ⁇¹ ⦄
  where

  module Real = Leios.Voting.Real Party EBRef honest Validated threshold
                                  Vote voter forEB Valid

  data CastT : Mode → Type where
    Cast : Vote → CastT Out

  Net : Channel
  Net = simpleChannel CastT

  data RWithState_receive_return_newState_ : MachineType I Net Real.RealState where

    Recv : ∀ {rs} (v : Vote)
         → RWithState rs
           receive L⊗ ϵ ᵗ¹ ↑ₒ Cast v
           return nothing
           newState (v ∷ rs)

  RealFunctionality : Machine I Net
  RealFunctionality .Machine.State   = Real.RealState
  RealFunctionality .Machine.stepRel = RWithState_receive_return_newState_

  machine⇒stepᴿ : ∀ {rs i o rs'}
                → RWithState rs receive i return o newState rs' → Real.Step rs rs'
  machine⇒stepᴿ (Recv v) = Real.Recv v

  step⇒machineᴿ : ∀ {rs rs'} → Real.Step rs rs'
                → ∃[ i ] RWithState rs receive i return nothing newState rs'
  step⇒machineᴿ (Real.Recv v) = -, Recv v
```

### Forward simulation at the machine level

Under `validated-if-honest`, each real machine step is matched by the ideal
machine under the abstraction `α`: a valid vote becomes an honest or adversarial
cast (depending on the voter's honesty), an invalid vote is a stutter step (`α`
is unchanged).

```agda
  simulate : ∀ {rs i o rs'}
    → (∀ v → Valid v → honest (voter v) → Validated (voter v) (forEB v))
    → RWithState rs receive i return o newState rs'
    → (Real.α rs' ≡ Real.α rs)
    ⊎ (∃[ i' ] WithState (Real.α rs) receive i' return nothing newState (Real.α rs'))
  simulate {rs} vih (Recv v) with ¿ Valid v ¿
  ... | no ¬val = inj₁ refl
  ... | yes val with ¿ honest (voter v) ¿
  ...   | yes hv = inj₂ (-, CastHonest hv (vih v val hv))
  ...   | no ¬hv = inj₂ (-, CastAdv ¬hv)

  simulate-trace : ∀ {rs rs'}
    → (∀ v → Valid v → honest (voter v) → Validated (voter v) (forEB v))
    → Trace RealFunctionality rs rs'
    → Trace IdealFunctionality (Real.α rs) (Real.α rs')
  simulate-trace vih [] = []
  simulate-trace vih (tr ∷ʳ⟨ _ , _ , stp ⟩) with simulate vih stp
  ... | inj₁ α≡          = subst (Trace IdealFunctionality _) (sym α≡)
                                 (simulate-trace vih tr)
  ... | inj₂ (i' , stp') = simulate-trace vih tr ∷ʳ⟨ i' , nothing , stp' ⟩
```

Combining the simulation with the machine-level ideal correctness: in any
reachable state of the *real* machine, a real certificate implies an honest node
validated the block.

```agda
  real-cert-correctᴹ : ∀ {rs eb}
    → (∀ v → Valid v → honest (voter v) → Validated (voter v) (forEB v))
    → (corrupt : List Party)
    → (∀ v → Valid v → ¬ honest (voter v) → voter v ∈ˡ corrupt)
    → length corrupt N.< threshold
    → Trace RealFunctionality [] rs
    → Real.RealCertified rs eb
    → ∃[ p ] (honest p × Validated p eb)
  real-cert-correctᴹ vih corrupt cc bound tr rc =
    Real.real-cert-correct (λ {v} _ → vih v) corrupt (λ {v} _ → cc v) bound rc
```
