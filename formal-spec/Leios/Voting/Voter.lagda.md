## The voter: a machine-level implementation of the voting interface

Where `Leios.Voting.Certifier` serves the `VotingC` interface as a single
*shared ideal functionality*, this module gives the corresponding *local
component*: a per-node machine that implements the same interface by sending
votes across the diffusion network.

The voter sits between its node and the network translation layer
(`NetTranslateV` in `Network.Leios`).  The network delivers one list of votes
per round, and the round protocol is a strict request-response chain, so the
voter behaves as follows:

- a `CAST` from the node is recorded and buffered in `pending`, since the
  voter cannot send on its own initiative,
- when the network delivers the round's votes (`Deliver`), the voter records
  them and responds with its buffered casts (`Diffuse`),
- a certificate `QUERY` is answered synchronously from the vote log,
  positively iff the log contains a real certificate (`Real.RealCertified`);
  as in the protocol, the RB producer assembles the certificate locally, and
  it is never a network object.

That `n` voters over the diffusion network realize `Leios.Voting.Certifier`
is open; see `Leios1ʳ` in `Network.Leios`.

<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude
open import CategoricalCrypto

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  renaming (ε to εˢ)

import Leios.Voting.Channel
import Leios.Voting.Real
```
-->

```agda
module Leios.Voting.Voter
  (Party      : Type)
  (EBRef      : Type)
  (threshold  : ℕ)
  (Vote       : Type)
  (voter      : Vote → Party)
  (forEB      : Vote → EBRef)
  (Valid      : Vote → Type) ⦃ _ : Valid ⁇¹ ⦄
  (EBCert     : Type)
  (mkCert     : EBRef → EBCert)
  where

open Leios.Voting.Channel Vote EBRef EBCert

module Real = Leios.Voting.Real Party EBRef threshold Vote voter forEB Valid
open Real
```

### Channels

Upward the voter speaks `VotingC`, the channel the node also uses towards
the certifier.

```agda
data VoteNetT : Mode → Type where
  Diffuse : List Vote → VoteNetT Out
  Deliver : List Vote → VoteNetT In

VoteNet : Channel
VoteNet = simpleChannel VoteNetT
```

### The machine

The network authenticates nothing: a vote's voter and block are claims
inside the `Vote` value, and validity is checked only in the certificate.

```agda
record VoterState : Type where
  field log     : RealState
        pending : List Vote

open VoterState

data WithState_receive_return_newState_ : MachineType VoteNet VotingC VoterState where

  Cast-step : ∀ {s} (v : Vote) →
    WithState s
    receive L⊗ ϵ ᵗ¹ ↑ₒ CAST v
    return nothing
    newState record { log = v ∷ log s ; pending = v ∷ pending s }

  Deliver-step : ∀ {s} (vs : List Vote) →
    WithState s
    receive ϵ ⊗R ↑ᵢ Deliver vs
    return just (ϵ ⊗R ↑ₒ Diffuse (pending s))
    newState record { log = vs ++ log s ; pending = [] }

  Query-step : ∀ {s eb} →
    RealCertified (log s) eb →
    WithState s
    receive L⊗ ϵ ᵗ¹ ↑ₒ QUERY eb
    return just (L⊗ ϵ ᵗ¹ ↑ᵢ CERT (just (mkCert eb)))
    newState s

  QueryNo-step : ∀ {s eb} →
    ¬ RealCertified (log s) eb →
    WithState s
    receive L⊗ ϵ ᵗ¹ ↑ₒ QUERY eb
    return just (L⊗ ϵ ᵗ¹ ↑ᵢ CERT nothing)
    newState s

Voter : Machine VoteNet VotingC
Voter .Machine.State   = VoterState
Voter .Machine.stepRel = WithState_receive_return_newState_
```

### Refinement into the real transition system

Every machine step is a sequence of `Real.Step`s on the vote log, so every
log the voter reaches is reachable in the real scheme.

```agda
Recv* : ∀ {rs} vs → Star Step rs (vs ++ rs)
Recv* []       = εˢ
Recv* (v ∷ vs) = Recv* vs ◅◅ Recv v ◅ εˢ

machine⇒steps : ∀ {s i o s'}
              → WithState s receive i return o newState s'
              → Star Step (log s) (log s')
machine⇒steps (Cast-step v)     = Recv v ◅ εˢ
machine⇒steps (Deliver-step vs) = Recv* vs
machine⇒steps (Query-step _)    = εˢ
machine⇒steps (QueryNo-step _)  = εˢ
```

### Certificate soundness

`AnswersCert` gives the block a step positively answers a query for, if
any.

```agda
AnswersCert : ∀ {s i o s'}
            → WithState s receive i return o newState s' → Maybe EBRef
AnswersCert (Cast-step _)             = nothing
AnswersCert (Deliver-step _)          = nothing
AnswersCert (Query-step {eb = eb} _)  = just eb
AnswersCert (QueryNo-step _)          = nothing

cert-answered-certified : ∀ {s i o s' eb}
  → (stp : WithState s receive i return o newState s')
  → AnswersCert stp ≡ just eb
  → RealCertified (log s') eb
cert-answered-certified (Query-step rc) refl = rc
```

Combining with the refinement `Leios.Voting.Real` → `Leios.Voting.Ideal`:
whenever the voter answers its node's certificate query positively, some
honest party validated that block — provided honest valid votes are backed
by validation, and the adversary controls fewer than `threshold` parties
(covering all dishonest valid voters).

```agda
module Correctness
  (honest     : Party → Type) ⦃ _ : honest ⁇¹ ⦄
  (Validated  : Party → EBRef → Type)
  where

  open Refines honest Validated

  answered-cert-correct : ∀ {s i o s' eb}
    → (stp : WithState s receive i return o newState s')
    → AnswersCert stp ≡ just eb
    → (∀ v → Valid v → honest (voter v) → Validated (voter v) (forEB v))
    → (corrupt : List Party)
    → (∀ v → Valid v → ¬ honest (voter v) → voter v ∈ˡ corrupt)
    → length corrupt N.< threshold
    → ∃[ p ] (honest p × Validated p eb)
  answered-cert-correct stp deq vih corrupt cc bound =
    real-cert-correct (λ {v} _ → vih v) corrupt (λ {v} _ → cc v) bound
      (cert-answered-certified stp deq)
```
