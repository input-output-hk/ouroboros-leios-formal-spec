## The voter: a machine-level implementation of the voting interface

Where `Leios.Voting.Certifier` serves the `VotingC` interface as a single
*shared ideal functionality*, this module gives the corresponding *local
component*: a per-node machine that implements the same interface by sending
votes across the diffusion network.

The voter sits between its node and the network translation layer
(`NetTranslateV` in `Network.Leios`), which multiplexes votes into the
diffusion network's message type. The network delivers one *list* of votes
per round, and the round protocol is a strict request-response chain, so:

- a `CAST` from the node is recorded and buffered (`pending`) — the voter
  cannot send on its own initiative,
- when the network delivers the round's votes (`Deliver`), the voter records
  them and *responds* with its buffered casts (`Diffuse`), which the
  translation layer folds into the round's outgoing messages,
- a certificate `QUERY` from the node is answered synchronously from the
  vote log: positively — with an assembled certificate — iff the recorded
  votes contain a real certificate (`Real.RealCertified`: a quorum of valid
  votes by distinct voters). This matches the protocol, where the RB
  producer assembles the certificate locally from the votes it holds; the
  certificate is never a network object.

The voter's vote log is `Real.RealState` from `Leios.Voting.Real` and every
step is a (sequence of) `Real.Step`s, so the state-level refinement into the
ideal model applies verbatim: every positive query answer is backed by a
vote of an honest party (`Correctness.answered-cert-correct`).

What this module does *not* provide is the UC-level statement that `n`
voters wired through a diffusion network realize the `Certifier`
functionality — that requires relating machines up to trace equivalence,
which the library does not support yet.

<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (_⊗_)
open import CategoricalCrypto

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅_; _◅◅_)
  renaming (ε to εˢ)

import Leios.Voting.Channel
import Leios.Voting.Real
```
-->

The parameters are those of `Leios.Voting.Real`, extended by the concrete
certificate type and constructor used on the `VotingC` interface. Honesty
and validation are not needed to build the machine; they parameterize the
`Correctness` module at the end.

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
```

### Channels

Upward the voter speaks `VotingC` — the same channel the node already uses
towards the certifier. Downward it speaks the per-round vote-diffusion
channel: a delivered batch of votes is answered with the batch of pending
casts.

```agda
data VoteNetT : Mode → Type where
  Diffuse : List Vote → VoteNetT Out
  Deliver : List Vote → VoteNetT In

VoteNet : Channel
VoteNet = simpleChannel VoteNetT
```

### The machine

The state is the log of votes seen so far (own casts and delivered ones)
together with the casts not yet handed to the network. A vote carries its
claimed voter and block inside the `Vote` value; the network is not assumed
to authenticate anything — validity is only checked where it matters, in
the certificate.

```agda
record VoterState : Type where
  field log     : Real.RealState
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

  Query-step : ∀ {s} {eb : EBRef} →
    Real.RealCertified (log s) eb →
    WithState s
    receive L⊗ ϵ ᵗ¹ ↑ₒ QUERY eb
    return just (L⊗ ϵ ᵗ¹ ↑ᵢ CERT (just (mkCert eb)))
    newState s

  QueryNo-step : ∀ {s} {eb : EBRef} →
    ¬ Real.RealCertified (log s) eb →
    WithState s
    receive L⊗ ϵ ᵗ¹ ↑ₒ QUERY eb
    return just (L⊗ ϵ ᵗ¹ ↑ᵢ CERT nothing)
    newState s

Voter : Machine VoteNet VotingC
Voter .Machine.State   = VoterState
Voter .Machine.stepRel = WithState_receive_return_newState_
```

### Refinement into the real transition system

Every machine step corresponds to a sequence of `Real.Step`s on the vote
log, so the voter's reachable logs are exactly the vote logs of the real
scheme.

```agda
Recv* : ∀ rs vs → Star Real.Step rs (vs ++ rs)
Recv* rs []       = εˢ
Recv* rs (v ∷ vs) = Recv* rs vs ◅◅ (Real.Recv v ◅ εˢ)

machine⇒steps : ∀ {s i o s'}
              → WithState s receive i return o newState s'
              → Star Real.Step (log s) (log s')
machine⇒steps (Cast-step v)     = Real.Recv v ◅ εˢ
machine⇒steps (Deliver-step vs) = Recv* _ vs
machine⇒steps (Query-step _)    = εˢ
machine⇒steps (QueryNo-step _)  = εˢ
```

### Certificate soundness

`AnswersCert` reads off the block a step answers a certificate query for
positively, if any. A positive answer is always backed by a real
certificate on the vote log — it is a premise of the only rule that gives
one.

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
  → Real.RealCertified (log s') eb
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

  open Real.Refines honest Validated

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
