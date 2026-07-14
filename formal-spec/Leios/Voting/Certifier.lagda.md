## The voting certifier

This module defines the voting functionality that is wired into the Leios
deployment as a functionality shared between all nodes, tensored with the
diffusion network.

The certifier exposes one `VotingC` channel *per party* (`n ⨂ⁿ VotingC`):
slot `p` of the tensor is party `p`'s channel. A vote cast on slot `p`
therefore *is* party `p`'s vote — the caster's identity is structural, given
by the wiring, and the functionality needs no honesty predicate: an adversary
can only cast through the slots of the parties it controls.

The functionality

- records casts (`Cast-step`),
- delivers a certificate for an endorser block to a party when instructed to
  by the adversary — standard UC-style scheduling — but *only* under the
  premise that the recorded votes certify the block (`Deliver-step`),
- lets the adversary observe the vote log (`Read-step`); votes are public.

Certificate correctness (`cert-correct`) is obtained by mapping the
certifier's vote log into the refined ideal functionality `Leios.Voting.Ideal`,
instantiating `honest` with "not controlled by the adversary" and `Validated`
with "has a recorded vote for the block", and reusing `Ideal.cert-correct`:
if the adversary controls fewer than `threshold` parties, any certificate
must be backed by a vote cast through a slot the adversary does not control.
<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (_⊗_; Unique)
open import CategoricalCrypto

open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Unary.All as All

import Leios.Voting.Ideal
import Leios.Voting.Channel
```
-->
The certifier is parameterized by the number of parties, the concrete vote
and certificate types, the block reference a vote endorses, a certificate
constructor and the quorum threshold.
```agda
module Leios.Voting.Certifier
  (n         : ℕ)
  (Vote      : Type)
  (EBRef     : Type)
  (EBCert    : Type)
  (forEB     : Vote → EBRef)
  (mkCert    : EBRef → EBCert)
  (threshold : ℕ)
  where

open Leios.Voting.Channel Vote EBCert

Party : Type
Party = Fin n
```

### Channels

One `VotingC` per party, and an adversary channel for scheduling deliveries
and observing the vote log.

```agda
data AdvT : Mode → Type where
  DeliverEB : Party → EBRef → AdvT Out
  Read      : AdvT Out
  ReadRes   : List (Party × Vote) → AdvT In

Adv : Channel
Adv = simpleChannel AdvT

CertifierChannel : Channel
CertifierChannel = (n ⨂ⁿ VotingC) ⊗₀ Adv
```

### State and certification

The state is the log of cast votes, each tagged with the *slot* it arrived
on. A block is certified by a quorum of `threshold`-many votes for it, cast
through distinct slots.

```agda
record CertifierState : Type where
  constructor ⟨_⟩
  field log : List (Party × Vote)

open CertifierState

init : CertifierState
init = ⟨ [] ⟩

record Certified (lg : List (Party × Vote)) (eb : EBRef) : Type where
  field
    votes  : List (Party × Vote)
    votes⊆ : ∀ {pv} → pv ∈ˡ votes → pv ∈ˡ lg
    forEB≡ : All.All (λ pv → forEB (proj₂ pv) ≡ eb) votes
    unique : Unique (L.map proj₁ votes)
    quorum : threshold N.≤ length votes
```

### The functionality

Messages on party `p`'s slot are addressed via the generic selection
`⨂⇒ p` into the `n`-fold tensor; `castMsg`/`certMsg` inject a cast received
from, and a certificate delivered to, party `p` into the machine channel.

```agda
private
  sel : ∀ {m} (p : Party) → VotingC [ m ]⇒[ ¬ₘ m ] I ⊗ᵀ CertifierChannel
  sel p = ⨂⇒ {f = const VotingC} p
       ⇒ₜ ⊗-right-intro
       ⇒ₜ ⇒-negate-transpose-right
       ⇒ₜ ⊗-left-intro

castMsg : Party → Vote → Channel.inType (I ⊗ᵀ CertifierChannel)
castMsg p v = app (sel {m = Out} p) (CAST v)

certMsg : Party → EBCert → Channel.outType (I ⊗ᵀ CertifierChannel)
certMsg p c = app (sel {m = In} p) (CERT c)

data WithState_receive_return_newState_ : MachineType I CertifierChannel CertifierState where

  Cast-step : ∀ {s} (p : Party) (v : Vote) →
    WithState s
    receive castMsg p v
    return nothing
    newState ⟨ (p , v) ∷ log s ⟩

  Deliver-step : ∀ {s} {p : Party} {eb : EBRef} →
    Certified (log s) eb →
    WithState s
    receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ DeliverEB p eb
    return just (certMsg p (mkCert eb))
    newState s

  Read-step : ∀ {s} →
    WithState s
    receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ Read
    return just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ ReadRes (log s))
    newState s

Functionality : Machine I CertifierChannel
Functionality .Machine.State   = CertifierState
Functionality .Machine.stepRel = WithState_receive_return_newState_
```

### Certificate correctness

A vote for `eb` recorded on party `p`'s slot:

```agda
HasVoteFor : List (Party × Vote) → Party → EBRef → Type
HasVoteFor lg p eb = Any.Any (λ qv → proj₁ qv ≡ p × forEB (proj₂ qv) ≡ eb) lg
```

The certifier log maps into the refined ideal functionality: `honest` becomes "not
one of the corrupt parties" and `Validated p eb` becomes `HasVoteFor lg p eb`
— under which *every* logged vote is trivially well-formed, so
`Ideal.cert-correct` applies unconditionally.

```agda
module _ (corrupt : List Party) {lg : List (Party × Vote)} where

  private
    honest : Party → Type
    honest p = p ∉ˡ corrupt

    Dec-honest : honest ⁇¹
    Dec-honest {p} .dec = ¬? (Any.any? (p ≟_) corrupt)

    module Id = Leios.Voting.Ideal Party EBRef honest ⦃ Dec-honest ⦄ (HasVoteFor lg) threshold

    voteRef : Party × Vote → Party × EBRef
    voteRef qv = proj₁ qv , forEB (proj₂ qv)

    α : Id.IdealState
    α = record { voteLog = L.map voteRef lg }

    wf : Id.WF α
    wf p∈ _ with ∈-map⁻ voteRef p∈
    ... | _ , qv∈lg , eq =
      Any.map (λ where refl → sym (cong proj₁ eq) , sym (cong proj₂ eq)) qv∈lg

    covers : ∀ {p eb} → Id.Voted p eb α → ¬ honest p → p ∈ˡ corrupt
    covers {p} _ ¬h with Any.any? (p ≟_) corrupt
    ... | yes p∈  = p∈
    ... | no  ¬p∈ = ⊥-elim (¬h ¬p∈)

    toIdealCert : ∀ {eb} → Certified lg eb → Id.Certified α eb
    toIdealCert {eb} cert = record
      { voters = L.map proj₁ votes
      ; unique = unique
      ; voted  = All.tabulate voted∈
      ; quorum = subst (threshold N.≤_) (sym (length-map proj₁ votes)) quorum
      }
      where
        open Certified cert
        voted∈ : ∀ {p} → p ∈ˡ L.map proj₁ votes → Id.Voted p eb α
        voted∈ p∈ with ∈-map⁻ proj₁ p∈
        ... | qv , qv∈votes , p≡ =
          subst (_∈ˡ L.map voteRef lg)
                (cong₂ _,_ (sym p≡) (All.lookup forEB≡ qv∈votes))
                (∈-map⁺ voteRef (votes⊆ qv∈votes))

  cert-correct : ∀ {eb}
    → length corrupt N.< threshold
    → Certified lg eb
    → ∃[ p ] (p ∉ˡ corrupt × HasVoteFor lg p eb)
  cert-correct bound cert =
    Id.cert-correct wf corrupt covers bound (toIdealCert cert)
```
