## The voting certifier

The voting functionality shared between all nodes of the Leios deployment,
where `Network.Leios` tensors it with the diffusion network.

The certifier exposes one `VotingC` channel per party (`n ⨂ⁿ VotingC`), and a
vote cast on slot `p` is party `p`'s vote.  The caster's identity is thus given
by the wiring, so the functionality needs no honesty predicate: an adversary
can cast only through the slots of the parties it controls.

The functionality does the following:

- it records casts without answering them (`Cast-step`),
- it answers a certificate query synchronously from the vote log, positively
  iff the recorded votes certify the block (`Query-step`/`QueryNo-step`); no
  certificate is delivered as an event, since in the protocol it is assembled
  at RB production and travels only inside the RB,
- it lets the adversary read the vote log (`Read-step`), as votes are public.

Certificate correctness (`cert-correct`) reuses `Leios.Voting.Ideal.cert-correct`:
if the adversary controls fewer than `threshold` parties, every certificate is
backed by a vote cast through a slot it does not control.  This is a counting
argument over slots; that such a voter validated the block is not proved here.
<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (Unique)
open import CategoricalCrypto

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Properties

import Leios.Voting.Ideal
import Leios.Voting.Channel
```
-->
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

open Leios.Voting.Channel Vote EBRef EBCert

Party : Type
Party = Fin n
```

### Channels

```agda
data AdvT : Mode → Type where
  Read    : AdvT Out
  ReadRes : List (Party × Vote) → AdvT In

Adv : Channel
Adv = simpleChannel AdvT

CertifierChannel : Channel
CertifierChannel = (n ⨂ⁿ VotingC) ⊗₀ Adv
```

### State and certification

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

```agda
private
  sel : ∀ {m} (p : Party) → VotingC [ m ]⇒[ ¬ₘ m ] I ⊗ᵀ CertifierChannel
  sel p = ⨂⇒ {f = const VotingC} p
       ⇒ₜ ⊗-right-intro
       ⇒ₜ ⇒-negate-transpose-right
       ⇒ₜ ⊗-left-intro

castMsg : Party → Vote → Channel.inType (I ⊗ᵀ CertifierChannel)
castMsg p v = app (sel {m = Out} p) (CAST v)

queryMsg : Party → EBRef → Channel.inType (I ⊗ᵀ CertifierChannel)
queryMsg p eb = app (sel {m = Out} p) (QUERY eb)

certMsg : Party → Maybe EBCert → Channel.outType (I ⊗ᵀ CertifierChannel)
certMsg p c = app (sel {m = In} p) (CERT c)

data WithState_receive_return_newState_ : MachineType I CertifierChannel CertifierState where

  Cast-step : ∀ {s} p v →
    WithState s
    receive castMsg p v
    return nothing
    newState ⟨ (p , v) ∷ log s ⟩

  Query-step : ∀ {s p eb} →
    Certified (log s) eb →
    WithState s
    receive queryMsg p eb
    return just (certMsg p (just (mkCert eb)))
    newState s

  QueryNo-step : ∀ {s p eb} →
    ¬ Certified (log s) eb →
    WithState s
    receive queryMsg p eb
    return just (certMsg p nothing)
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

```agda
HasVoteFor : List (Party × Vote) → Party → EBRef → Type
HasVoteFor lg p eb = Any.Any (λ qv → proj₁ qv ≡ p × forEB (proj₂ qv) ≡ eb) lg
```

The log maps into `Leios.Voting.Ideal` with `honest` as "not corrupt" and
`Validated` as `HasVoteFor lg`.  Under that choice every logged vote is
well-formed by construction, so `wf` and `covers` hold for any log.

```agda
module _ (corrupt : List Party) {lg : List (Party × Vote)} where

  private
    honest : Party → Type
    honest p = p ∉ˡ corrupt

    module Id = Leios.Voting.Ideal Party EBRef honest (HasVoteFor lg) threshold

    voteRef : Party × Vote → Party × EBRef
    voteRef qv = proj₁ qv , forEB (proj₂ qv)

    α : Id.IdealState
    α = Id.⟨ L.map voteRef lg ⟩

    wf : Id.WF α
    wf p∈ _ with ∈-map⁻ voteRef p∈
    ... | _ , qv∈lg , refl = Any.map (λ where refl → refl , refl) qv∈lg

    covers : ∀ {p eb} → Id.Voted p eb α → ¬ honest p → p ∈ˡ corrupt
    covers {p} _ = decidable-stable (Any.any? (p ≟_) corrupt)

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
        ... | qv , qv∈votes , refl =
          subst (λ e → (proj₁ qv , e) ∈ˡ L.map voteRef lg) (All.lookup forEB≡ qv∈votes)
            (∈-map⁺ voteRef (votes⊆ qv∈votes))

  cert-correct : ∀ {eb}
    → length corrupt N.< threshold
    → Certified lg eb
    → ∃[ p ] (p ∉ˡ corrupt × HasVoteFor lg p eb)
  cert-correct bound cert =
    Id.cert-correct wf corrupt covers bound (toIdealCert cert)
```
