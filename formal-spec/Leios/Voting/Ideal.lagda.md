## An ideal model of the Leios voting scheme

This module covers tasks 2–4 of
[#689 "Formalize correctness of certificates"](https://github.com/input-output-hk/ouroboros-leios/issues/689):
it defines the correctness property, gives the ideal model, and proves the
property (the real side and its transfer live in `Leios.Voting.Real`). Task 1 —
the composable-state-machine refactor — lives in `Leios.Voting.Machine`, where the
`Step` relations below are recast as `CategoricalCrypto` machines and the protocol
drives the real voting machine through a machine-backed `VotingAbstract`. What
remains of #689 is the UC-level statement `Real ≤'UC Ideal`, for which the library
lacks a workable `≈ℰ` proof principle — see the note in `Leios.Voting.Real`.

It gives an *ideal* model of voting as a small state machine and states — and
proves — the central correctness property:

> **If a certificate for a block exists, then at least one honest node has
> validated that block.**

The ideal functionality records a vote for a block only under the premise that the
voter validated the block (for honest parties) or that the voter is dishonest (for
adversarial parties). A *certificate* is a quorum of `threshold`-many distinct
voters. As long as the adversary controls fewer than `threshold` parties, any
certifying set must contain an honest voter, whose recorded vote carries the
validation evidence — so the property holds by construction of the ideal.

Here the certificate predicate (`Certified`) is *derived* from the recorded votes
and an explicit `threshold`, rather than being the opaque `isVoteCertified` field of
`Leios.Voting.VotingAbstract`. The correctness property below (`cert-correct`) has
since been folded back into that shared `VotingAbstract` (which
`SpecStructure`/`Protocol`/`Blockchain.Safety` depend on) as a `cert-correct`
proof obligation next to `isVoteCertified`: the abstraction now guarantees that a
certificate implies an honest voter validated the block. That obligation is
discharged via this ideal model — see `Leios.Voting.Real` (`real-cert-correct`) and
the machine-backed instance built by `Leios.Voting.Machine.RealMachine.Realize`,
where `isVoteCertified` is realised from the vote log and `threshold`.

<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (Unique)

open import Data.List.Membership.Propositional using () renaming (find to find∈)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Properties using (length-++)
```
-->

The model is parameterised over an abstract notion of party, block reference, a
(decidable) honesty predicate, a validation predicate, and the certificate
threshold.

```agda
module Leios.Voting.Ideal
  (Party      : Type)
  (EBRef      : Type)
  (honest     : Party → Type) ⦃ _ : honest ⁇¹ ⦄
  (Validated  : Party → EBRef → Type)
  (threshold  : ℕ)
  where
```

### A combinatorial pigeonhole lemma

A duplicate-free list contained in another list is no longer than it. This is the
counting core of the correctness argument: a quorum of distinct voters cannot fit
inside a strictly smaller set of corrupt parties.

```agda
private
  ∈-remove : ∀ {A : Type} {z x : A} (ys zs : List A)
           → z ∈ˡ ys ++ x ∷ zs → z ≢ x → z ∈ˡ ys ++ zs
  ∈-remove ys zs z∈ z≢x with ∈-++⁻ ys z∈
  ... | inj₁ z∈ys         = ∈-++⁺ˡ z∈ys
  ... | inj₂ (here z≡x)   = ⊥-elim (z≢x z≡x)
  ... | inj₂ (there z∈zs) = ∈-++⁺ʳ ys z∈zs

  unique-⊆⇒length≤ : ∀ {A : Type} {xs ys : List A}
                   → Unique xs → (∀ {z} → z ∈ˡ xs → z ∈ˡ ys) → length xs N.≤ length ys
  unique-⊆⇒length≤ {xs = []}     _                _   = N.z≤n
  unique-⊆⇒length≤ {xs = x ∷ xs} (x≢ AllPairs.∷ u) sub with ∈-∃++ (sub (here refl))
  ... | ys₁ , ys₂ , refl =
    subst (λ n → suc (length xs) N.≤ n)
          (sym (trans (length-++ ys₁) (N.+-suc (length ys₁) (length ys₂))))
          (N.s≤s (subst (λ n → length xs N.≤ n) (length-++ ys₁) (unique-⊆⇒length≤ u sub')))
    where
      sub' : ∀ {z} → z ∈ˡ xs → z ∈ˡ ys₁ ++ ys₂
      sub' {z} z∈ = ∈-remove ys₁ ys₂ (sub (there z∈)) (λ z≡x → All.lookup x≢ z∈ (sym z≡x))
```

### The ideal functionality

The state is just the log of votes cast so far.

```agda
record IdealState : Type where
  constructor ⟨_⟩
  field voteLog : List (Party × EBRef)

open IdealState

init : IdealState
init = ⟨ [] ⟩

Voted : Party → EBRef → IdealState → Type
Voted p eb st = (p , eb) ∈ˡ voteLog st
```

A step either records an honest vote — only permitted once the voter has validated
the block — or an adversarial vote from a dishonest party.

```agda
data Step : IdealState → IdealState → Type where
  CastHonest : ∀ {st p eb} → honest p → Validated p eb
             → Step st ⟨ (p , eb) ∷ voteLog st ⟩
  CastAdv    : ∀ {st p eb} → ¬ honest p
             → Step st ⟨ (p , eb) ∷ voteLog st ⟩
```

The functionality maintains the invariant that every honest recorded vote is backed
by a validation. This is what makes the ideal model *ideal*.

```agda
WF : IdealState → Type
WF st = ∀ {p eb} → Voted p eb st → honest p → Validated p eb

wf-init : WF init
wf-init ()

wf-step : ∀ {st st'} → WF st → Step st st' → WF st'
wf-step wf (CastHonest hp val) (here refl) hq = val
wf-step wf (CastHonest hp val) (there v)   hq = wf v hq
wf-step wf (CastAdv ¬hp)       (here refl) hq = ⊥-elim (¬hp hq)
wf-step wf (CastAdv ¬hp)       (there v)   hq = wf v hq
```

### Certificates and correctness

A certificate is a quorum of `threshold`-many *distinct* parties that have all voted
for the block.

```agda
record Certified (st : IdealState) (eb : EBRef) : Type where
  field
    voters : List Party
    unique : Unique voters
    voted  : All.All (λ p → Voted p eb st) voters
    quorum : threshold N.≤ length voters
```

If the certificate's quorum is larger than the set of corrupt parties, one of the
voters must be honest.

```agda
∃honestVoter :
    (voters : List Party) → Unique voters
  → (corrupt : List Party) → length corrupt N.< length voters
  → (∀ {p} → p ∈ˡ voters → ¬ honest p → p ∈ˡ corrupt)
  → ∃[ p ] (p ∈ˡ voters × honest p)
∃honestVoter voters uniq corrupt corrupt<voters cov with Any.any? ¿ honest ¿¹ voters
... | yes h = find∈ h
... | no ¬h = ⊥-elim (N.<-irrefl refl (N.≤-<-trans (unique-⊆⇒length≤ uniq sub) corrupt<voters))
  where
    sub : ∀ {z} → z ∈ˡ voters → z ∈ˡ corrupt
    sub {z} z∈ = cov z∈ (All.lookup (¬Any⇒All¬ voters ¬h) z∈)
```

The main property: a certificate implies an honest node validated the block. The
adversary is modelled by a list `corrupt` of parties it controls, assumed smaller
than the quorum threshold (this is the honest-participation assumption); every
dishonest voter must be one of them.

```agda
cert-correct : ∀ {st eb}
  → WF st
  → (corrupt : List Party)
  → (∀ {p} → Voted p eb st → ¬ honest p → p ∈ˡ corrupt)
  → length corrupt N.< threshold
  → Certified st eb
  → ∃[ p ] (honest p × Validated p eb)
cert-correct {st} {eb} wf corrupt corrupt-covers bound cert =
  let open Certified cert
      (p , p∈voters , hp) =
        ∃honestVoter voters unique corrupt (N.<-≤-trans bound quorum)
          (λ q∈ ¬hq → corrupt-covers (All.lookup voted q∈) ¬hq)
  in p , hp , wf (All.lookup voted p∈voters) hp
```
