## An ideal model of the Leios voting scheme

This gives an ideal model of voting as a small state machine and proves
the central correctness property:

> If a certificate for a block exists, then at least one honest node has
> validated that block.

The ideal functionality records a vote for a block only under the premise that the
voter validated the block (for honest parties) or that the voter is dishonest (for
adversarial parties). A *certificate* is a quorum of `threshold`-many distinct
voters. As long as the adversary controls fewer than `threshold` parties, any
certifying set must contain an honest voter, whose recorded vote carries the
validation evidence and therefore the property holds by construction.

TODO: What remains is the UC-level statement `Real ≤'UC Ideal`, for which the
library lacks a workable `≈ℰ` proof principle.
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
```agda
module Leios.Voting.Ideal
  (Party      : Type)
  (Subject    : Type)
  (honest     : Party → Type) ⦃ _ : honest ⁇¹ ⦄
  (Validated  : Party → Subject → Type)
  (threshold  : ℕ)
  where

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


```agda
Vote : Type
Vote = Party × Subject

record IdealState : Type where
  constructor ⟨_⟩
  field voteLog : List Vote

open IdealState

init : IdealState
init = ⟨ [] ⟩

Voted : Party → Subject → IdealState → Type
Voted p x st = (p , x) ∈ˡ voteLog st

data Step : IdealState → IdealState → Type where

  CastHonest : ∀ {st p x} → honest p → Validated p x
             → Step st ⟨ (p , x) ∷ voteLog st ⟩

  CastAdv    : ∀ {st p x} → ¬ honest p
             → Step st ⟨ (p , x) ∷ voteLog st ⟩
```

The functionality maintains the invariant that every honest recorded vote is backed
by a validation. This is what makes the ideal model *ideal*.

### Well-formed

```agda
WF : IdealState → Type
WF st = ∀ {p x} → Voted p x st → honest p → Validated p x

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
record Certified (st : IdealState) (x : Subject) : Type where
  field
    voters : List Party
    unique : Unique voters
    voted  : All.All (λ p → Voted p x st) voters
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
adversary is modelled by a list of parties it controls, assumed smaller than the
quorum threshold (this is the honest-participation assumption); every dishonest
voter must be one of them.

```agda
cert-correct : ∀ {st x}
  → WF st
  → (corrupt : List Party)
  → (∀ {p} → Voted p x st → ¬ honest p → p ∈ˡ corrupt)
  → length corrupt N.< threshold
  → Certified st x
  → ∃[ p ] (honest p × Validated p x)
cert-correct {st} {x} wf corrupt corrupt-covers bound cert =
  let open Certified cert
      (p , p∈voters , hp) =
        ∃honestVoter voters unique corrupt (N.<-≤-trans bound quorum)
          (λ q∈ ¬hq → corrupt-covers (All.lookup voted q∈) ¬hq)
  in p , hp , wf (All.lookup voted p∈voters) hp
```
