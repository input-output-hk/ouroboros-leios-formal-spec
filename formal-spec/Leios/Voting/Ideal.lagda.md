## An ideal model of the Leios voting scheme

This gives an ideal model of voting as a small state machine and proves
the central correctness property:

> If a certificate for a block exists, then at least one honest node has
> validated that block.

The functionality records a vote only if the voter is honest and validated
the block, or is dishonest.  A *certificate* is a quorum of `threshold`-many
distinct voters.  As long as the adversary controls fewer than `threshold`
parties, every certifying set contains an honest voter, whose validation the
invariant `WF` provides.
<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (Unique)

open import Data.List.Membership.Propositional using () renaming (find to find∈)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Relation.Unary.All.Properties
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Properties
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
           → z ∈ˡ ys ++ x ∷ zs → x ≢ z → z ∈ˡ ys ++ zs
  ∈-remove ys zs z∈ x≢z with ∈-++⁻ ys z∈
  ... | inj₁ z∈ys         = ∈-++⁺ˡ z∈ys
  ... | inj₂ (here refl)  = ⊥-elim (x≢z refl)
  ... | inj₂ (there z∈zs) = ∈-++⁺ʳ ys z∈zs

  unique-⊆⇒length≤ : ∀ {A : Type} {xs ys : List A}
                   → Unique xs → (∀ {z} → z ∈ˡ xs → z ∈ˡ ys) → length xs N.≤ length ys
  unique-⊆⇒length≤ {xs = []}     _                _   = N.z≤n
  unique-⊆⇒length≤ {xs = x ∷ xs} (x≢ AllPairs.∷ u) sub with ∈-∃++ (sub (here refl))
  ... | ys₁ , ys₂ , refl =
    subst (suc (length xs) N.≤_) (sym (length-++-sucʳ ys₁ x ys₂))
      (N.s≤s (unique-⊆⇒length≤ u λ z∈ → ∈-remove ys₁ ys₂ (sub (there z∈)) (All.lookup x≢ z∈)))
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

### Well-formed

```agda
WF : IdealState → Type
WF st = ∀ {p x} → Voted p x st → honest p → Validated p x

wf-init : WF init
wf-init ()

wf-step : ∀ {st st'} → WF st → Step st st' → WF st'
wf-step _  (CastHonest _ val) (here refl) _  = val
wf-step wf (CastHonest _ _)   (there v)   hq = wf v hq
wf-step _  (CastAdv ¬hp)      (here refl) hq = ⊥-elim (¬hp hq)
wf-step wf (CastAdv _)        (there v)   hq = wf v hq
```

### Certificates and correctness

```agda
record Certified (st : IdealState) (x : Subject) : Type where
  field
    voters : List Party
    unique : Unique voters
    voted  : All.All (λ p → Voted p x st) voters
    quorum : threshold N.≤ length voters

∃honestVoter :
    (voters : List Party) → Unique voters
  → (corrupt : List Party) → length corrupt N.< length voters
  → (∀ {p} → p ∈ˡ voters → ¬ honest p → p ∈ˡ corrupt)
  → ∃[ p ] (p ∈ˡ voters × honest p)
∃honestVoter voters uniq corrupt corrupt<voters cov with Any.any? ¿ honest ¿¹ voters
... | yes h = find∈ h
... | no ¬h = ⊥-elim (N.≤⇒≯ (unique-⊆⇒length≤ uniq sub) corrupt<voters)
  where
    sub : ∀ {z} → z ∈ˡ voters → z ∈ˡ corrupt
    sub z∈ = cov z∈ (All.lookup (¬Any⇒All¬ voters ¬h) z∈)
```

The adversary is modelled by a list `corrupt` of the parties it controls,
shorter than the threshold (the honest-participation assumption); every
dishonest voter must be in it.

```agda
cert-correct : ∀ {st x}
  → WF st
  → (corrupt : List Party)
  → (∀ {p} → Voted p x st → ¬ honest p → p ∈ˡ corrupt)
  → length corrupt N.< threshold
  → Certified st x
  → ∃[ p ] (honest p × Validated p x)
cert-correct wf corrupt corrupt-covers bound cert =
  let open Certified cert
      (p , p∈voters , hp) =
        ∃honestVoter voters unique corrupt (N.<-≤-trans bound quorum)
          (λ q∈ → corrupt-covers (All.lookup voted q∈))
  in p , hp , wf (All.lookup voted p∈voters) hp
```
