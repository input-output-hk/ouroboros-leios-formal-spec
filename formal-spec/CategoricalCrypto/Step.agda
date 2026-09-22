{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id; _∘_)
import CategoricalCrypto as CC

-- Building steps of composite machines from steps of their components.
--
-- `_⊗₁_` and `_∘_` reroute the messages of their components through
-- `⊗σ`/`∘σ` and the restrictions `_∣ˡ`/`_∣^ˡ`, all of which compute only
-- once `_⊗₀_` is unfolded.  The lemmas below do that unfolding once, so that
-- a step of a composite can be assembled outside any `opaque` block, in the
-- selection syntax the machines' own rules are written in.
--
-- Message spellings, for a machine `M : Machine A B` (channel `A ⊗₀ B ᵀ`):
--   domain input     `ϵ ⊗R ↑ᵢ a`         a  : inType A
--   domain output    `ϵ ⊗R ↑ₒ a'`        a' : outType A
--   codomain input   `L⊗ ϵ ᵗ¹ ↑ₒ b`      b  : outType B
--   codomain output  `L⊗ ϵ ᵗ¹ ↑ᵢ b'`     b' : inType B
module CategoricalCrypto.Step where

open Channel using (inType; outType)

private variable
  A B C D : Channel

-- A step of a machine, behind an opaque name.  The step relation of a
-- composite unfolds to a trace relation over rerouted messages, and a
-- metavariable caught under that rerouting is never solved; with `Step`
-- opaque, unification stays first-order on the messages as written.
opaque
  Step : (M : Machine A B) → Machine.State M
       → inType (A ⊗ᵀ B) → Maybe (outType (A ⊗ᵀ B)) → Machine.State M → Type
  Step M = Machine.stepRel M

  toStep : ∀ {M : Machine A B} {s s' i o} → Machine.stepRel M s i o s' → Step M s i o s'
  toStep st = st

  fromStep : ∀ {M : Machine A B} {s s' i o} → Step M s i o s' → Machine.stepRel M s i o s'
  fromStep st = st

-- Rewriting the messages of a step.
step-subst : ∀ {M : Machine A B} {s s' i i' o o'} → i ≡ i' → o ≡ o'
           → Step M s i o s' → Step M s i' o' s'
step-subst refl refl st = st

-- Injectivity and conflict helpers over transparent sums, and the inversion
-- views at general indices.  Public: modules inverting their own machines'
-- steps need them too.
module Raw where
  -- Injectivity and conflict helpers over transparent sums.  They are applied
  -- to equations between channel messages inside the unfolding blocks, where
  -- those messages reduce to sums.
  inj₁-inj : ∀ {X Y : Type} {x y : X} → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y) → x ≡ y
  inj₁-inj refl = refl

  inj₂-inj : ∀ {X Y : Type} {x y : Y} → _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y) → x ≡ y
  inj₂-inj refl = refl

  inj₁≢inj₂ : ∀ {X Y : Type} {x : X} {y : Y} {ℓ} {W : Set ℓ}
            → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
  inj₁≢inj₂ ()

  just-inj : ∀ {X : Type} {x y : X} → _≡_ {A = Maybe X} (just x) (just y) → x ≡ y
  just-inj refl = refl

  just≢nothing : ∀ {X : Type} {x : X} {ℓ} {W : Set ℓ} → _≡_ {A = Maybe X} (just x) nothing → W
  just≢nothing ()

  nothing≢just : ∀ {X : Type} {x : X} {ℓ} {W : Set ℓ} → _≡_ {A = Maybe X} nothing (just x) → W
  nothing≢just ()

  -- Inversion views at fully general indices.  Splitting a trace or tensor
  -- step with general indices always succeeds; the resulting equations are
  -- then discharged by conversion inside the unfolding blocks, since the
  -- case-split unifier itself does not see the unfolding.
  trace-view :
    ∀ {A B C} {M : Machine (A ⊗₀ C) (B ⊗₀ C)} {s i w s'}
    → TraceRel M s i w s'
    → (Machine.stepRel M s i w s')
    ⊎ (∃ λ s₁ → ∃ λ outC →
         Machine.stepRel M s i (just ((L⊗ ϵ) ⊗R ↑ₒ outC)) s₁
         × TraceRel M s₁ ((L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹) ↑ᵢ outC) w s')
    ⊎ (∃ λ s₁ → ∃ λ inC →
         Machine.stepRel M s i (just ((L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹) ↑ₒ inC)) s₁
         × TraceRel M s₁ (((L⊗ ϵ) ⊗R) ↑ᵢ inC) w s')
  trace-view Trace[ p ]      = inj₁ p
  trace-view (p Trace∷ₒ tr₀) = inj₂ (inj₁ (_ , _ , p , tr₀))
  trace-view (p Trace∷ᵢ tr₀) = inj₂ (inj₂ (_ , _ , p , tr₀))

  comp-view :
    ∀ {A B C D} {M₁ : Machine A B} {M₂ : Machine C D}
      {sp : Machine.State M₁ × Machine.State M₂} {x y sp'}
    → Tensor.CompRel M₁ M₂ sp x y sp'
    → (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (ϵ ⊗R) ↑ᵢ mᵢ) × (y ≡ ((ϵ ⊗R) ↑ₒ_ <$> mo))
         × (proj₂ sp' ≡ proj₂ sp)
         × Machine.stepRel M₁ (proj₁ sp) mᵢ mo (proj₁ sp'))
    ⊎ (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (L⊗ ϵ) ↑ᵢ mᵢ) × (y ≡ ((L⊗ ϵ) ↑ₒ_ <$> mo))
         × (proj₁ sp' ≡ proj₁ sp)
         × Machine.stepRel M₂ (proj₂ sp) mᵢ mo (proj₂ sp'))
  comp-view (Tensor.Step₁ q) = inj₁ (_ , _ , refl , refl , refl , q)
  comp-view (Tensor.Step₂ q) = inj₂ (_ , _ , refl , refl , refl , q)

open Raw

------------------------------------------------------------------------
-- Nesting selections.  A two-level selection is the one-level selection
-- of a one-level message; the rules of a machine use the flat form, the
-- lemmas below the nested one.

opaque
  unfolding _⊗₀_

  nest-⊗Rᵢ : ∀ {X Y} (p : X [ In ]⇒[ In ]ᵍ Y) (x : inType X)
           → (p ⊗R) ↑ᵢ x ≡ (_⊗R {C = C} ϵ) ↑ᵢ (p ↑ᵢ x)
  nest-⊗Rᵢ p x = refl

  nest-⊗Rₒ : ∀ {X Y} (p : X [ Out ]⇒[ Out ]ᵍ Y) (x : outType X)
           → (p ⊗R) ↑ₒ x ≡ (_⊗R {C = C} ϵ) ↑ₒ (p ↑ₒ x)
  nest-⊗Rₒ p x = refl

  nest-L⊗ᵢ : ∀ {X Y} (p : X [ In ]⇒[ In ]ᵍ Y) (x : inType X)
           → (L⊗ p) ↑ᵢ x ≡ (L⊗_ {C = C} ϵ) ↑ᵢ (p ↑ᵢ x)
  nest-L⊗ᵢ p x = refl

  nest-L⊗ₒ : ∀ {X Y} (p : X [ Out ]⇒[ Out ]ᵍ Y) (x : outType X)
           → (L⊗ p) ↑ₒ x ≡ (L⊗_ {C = C} ϵ) ↑ₒ (p ↑ₒ x)
  nest-L⊗ₒ p x = refl

  -- The codomain side of a machine channel: `L⊗ p ᵗ¹` for a selection `p`
  -- into the codomain.
  nest-ᵗ¹ᵢ : ∀ {X Y} (p : X [ In ]⇒[ In ]ᵍ Y) (x : inType X)
           → (L⊗ p ᵗ¹) ↑ᵢ x ≡ (L⊗_ {C = C} (ϵ ᵗ¹)) ↑ᵢ (p ↑ᵢ x)
  nest-ᵗ¹ᵢ p x = refl

  nest-ᵗ¹ₒ : ∀ {X Y} (p : X [ Out ]⇒[ Out ]ᵍ Y) (x : outType X)
           → (L⊗ p ᵗ¹) ↑ₒ x ≡ (L⊗_ {C = C} (ϵ ᵗ¹)) ↑ₒ (p ↑ₒ x)
  nest-ᵗ¹ₒ p x = refl

------------------------------------------------------------------------
-- The four message shapes of a machine channel are disjoint and injective.

opaque
  unfolding _⊗₀_

  inᵈ-inj : ∀ {a a' : inType A} → _≡_ {A = inType (A ⊗ᵀ B)} (ϵ ⊗R ↑ᵢ a) (ϵ ⊗R ↑ᵢ a') → a ≡ a'
  inᵈ-inj refl = refl

  inᶜ-inj : ∀ {b b' : outType B} → _≡_ {A = inType (A ⊗ᵀ B)} (L⊗ ϵ ᵗ¹ ↑ₒ b) (L⊗ ϵ ᵗ¹ ↑ₒ b') → b ≡ b'
  inᶜ-inj refl = refl

  outᵈ-inj : ∀ {a a' : outType A} → _≡_ {A = outType (A ⊗ᵀ B)} (ϵ ⊗R ↑ₒ a) (ϵ ⊗R ↑ₒ a') → a ≡ a'
  outᵈ-inj refl = refl

  outᶜ-inj : ∀ {b b' : inType B} → _≡_ {A = outType (A ⊗ᵀ B)} (L⊗ ϵ ᵗ¹ ↑ᵢ b) (L⊗ ϵ ᵗ¹ ↑ᵢ b') → b ≡ b'
  outᶜ-inj refl = refl

  inᵈ≢inᶜ : ∀ {a : inType A} {b : outType B} {ℓ} {W : Set ℓ}
          → _≡_ {A = inType (A ⊗ᵀ B)} (ϵ ⊗R ↑ᵢ a) (L⊗ ϵ ᵗ¹ ↑ₒ b) → W
  inᵈ≢inᶜ ()

  outᵈ≢outᶜ : ∀ {a : outType A} {b : inType B} {ℓ} {W : Set ℓ}
            → _≡_ {A = outType (A ⊗ᵀ B)} (ϵ ⊗R ↑ₒ a) (L⊗ ϵ ᵗ¹ ↑ᵢ b) → W
  outᵈ≢outᶜ ()

------------------------------------------------------------------------
-- Forwarders: `TotalFunctionMachine' p q` relays a domain input through
-- `p` and a codomain input through `q`.

opaque
  unfolding _⊗₀_ Step

  fwd-dom : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A) (a : inType A)
          → Step (TotalFunctionMachine' p q) tt
              (ϵ ⊗R ↑ᵢ a) (just (L⊗ ϵ ᵗ¹ ↑ᵢ app p a)) tt
  fwd-dom p q a = refl

  fwd-cod : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A) (b : outType B)
          → Step (TotalFunctionMachine' p q) tt
              (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (ϵ ⊗R ↑ₒ app q b)) tt
  fwd-cod p q b = refl

  -- Conversely, a forwarder's step is determined by its input.
  fwd-dom-inv : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A) → ∀ {a o s s'}
          → Step (TotalFunctionMachine' p q) s (ϵ ⊗R ↑ᵢ a) o s'
          → o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ app p a)
  fwd-dom-inv p q st = sym st

  fwd-cod-inv : (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A) → ∀ {b o s s'}
          → Step (TotalFunctionMachine' p q) s (L⊗ ϵ ᵗ¹ ↑ₒ b) o s'
          → o ≡ just (ϵ ⊗R ↑ₒ app q b)
  fwd-cod-inv p q st = sym st

  id-dom : (a : inType A) → Step (CC.id {A}) tt (ϵ ⊗R ↑ᵢ a) (just (L⊗ ϵ ᵗ¹ ↑ᵢ a)) tt
  id-dom a = refl

  id-dom-inv : ∀ {a o} {s s' : ⊤} → Step (CC.id {A}) s (ϵ ⊗R ↑ᵢ a) o s' → o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ a)
  id-dom-inv st = sym st

  id-cod-inv : ∀ {a o} {s s' : ⊤} → Step (CC.id {A}) s (L⊗ ϵ ᵗ¹ ↑ₒ a) o s' → o ≡ just (ϵ ⊗R ↑ₒ a)
  id-cod-inv st = sym st

  id-cod : (a : outType A) → Step (CC.id {A}) tt (L⊗ ϵ ᵗ¹ ↑ₒ a) (just (ϵ ⊗R ↑ₒ a)) tt
  id-cod a = refl

------------------------------------------------------------------------
-- Tensor: a step of either component is a step of `M₁ ⊗₁ M₂`, on the
-- corresponding half of each channel.

module Tensor′ {A B C D : Channel} (M₁ : Machine A B) (M₂ : Machine C D) where
  private
    step₁ = Step M₁
    step₂ = Step M₂
    step  = Step (M₁ ⊗₁ M₂)

  opaque
    unfolding _⊗₀_ Step

    -- M₁, domain input
    ⊗₁-dom₁-∅ : ∀ {s₁ s₁' s₂ a}
      → step₁ s₁ (ϵ ⊗R ↑ᵢ a) nothing s₁'
      → step (s₁ , s₂) ((ϵ ⊗R) ⊗R ↑ᵢ a) nothing (s₁' , s₂)
    ⊗₁-dom₁-∅ st = Tensor.Step₁ st

    ⊗₁-dom₁-dom : ∀ {s₁ s₁' s₂ a a'}
      → step₁ s₁ (ϵ ⊗R ↑ᵢ a) (just (ϵ ⊗R ↑ₒ a')) s₁'
      → step (s₁ , s₂) ((ϵ ⊗R) ⊗R ↑ᵢ a) (just ((ϵ ⊗R) ⊗R ↑ₒ a')) (s₁' , s₂)
    ⊗₁-dom₁-dom st = Tensor.Step₁ st

    ⊗₁-dom₁-cod : ∀ {s₁ s₁' s₂ a b'}
      → step₁ s₁ (ϵ ⊗R ↑ᵢ a) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₁'
      → step (s₁ , s₂) ((ϵ ⊗R) ⊗R ↑ᵢ a) (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ b')) (s₁' , s₂)
    ⊗₁-dom₁-cod st = Tensor.Step₁ st

    -- M₁, codomain input
    ⊗₁-cod₁-∅ : ∀ {s₁ s₁' s₂ b}
      → step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ b) nothing s₁'
      → step (s₁ , s₂) (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ b) nothing (s₁' , s₂)
    ⊗₁-cod₁-∅ st = Tensor.Step₁ st

    ⊗₁-cod₁-dom : ∀ {s₁ s₁' s₂ b a'}
      → step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (ϵ ⊗R ↑ₒ a')) s₁'
      → step (s₁ , s₂) (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ b) (just ((ϵ ⊗R) ⊗R ↑ₒ a')) (s₁' , s₂)
    ⊗₁-cod₁-dom st = Tensor.Step₁ st

    ⊗₁-cod₁-cod : ∀ {s₁ s₁' s₂ b b'}
      → step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₁'
      → step (s₁ , s₂) (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ b) (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ b')) (s₁' , s₂)
    ⊗₁-cod₁-cod st = Tensor.Step₁ st

    -- M₂, domain input
    ⊗₁-dom₂-∅ : ∀ {s₁ s₂ s₂' c}
      → step₂ s₂ (ϵ ⊗R ↑ᵢ c) nothing s₂'
      → step (s₁ , s₂) ((L⊗ ϵ) ⊗R ↑ᵢ c) nothing (s₁ , s₂')
    ⊗₁-dom₂-∅ st = Tensor.Step₂ st

    ⊗₁-dom₂-dom : ∀ {s₁ s₂ s₂' c c'}
      → step₂ s₂ (ϵ ⊗R ↑ᵢ c) (just (ϵ ⊗R ↑ₒ c')) s₂'
      → step (s₁ , s₂) ((L⊗ ϵ) ⊗R ↑ᵢ c) (just ((L⊗ ϵ) ⊗R ↑ₒ c')) (s₁ , s₂')
    ⊗₁-dom₂-dom st = Tensor.Step₂ st

    ⊗₁-dom₂-cod : ∀ {s₁ s₂ s₂' c d'}
      → step₂ s₂ (ϵ ⊗R ↑ᵢ c) (just (L⊗ ϵ ᵗ¹ ↑ᵢ d')) s₂'
      → step (s₁ , s₂) ((L⊗ ϵ) ⊗R ↑ᵢ c) (just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ d')) (s₁ , s₂')
    ⊗₁-dom₂-cod st = Tensor.Step₂ st

    -- M₂, codomain input
    ⊗₁-cod₂-∅ : ∀ {s₁ s₂ s₂' d}
      → step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ d) nothing s₂'
      → step (s₁ , s₂) (L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ d) nothing (s₁ , s₂')
    ⊗₁-cod₂-∅ st = Tensor.Step₂ st

    ⊗₁-cod₂-dom : ∀ {s₁ s₂ s₂' d c'}
      → step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ d) (just (ϵ ⊗R ↑ₒ c')) s₂'
      → step (s₁ , s₂) (L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ d) (just ((L⊗ ϵ) ⊗R ↑ₒ c')) (s₁ , s₂')
    ⊗₁-cod₂-dom st = Tensor.Step₂ st

    ⊗₁-cod₂-cod : ∀ {s₁ s₂ s₂' d d'}
      → step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ d) (just (L⊗ ϵ ᵗ¹ ↑ᵢ d')) s₂'
      → step (s₁ , s₂) (L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ d) (just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ d')) (s₁ , s₂')
    ⊗₁-cod₂-cod st = Tensor.Step₂ st

  -- Inversion: a step of the tensor on a message for one component is a
  -- step of that component, the other one standing still, with one of the
  -- three output shapes.  The helpers are stated over the transparent sums the
  -- channels unfold to, and convert back at the boundary.
  opaque
    unfolding _⊗₀_ Step

    ⊗₁-dom₁-view : ∀ {s₁ s₂ s' a o}
      → step (s₁ , s₂) ((ϵ ⊗R) ⊗R ↑ᵢ a) o s'
      → ∃[ s₁' ] (s' ≡ (s₁' , s₂)) ×
          ( (o ≡ nothing × step₁ s₁ (ϵ ⊗R ↑ᵢ a) nothing s₁')
          ⊎ (∃[ a' ] (o ≡ just ((ϵ ⊗R) ⊗R ↑ₒ a')) × step₁ s₁ (ϵ ⊗R ↑ᵢ a) (just (ϵ ⊗R ↑ₒ a')) s₁')
          ⊎ (∃[ b' ] (o ≡ just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ b')) × step₁ s₁ (ϵ ⊗R ↑ᵢ a) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₁'))
    ⊗₁-dom₁-view {s₁} {s₂} {s'} {a} {o} st = go o st
      where
      go : (o : Maybe ((outType A ⊎ outType C) ⊎ (inType B ⊎ inType D)))
         → step (s₁ , s₂) (inj₁ (inj₁ a)) o s'
         → ∃[ s₁' ] (s' ≡ (s₁' , s₂)) ×
             ( (o ≡ nothing × step₁ s₁ (inj₁ a) nothing s₁')
             ⊎ (∃[ a' ] (o ≡ just (inj₁ (inj₁ a'))) × step₁ s₁ (inj₁ a) (just (inj₁ a')) s₁')
             ⊎ (∃[ b' ] (o ≡ just (inj₂ (inj₁ b'))) × step₁ s₁ (inj₁ a) (just (inj₂ b')) s₁'))
      go o st with comp-view st
      go o st | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go nothing st | inj₁ (mᵢ , nothing , xeq , yeq , seq , q) =
        proj₁ s' , cong (proj₁ s' ,_) seq , inj₁ (refl , subst (λ u → step₁ s₁ u nothing (proj₁ s')) (sym (inj₁-inj xeq)) q)
      go nothing st | inj₁ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₁ (inj₁ a'))) st | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₁ s' , cong (proj₁ s' ,_) seq , inj₂ (inj₁ (a' , refl ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₁ s')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q))
      go (just (inj₂ (inj₁ b'))) st | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₁ s' , cong (proj₁ s' ,_) seq , inj₂ (inj₂ (b' , refl ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₁ s')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q))
      go (just (inj₁ (inj₂ _))) st | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      go (just (inj₂ (inj₂ _))) st | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))

    ⊗₁-cod₁-view : ∀ {s₁ s₂ s' b o}
      → step (s₁ , s₂) (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ b) o s'
      → ∃[ s₁' ] (s' ≡ (s₁' , s₂)) ×
          ( (o ≡ nothing × step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ b) nothing s₁')
          ⊎ (∃[ a' ] (o ≡ just ((ϵ ⊗R) ⊗R ↑ₒ a')) × step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (ϵ ⊗R ↑ₒ a')) s₁')
          ⊎ (∃[ b' ] (o ≡ just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ b')) × step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₁'))
    ⊗₁-cod₁-view {s₁} {s₂} {s'} {b} {o} st = go o st
      where
      go : (o : Maybe ((outType A ⊎ outType C) ⊎ (inType B ⊎ inType D)))
         → step (s₁ , s₂) (inj₂ (inj₁ b)) o s'
         → ∃[ s₁' ] (s' ≡ (s₁' , s₂)) ×
             ( (o ≡ nothing × step₁ s₁ (inj₂ b) nothing s₁')
             ⊎ (∃[ a' ] (o ≡ just (inj₁ (inj₁ a'))) × step₁ s₁ (inj₂ b) (just (inj₁ a')) s₁')
             ⊎ (∃[ b' ] (o ≡ just (inj₂ (inj₁ b'))) × step₁ s₁ (inj₂ b) (just (inj₂ b')) s₁'))
      go o st with comp-view st
      go o st | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go nothing st | inj₁ (mᵢ , nothing , xeq , yeq , seq , q) =
        proj₁ s' , cong (proj₁ s' ,_) seq , inj₁ (refl , subst (λ u → step₁ s₁ u nothing (proj₁ s')) (sym (inj₁-inj xeq)) q)
      go nothing st | inj₁ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₁ (inj₁ a'))) st | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₁ s' , cong (proj₁ s' ,_) seq , inj₂ (inj₁ (a' , refl ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₁ s')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q))
      go (just (inj₂ (inj₁ b'))) st | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₁ s' , cong (proj₁ s' ,_) seq , inj₂ (inj₂ (b' , refl ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₁ s')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q))
      go (just (inj₁ (inj₂ _))) st | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      go (just (inj₂ (inj₂ _))) st | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))

    ⊗₁-dom₂-view : ∀ {s₁ s₂ s' c o}
      → step (s₁ , s₂) ((L⊗ ϵ) ⊗R ↑ᵢ c) o s'
      → ∃[ s₂' ] (s' ≡ (s₁ , s₂')) ×
          ( (o ≡ nothing × step₂ s₂ (ϵ ⊗R ↑ᵢ c) nothing s₂')
          ⊎ (∃[ c' ] (o ≡ just ((L⊗ ϵ) ⊗R ↑ₒ c')) × step₂ s₂ (ϵ ⊗R ↑ᵢ c) (just (ϵ ⊗R ↑ₒ c')) s₂')
          ⊎ (∃[ d' ] (o ≡ just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ d')) × step₂ s₂ (ϵ ⊗R ↑ᵢ c) (just (L⊗ ϵ ᵗ¹ ↑ᵢ d')) s₂'))
    ⊗₁-dom₂-view {s₁} {s₂} {s'} {c} {o} st = go o st
      where
      go : (o : Maybe ((outType A ⊎ outType C) ⊎ (inType B ⊎ inType D)))
         → step (s₁ , s₂) (inj₁ (inj₂ c)) o s'
         → ∃[ s₂' ] (s' ≡ (s₁ , s₂')) ×
             ( (o ≡ nothing × step₂ s₂ (inj₁ c) nothing s₂')
             ⊎ (∃[ c' ] (o ≡ just (inj₁ (inj₂ c'))) × step₂ s₂ (inj₁ c) (just (inj₁ c')) s₂')
             ⊎ (∃[ d' ] (o ≡ just (inj₂ (inj₂ d'))) × step₂ s₂ (inj₁ c) (just (inj₂ d')) s₂'))
      go o st with comp-view st
      go o st | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go nothing st | inj₂ (mᵢ , nothing , xeq , yeq , seq , q) =
        proj₂ s' , cong (_, proj₂ s') seq , inj₁ (refl , subst (λ u → step₂ s₂ u nothing (proj₂ s')) (sym (inj₂-inj xeq)) q)
      go nothing st | inj₂ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₁ (inj₂ c'))) st | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₂ s' , cong (_, proj₂ s') seq , inj₂ (inj₁ (c' , refl ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₂ s')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q))
      go (just (inj₂ (inj₂ d'))) st | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₂ s' , cong (_, proj₂ s') seq , inj₂ (inj₂ (d' , refl ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₂ s')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q))
      go (just (inj₁ (inj₁ _))) st | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      go (just (inj₂ (inj₁ _))) st | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

    ⊗₁-cod₂-view : ∀ {s₁ s₂ s' d o}
      → step (s₁ , s₂) (L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ d) o s'
      → ∃[ s₂' ] (s' ≡ (s₁ , s₂')) ×
          ( (o ≡ nothing × step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ d) nothing s₂')
          ⊎ (∃[ c' ] (o ≡ just ((L⊗ ϵ) ⊗R ↑ₒ c')) × step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ d) (just (ϵ ⊗R ↑ₒ c')) s₂')
          ⊎ (∃[ d' ] (o ≡ just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ d')) × step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ d) (just (L⊗ ϵ ᵗ¹ ↑ᵢ d')) s₂'))
    ⊗₁-cod₂-view {s₁} {s₂} {s'} {d} {o} st = go o st
      where
      go : (o : Maybe ((outType A ⊎ outType C) ⊎ (inType B ⊎ inType D)))
         → step (s₁ , s₂) (inj₂ (inj₂ d)) o s'
         → ∃[ s₂' ] (s' ≡ (s₁ , s₂')) ×
             ( (o ≡ nothing × step₂ s₂ (inj₂ d) nothing s₂')
             ⊎ (∃[ c' ] (o ≡ just (inj₁ (inj₂ c'))) × step₂ s₂ (inj₂ d) (just (inj₁ c')) s₂')
             ⊎ (∃[ d' ] (o ≡ just (inj₂ (inj₂ d'))) × step₂ s₂ (inj₂ d) (just (inj₂ d')) s₂'))
      go o st with comp-view st
      go o st | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go nothing st | inj₂ (mᵢ , nothing , xeq , yeq , seq , q) =
        proj₂ s' , cong (_, proj₂ s') seq , inj₁ (refl , subst (λ u → step₂ s₂ u nothing (proj₂ s')) (sym (inj₂-inj xeq)) q)
      go nothing st | inj₂ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₁ (inj₂ c'))) st | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₂ s' , cong (_, proj₂ s') seq , inj₂ (inj₁ (c' , refl ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₂ s')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q))
      go (just (inj₂ (inj₂ d'))) st | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        proj₂ s' , cong (_, proj₂ s') seq , inj₂ (inj₂ (d' , refl ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₂ s')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q))
      go (just (inj₁ (inj₁ _))) st | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      go (just (inj₂ (inj₁ _))) st | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

------------------------------------------------------------------------
-- Composition.  A step of `M₁ ∘ M₂` is a chain: an external input enters
-- one component, messages bounce through the shared channel `B`, and the
-- chain ends with an external output or with silence.  `Mid₁ s b o s'`
-- is the remainder of a chain in which `M₁` is about to receive `b` on
-- its domain, `Mid₂ s b o s'` one in which `M₂` is about to receive `b`
-- on its codomain; `o` is the composite's eventual output.

module Compose {A B C : Channel} (M₁ : Machine B C) (M₂ : Machine A B) where
  private
    K = modifyStepRel ∘σ (M₂ ⊗₁ M₁)
    step₁ = Step M₁
    step₂ = Step M₂
    step  = Step (M₁ CC.∘ M₂)

  State = Machine.State M₂ × Machine.State M₁

  opaque
    -- The composite's output, as the underlying trace relation sees it,
    -- spelled exactly as `tr`'s two restrictions spell it.
    ρₒ : Maybe (outType (A ⊗ᵀ C)) → Maybe (outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
    ρₒ o = app (∣ˡσ  {A = A} {B = B} {C = C ⊗₀ B} {m = Out}) <$>
           (app (∣^ˡσ {A = A} {B = C} {C = B}      {m = Out}) <$> o)

    Mid₁ : State → inType B → Maybe (outType (A ⊗ᵀ C)) → State → Type
    Mid₁ s b' o s' = TraceRel K s ((L⊗ ϵ) ⊗R ↑ᵢ b') (ρₒ o) s'

    Mid₂ : State → outType B → Maybe (outType (A ⊗ᵀ C)) → State → Type
    Mid₂ s b o s' = TraceRel K s (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ b) (ρₒ o) s'

  -- Rewriting the messages of a continuation.
  mid₁-subst : ∀ {s s' b b' o o'} → b ≡ b' → o ≡ o' → Mid₁ s b o s' → Mid₁ s b' o' s'
  mid₁-subst refl refl k = k

  mid₂-subst : ∀ {s s' b b' o o'} → b ≡ b' → o ≡ o' → Mid₂ s b o s' → Mid₂ s b' o' s'
  mid₂-subst refl refl k = k

  opaque
    unfolding _⊗₀_ Step ρₒ Mid₁ Mid₂

    -- Entering at M₂, on the composite's domain.
    ∘-dom-∅ : ∀ {s₂ s₂' s₁ a}
      → step₂ s₂ (ϵ ⊗R ↑ᵢ a) nothing s₂'
      → step (s₂ , s₁) (ϵ ⊗R ↑ᵢ a) nothing (s₂' , s₁)
    ∘-dom-∅ st = Trace[ Tensor.Step₁ st ]

    ∘-dom-dom : ∀ {s₂ s₂' s₁ a a'}
      → step₂ s₂ (ϵ ⊗R ↑ᵢ a) (just (ϵ ⊗R ↑ₒ a')) s₂'
      → step (s₂ , s₁) (ϵ ⊗R ↑ᵢ a) (just (ϵ ⊗R ↑ₒ a')) (s₂' , s₁)
    ∘-dom-dom st = Trace[ Tensor.Step₁ st ]

    ∘-dom-mid : ∀ {s₂ s₂' s₁ a b' o s'}
      → step₂ s₂ (ϵ ⊗R ↑ᵢ a) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₂'
      → Mid₁ (s₂' , s₁) b' o s'
      → step (s₂ , s₁) (ϵ ⊗R ↑ᵢ a) o s'
    ∘-dom-mid st k = Tensor.Step₁ st Trace∷ᵢ k

    -- Entering at M₁, on the composite's codomain.
    ∘-cod-∅ : ∀ {s₂ s₁ s₁' c}
      → step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ c) nothing s₁'
      → step (s₂ , s₁) (L⊗ ϵ ᵗ¹ ↑ₒ c) nothing (s₂ , s₁')
    ∘-cod-∅ st = Trace[ Tensor.Step₂ st ]

    ∘-cod-cod : ∀ {s₂ s₁ s₁' c c'}
      → step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ c) (just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) s₁'
      → step (s₂ , s₁) (L⊗ ϵ ᵗ¹ ↑ₒ c) (just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) (s₂ , s₁')
    ∘-cod-cod st = Trace[ Tensor.Step₂ st ]

    ∘-cod-mid : ∀ {s₂ s₁ s₁' c b o s'}
      → step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ c) (just (ϵ ⊗R ↑ₒ b)) s₁'
      → Mid₂ (s₂ , s₁') b o s'
      → step (s₂ , s₁) (L⊗ ϵ ᵗ¹ ↑ₒ c) o s'
    ∘-cod-mid st k = Tensor.Step₂ st Trace∷ₒ k

    -- M₁ receives on its domain.
    mid₁-∅ : ∀ {s₂ s₁ s₁' b'}
      → step₁ s₁ (ϵ ⊗R ↑ᵢ b') nothing s₁'
      → Mid₁ (s₂ , s₁) b' nothing (s₂ , s₁')
    mid₁-∅ st = Trace[ Tensor.Step₂ st ]

    mid₁-cod : ∀ {s₂ s₁ s₁' b' c'}
      → step₁ s₁ (ϵ ⊗R ↑ᵢ b') (just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) s₁'
      → Mid₁ (s₂ , s₁) b' (just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) (s₂ , s₁')
    mid₁-cod st = Trace[ Tensor.Step₂ st ]

    mid₁-mid : ∀ {s₂ s₁ s₁' b' b o s'}
      → step₁ s₁ (ϵ ⊗R ↑ᵢ b') (just (ϵ ⊗R ↑ₒ b)) s₁'
      → Mid₂ (s₂ , s₁') b o s'
      → Mid₁ (s₂ , s₁) b' o s'
    mid₁-mid st k = Tensor.Step₂ st Trace∷ₒ k

    -- M₂ receives on its codomain.
    mid₂-∅ : ∀ {s₂ s₂' s₁ b}
      → step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ b) nothing s₂'
      → Mid₂ (s₂ , s₁) b nothing (s₂' , s₁)
    mid₂-∅ st = Trace[ Tensor.Step₁ st ]

    mid₂-dom : ∀ {s₂ s₂' s₁ b a'}
      → step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (ϵ ⊗R ↑ₒ a')) s₂'
      → Mid₂ (s₂ , s₁) b (just (ϵ ⊗R ↑ₒ a')) (s₂' , s₁)
    mid₂-dom st = Trace[ Tensor.Step₁ st ]

    mid₂-mid : ∀ {s₂ s₂' s₁ b b' o s'}
      → step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₂'
      → Mid₁ (s₂' , s₁) b' o s'
      → Mid₂ (s₂ , s₁) b o s'
    mid₂-mid st k = Tensor.Step₁ st Trace∷ᵢ k

  -- Inversion.  A step of the composite, or a continuation, decomposes into
  -- the first component step and what follows.  Helpers over the transparent
  -- sums, as for the tensor.
  opaque
    unfolding _⊗₀_ Step ρₒ Mid₁ Mid₂

    ∘-dom-view : ∀ {s₂ s₁ s' a o}
      → step (s₂ , s₁) (ϵ ⊗R ↑ᵢ a) o s'
      → (∃[ s₂' ] (s' ≡ (s₂' , s₁)) × (o ≡ nothing) × step₂ s₂ (ϵ ⊗R ↑ᵢ a) nothing s₂')
      ⊎ (∃[ s₂' ] ∃[ a' ] (s' ≡ (s₂' , s₁)) × (o ≡ just (ϵ ⊗R ↑ₒ a')) × step₂ s₂ (ϵ ⊗R ↑ᵢ a) (just (ϵ ⊗R ↑ₒ a')) s₂')
      ⊎ (∃[ s₂' ] ∃[ b' ] step₂ s₂ (ϵ ⊗R ↑ᵢ a) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₂' × Mid₁ (s₂' , s₁) b' o s')
    ∘-dom-view {s₂} {s₁} {s'} {a} {o} st = go o st
      where
      go : (o : Maybe (outType A ⊎ inType C)) → step (s₂ , s₁) (inj₁ a) o s'
         → (∃[ s₂' ] (s' ≡ (s₂' , s₁)) × (o ≡ nothing) × step₂ s₂ (inj₁ a) nothing s₂')
         ⊎ (∃[ s₂' ] ∃[ a' ] (s' ≡ (s₂' , s₁)) × (o ≡ just (inj₁ a')) × step₂ s₂ (inj₁ a) (just (inj₁ a')) s₂')
         ⊎ (∃[ s₂' ] ∃[ b' ] step₂ s₂ (inj₁ a) (just (inj₂ b')) s₂' × Mid₁ (s₂' , s₁) b' o s')
      go o st with trace-view st
      go o st | inj₁ p with comp-view p
      go o st | inj₁ p | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go nothing st | inj₁ p | inj₁ (mᵢ , nothing , xeq , yeq , seq , q) =
        inj₁ (proj₁ s' , cong (proj₁ s' ,_) seq , refl , subst (λ u → step₂ s₂ u nothing (proj₁ s')) (sym (inj₁-inj xeq)) q)
      go nothing st | inj₁ p | inj₁ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₁ p | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₁ a')) st | inj₁ p | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₁ (proj₁ s' , a' , cong (proj₁ s' ,_) seq , refl ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₁ s')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q))
      go (just (inj₂ _)) st | inj₁ p | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      go o st | inj₂ (inj₁ (_ , _ , p , _)) with comp-view p
      go o st | inj₂ (inj₁ (_ , _ , p , _)) | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go o st | inj₂ (inj₁ (_ , _ , p , _)) | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₁ (_ , _ , p , _)) | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) with comp-view p
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₂ (proj₁ s₁' , inC ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₁ s₁')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q ,
          subst (λ z → Mid₁ z inC o s') (cong (proj₁ s₁' ,_) seq) rest))

    ∘-cod-view : ∀ {s₂ s₁ s' c o}
      → step (s₂ , s₁) (L⊗ ϵ ᵗ¹ ↑ₒ c) o s'
      → (∃[ s₁' ] (s' ≡ (s₂ , s₁')) × (o ≡ nothing) × step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ c) nothing s₁')
      ⊎ (∃[ s₁' ] ∃[ c' ] (s' ≡ (s₂ , s₁')) × (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) × step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ c) (just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) s₁')
      ⊎ (∃[ s₁' ] ∃[ b ] step₁ s₁ (L⊗ ϵ ᵗ¹ ↑ₒ c) (just (ϵ ⊗R ↑ₒ b)) s₁' × Mid₂ (s₂ , s₁') b o s')
    ∘-cod-view {s₂} {s₁} {s'} {c} {o} st = go o st
      where
      go : (o : Maybe (outType A ⊎ inType C)) → step (s₂ , s₁) (inj₂ c) o s'
         → (∃[ s₁' ] (s' ≡ (s₂ , s₁')) × (o ≡ nothing) × step₁ s₁ (inj₂ c) nothing s₁')
         ⊎ (∃[ s₁' ] ∃[ c' ] (s' ≡ (s₂ , s₁')) × (o ≡ just (inj₂ c')) × step₁ s₁ (inj₂ c) (just (inj₂ c')) s₁')
         ⊎ (∃[ s₁' ] ∃[ b ] step₁ s₁ (inj₂ c) (just (inj₁ b)) s₁' × Mid₂ (s₂ , s₁') b o s')
      go o st with trace-view st
      go o st | inj₁ p with comp-view p
      go o st | inj₁ p | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go nothing st | inj₁ p | inj₂ (mᵢ , nothing , xeq , yeq , seq , q) =
        inj₁ (proj₂ s' , cong (_, proj₂ s') seq , refl , subst (λ u → step₁ s₁ u nothing (proj₂ s')) (sym (inj₂-inj xeq)) q)
      go nothing st | inj₁ p | inj₂ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₁ p | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₂ c')) st | inj₁ p | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₁ (proj₂ s' , c' , cong (_, proj₂ s') seq , refl ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₂ s')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q))
      go (just (inj₁ _)) st | inj₁ p | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) with comp-view p
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₂ (proj₂ s₁' , outC ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₂ s₁')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q ,
          subst (λ z → Mid₂ z outC o s') (cong (_, proj₂ s₁') seq) rest))
      go o st | inj₂ (inj₂ (_ , _ , p , _)) with comp-view p
      go o st | inj₂ (inj₂ (_ , _ , p , _)) | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go o st | inj₂ (inj₂ (_ , _ , p , _)) | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₂ (_ , _ , p , _)) | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

    mid₁-view : ∀ {s₂ s₁ s' b' o}
      → Mid₁ (s₂ , s₁) b' o s'
      → (∃[ s₁' ] (s' ≡ (s₂ , s₁')) × (o ≡ nothing) × step₁ s₁ (ϵ ⊗R ↑ᵢ b') nothing s₁')
      ⊎ (∃[ s₁' ] ∃[ c' ] (s' ≡ (s₂ , s₁')) × (o ≡ just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) × step₁ s₁ (ϵ ⊗R ↑ᵢ b') (just (L⊗ ϵ ᵗ¹ ↑ᵢ c')) s₁')
      ⊎ (∃[ s₁' ] ∃[ b ] step₁ s₁ (ϵ ⊗R ↑ᵢ b') (just (ϵ ⊗R ↑ₒ b)) s₁' × Mid₂ (s₂ , s₁') b o s')
    mid₁-view {s₂} {s₁} {s'} {b'} {o} st = go o st
      where
      go : (o : Maybe (outType A ⊎ inType C)) → Mid₁ (s₂ , s₁) b' o s'
         → (∃[ s₁' ] (s' ≡ (s₂ , s₁')) × (o ≡ nothing) × step₁ s₁ (inj₁ b') nothing s₁')
         ⊎ (∃[ s₁' ] ∃[ c' ] (s' ≡ (s₂ , s₁')) × (o ≡ just (inj₂ c')) × step₁ s₁ (inj₁ b') (just (inj₂ c')) s₁')
         ⊎ (∃[ s₁' ] ∃[ b ] step₁ s₁ (inj₁ b') (just (inj₁ b)) s₁' × Mid₂ (s₂ , s₁') b o s')
      go o st with trace-view st
      go o st | inj₁ p with comp-view p
      go o st | inj₁ p | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go nothing st | inj₁ p | inj₂ (mᵢ , nothing , xeq , yeq , seq , q) =
        inj₁ (proj₂ s' , cong (_, proj₂ s') seq , refl , subst (λ u → step₁ s₁ u nothing (proj₂ s')) (sym (inj₂-inj xeq)) q)
      go nothing st | inj₁ p | inj₂ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₁ p | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₂ c')) st | inj₁ p | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₁ (proj₂ s' , c' , cong (_, proj₂ s') seq , refl ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₂ s')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q))
      go (just (inj₁ _)) st | inj₁ p | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) with comp-view p
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₁ (s₁' , outC , p , rest)) | inj₂ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₂ (proj₂ s₁' , outC ,
          subst₂ (λ u v → step₁ s₁ u (just v) (proj₂ s₁')) (sym (inj₂-inj xeq)) (sym (inj₂-inj (just-inj yeq))) q ,
          subst (λ z → Mid₂ z outC o s') (cong (_, proj₂ s₁') seq) rest))
      go o st | inj₂ (inj₂ (_ , _ , p , _)) with comp-view p
      go o st | inj₂ (inj₂ (_ , _ , p , _)) | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      go o st | inj₂ (inj₂ (_ , _ , p , _)) | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₂ (_ , _ , p , _)) | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

    mid₂-view : ∀ {s₂ s₁ s' b o}
      → Mid₂ (s₂ , s₁) b o s'
      → (∃[ s₂' ] (s' ≡ (s₂' , s₁)) × (o ≡ nothing) × step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ b) nothing s₂')
      ⊎ (∃[ s₂' ] ∃[ a' ] (s' ≡ (s₂' , s₁)) × (o ≡ just (ϵ ⊗R ↑ₒ a')) × step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (ϵ ⊗R ↑ₒ a')) s₂')
      ⊎ (∃[ s₂' ] ∃[ b' ] step₂ s₂ (L⊗ ϵ ᵗ¹ ↑ₒ b) (just (L⊗ ϵ ᵗ¹ ↑ᵢ b')) s₂' × Mid₁ (s₂' , s₁) b' o s')
    mid₂-view {s₂} {s₁} {s'} {b} {o} st = go o st
      where
      go : (o : Maybe (outType A ⊎ inType C)) → Mid₂ (s₂ , s₁) b o s'
         → (∃[ s₂' ] (s' ≡ (s₂' , s₁)) × (o ≡ nothing) × step₂ s₂ (inj₂ b) nothing s₂')
         ⊎ (∃[ s₂' ] ∃[ a' ] (s' ≡ (s₂' , s₁)) × (o ≡ just (inj₁ a')) × step₂ s₂ (inj₂ b) (just (inj₁ a')) s₂')
         ⊎ (∃[ s₂' ] ∃[ b' ] step₂ s₂ (inj₂ b) (just (inj₂ b')) s₂' × Mid₁ (s₂' , s₁) b' o s')
      go o st with trace-view st
      go o st | inj₁ p with comp-view p
      go o st | inj₁ p | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go nothing st | inj₁ p | inj₁ (mᵢ , nothing , xeq , yeq , seq , q) =
        inj₁ (proj₁ s' , cong (proj₁ s' ,_) seq , refl , subst (λ u → step₂ s₂ u nothing (proj₁ s')) (sym (inj₁-inj xeq)) q)
      go nothing st | inj₁ p | inj₁ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
      go (just _) st | inj₁ p | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go (just (inj₁ a')) st | inj₁ p | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₁ (proj₁ s' , a' , cong (proj₁ s' ,_) seq , refl ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₁ s')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q))
      go (just (inj₂ _)) st | inj₁ p | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      go o st | inj₂ (inj₁ (_ , _ , p , _)) with comp-view p
      go o st | inj₂ (inj₁ (_ , _ , p , _)) | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go o st | inj₂ (inj₁ (_ , _ , p , _)) | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₁ (_ , _ , p , _)) | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) with comp-view p
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      go o st | inj₂ (inj₂ (s₁' , inC , p , rest)) | inj₁ (mᵢ , just w , xeq , yeq , seq , q) =
        inj₂ (inj₂ (proj₁ s₁' , inC ,
          subst₂ (λ u v → step₂ s₂ u (just v) (proj₁ s₁')) (sym (inj₁-inj xeq)) (sym (inj₁-inj (just-inj yeq))) q ,
          subst (λ z → Mid₁ z inC o s') (cong (proj₁ s₁' ,_) seq) rest))
