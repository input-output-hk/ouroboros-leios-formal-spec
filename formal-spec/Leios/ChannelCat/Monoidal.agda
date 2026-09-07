{-# OPTIONS --safe #-}

-- ============================================================================
-- The two rewiring laws of `Leios.ChannelCat`, derived from monoidal laws.
--
-- `insert-id` and `⨂-absorb-env` — equations about rewiring a ⨂ of per-node
-- machines past the environment, the last two fields of the `ChannelCat`
-- record that the transfer theorems used to assume — are derived here, WITHOUT
-- ASSUMPTIONS, from nine binary laws, none
-- of which mentions `⨂`, the node count, per-node channel families, the
-- environment, or anything else specific to a deployment; and all nine are now
-- theorems:
--
--   `⊗₁-interchange` — `_⊗₁_` is a functor for `_∘_`, the genuinely
--     categorical part (`Leios.ChannelCat.Interchange`);
--   `⊗₁-id`, `ρ-∘ᴷ-fwd`, `ρ-idᴷ`, `λ-zip-idᴷ` — forwarders are closed under
--     `_⊗₁_`, `modifyStepRel` and `_∘_`, so an equation between two composites
--     of them is a finite message-level computation (`Leios.ChannelCat.Fwd`);
--   `∘ᴷ-fwd-natural`, `⊗ᴷ-fwd-natural` — the shuffles inside `_∘ᴷ_`/`_⊗ᴷ_`
--     are natural, because a forwarder is a reindexed identity and a
--     relabelling that fixes the traced channel slides out of `_∘_`
--     (`Leios.ChannelCat.Naturality`, on `Slide`, `Collapse`, `FwdId`,
--     `PairAssoc`);
--   `∘ᴷ-assoc`, `⊗ᴷ-∘ᴷ` — `_∘ᴷ_` associates and interchanges with `_⊗ᴷ_`,
--     by flattening with `⊗₁-interchange`, re-bracketing, carrying the abstract
--     machines across the shuffles with the naturality laws, and closing the
--     forwarder-only heads pointwise (`Leios.ChannelCat.Kleisli`).
--
-- The `ChannelCat` record itself, and the `Forwarders`/`KleisliLaws` records
-- that used to hold the last four laws, are gone.  `Derived` is kept as a
-- module name so the proof reads as before.
--
-- Elaboration note.  Channel families must be PINNED wherever `⨂` appears in
-- an inferred position (hence `strip`, and the explicit `{n} {E₁} {E₂}` on
-- `⨂-zip` below).  Left implicit they generate `⨂ ?B ≟ ⨂ E` constraints that
-- block on an abstract `n` — `⨂` is a stuck recursion, not a constructor, so
-- Agda cannot invert it — and the elaborator then diverges into heap
-- exhaustion.  For the same reason the reasoning steps are stated over
-- abstract machines (`slide-∘ᴷ`, `slide-⊗ᴷ`, `post-α`) and only afterwards
-- instantiated at the ⨂ composites.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.IsoExt
open import CategoricalCrypto.Machine.Iso
  using (_≅ᴹ_; ≅ᴹ-refl; ≅ᴹ-sym; ≅ᴹ-trans; ∘-resp-≅ᴹ; ∘-assoc-≅ᴹ; ∘-identityˡ-≅ᴹ)
open import Leios.ChannelCat
  using (ρ⇒; λ⇒; insert-id-helper; ⨂-zip; ⨂-absorb-env-helper;
         absorb-regroup; mid4)
open import Leios.ChannelCat.Fwd
  using (∘ᴷ-fwd; ⊗ᴷ-fwd; ⊗₁-id; ρ-∘ᴷ-fwd; ρ-idᴷ; λ-zip-idᴷ)
open import Leios.ChannelCat.Interchange using (⊗₁-interchange)
open import Leios.ChannelCat.Naturality using (∘ᴷ-fwd-natural; ⊗ᴷ-fwd-natural)
open import Leios.ChannelCat.Kleisli using (∘ᴷ-assoc; ⊗ᴷ-∘ᴷ)
open import Tactic.Defaults

module Leios.ChannelCat.Monoidal where

-- ----------------------------------------------------------------------------
-- The shuffles inside `_∘ᴷ_` and `_⊗ᴷ_` are `∘ᴷ-fwd` and `⊗ᴷ-fwd`, defined
-- (and shown to be forwarders) in `Leios.ChannelCat.Fwd` and re-exported
-- above.  `⇒-solver` is deterministic, so re-running it at the same type
-- yields the same term and the `unfold` lemmas below hold by `refl`.  Naming
-- them is what makes the whole derivation possible: every operator in
-- `ChannelCat`'s fields becomes a composite of `_∘_`, `_⊗₁_` and these two.
-- ----------------------------------------------------------------------------

∘ᴷ-unfold : ∀ {A B C E₁ E₂} (M₂ : Machine B (C ⊗₀ E₂)) (M₁ : Machine A (B ⊗₀ E₁))
          → (M₂ ∘ᴷ M₁) ≡ (∘ᴷ-fwd CC.∘ ((M₂ ⊗ʳ E₁) CC.∘ M₁))
∘ᴷ-unfold _ _ = refl

⊗ᴷ-unfold : ∀ {A₁ B₁ E₁ A₂ B₂ E₂} (M₁ : Machine A₁ (B₁ ⊗₀ E₁)) (M₂ : Machine A₂ (B₂ ⊗₀ E₂))
          → (M₁ ⊗ᴷ M₂) ≡ (⊗ᴷ-fwd CC.∘ (M₁ ⊗₁ M₂))
⊗ᴷ-unfold _ _ = refl

-- `insert-id-helper`'s inner `⨂₁ (λ _ → ρ⇒)`, with its channel families
-- PINNED.  Left implicit they generate `⨂ ?B ≟ ⨂ E` constraints that block on
-- the abstract `n` — `⨂` is a stuck recursion, not a constructor, so Agda
-- cannot invert it — and the elaborator then diverges (heap exhaustion).
strip : ∀ {n} (E : Fin n → Channel) → Machine (⨂ (λ k → E k ⊗₀ I)) (⨂ E)
strip {n} E = ⨂₁ {n = n} {A = λ k → E k ⊗₀ I} {B = E} (λ _ → ρ⇒)

-- ----------------------------------------------------------------------------
-- The derivation.
-- ----------------------------------------------------------------------------

module Derived where

  -- Inserting a unit with `idᴷ ∘ᴷ _` and stripping it again is a no-op.
  unit-∘ᴷ : ∀ {A C E₁} (h : Machine A (C ⊗₀ E₁))
          → ((CC.id ⊗₁ ρ⇒) CC.∘ (idᴷ ∘ᴷ h)) ≅ᴹ h
  unit-∘ᴷ h =
    ≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ ρ-∘ᴷ-fwd ≅ᴹ-refl)
    (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-sym (⊗₁-interchange idᴷ ρ⇒ CC.id CC.id)) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ ρ-idᴷ ∘-identityˡ-≅ᴹ) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl)
              ∘-identityˡ-≅ᴹ)))))

  -- The n-ary version: `insert-id-helper` undoes the per-node unit insertion.
  ⨂-unit : ∀ {n} {B C E₂ : Fin n → Channel}
           (f : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k))
         → ((CC.id ⊗₁ strip E₂) CC.∘ ⨂ᴷ (λ k → idᴷ ∘ᴷ f k)) ≅ᴹ ⨂ᴷ f
  ⨂-unit {zero}  f = ≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl) ∘-identityˡ-≅ᴹ
  ⨂-unit {suc n} f =
    ≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ (≅ᴹ-sym ⊗₁-id) ≅ᴹ-refl) ≅ᴹ-refl)
    (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (⊗ᴷ-fwd-natural CC.id ρ⇒ CC.id (strip _)) ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
              (∘-resp-≅ᴹ ≅ᴹ-refl
                (≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange _ _ _ _))
                          (⊗₁-resp-≅ᴹ (unit-∘ᴷ (f fzero))
                                      (⨂-unit (λ k → f (fsuc k)))))))))

  -- Sliding a post-composed `CC.id ⊗₁ u` through `_∘ᴷ g`.  Stated over abstract
  -- machines: instantiating it at the ⨂ composites is then cheap, whereas
  -- inlining the same chain at those types is not.
  slide-∘ᴷ : ∀ {A B C E₁ E₂ E₂'}
             (F : Machine B (C ⊗₀ E₂)) (F' : Machine B (C ⊗₀ E₂'))
             (u : Machine E₂' E₂) (g : Machine A (B ⊗₀ E₁))
           → ((CC.id ⊗₁ u) CC.∘ F') ≅ᴹ F
           → ((CC.id ⊗₁ (CC.id ⊗₁ u)) CC.∘ (F' ∘ᴷ g)) ≅ᴹ (F ∘ᴷ g)
  slide-∘ᴷ F F' u g eq =
    ≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (∘ᴷ-fwd-natural CC.id CC.id u) ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
              (∘-resp-≅ᴹ ≅ᴹ-refl
                (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
                  (∘-resp-≅ᴹ
                    (≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange F' (CC.id ⊗₁ u) CC.id CC.id))
                              (⊗₁-resp-≅ᴹ eq ∘-identityˡ-≅ᴹ))
                    ≅ᴹ-refl)))))

  -- Re-bracketing the outer `α`, again over abstract machines.
  post-α : ∀ {A X Y D} (α : Machine Y D) (H : Machine X Y)
             (P : Machine A X) (Q : Machine A Y)
         → (H CC.∘ P) ≅ᴹ Q → (α CC.∘ Q) ≅ᴹ ((α CC.∘ H) CC.∘ P)
  post-α α H P Q eq = ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym eq)) (≅ᴹ-sym ∘-assoc-≅ᴹ)

  -- --------------------------------------------------------------------------
  -- `ChannelCat.insert-id`, discharged.  The type below is that field verbatim.
  -- --------------------------------------------------------------------------

  insert-id : ∀ {A D} {n} {E₁} {B C E₂ : Fin n → Channel}
    (f : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k)) (g : Machine A (⨂ B ⊗₀ E₁))
    (α : Machine (⨂ C ⊗₀ E₁ ⊗₀ ⨂ E₂) D)
    → (α CC.∘ (⨂ᴷ f ∘ᴷ g))
      ≅ᴹ ((α CC.∘ insert-id-helper E₂) CC.∘ (⨂ᴷ (λ k → idᴷ ∘ᴷ f k) ∘ᴷ g))
  insert-id {E₂ = E₂} f g α =
    post-α α (insert-id-helper E₂)
             (⨂ᴷ (λ k → idᴷ ∘ᴷ f k) ∘ᴷ g)
             (⨂ᴷ f ∘ᴷ g)
             (slide-∘ᴷ (⨂ᴷ f) (⨂ᴷ (λ k → idᴷ ∘ᴷ f k)) (strip E₂) g (⨂-unit f))

  -- Sliding a post-composed `CC.id ⊗₁ u` into the right factor of a `_⊗ᴷ_`.
  slide-⊗ᴷ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂ E₂'}
             (X : Machine A₁ (B₁ ⊗₀ E₁)) (Y : Machine A₂ (B₂ ⊗₀ E₂)) (u : Machine E₂ E₂')
           → ((CC.id ⊗₁ (CC.id ⊗₁ u)) CC.∘ (X ⊗ᴷ Y)) ≅ᴹ (X ⊗ᴷ ((CC.id ⊗₁ u) CC.∘ Y))
  slide-⊗ᴷ X Y u =
    ≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ (≅ᴹ-sym ⊗₁-id) ≅ᴹ-refl) ≅ᴹ-refl) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-resp-≅ᴹ (⊗ᴷ-fwd-natural CC.id CC.id CC.id u) ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
              (∘-resp-≅ᴹ ≅ᴹ-refl
                (≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange X (CC.id ⊗₁ CC.id) Y (CC.id ⊗₁ u)))
                          (⊗₁-resp-≅ᴹ (≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl) ∘-identityˡ-≅ᴹ)
                                      ≅ᴹ-refl))))))

  -- `⨂ᴷ` is functorial for `_∘ᴷ_`, once the per-node environment channels are
  -- zipped together.  The induction; the step is the binary `⊗ᴷ-∘ᴷ`.
  ⨂-functorial : ∀ {n} {B C D E₁ E₂ : Fin n → Channel}
    (f : (k : Fin n) → Machine (C k) (D k ⊗₀ E₂ k))
    (g : (k : Fin n) → Machine (B k) (C k ⊗₀ E₁ k))
    → ((CC.id ⊗₁ ⨂-zip {n} {E₁} {E₂}) CC.∘ (⨂ᴷ f ∘ᴷ ⨂ᴷ g)) ≅ᴹ ⨂ᴷ (λ k → f k ∘ᴷ g k)
  ⨂-functorial {zero}  f g = λ-zip-idᴷ
  ⨂-functorial {suc n} {E₁ = E₁} {E₂ = E₂} f g =
    ≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-trans (⊗₁-resp-≅ᴹ (≅ᴹ-sym ∘-identityˡ-≅ᴹ) ≅ᴹ-refl)
                                  (⊗₁-interchange CC.id CC.id mid4 (CC.id ⊗₁ ⨂-zip)))
                        ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
    (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl
                (⊗ᴷ-∘ᴷ (f fzero) (g fzero)
                       (⨂ᴷ (λ k → f (fsuc k))) (⨂ᴷ (λ k → g (fsuc k)))))
    (≅ᴹ-trans (slide-⊗ᴷ (f fzero ∘ᴷ g fzero)
                        (⨂ᴷ (λ k → f (fsuc k)) ∘ᴷ ⨂ᴷ (λ k → g (fsuc k)))
                        (⨂-zip {n} {λ k → E₁ (fsuc k)} {λ k → E₂ (fsuc k)}))
              (⊗ᴷ-resp-≅ᴹ ≅ᴹ-refl
                (⨂-functorial (λ k → f (fsuc k)) (λ k → g (fsuc k)))))))

  -- --------------------------------------------------------------------------
  -- `ChannelCat.⨂-absorb-env`, discharged.  The type below is that field
  -- verbatim.
  -- --------------------------------------------------------------------------

  ⨂-absorb-env : ∀ {A E F} {n} {B C D E₁ E₂ : Fin n → Channel}
    (f : (k : Fin n) → Machine (C k) (D k ⊗₀ E₂ k))
    (g : (k : Fin n) → Machine (B k) (C k ⊗₀ E₁ k))
    (h : Machine A (⨂ B ⊗₀ E))
    (α : Machine (⨂ D ⊗₀ E ⊗₀ ⨂ (λ k → E₁ k ⊗₀ E₂ k)) F)
    → (α CC.∘ (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h))
      ≅ᴹ ((α CC.∘ (⨂-absorb-env-helper D) CC.∘ (⨂ᴷ f ⊗₁ CC.id)) CC.∘ (⨂ᴷ g ∘ᴷ h))
  ⨂-absorb-env {n = n} {D = D} {E₁ = E₁} {E₂ = E₂} f g h α =
    post-α α (⨂-absorb-env-helper D CC.∘ (⨂ᴷ f ⊗₁ CC.id))
             (⨂ᴷ g ∘ᴷ h)
             (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h)
             eq
    where
      eq : ((⨂-absorb-env-helper D CC.∘ (⨂ᴷ f ⊗₁ CC.id)) CC.∘ (⨂ᴷ g ∘ᴷ h))
         ≅ᴹ (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h)
      eq =
        ≅ᴹ-trans (∘-resp-≅ᴹ ∘-assoc-≅ᴹ ≅ᴹ-refl)
        (≅ᴹ-trans ∘-assoc-≅ᴹ
        (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (∘ᴷ-assoc (⨂ᴷ f) (⨂ᴷ g) h))
                  (slide-∘ᴷ (⨂ᴷ (λ k → f k ∘ᴷ g k)) (⨂ᴷ f ∘ᴷ ⨂ᴷ g)
                            (⨂-zip {n} {E₁} {E₂}) h (⨂-functorial f g))))

-- The two laws the transfer theorems use.
open Derived public using (insert-id; ⨂-absorb-env)
