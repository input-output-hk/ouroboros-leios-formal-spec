{-# OPTIONS --safe #-}

-- ============================================================================
-- Congruences for the machine isomorphism `_≅ᴹ_`, and transport of `Trace`
-- along one.
--
-- `Machine.Iso` proves the `_∘_` congruence (`∘-resp-≅ᴹ`) and the ∘-laws, but
-- states nothing for `_⊗₁_`, `_∘ᴷ_` or `⨂ᴷ` — which is what the safety /
-- liveness transfer needs in order to rebuild `transProtocol` without the
-- (inconsistent, see `Leios.ChannelCat`) `ChannelCat` postulates.
--
-- `×-map`/`CompRel-map` mirror the corresponding PRIVATE helpers of
-- `Machine.Iso`.  `CompRel-map` is fully generic in the message indices
-- (i, mo), so it applies unchanged through the definitionally-transparent
-- `modifyStepRel` relabel baked into `_⊗₁_`.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id; _∘_)
import CategoricalCrypto as CC
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_; MkIso; ≅ᴹ-refl; ≅ᴹ-sym; ≅ᴹ-trans; ∘-resp-≅ᴹ)

module CategoricalCrypto.IsoExt where

open _≅ᴹ_

private
  ×-map : ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
        → (A → C) → (B → D) → A × B → C × D
  ×-map f g (a , b) = f a , g b

  CompRel-map :
    ∀ {A B C D} {M₁ M₁' : Machine A B} {M₂ M₂' : Machine C D}
      (φ₁ : M₁ ≅ᴹ M₁') (φ₂ : M₂ ≅ᴹ M₂')
    → ∀ {s i mo s'} → Tensor.CompRel M₁ M₂ s i mo s'
    → Tensor.CompRel M₁' M₂'
        (×-map (to φ₁) (to φ₂) s) i mo
        (×-map (to φ₁) (to φ₂) s')
  CompRel-map φ₁ φ₂ (Tensor.Step₁ p) = Tensor.Step₁ (step-to φ₁ p)
  CompRel-map φ₁ φ₂ (Tensor.Step₂ p) = Tensor.Step₂ (step-to φ₂ p)

-- The tensor congruence.
⊗₁-resp-≅ᴹ : ∀ {A B C D} {M M' : Machine A B} {N N' : Machine C D}
           → M ≅ᴹ M' → N ≅ᴹ N' → (M ⊗₁ N) ≅ᴹ (M' ⊗₁ N')
⊗₁-resp-≅ᴹ φ ψ = MkIso
  (×-map (to φ) (to ψ))
  (×-map (from φ) (from ψ))
  (λ (s₁ , s₂) → cong₂ _,_ (from∘to φ s₁) (from∘to ψ s₂))
  (λ (s₁ , s₂) → cong₂ _,_ (to∘from φ s₁) (to∘from ψ s₂))
  (CompRel-map φ ψ)
  (CompRel-map (≅ᴹ-sym φ) (≅ᴹ-sym ψ))

-- The derived congruences.  `_⊗ʳ_`/`_⊗ˡ_`, `_∘ᴷ_`, `_⊗ᴷ_` and `⨂ᴷ` are all
-- built from `_⊗₁_`, `_∘_` and `id`, so each is a direct corollary.

⊗ʳ-resp-≅ᴹ : ∀ {A B} {M M' : Machine A B} (C : Channel)
           → M ≅ᴹ M' → (M ⊗ʳ C) ≅ᴹ (M' ⊗ʳ C)
⊗ʳ-resp-≅ᴹ _ φ = ⊗₁-resp-≅ᴹ φ ≅ᴹ-refl

∘ᴷ-resp-≅ᴹ : ∀ {A B C E₁ E₂} {M M' : Machine B (C ⊗₀ E₂)} {N N' : Machine A (B ⊗₀ E₁)}
           → M ≅ᴹ M' → N ≅ᴹ N' → (M ∘ᴷ N) ≅ᴹ (M' ∘ᴷ N')
∘ᴷ-resp-≅ᴹ {E₁ = E₁} φ ψ =
  ∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ (⊗ʳ-resp-≅ᴹ E₁ φ) ψ)

⊗ᴷ-resp-≅ᴹ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂}
             {M M' : Machine A₁ (B₁ ⊗₀ E₁)} {N N' : Machine A₂ (B₂ ⊗₀ E₂)}
           → M ≅ᴹ M' → N ≅ᴹ N' → (M ⊗ᴷ N) ≅ᴹ (M' ⊗ᴷ N')
⊗ᴷ-resp-≅ᴹ φ ψ = ∘-resp-≅ᴹ ≅ᴹ-refl (⊗₁-resp-≅ᴹ φ ψ)

⨂ᴷ-resp-≅ᴹ : ∀ {n} {A B E : Fin n → Channel}
             {f g : (k : Fin n) → Machine (A k) (B k ⊗₀ E k)}
           → (∀ k → f k ≅ᴹ g k) → ⨂ᴷ f ≅ᴹ ⨂ᴷ g
⨂ᴷ-resp-≅ᴹ {zero}  φ = ≅ᴹ-refl
⨂ᴷ-resp-≅ᴹ {suc n} φ = ⊗ᴷ-resp-≅ᴹ (φ fzero) (⨂ᴷ-resp-≅ᴹ (φ ∘ fsuc))
  where open import Function using (_∘_)

-- `assoc²γδ` of `ChannelCat`, now a theorem.
module _ where
  open import CategoricalCrypto.Machine.Iso using (∘-assoc-≅ᴹ)

  assoc²γδ-≅ᴹ : ∀ {A B C D E} {f : Machine A B} {g : Machine B C}
                  {h : Machine C D} {i : Machine D E}
              → ((i CC.∘ h) CC.∘ (g CC.∘ f)) ≅ᴹ (i CC.∘ ((h CC.∘ g) CC.∘ f))
  assoc²γδ-≅ᴹ {f = f} {g} {h} {i} =
    ≅ᴹ-trans (∘-assoc-≅ᴹ {f = g CC.∘ f} {g = h} {h = i})
             (∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym (∘-assoc-≅ᴹ {f = f} {g = g} {h = h})))

-- ----------------------------------------------------------------------------
-- `_≡ᴹ_` (heterogeneous machine equality, `Machine.Core`) is sound and stays —
-- it is what carries the channel-level bookkeeping that `_≅ᴹ_`, being
-- homogeneous, cannot express.  What follows are the two facts relating it to
-- `_≅ᴹ_`, plus the `∘ᴷ` congruence that used to be a `ChannelCat` postulate
-- and is in fact provable by matching on the equalities.
-- ----------------------------------------------------------------------------

module _ where
  open import Relation.Binary.HeterogeneousEquality using () renaming (refl to H-refl)

  ≡ᴹ→≅ᴹ : ∀ {A B} {M N : Machine A B} → M ≡ᴹ N → M ≅ᴹ N
  ≡ᴹ→≅ᴹ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H-refl } = ≅ᴹ-refl

  -- NB: the channel equalities are explicit arguments.  Matching them off the
  -- `_≡ᴹ_` fields instead would require inverting `_⊗₀_` — that is exactly the
  -- `⊗-injectiveˡ/ʳ` the old record postulated, and it is unprovable (the
  -- inconsistency lived in asserting it alongside the unit laws).  Every call
  -- site has the component equalities to hand anyway.
  ∘ᴷ-cong-≡ᴹ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂ E₁₁ E₁₂ E₂₁ E₂₂}
              → B₁ ≡ B₂ → C₁ ≡ C₂ → E₂₁ ≡ E₂₂ → E₁₁ ≡ E₁₂
              → {M : Machine B₁ (C₁ ⊗₀ E₂₁)} {M' : Machine B₂ (C₂ ⊗₀ E₂₂)}
                {N : Machine A₁ (B₁ ⊗₀ E₁₁)} {N' : Machine A₂ (B₂ ⊗₀ E₁₂)}
              → M ≡ᴹ M' → N ≡ᴹ N' → (M ∘ᴷ N) ≡ᴹ (M' ∘ᴷ N')
  ∘ᴷ-cong-≡ᴹ refl refl refl refl
             record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H-refl }
             record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H-refl } = ≡ᴹ-refl

-- ----------------------------------------------------------------------------
-- Transport of a run along an isomorphism.  This is the `≅ᴹ` replacement for
-- `Trace-subst`: only the states move (`to φ`), every input/output is kept.
-- ----------------------------------------------------------------------------

Trace-map : ∀ {A B} {P Q : Machine A B} (φ : P ≅ᴹ Q) {s s'}
          → Trace P s s' → Trace Q (to φ s) (to φ s')
Trace-map φ []                    = []
Trace-map φ (tr ∷ʳ⟨ i , o , st ⟩) = Trace-map φ tr ∷ʳ⟨ i , o , step-to φ st ⟩
