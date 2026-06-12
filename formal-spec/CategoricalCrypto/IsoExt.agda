{-# OPTIONS --safe #-}

-- ============================================================================
-- `_⊗₁_` congruence for the machine isomorphism `_≅ᴹ_`.
--
-- Proven here, pending upstreaming to categorical-crypto: `Machine.Iso`
-- proves the `_∘_` congruence (`∘-resp-≅ᴹ`) but states none for `_⊗₁_`.
-- `×-map`/`CompRel-map` mirror the corresponding PRIVATE helpers of
-- `Machine.Iso`.  `CompRel-map` is fully generic in the message indices
-- (i, mo), so it applies unchanged through the definitionally-transparent
-- `modifyStepRel` relabel baked into `_⊗₁_`.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_; MkIso; ≅ᴹ-sym)

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

⊗₁-resp-≅ᴹ : ∀ {A B C D} {M M' : Machine A B} {N N' : Machine C D}
           → M ≅ᴹ M' → N ≅ᴹ N' → (M ⊗₁ N) ≅ᴹ (M' ⊗₁ N')
⊗₁-resp-≅ᴹ φ ψ = MkIso
  (×-map (to φ) (to ψ))
  (×-map (from φ) (from ψ))
  (λ (s₁ , s₂) → cong₂ _,_ (from∘to φ s₁) (from∘to ψ s₂))
  (λ (s₁ , s₂) → cong₂ _,_ (to∘from φ s₁) (to∘from ψ s₂))
  (CompRel-map φ ψ)
  (CompRel-map (≅ᴹ-sym φ) (≅ᴹ-sym ψ))
