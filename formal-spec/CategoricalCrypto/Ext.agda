{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)
open import CategoricalCrypto hiding (id; _∘_)
import Relation.Binary.HeterogeneousEquality as H

-- | General-purpose helpers around `_≡ᴹ_` and `subst` on machines.
module CategoricalCrypto.Ext where

-- Transitivity of `_≡ᴹ_`.
≡ᴹ-trans : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
           {M₁ : Machine A₁ B₁} {M₂ : Machine A₂ B₂} {M₃ : Machine A₃ B₃}
         → M₁ ≡ᴹ M₂ → M₂ ≡ᴹ M₃ → M₁ ≡ᴹ M₃
≡ᴹ-trans record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
         record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
  = ≡ᴹ-refl

-- When both sides already have the same type, `_≡ᴹ_` collapses to `_≡_`.
≡ᴹ→≡ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ᴹ M₂ → M₁ ≡ M₂
≡ᴹ→≡ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } = refl

-- Inclusion `_≡_ → _≡ᴹ_` at matching types.
≡→≡ᴹ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ M₂ → M₁ ≡ᴹ M₂
≡→≡ᴹ refl = ≡ᴹ-refl

-- `subst` along a channel equality preserves the machine up to `_≡ᴹ_`
-- (variant of `subst-≡ᴹ` where the channel equation affects only the
-- output type).
subst-≡ᴹ-out : ∀ {x y} {A : Channel} {B : Channel → Channel}
             → (eq : x ≡ y) (M : Machine A (B x))
             → subst (λ c → Machine A (B c)) eq M ≡ᴹ M
subst-≡ᴹ-out refl _ = ≡ᴹ-refl

-- `idᴷ` instantiated at different (but propositionally equal) channels
-- are `_≡ᴹ_`.
idᴷ-cong-≡ᴹ : ∀ {A B} → A ≡ B → _≡ᴹ_ (idᴷ {A = A}) (idᴷ {A = B})
idᴷ-cong-≡ᴹ refl = ≡ᴹ-refl
