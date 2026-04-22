{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)
open import CategoricalCrypto hiding (id; _∘_)
import Relation.Binary.HeterogeneousEquality as H

module CategoricalCrypto.Ext where

≡ᴹ-trans : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
           {M₁ : Machine A₁ B₁} {M₂ : Machine A₂ B₂} {M₃ : Machine A₃ B₃}
         → M₁ ≡ᴹ M₂ → M₂ ≡ᴹ M₃ → M₁ ≡ᴹ M₃
≡ᴹ-trans record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
         record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
  = ≡ᴹ-refl

≡ᴹ→≡ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ᴹ M₂ → M₁ ≡ M₂
≡ᴹ→≡ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } = refl

≡→≡ᴹ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ M₂ → M₁ ≡ᴹ M₂
≡→≡ᴹ refl = ≡ᴹ-refl

subst-≡ᴹ-out : ∀ {x y} {A : Channel} {B : Channel → Channel}
             → (eq : x ≡ y) (M : Machine A (B x))
             → subst (λ c → Machine A (B c)) eq M ≡ᴹ M
subst-≡ᴹ-out refl _ = ≡ᴹ-refl

idᴷ-cong-≡ᴹ : ∀ {A B} → A ≡ B → _≡ᴹ_ (idᴷ {A = A}) (idᴷ {A = B})
idᴷ-cong-≡ᴹ refl = ≡ᴹ-refl
