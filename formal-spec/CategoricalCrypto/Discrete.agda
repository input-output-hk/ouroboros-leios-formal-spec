{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Discrete where

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Discrete

open import Categories.Functor
open import CategoricalCrypto.NaturalTransformationHelper

open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

module Discrete (X : Set) where

  Discrete : Category 0ℓ 0ℓ 0ℓ
  Discrete = categoryHelper record
    { Obj       = X
    ; _⇒_       = _≡_
    ; _≈_       = λ _ _ → ⊤ -- if we used _≡_ here then it's only discrete if we assume K
    ; id        = refl
    ; _∘_       = λ p q → trans q p
    ; assoc     = λ where {_} {_} {_} {_} {refl} {refl} {refl} → _
    ; identityˡ = λ where {_} {_} {refl} → _
    ; identityʳ = λ where {_} {_} {refl} → _
    ; equiv     = record { refl = _ ; sym = λ _ → _ ; trans = λ _ _ → _ }
    ; ∘-resp-≈  = λ _ _ → _
    }

  IsDiscrete-Discrete : IsDiscrete Discrete
  IsDiscrete-Discrete = record
    { isGroupoid = record { _⁻¹ = sym ; iso = record { isoˡ = _ ; isoʳ = _ } }
    ; preorder = λ where _ _ → _ }

  Discrete-NaturalD : {D : Category 0ℓ 0ℓ 0ℓ} {F G : Functor Discrete D} (η : Family F G)
                    → Natural F G η
  Discrete-NaturalD {C} {F} {G} η refl = begin
    η _ C.∘ Functor.F₁ F _
      ≈⟨ refl⟩∘⟨ Functor.identity F ⟩
    η _ C.∘ C.id
      ≈⟨ C.identityʳ ○ ⟺ C.identityˡ ⟩
    C.id C.∘ η _
      ≈⟨ Functor.identity G ⟩∘⟨refl ⟨
    Functor.F₁ G _ C.∘ η _ ∎
    where module C = Category C
          open C.HomReasoning

module Properties {o ℓ e} (CD : DiscreteCategory o ℓ e) where
  open DiscreteCategory CD renaming (category to C)
  open Category C

  all-Comm-Discrete : ∀ {A B} (f g : A ⇒ B) → f ≈ g
  all-Comm-Discrete = preorder

  Discrete-NaturalR : {D : Category 0ℓ 0ℓ 0ℓ} {F G : Functor D C} (η : Family F G)
                    → Natural F G η
  Discrete-NaturalR η f = all-Comm-Discrete _ _
