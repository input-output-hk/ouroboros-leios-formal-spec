{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.NaturalTransformationHelper where

open import Level

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

open import Categories.Tactic.Category

open import Data.Product

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e


module _ (F G : Functor C D) where
  private
    module C = Category C
    module F = Functor F
    module G = Functor G

  open Category D

  Family : Set _
  Family = ∀ X → D [ F.F₀ X , G.F₀ X ]

  Natural : Family → Set _
  Natural η = ∀ {X Y} → (f : C [ X , Y ]) → (η Y) ∘ F.F₁ f ≈ G.F₁ f ∘ (η X)

module _ (F G : Bifunctor C D E) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  open Category E

  open import Categories.Functor.Bifunctor.Properties

  natural-components : (η : Family F G)
                     → (∀ d → Natural (appʳ F d) (appʳ G d) (λ c → η (c , d)))
                     → (∀ c → Natural (appˡ F c) (appˡ G c) (λ d → η (c , d)))
                     → Natural F G η
  natural-components η natural₁ natural₂ {X} {Y} (f₁ , f₂) = begin
    η Y ∘ F.F₁ (f₁ , f₂)
      ≈⟨ refl⟩∘⟨ [ F ]-decompose₁ ⟩
    η Y ∘ F.F₁ (f₁ , D.id) ∘ F.F₁ (C.id , f₂)
      ≈⟨ solve E ⟩
    (η Y ∘ F.F₁ (f₁ , D.id)) ∘ F.F₁ (C.id , f₂)
      ≈⟨ natural₁ _ f₁ ⟩∘⟨refl ⟩
    (G.F₁ (f₁ , D.id) ∘ η _) ∘ F.F₁ (C.id , f₂)
      ≈⟨ solve E ⟩
    G.F₁ (f₁ , D.id) ∘ η _ ∘ F.F₁ (C.id , f₂)
      ≈⟨ refl⟩∘⟨ natural₂ _ f₂ ⟩
    G.F₁ (f₁ , D.id) ∘ G.F₁ (C.id , f₂) ∘ η X
      ≈⟨ solve E ⟩
    (G.F₁ (f₁ , D.id) ∘ G.F₁ (C.id , f₂)) ∘ η X
      ≈⟨ [ G ]-decompose₁ ⟩∘⟨refl ⟨
    G.F₁ (f₁ , f₂) ∘ η X ∎
    where open HomReasoning
