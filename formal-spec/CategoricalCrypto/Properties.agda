{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Properties where

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Product.Properties
open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.Morphism
open import Categories.Morphism.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

open import Categories.Category.Monoidal

import Relation.Binary.Reasoning.Setoid as SetoidR
import Categories.Functor as F

module _ {a} {b} {c} where
  ※-distrib₃ : {C D E : Category a b c} → (F : Functor C D) → (G : Functor C E)
      → NaturalIsomorphism (F ※ G) ((F ⁂ G) ∘F (id ※ id))
  ※-distrib₃ {C} {D} {E} F G = unique {i = F} {j = G} {h = ((F ⁂ G) ∘F (id ※ id))}
    (niHelper record
      { η = λ _ → D.id
      ; η⁻¹ = λ _ → D.id
      ; commute = λ _ → let open D.HomReasoning in D.identityˡ ○ ⟺ D.identityʳ
      ; iso = λ _ → IsIso.iso (id-is-iso D) })
    (niHelper record
      { η = λ _ → E.id
      ; η⁻¹ = λ _ → E.id
      ; commute = λ _ → let open E.HomReasoning in E.identityˡ ○ ⟺ E.identityʳ
      ; iso = λ _ → IsIso.iso (id-is-iso E) })
    where module D = Category D
          module E = Category E

  ⁂-∘F : {C C' D D' E E' : Category a b c}
       → (F : Functor C D) → (F' : Functor C' D') → (G : Functor D E) → (G' : Functor D' E')
       → NaturalIsomorphism ((G ⁂ G') ∘F (F ⁂ F')) ((G ∘F F) ⁂ (G' ∘F F'))
  ⁂-∘F {E = E} {E'} F F' G G' = niHelper record
    { η = λ _ → P.id
    ; η⁻¹ = λ _ → P.id
    ; commute = λ _ → let open P.HomReasoning in P.identityˡ ○ ⟺ P.identityʳ
    ; iso = λ _ → IsIso.iso (id-is-iso (Product E E'))
    }
    where module P  = Category (Product E E')

  ⁂-※ : {C D D' E E' : Category a b c}
      → (F : Functor C D) → (F' : Functor C D') → (G : Functor D E) → (G' : Functor D' E')
      → NaturalIsomorphism ((G ⁂ G') ∘F (F ※ F')) ((G ∘F F) ※ (G' ∘F F'))
  ⁂-※ F F' G G' = begin
    ((G ⁂ G') ∘F (F ※ F')) ≈⟨ (G ⁂ G') ⓘˡ ※-distrib₃ F F' ⟩
    ((G ⁂ G') ∘F (F ⁂ F') ∘F (id ※ id)) ≈⟨ NI.associator (id ※ id) (F ⁂ F') (G ⁂ G') ⟨
    (((G ⁂ G') ∘F (F ⁂ F')) ∘F (id ※ id)) ≈⟨ ⁂-∘F F F' G G' ⓘʳ (id ※ id) ⟩
    (((G ∘F F) ⁂ (G' ∘F F')) ∘F (id ※ id)) ≈⟨ ※-distrib₃ (G ∘F F) (G' ∘F F') ⟨
    ((G ∘F F) ※ (G' ∘F F')) ∎
    where open SetoidR (Functor-NI-setoid _ _)

  ∘F-const : ∀ {C D E : Category a b c} d
           → (F : Functor D E) → NaturalIsomorphism {C = C} (F ∘F const d) (const (Functor.F₀ F d))
  ∘F-const {E = E} d F = niHelper record
    { η = λ _ → E.id
    ; η⁻¹ = λ _ → E.id
    ; commute = λ f → begin E.id E.∘ Functor.F₁ F _ ≈⟨ refl⟩∘⟨ Functor.identity F ⟩ E.id E.∘ E.id ∎
    ; iso = λ _ → IsIso.iso (id-is-iso E) }
    where module E = Category E
          open E.HomReasoning

  -×_ : {C D : Category a b c} → D .Category.Obj → Functor C (Product C D)
  -×_ {C} {D} d = F.id ※ const d

  ⁂-× : {C D E : Category a b c} → (G : Functor D E) → (d : D .Category.Obj)
      → NaturalIsomorphism ((F.id {C = C} ⁂ G) ∘F -× d) (-× Functor.F₀ G d)
  ⁂-× G d = begin
    (F.id ⁂ G) ∘F -× d ≈⟨ ⁂-※ _ _ F.id G ⟩
    ((F.id ∘F F.id) ※ (G ∘F const d)) ≈⟨ NI.unitorˡ ※ⁿⁱ NI.refl ⟩
    (F.id ※ (G ∘F const d)) ≈⟨ NI.refl ※ⁿⁱ ∘F-const d G ⟩
    (F.id ※ (const (Functor.F₀ G d))) ≈⟨ NI.refl ⟩
    -× Functor.F₀ G d ∎
    where open SetoidR (Functor-NI-setoid _ _)
