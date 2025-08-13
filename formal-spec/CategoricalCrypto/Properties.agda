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

module Mon {a} {b} {c} (C : Category a b c) (Mon-C : Monoidal C) where

  module M where
    open Category C public
    open Monoidal Mon-C public
    open import Categories.Category.Monoidal.Utilities Mon-C public
    open Shorthands public
    open import Categories.Category.Monoidal.Properties Mon-C public

  module FMReasoning where
    open import Categories.Category.Monoidal.Reasoning Mon-C public

  open M
  open FMReasoning

  open import Categories.Morphism.Reasoning C
  import Categories.Category.Construction.Core as Core
  open Core.Shorthands C
  open Commutation C

  pentagon-helper : ∀ {X Y Z W}
                  → [ X ⊗₀ (Y ⊗₀ (Z ⊗₀ W)) ⇒ (X ⊗₀ (Y ⊗₀ Z)) ⊗₀ W ]⟨
                      α⇐ ∘ M.id ⊗₁ α⇐ ≈ α⇒ ⊗₁ M.id ∘ α⇐ ∘ α⇐ ⟩
  pentagon-helper = begin
    α⇐ ∘ M.id ⊗₁ α⇐
      ≈⟨ switch-fromtoʳ M.associator (switch-fromtoʳ M.associator (pentagon-helper')) ⟩
    (α⇒ ⊗₁ M.id ∘ α⇐) ∘ α⇐
      ≈⟨ assoc ⟩
    α⇒ ⊗₁ M.id ∘ α⇐ ∘ α⇐ ∎
    where
      pentagon-helper' : ((α⇐ ∘ M.id ⊗₁ α⇐) ∘ α⇒) ∘ α⇒ ≈ α⇒ ⊗₁ M.id
      pentagon-helper' = begin
        ((α⇐ ∘ M.id ⊗₁ α⇐) ∘ α⇒) ∘ α⇒
          ≈⟨ assoc ○ assoc ⟩
        α⇐ ∘ M.id ⊗₁ α⇐ ∘ α⇒ ∘ α⇒
          ≈⟨ switch-fromtoˡ M.associator (switch-fromtoˡ (idᵢ ⊗ᵢ M.associator) pentagon) ⟨
        α⇒ ⊗₁ M.id ∎

  pentagon' : ∀ {X Y Z W}
            → [ X ⊗₀ Y ⊗₀ Z ⊗₀ W ⇒ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ]⟨
                α⇐ ⊗₁ M.id ∘ α⇐ ∘ M.id ⊗₁ α⇐ ≈ α⇐ ∘ α⇐ ⟩
  pentagon' = ⟺ (switch-fromtoˡ (M.associator ⊗ᵢ idᵢ) (⟺ pentagon-helper))

  λ-lemma : ∀ {A B C} {f : A ⇒ (B ⊗₀ C)} → α⇐ ∘ M.id ⊗₁ f ∘ λ⇐ ≈ λ⇐ ⊗₁ M.id ∘ f
  λ-lemma {A} {B} {C} {f} = begin
    α⇐ ∘ M.id ⊗₁ f ∘ λ⇐
      ≈⟨ refl⟩∘⟨ unitorˡ-commute-to ⟨
    α⇐ ∘ λ⇐ ∘ f
      ≈⟨ assoc ⟨
    (α⇐ ∘ λ⇐) ∘ f
      ≈⟨ coherence-inv₁ ⟩∘⟨refl ⟩
    λ⇐ ⊗₁ M.id ∘ f ∎

  α-lemma : ∀ {A B C D E F} {f : A ⇒ B ⊗₀ C} {g : C ⇒ D ⊗₀ E}
          → α⇐ ∘ M.id ⊗₁ ((α⇐ ∘ M.id ⊗₁ g) ∘ f) ≈ α⇒ ⊗₁ M.id ∘ (α⇐ ∘ M.id ⊗₁ g) ∘ (α⇐ ∘ M.id {A = F} ⊗₁ f)
  α-lemma {f = f} {g} = begin
    α⇐ ∘ M.id ⊗₁ ((α⇐ ∘ M.id ⊗₁ g) ∘ f)
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩
    α⇐ ∘ M.id ⊗₁ (α⇐ ∘ (M.id ⊗₁ g ∘ f))
      ≈⟨ refl⟩∘⟨ identityˡ ⟩⊗⟨refl ⟨
    α⇐ ∘ (M.id ∘ M.id) ⊗₁ (α⇐ ∘ (M.id ⊗₁ g ∘ f))
      ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟩
    α⇐ ∘ M.id ⊗₁ α⇐ ∘ M.id ⊗₁ (M.id ⊗₁ g ∘ f)
      ≈⟨ assoc ⟨
    (α⇐ ∘ M.id ⊗₁ α⇐) ∘ M.id ⊗₁ (M.id ⊗₁ g ∘ f)
      ≈⟨ pentagon-helper ⟩∘⟨refl ⟩
    (α⇒ ⊗₁ M.id ∘ α⇐ ∘ α⇐) ∘ M.id ⊗₁ (M.id ⊗₁ g ∘ f)
      ≈⟨ refl⟩∘⟨ identityˡ ⟩⊗⟨refl ⟨
    (α⇒ ⊗₁ M.id ∘ α⇐ ∘ α⇐) ∘ (M.id ∘ M.id) ⊗₁ (M.id ⊗₁ g ∘ f)
      ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟩
    (α⇒ ⊗₁ M.id ∘ α⇐ ∘ α⇐) ∘ M.id ⊗₁ M.id ⊗₁ g ∘ M.id ⊗₁ f
      ≈⟨ assoc ○ refl⟩∘⟨ assoc ⟩
    α⇒ ⊗₁ M.id ∘ α⇐ ∘ α⇐ ∘ M.id ⊗₁ M.id ⊗₁ g ∘ M.id ⊗₁ f
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟨
    α⇒ ⊗₁ M.id ∘ α⇐ ∘ (α⇐ ∘ M.id ⊗₁ M.id ⊗₁ g) ∘ M.id ⊗₁ f
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-to ⟩∘⟨refl ⟩
    α⇒ ⊗₁ M.id ∘ α⇐ ∘ ((M.id ⊗₁ M.id) ⊗₁ g ∘ α⇐) ∘ M.id ⊗₁ f
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
    α⇒ ⊗₁ M.id ∘ α⇐ ∘ (M.id ⊗₁ g ∘ α⇐) ∘ M.id ⊗₁ f
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ○ refl⟩∘⟨ ⟺ assoc ⟩
    α⇒ ⊗₁ M.id ∘ (α⇐ ∘ M.id ⊗₁ g) ∘ α⇐ ∘ M.id ⊗₁ f ∎
