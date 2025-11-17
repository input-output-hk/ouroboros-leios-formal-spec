{-# OPTIONS --safe #-}
module CategoricalCrypto.MonoidalCoherence where

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Properties
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Monad.Graded
open import Categories.Morphism
open import Categories.NaturalTransformation hiding (id)

open import Categories.Category.Instance.Sets

open import Categories.Tactic.Category

open import Data.Product
open import Data.List as L hiding ([_])

open import CategoricalCrypto.NaturalTransformationHelper

open import CategoricalCrypto.FreeMonoidal

open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

open import Categories.Category.Construction.Functors using () renaming (curry to curryF)

open import Categories.Category.Product
open import CategoricalCrypto.Properties

import Data.Vec as V
open import Data.Fin using (Fin)
open import Data.Empty

module CoherenceThm (X : Set) where
  open FreeMonoidal (record { v = Mon ; X = X ; mor = λ _ _ → ⊥ ; _≈mor_ = λ _ _ → ⊥ })

  open Commutation FreeMonoidal
  open import CategoricalCrypto.Discrete
  open Discrete (List X)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
  open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (refl; trans; unitorˡ; unitorʳ; associator)

  import Categories.Functor as F

  module FM where
    open Category FreeMonoidal public
    open Monoidal Monoidal-FreeMonoidal public
    open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal public
    open Shorthands public
    open Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal public

  module FMReasoning where
    open import Categories.Category.Monoidal.Reasoning Monoidal-FreeMonoidal public

  import Relation.Binary.Reasoning.Setoid as SetoidR

  ⟦_⟧ : ObjTerm → List X → List X
  ⟦ unit ⟧ n = n
  ⟦ t ⊗₀ t₁ ⟧ n = ⟦ t ⟧ (⟦ t₁ ⟧ n)
  ⟦ Var x ⟧ n = x ∷ n

  hom⇒≡⟦⟧' : ∀ {A B x y} → HomTerm A B → x ≡ y → ⟦ A ⟧ x ≡ ⟦ B ⟧ y
  hom⇒≡⟦⟧' id refl = refl
  hom⇒≡⟦⟧' {x} {y} (h ∘ h') eq = trans (hom⇒≡⟦⟧' h' eq) (hom⇒≡⟦⟧' h refl)
  hom⇒≡⟦⟧' {A ⊗₀ B} {C ⊗₀ D} {x} {y} (h ⊗₁ h') eq = hom⇒≡⟦⟧' h (hom⇒≡⟦⟧' h' eq)
  hom⇒≡⟦⟧' λ⇒ refl = refl
  hom⇒≡⟦⟧' λ⇐ refl = refl
  hom⇒≡⟦⟧' ρ⇒ refl = refl
  hom⇒≡⟦⟧' ρ⇐ refl = refl
  hom⇒≡⟦⟧' α⇒ refl = refl
  hom⇒≡⟦⟧' α⇐ refl = refl

  ⟦_⟧₀ = uncurry ⟦_⟧
  ⟦_⟧₁ : ∀ {A B x y} → HomTerm A B × x ≡ y → ⟦ A ⟧ x ≡ ⟦ B ⟧ y
  ⟦_⟧₁ = uncurry hom⇒≡⟦⟧'

  ι₀ : Discrete .Category.Obj → FreeMonoidal .Category.Obj
  ι₀ [] = unit
  ι₀ (x ∷ []) = Var x
  ι₀ (x ∷ x₁ ∷ x₂) = Var x ⊗₀ ι₀ (x₁ ∷ x₂)

  ι₁ : ∀ {A B} → Discrete [ A , B ] → FreeMonoidal [ ι₀ A , ι₀ B ]
  ι₁ refl = id

  opaque
    ⟦_⟧F : Bifunctor FreeMonoidal Discrete Discrete
    ⟦_⟧F = record
      { F₀ = ⟦_⟧₀
      ; F₁ = ⟦_⟧₁
      ; identity = _
      ; homomorphism = _
      ; F-resp-≈ = λ _ → _
      }

    ι : Functor Discrete FreeMonoidal
    ι = record
      { F₀ = ι₀
      ; F₁ = ι₁
      ; identity = FM.Equiv.refl
      ; homomorphism = λ where {_} {_} {_} {refl} {refl} → FM.HomReasoning.⟺ FM.identityˡ
      ; F-resp-≈ = λ where {_} {_} {refl} {refl} _ → FM.Equiv.refl
      }

  Nf : Functor FreeMonoidal Discrete
  Nf = appʳ ⟦_⟧F []

  module C where
    open import Categories.Category.Construction.Core FreeMonoidal public
    open Category Core public

  F1 F2 : Bifunctor FreeMonoidal Discrete FreeMonoidal
  F1 = FM.⊗ ∘F (F.id ⁂ ι)
  F2 = ι ∘F ⟦_⟧F

  opaque
    unfolding ⟦_⟧F
    -- making the termination checker happy
    iso' : (x : ObjTerm) → (y : List X) → C.Core [ Functor.₀ F1 (x , y) , Functor.₀ F2 (x , y) ]
    iso' unit n = FM.unitorˡ
    iso' (a ⊗₀ b) n = iso' a (⟦ b ⟧ n) C.∘ (≅.refl _ FM.⊗ᵢ iso' b n) C.∘ FM.associator
    iso' (Var x) [] = FM.unitorʳ
    iso' (Var x) (x₁ ∷ n) = ≅.refl _

    iso : (X : ObjTerm × List X) → C.Core [ Functor.₀ F1 X , Functor.₀ F2 X ]
    iso = uncurry iso'

    iso₁ : (X : ObjTerm × List X) → FreeMonoidal [ Functor.₀ F1 X , Functor.₀ F2 X ]
    iso₁ X = _≅_.from (iso X)

    iso₁-assoc-ty : Set
    iso₁-assoc-ty = ∀ {A B d} → iso₁ (A ⊗₀ B , d) ≈Term iso₁ (A , ⟦ B ⟧ d) ∘ (id ⊗₁ iso₁ (B , d)) ∘ FM.α⇒

    -- It's necessary to hide this type behind a definition, otherwise it won't type check in an opaque block
    iso₁-assoc : iso₁-assoc-ty
    iso₁-assoc = ≈-Term-refl

  P = Product FreeMonoidal Discrete

  module _ where opaque
    unfolding ⟦_⟧F ι iso iso₁-assoc iso₁-assoc-ty
    open FMReasoning
    open import Categories.Morphism.Reasoning FreeMonoidal

    iso-comm-ty : Set
    iso-comm-ty = ∀ {A} {d₁} {d₂} {g : d₁ ≡ d₂}
           → iso₁ (A , d₂) ∘ id ⊗₁ ι₁ g
        FM.≈ ι₁ (hom⇒≡⟦⟧' (id {A}) g) ∘ iso₁ (A , d₁)

    iso-comm : iso-comm-ty
    iso-comm {A} {d} {d} {refl} = begin
      iso₁ (A , d) ∘ id ⊗₁ id
        ≈⟨ refl⟩∘⟨ FM.⊗.identity ○ id-comm ⟩
      id ∘ iso₁ (A , d) ∎

    ι-∘ : ∀ {A B C D} d (f : HomTerm A B) (g : HomTerm C D)
        → ι₁ ⟦ f , ⟦ g , refl {x = d} ⟧₁ ⟧₁
          FM.≈ ι₁ ⟦ id {A = B} , ⟦ g , refl {x = d} ⟧₁ ⟧₁ ∘ ι₁ ⟦ f , refl {x = ⟦ C ⟧ d} ⟧₁
    ι-∘ d f g = begin
      ι₁ ⟦ f , ⟦ g , refl ⟧₁ ⟧₁
        ≈⟨ ι.F-resp-≈ _ ⟩
      ι₁ (⟦ id , ⟦ g , refl ⟧₁ ⟧₁ D.∘ ⟦ f , refl ⟧₁)
        ≈⟨ ι.homomorphism ⟩
      ι₁ ⟦ id , ⟦ g , refl ⟧₁ ⟧₁ ∘ ι₁ ⟦ f , refl ⟧₁ ∎
      where module ι = Functor ι
            module D = Category Discrete

    natural-id : ∀ {X} → iso₁ X ∘ Functor.F₁ F1 (id , refl) FM.≈ Functor.F₁ F2 (id , refl) ∘ iso₁ X
    natural-id {X} = begin
      iso₁ X ∘ id ⊗₁ id
        ≈⟨ refl⟩∘⟨ FM.⊗.identity ○ ⟺ id-comm-sym ⟩
      id ∘ iso₁ X ∎

    natural-∘ : ∀ {A B C} d (g : HomTerm B C) (f : HomTerm A B)
      → iso₁ (C , d) ∘ Functor.F₁ F1 (g , refl) FM.≈ Functor.F₁ F2 (g , refl) ∘ iso₁ (B , d)
      → iso₁ (B , d) ∘ Functor.F₁ F1 (f , refl) FM.≈ Functor.F₁ F2 (f , refl) ∘ iso₁ (A , d)
      → iso₁ (C , d) ∘ Functor.F₁ F1 (g ∘ f , refl) FM.≈ Functor.F₁ F2 (g ∘ f , refl) ∘ iso₁ (A , d)
    natural-∘ {A} {B} {C} d g f Hg Hf = begin
      iso₁ (C , d) ∘ Functor.F₁ F1 (g ∘ f , refl)
        ≈⟨ refl⟩∘⟨ Functor.homomorphism F1 {f = f , refl} {g , refl} ⟩
      iso₁ (C , d) ∘ Functor.F₁ F1 (g , refl) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ FM.assoc ⟨
      (iso₁ (C , d) ∘ Functor.F₁ F1 (g , refl)) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ Hg ⟩∘⟨refl ⟩
      (Functor.F₁ F2 (g , refl) ∘ iso₁ (B , d)) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ FM.assoc ⟩
      Functor.F₁ F2 (g , refl) ∘ iso₁ (B , d) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ refl⟩∘⟨ Hf ⟩
      Functor.F₁ F2 (g , refl) ∘ Functor.F₁ F2 (f , refl) ∘ iso₁ (A , d)
        ≈⟨ FM.assoc ⟨
      (Functor.F₁ F2 (g , refl) ∘ Functor.F₁ F2 (f , refl)) ∘ iso₁ (A , d)
        ≈⟨ Functor.homomorphism F2 {f = f , refl} {g = g , refl} ⟩∘⟨refl ⟨
      Functor.F₁ F2 (g ∘ f , refl) ∘ iso₁ (A , d) ∎

    natural-⊗ : ∀ {A B C D} d (f : HomTerm A B) (g : HomTerm C D)
      → iso₁ (B , ⟦ C ⟧ d) ∘ Functor.F₁ F1 (f , refl) FM.≈ Functor.F₁ F2 (f , refl) ∘ iso₁ (A , ⟦ C ⟧ d)
      → iso₁ (D , d) ∘ Functor.F₁ F1 (g , refl) FM.≈ Functor.F₁ F2 (g , refl) ∘ iso₁ (C , d)
      → iso₁ (B ⊗₀ D , d) ∘ Functor.F₁ F1 (f ⊗₁ g , refl) FM.≈ Functor.F₁ F2 (f ⊗₁ g , refl) ∘ iso₁ (A ⊗₀ C , d)
    natural-⊗ {A} {B} {C} {D} d f g Hf Hg = begin
      (iso₁ (B , ⟦ D ⟧ d) ∘ id ⊗₁ iso₁ (D , d) ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ id
        ≈⟨ assoc²' ○ refl⟩∘⟨ refl⟩∘⟨ FM.assoc-commute-from ○ refl⟩∘⟨ ⟺ assoc ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ⊗₁ iso₁ (D , d) ∘ f ⊗₁ g ⊗₁ id) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ∘ f) ⊗₁ (iso₁ (D , d) ∘ g ⊗₁ id) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ Hg ⟩∘⟨refl ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ∘ f) ⊗₁ (ι₁ ⟦ (g , refl) ⟧₁ ∘ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      iso₁ (B , ⟦ D ⟧ d) ∘ (id ⊗₁ ι₁ ⟦ (g , refl) ⟧₁ ∘ f ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ assoc²'' ⟩
      (iso₁ (B , ⟦ D ⟧ d) ∘ id ⊗₁ ι₁ ⟦ (g , refl) ⟧₁) ∘ f ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ iso-comm ⟩∘⟨refl ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ f ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ idʳ ⟩⊗⟨ ⟺ idˡ ⟩∘⟨refl ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ (f ∘ id) ⊗₁ (id ∘ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ (f ⊗₁ id ∘ id ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ iso₁ (B , ⟦ C ⟧ d)) ∘ f ⊗₁ id ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ assoc ○ refl⟩∘⟨ ⟺ assoc ⟩
      ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ (iso₁ (B , ⟦ C ⟧ d) ∘ f ⊗₁ id) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ refl⟩∘⟨ Hf ⟩∘⟨refl ⟩
      ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ (ι₁ ⟦ (f , refl) ⟧₁ ∘ iso₁ (A , ⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ assoc²'' ⟩
      (ι₁ ⟦ (id {B} ⊗₁ g , refl {x = d}) ⟧₁ ∘ ι₁ ⟦ (f , refl) ⟧₁) ∘ iso₁ (A , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒
        ≈⟨ ⟺ (ι-∘ d f g) ⟩∘⟨refl ⟩
      ι₁ ⟦ (f ⊗₁ g , refl) ⟧₁ ∘ iso₁ (A , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒ ∎

    natural-λ⇒ : ∀ {A d}
               → iso₁ (A , d) ∘ Functor.F₁ F1 (λ⇒ , refl)
            FM.≈ Functor.F₁ F2 (λ⇒ , refl) ∘ iso₁ (unit ⊗₀ A , d)
    natural-λ⇒ {A} {d} = begin
      iso₁ (A , d) ∘ λ⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.coherence₁ ⟩
      iso₁ (A , d) ∘ λ⇒ ∘ α⇒
        ≈⟨ ⟺ assoc ⟩
      (iso₁ (A , d) ∘ λ⇒) ∘ α⇒
        ≈⟨ ⟺ FM.unitorˡ-commute-from ⟩∘⟨refl ⟩
      (λ⇒ ∘ id ⊗₁ iso₁ (A , d)) ∘ α⇒
        ≈⟨ assoc ○ (⟺ idˡ) ⟩
      id ∘ λ⇒ ∘ id ⊗₁ iso₁ (A , d) ∘ α⇒ ∎

    natural-λ⇐ : ∀ {A d}
               → iso₁ (unit ⊗₀ A , d) ∘ Functor.F₁ F1 (λ⇐ , refl)
            FM.≈ Functor.F₁ F2 (λ⇐ , refl) ∘ iso₁ (A , d)
    natural-λ⇐ {A} {d} = begin
      (λ⇒ ∘ id ⊗₁ iso₁ (A , d) ∘ α⇒) ∘ λ⇐ ⊗₁ id
        ≈⟨ ⟺ idˡ ⟩∘⟨refl ⟩
      (id ∘ λ⇒ ∘ id ⊗₁ iso₁ (A , d) ∘ α⇒) ∘ λ⇐ ⊗₁ id
        ≈⟨ ⟺ natural-λ⇒ ⟩∘⟨refl ⟩
      (iso₁ (A , d) ∘ λ⇒ ⊗₁ id) ∘ λ⇐ ⊗₁ id
        ≈⟨ assoc ⟩
      iso₁ (A , d) ∘ λ⇒ ⊗₁ id ∘ λ⇐ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.⊗.homomorphism ⟩
      iso₁ (A , d) ∘ (λ⇒ ∘ λ⇐) ⊗₁ (id ∘ id)
        ≈⟨ refl⟩∘⟨ λ⇒∘λ⇐≈id ⟩⊗⟨ idˡ ⟩
      iso₁ (A , d) ∘ id ⊗₁ id
        ≈⟨ refl⟩∘⟨ FM.⊗.identity ⟩
      iso₁ (A , d) ∘ id
        ≈⟨ id-comm ⟩
      id ∘ iso₁ (A , d) ∎

    natural-ρ⇒ : ∀ {A d}
               → iso₁ (A , d) ∘ Functor.F₁ F1 (ρ⇒ , refl)
            FM.≈ Functor.F₁ F2 (ρ⇒ , refl) ∘ iso₁ (A ⊗₀ unit , d)
    natural-ρ⇒ {A} {d} = begin
      iso₁ (A , d) ∘ ρ⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.triangle ⟩
      iso₁ (A , d) ∘ id ⊗₁ λ⇒ ∘ α⇒
        ≈⟨ ⟺ idˡ ⟩
      id ∘ iso₁ (A , d) ∘ id ⊗₁ λ⇒ ∘ α⇒ ∎

    natural-ρ⇐ : ∀ {A d}
               → iso₁ (A ⊗₀ unit , d) ∘ Functor.F₁ F1 (ρ⇐ , refl)
            FM.≈ Functor.F₁ F2 (ρ⇐ , refl) ∘ iso₁ (A , d)
    natural-ρ⇐ {A} {d} = begin
      (iso₁ (A , d) ∘ id ⊗₁ λ⇒ ∘ α⇒) ∘ ρ⇐ ⊗₁ id
        ≈⟨ (refl⟩∘⟨ FM.triangle) ⟩∘⟨refl ⟩
      (iso₁ (A , d) ∘ ρ⇒ ⊗₁ id) ∘ ρ⇐ ⊗₁ id
        ≈⟨ assoc ⟩
      iso₁ (A , d) ∘ ρ⇒ ⊗₁ id ∘ ρ⇐ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.⊗.homomorphism ⟩
      iso₁ (A , d) ∘ (ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ id)
        ≈⟨ refl⟩∘⟨ FM.unitorʳ.isoʳ ⟩⊗⟨ idˡ ⟩
      iso₁ (A , d) ∘ id ⊗₁ id
        ≈⟨ refl⟩∘⟨ FM.⊗.identity ⟩
      iso₁ (A , d) ∘ id
        ≈⟨ id-comm ⟩
      id ∘ iso₁ (A , d) ∎

    natural-α⇒ : ∀ {A B C d}
               → iso₁ (A ⊗₀ B ⊗₀ C , d) ∘ Functor.F₁ F1 (α⇒ , refl)
            FM.≈ Functor.F₁ F2 (α⇒ , refl) ∘ iso₁ ((A ⊗₀ B) ⊗₀ C , d)
    natural-α⇒ {A} {B} {C} {d} = begin
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒) ∘ α⇒ ⊗₁ id
        ≈⟨ assoc²' ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ Functor.homomorphism (A FM.⊗-) ⟩∘⟨refl ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ (id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ (id ⊗₁ iso₁ (C , d) ∘ α⇒)) ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Functor.homomorphism (A FM.⊗-)) ⟩∘⟨refl) ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ (id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ (id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ id ⊗₁ α⇒)) ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ assoc²' ○ ⟺ assoc ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.pentagon ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ α⇒ ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ assoc ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ (id ⊗₁ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ FM.assoc-commute-from ⟩∘⟨refl ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ (α⇒ ∘ (id ⊗₁ id) ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ FM.⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d)) ∘ (α⇒ ∘ id ⊗₁ iso₁ (C , d)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ assoc ○ assoc ○ ⟺ assoc²' ○ ⟺ idˡ ⟩
      id ∘ (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ α⇒) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒ ∎

    natural-α⇐ : ∀ {A B C d}
               → iso₁ ((A ⊗₀ B) ⊗₀ C , d) ∘ Functor.F₁ F1 (α⇐ , refl)
            FM.≈ Functor.F₁ F2 (α⇐ , refl) ∘ iso₁ (A ⊗₀ B ⊗₀ C , d)
    natural-α⇐ {A} {B} {C} {d} = begin
      ((iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ α⇒) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇐ ⊗₁ id
        ≈⟨ ⟺ idˡ ⟩∘⟨refl ⟩
      (id ∘ ((iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ iso₁ (B , ⟦ C ⟧ d) ∘ α⇒) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒)) ∘ α⇐ ⊗₁ id
        ≈⟨ ⟺ natural-α⇒ ⟩∘⟨refl ⟩
      ((iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒) ∘ α⇒ ⊗₁ id) ∘ α⇐ ⊗₁ id
        ≈⟨ assoc ○ assoc²' ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒ ∘ α⇒ ⊗₁ id ∘ α⇐ ⊗₁ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (Functor.homomorphism (FM.-⊗ _)) ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒ ∘ (α⇒ ∘ α⇐) ⊗₁ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (FM.associator.isoʳ ⟩⊗⟨refl ○ FM.⊗.identity) ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒ ∘ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idʳ ⟩
      iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒
        ≈⟨ ⟺ idˡ ⟩
      id ∘ iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∘ id ⊗₁ (iso₁ (B , ⟦ C ⟧ d) ∘ id ⊗₁ iso₁ (C , d) ∘ α⇒) ∘ α⇒ ∎

  natural₁ : ∀ d → Natural (appʳ F1 d) (appʳ F2 d) (λ c → iso₁ (c , d))
  natural₁ d id = natural-id
  natural₁ d (g ∘ f) = natural-∘ _ g f (natural₁ _ g) (natural₁ _ f)
  natural₁ d (_⊗₁_ {A} {B} {C} {D} f g) = natural-⊗ _ f g (natural₁ _ f) (natural₁ _ g)
  natural₁ d λ⇒ = natural-λ⇒
  natural₁ d λ⇐ = natural-λ⇐
  natural₁ d ρ⇒ = natural-ρ⇒
  natural₁ d ρ⇐ = natural-ρ⇐
  natural₁ d α⇒ = natural-α⇒
  natural₁ d α⇐ = natural-α⇐

  opaque
    unfolding iso₁
    ⟦⟧≅⊗ : NaturalIsomorphism F2 F1
    ⟦⟧≅⊗ = NI.sym (pointwise-iso iso natural)
      where
        natural : ∀ {X Y} → (f : P [ X , Y ])
                → FreeMonoidal [ iso₁ Y ∘ Functor.₁ F1 f ≈ Functor.₁ F2 f ∘ iso₁ X ]
        natural = natural-components F1 F2 iso₁ natural₁
          (λ c → Discrete-NaturalD {F = appˡ F1 c} {appˡ F2 c} (λ d → iso₁ (c , d)))

  opaque
    unfolding ι
    Nf≅id : NaturalIsomorphism (ι ∘F Nf) Categories.Functor.id
    Nf≅id = begin
      ι ∘F Nf ≈⟨ NI.associator (-× []) ⟦_⟧F ι ⟨
      (ι ∘F ⟦_⟧F) ∘F -× [] ≈⟨ ⟦⟧≅⊗ ⓘʳ (-× []) ⟩
      (FM.⊗ ∘F (F.id ⁂ ι)) ∘F -× [] ≈⟨ NI.associator (-× []) (F.id ⁂ ι) FM.⊗ ⟩
      FM.⊗ ∘F (F.id ⁂ ι) ∘F (-× []) ≈⟨ FM.⊗ ⓘˡ (⁂-× {C = FreeMonoidal} ι []) ⟩
      FM.⊗ ∘F (-× unit) ≈⟨ NI.refl ⟩
      appʳ FM.⊗ unit ≈⟨ FM.unitorʳ-naturalIsomorphism ⟩
      Categories.Functor.id ∎
      where open SetoidR (Functor-NI-setoid FreeMonoidal FreeMonoidal)

  all-Comm : ∀ {A B} f g → [ A ⇒ B ]⟨ f ≈ g ⟩
  all-Comm f g = push-eq Nf≅id (ι.F-resp-≈ _)
    where module ι = Functor ι

module Solver (C : MonoidalCategory 0ℓ 0ℓ 0ℓ)
              {n} (vars : V.Vec (C .MonoidalCategory.Obj) n) where
  open MonoidalCategory
  d : FreeMonoidalData
  d = record { v = Mon ; X = Fin n ; mor = λ _ _ → ⊥ ; _≈mor_ = λ _ _ → ⊥ }
  open FreeMonoidal d public
  open CoherenceThm (Fin n) hiding (⟦_⟧₁)
  open FreeFunctor {d = d} record
    { ⟦v⟧ = record { C = C .U ; Monoidal-C = C .monoidal ; Symmetric-C = λ where ⦃ () ⦄ }
    ; ⟦_⟧ᵖ₀ = V.lookup vars
    ; ⟦_⟧ᵖ₁ = λ ()
    ; ⟦⟧-≈ = λ ()
    }

  opaque
    solveM : ∀ {X Y} → (f g : FreeMonoidal [ X , Y ]) → (C .U) [ ⟦ f ⟧₁ ≈ ⟦ g ⟧₁ ]
    solveM f g = Functor.F-resp-≈ freeFunctor (all-Comm f g)
  {-# INJECTIVE_FOR_INFERENCE solveM #-}
