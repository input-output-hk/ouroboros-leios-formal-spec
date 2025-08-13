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

module CoherenceThm (X : Set) where
  open FreeMonoidal X

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

  open Monoidal Monoidal-FreeMonoidal using (unitorˡ; unitorʳ; associator)

  module C where
    open import Categories.Category.Construction.Core FreeMonoidal public
    open Category Core public

  F1 F2 : Bifunctor FreeMonoidal Discrete FreeMonoidal
  F1 = ι ∘F ⟦_⟧F
  F2 = FM.⊗ ∘F (F.id ⁂ ι)

  opaque
    unfolding ⟦_⟧F
    iso : (X : Category.Obj FreeMonoidal) → (Y : Category.Obj Discrete)
        → C.Core [ Functor.₀ (FM.⊗ ∘F (F.id ⁂ ι)) (X , Y) , (Functor.₀ (ι ∘F ⟦_⟧F) (X , Y)) ]
    iso unit n = unitorˡ
    iso (a ⊗₀ b) n = iso a (⟦ b ⟧ n) C.∘ (≅.refl _ FM.⊗ᵢ iso b n) C.∘ associator
    iso (Var x) [] = unitorʳ
    iso (Var x) (x₁ ∷ n) = ≅.refl _

    iso' : (X : ObjTerm × List X)
         → C.Core [ (Functor.₀ (ι ∘F ⟦_⟧F) X) , Functor.₀ (FM.⊗ ∘F (F.id ⁂ ι)) X ]
    iso' (X , Y) = ≅.sym _ (iso X Y)

    iso'₁ : (X : ObjTerm × List X)
          → FreeMonoidal [ (Functor.₀ F1 X) , Functor.₀ F2 X ]
    iso'₁ X = _≅_.from (iso' X)

    iso'₁-assoc-ty : Set
    iso'₁-assoc-ty = ∀ {A B d} → iso'₁ (A ⊗₀ B , d) ≈Term FM.α⇐ ∘ (id ⊗₁ iso'₁ (B , d)) ∘ iso'₁ (A , ⟦ B ⟧ d)

    -- It's necessary to hide this type behind a definition, otherwise it won't type check in an opaque block
    iso'₁-assoc : iso'₁-assoc-ty
    iso'₁-assoc = assoc

  P = Product FreeMonoidal Discrete

  module _ where opaque
    unfolding ⟦_⟧F ι iso iso'₁-assoc iso'₁-assoc-ty
    open FMReasoning
    open Mon FreeMonoidal Monoidal-FreeMonoidal
    open import Categories.Morphism.Reasoning FreeMonoidal

    natural-id : ∀ X → iso'₁ X ∘ Functor.F₁ F1 (id , refl) ≈Term Functor.F₁ F2 (id , refl) ∘ iso'₁ X
    natural-id X = begin
      iso'₁ X ∘ id
        ≈⟨ FM.identityʳ ○ ⟺ FM.identityˡ ⟩
      id ∘ iso'₁ X
        ≈⟨ FM.⊗.identity ⟩∘⟨refl ⟨
      id ⊗₁ id ∘ iso'₁ X ∎

    natural-∘ : ∀ {A B C} d (g : HomTerm B C) (f : HomTerm A B)
      → iso'₁ (C , d) ∘ Functor.F₁ F1 (g , refl) FM.≈ Functor.F₁ F2 (g , refl) ∘ iso'₁ (B , d)
      → iso'₁ (B , d) ∘ Functor.F₁ F1 (f , refl) FM.≈ Functor.F₁ F2 (f , refl) ∘ iso'₁ (A , d)
      → iso'₁ (C , d) ∘ Functor.F₁ F1 (g ∘ f , refl) FM.≈ Functor.F₁ F2 (g ∘ f , refl) ∘ iso'₁ (A , d)
    natural-∘ {A} {B} {C} d g f Hg Hf = begin
      iso'₁ (C , d) ∘ Functor.F₁ F1 (g ∘ f , refl)
        ≈⟨ refl⟩∘⟨ Functor.homomorphism F1 {f = f , refl} {g , refl} ⟩
      iso'₁ (C , d) ∘ Functor.F₁ F1 (g , refl) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ FM.assoc ⟨
      (iso'₁ (C , d) ∘ Functor.F₁ F1 (g , refl)) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ Hg ⟩∘⟨refl ⟩
      (Functor.F₁ F2 (g , refl) ∘ iso'₁ (B , d)) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ FM.assoc ⟩
      Functor.F₁ F2 (g , refl) ∘ iso'₁ (B , d) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ refl⟩∘⟨ Hf ⟩
      Functor.F₁ F2 (g , refl) ∘ Functor.F₁ F2 (f , refl) ∘ iso'₁ (A , d)
        ≈⟨ FM.assoc ⟨
      (Functor.F₁ F2 (g , refl) ∘ Functor.F₁ F2 (f , refl)) ∘ iso'₁ (A , d)
        ≈⟨ Functor.homomorphism F2 ⟩∘⟨refl ⟨
      Functor.F₁ F2 (g ∘ f , refl) ∘ iso'₁ (A , d) ∎

    F1-lemma₁ : ∀ {A B d} (f : HomTerm A B) → Functor.F₀ F1 (A , d) ≡ Functor.F₀ F1 (A , d)
    F1-lemma₁ = λ _ → refl

    open import Categories.Category.Discrete

    ι-lemma₂ : ∀ {A} (f : A ≡ A) → Functor.F₁ ι f ≈Term id
    ι-lemma₂ refl = FM.Equiv.refl

    F1-lemma₂ : ∀ {A d} (f : HomTerm A A) → Functor.F₁ F1 (f , refl {x = d}) ≈Term id
    F1-lemma₂ _ = ι-lemma₂ _

    iso-comm-ty : Set
    iso-comm-ty = ∀ {A d₁ d₂} {f : d₁ ≡ d₂}
      → iso'₁ (A , d₂) ∘ ι₁ (⟦ id {A = A} , f ⟧₁) FM.≈ id ⊗₁ ι₁ f ∘ iso'₁ (A , d₁)

    iso-comm : iso-comm-ty
    iso-comm {A} {d} {_} {refl} = begin
      iso'₁ (A , d) ∘ id
        ≈⟨ FM.identityʳ ⟩
      iso'₁ (A , d)
        ≈⟨ FM.identityˡ ⟨
      id ∘ iso'₁ (A , d)
        ≈⟨ FM.⊗.identity ⟩∘⟨refl ⟨
      id ⊗₁ id ∘ iso'₁ (A , d) ∎

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

    natural-⊗ : ∀ {A B C D} d (f : HomTerm A B) (g : HomTerm C D)
      → iso'₁ (B , ⟦ C ⟧ d) ∘ Functor.F₁ F1 (f , refl) FM.≈ Functor.F₁ F2 (f , refl) ∘ iso'₁ (A , ⟦ C ⟧ d)
      → iso'₁ (D , d) ∘ Functor.F₁ F1 (g , refl) FM.≈ Functor.F₁ F2 (g , refl) ∘ iso'₁ (C , d)
      → iso'₁ (B ⊗₀ D , d) ∘ Functor.F₁ F1 (f ⊗₁ g , refl) FM.≈ Functor.F₁ F2 (f ⊗₁ g , refl) ∘ iso'₁ (A ⊗₀ C , d)
    natural-⊗ {A} {B} {C} {D} d f g Hf Hg = begin
      iso'₁ (B ⊗₀ D , d) ∘ ι₁ (⟦ f , ⟦ g , refl ⟧₁ ⟧₁)
        ≈⟨ iso'₁-assoc {A = B} {D} ⟩∘⟨refl ⟩
      (FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d) ∘ iso'₁ (B , ⟦ D ⟧ d)) ∘ ι₁ (⟦ f , ⟦ g , refl ⟧₁ ⟧₁)
        ≈⟨ refl⟩∘⟨ ι-∘ d f g ⟩
      (FM.α⇐ ∘ (id ⊗₁ iso'₁ (D , d) ∘ iso'₁ (B , ⟦ D ⟧ d))) ∘ (ι₁ (⟦ id {A = B} , ⟦ g , refl ⟧₁ ⟧₁) ∘ ι₁ (⟦ f , refl ⟧₁))
        ≈⟨ ⟺ FM.assoc ⟩
      ((FM.α⇐ ∘ (id ⊗₁ iso'₁ (D , d) ∘ iso'₁ (B , ⟦ D ⟧ d))) ∘ ι₁ (⟦ id {A = B} , ⟦ g , refl ⟧₁ ⟧₁)) ∘ ι₁ (⟦ f , refl ⟧₁)
        ≈⟨ FM.assoc ⟩∘⟨refl ⟩
      (FM.α⇐ ∘ (id ⊗₁ iso'₁ (D , d) ∘ iso'₁ (B , ⟦ D ⟧ d)) ∘ ι₁ (⟦ id {A = B} , ⟦ g , refl ⟧₁ ⟧₁)) ∘ ι₁ (⟦ f , refl ⟧₁)
        ≈⟨ (refl⟩∘⟨ FM.assoc) ⟩∘⟨refl ⟩
      (FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d) ∘ (iso'₁ (B , ⟦ D ⟧ d) ∘ ι₁ (⟦ id {A = B} , ⟦ g , refl ⟧₁ ⟧₁))) ∘ ι₁ (⟦ f , refl ⟧₁)
        ≈⟨ ⟺ FM.assoc ⟩∘⟨refl ⟩
      ((FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d)) ∘ (iso'₁ (B , ⟦ D ⟧ d) ∘ ι₁ (⟦ id {A = B} , ⟦ g , refl ⟧₁ ⟧₁))) ∘ ι₁ (⟦ f , refl ⟧₁)
        ≈⟨ FM.assoc ⟩
      (FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d)) ∘ (iso'₁ (B , ⟦ D ⟧ d) ∘ ι₁ (⟦ id {A = B} , ⟦ g , refl ⟧₁ ⟧₁)) ∘ ι₁ (⟦ f , refl ⟧₁)
        ≈⟨ refl⟩∘⟨ iso-comm ⟩∘⟨refl ⟩
      (FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d)) ∘ ((id ⊗₁ ι₁ (⟦ g , refl ⟧₁) ∘ iso'₁ (B , ⟦ C ⟧ d)) ∘ ι₁ (⟦ f , refl ⟧₁))
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      (FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d)) ∘ (id ⊗₁ ι₁ (⟦ g , refl ⟧₁) ∘ (iso'₁ (B , ⟦ C ⟧ d) ∘ ι₁ (⟦ f , refl ⟧₁)))
        ≈⟨ ⟺ FM.assoc ⟩
      ((FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d)) ∘ id ⊗₁ ι₁ (⟦ g , refl ⟧₁)) ∘ (iso'₁ (B , ⟦ C ⟧ d) ∘ ι₁ (⟦ f , refl ⟧₁))
        ≈⟨ FM.assoc ⟩∘⟨refl ⟩
      (FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d) ∘ id ⊗₁ ι₁ (⟦ g , refl ⟧₁)) ∘ (iso'₁ (B , ⟦ C ⟧ d) ∘ ι₁ (⟦ f , refl ⟧₁))
        ≈⟨ refl⟩∘⟨ Hf ⟩
      (FM.α⇐ ∘ id ⊗₁ iso'₁ (D , d) ∘ id ⊗₁ ι₁ (⟦ g , refl ⟧₁)) ∘ (f ⊗₁ id ∘ iso'₁ (A , ⟦ C ⟧ d))
        ≈⟨ FM.assoc ⟩
      FM.α⇐ ∘ (id ⊗₁ iso'₁ (D , d) ∘ id ⊗₁ ι₁ (⟦ g , refl ⟧₁)) ∘ (f ⊗₁ id ∘ iso'₁ (A , ⟦ C ⟧ d))
        ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩∘⟨refl ⟩
      FM.α⇐ ∘ (id ⊗₁ (iso'₁ (D , d) ∘ ι₁ (⟦ g , refl ⟧₁))) ∘ (f ⊗₁ id ∘ iso'₁ (A , ⟦ C ⟧ d))
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ Hg ⟩∘⟨refl ⟩
      FM.α⇐ ∘ (id ⊗₁ (g ⊗₁ id ∘ iso'₁ (C , d))) ∘ (f ⊗₁ id ∘ iso'₁ (A , ⟦ C ⟧ d))
        ≈⟨ refl⟩∘⟨ ⟺ FM.assoc ⟩
      FM.α⇐ ∘ (id ⊗₁ (g ⊗₁ id ∘ iso'₁ (C , d)) ∘ f ⊗₁ id) ∘ iso'₁ (A , ⟦ C ⟧ d)
        ≈⟨ refl⟩∘⟨ serialize₂₁ ⟩∘⟨refl ⟨
      FM.α⇐ ∘ f ⊗₁ (g ⊗₁ id ∘ iso'₁ (C , d)) ∘ iso'₁ (A , ⟦ C ⟧ d)
        ≈⟨ refl⟩∘⟨ split₂ʳ ⟩∘⟨refl ⟩
      FM.α⇐ ∘ ((f ⊗₁ (g ⊗₁ id) ∘ id ⊗₁ iso'₁ (C , d)) ∘ iso'₁ (A , ⟦ C ⟧ d))
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      FM.α⇐ ∘ (f ⊗₁ (g ⊗₁ id) ∘ (id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (A , ⟦ C ⟧ d)))
        ≈⟨ ⟺ FM.assoc ⟩
      (FM.α⇐ ∘ f ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (A , ⟦ C ⟧ d))
        ≈⟨ FM.assoc-commute-to ⟩∘⟨refl ⟩
      ((f ⊗₁ g) ⊗₁ id ∘ FM.α⇐) ∘ id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (A , ⟦ C ⟧ d)
        ≈⟨ FM.assoc ⟩
      (f ⊗₁ g) ⊗₁ id ∘ (FM.α⇐ ∘ id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (A , ⟦ C ⟧ d))
        ≈⟨ refl⟩∘⟨ iso'₁-assoc {A = A} {C} ⟨
      (f ⊗₁ g) ⊗₁ id ∘ iso'₁ (A ⊗₀ C , d) ∎

    natural-λ⇒ : ∀ {A d}
               → iso'₁ (A , d) ∘ Functor.F₁ ι (Functor.F₁ ⟦_⟧F (λ⇒ , refl))
            FM.≈ λ⇒ ⊗₁ Functor.F₁ ι refl ∘ iso'₁ (unit ⊗₀ A , d)
    natural-λ⇒ {A} {d} = begin
      iso'₁ (A , d) ∘ id
        ≈⟨ id-comm ⟩
      id ∘ iso'₁ (A , d)
        ≈⟨ FM.⊗.identity ⟩∘⟨refl ⟨
      id ⊗₁ id ∘ iso'₁ (A , d)
        ≈⟨ ⟺ λ⇒∘λ⇐≈id ⟩⊗⟨ ⟺ idˡ ⟩∘⟨refl ⟩
      (λ⇒ ∘ λ⇐) ⊗₁ (id ∘ id) ∘ iso'₁ (A , d)
        ≈⟨ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      (λ⇒ ⊗₁ id ∘ λ⇐ ⊗₁ id) ∘ iso'₁ (A , d)
        ≈⟨ assoc ⟩
      λ⇒ ⊗₁ id ∘ λ⇐ ⊗₁ id ∘ iso'₁ (A , d)
        ≈⟨ refl⟩∘⟨ λ-lemma ⟨
      λ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ iso'₁ (A , d) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ ⟺ assoc ⟩
      λ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ iso'₁ (A , d)) ∘ λ⇐ ∎

    natural-λ⇐ : ∀ {A d}
               → iso'₁ (unit ⊗₀ A , d) ∘ Functor.F₁ ι (Functor.F₁ ⟦_⟧F (λ⇐ , refl))
            FM.≈ λ⇐ ⊗₁ Functor.F₁ ι refl ∘ iso'₁ (A , d)
    natural-λ⇐ {A} {d} = begin
      ((α⇐ ∘ id ⊗₁ iso'₁ (A , d)) ∘ λ⇐) ∘ id
        ≈⟨ idʳ ○ assoc ⟩
      α⇐ ∘ id ⊗₁ iso'₁ (A , d) ∘ λ⇐
        ≈⟨ λ-lemma ⟩
      λ⇐ ⊗₁ id ∘ iso'₁ (A , d) ∎

    natural-ρ⇒ : ∀ {A d}
               → iso'₁ (A , d) ∘ Functor.F₁ ι (Functor.F₁ ⟦_⟧F (ρ⇒ , refl))
            FM.≈ ρ⇒ ⊗₁ Functor.F₁ ι refl ∘ iso'₁ (A ⊗₀ unit , d)
    natural-ρ⇒ {A} {d} = begin
      iso'₁ (A , d) ∘ id
        ≈⟨ id-comm ⟩
      id ∘ iso'₁ (A , d)
        ≈⟨ FM.⊗.identity ⟩∘⟨refl ⟨
      id ⊗₁ id ∘ iso'₁ (A , d)
        ≈⟨ ⟺ ρ⇒∘ρ⇐≈id ⟩⊗⟨ ⟺ idˡ ⟩∘⟨refl ⟩
      (ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ id) ∘ iso'₁ (A , d)
        ≈⟨ FM.⊗.homomorphism ⟩∘⟨refl ⟩
      (ρ⇒ ⊗₁ id ∘ ρ⇐ ⊗₁ id) ∘ iso'₁ (A , d)
        ≈⟨ (refl⟩∘⟨ ⟺ FM.triangle-inv) ⟩∘⟨refl ⟩
      (ρ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ λ⇐)) ∘ iso'₁ (A , d)
        ≈⟨ assoc ⟩
      ρ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ λ⇐) ∘ iso'₁ (A , d) ∎

    natural-ρ⇐ : ∀ {A d}
               → iso'₁ (A ⊗₀ unit , d) ∘ Functor.F₁ ι (Functor.F₁ ⟦_⟧F (ρ⇐ , refl))
            FM.≈ ρ⇐ ⊗₁ Functor.F₁ ι refl ∘ iso'₁ (A , d)
    natural-ρ⇐ {A} {d} = begin
      ((α⇐ ∘ id ⊗₁ λ⇐) ∘ iso'₁ (A , d)) ∘ id
        ≈⟨ idʳ ⟩
      (α⇐ ∘ id ⊗₁ λ⇐) ∘ iso'₁ (A , d)
        ≈⟨ FM.triangle-inv ⟩∘⟨refl ⟩
      ρ⇐ ⊗₁ id ∘ iso'₁ (A , d) ∎

    natural-α⇒ : ∀ {A B C d}
               → iso'₁ (A ⊗₀ B ⊗₀ C , d) ∘ Functor.F₁ ι (Functor.F₁ ⟦_⟧F (α⇒ , refl))
            FM.≈ α⇒ ⊗₁ Functor.F₁ ι refl ∘ iso'₁ ((A ⊗₀ B) ⊗₀ C , d)
    natural-α⇒ {A} {B} {C} {d} = begin
      ((α⇐ ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))) ∘ id
        ≈⟨ idʳ ⟩
      (α⇐ ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ α-lemma ⟩∘⟨refl ⟩
      (α⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ (α⇐ ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ assoc ○ refl⟩∘⟨ assoc ⟩
      α⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ (α⇐ ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∎

    natural-α⇐ : ∀ {A B C d}
               → iso'₁ ((A ⊗₀ B) ⊗₀ C , d) ∘ Functor.F₁ ι (Functor.F₁ ⟦_⟧F (α⇐ , refl))
            FM.≈ α⇐ ⊗₁ Functor.F₁ ι refl ∘ iso'₁ (A ⊗₀ B ⊗₀ C , d)
    natural-α⇐ {A} {B} {C} {d} = begin
      ((α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ (α⇐ ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))) ∘ id
        ≈⟨ idʳ ⟩
      (α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ (α⇐ ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ ⟺ assoc ⟩
      ((α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ α⇐ ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ ⟺ assoc²'' ⟩∘⟨refl ⟩
      (α⇐ ∘ (id ⊗₁ iso'₁ (C , d) ∘ α⇐) ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ (refl⟩∘⟨ (⟺ M.⊗.identity ⟩⊗⟨refl ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (α⇐ ∘ ((id ⊗₁ id) ⊗₁ iso'₁ (C , d) ∘ α⇐) ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ (refl⟩∘⟨ ⟺ M.assoc-commute-to ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (α⇐ ∘ (α⇐ ∘ id ⊗₁ id ⊗₁ iso'₁ (C , d)) ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ assoc²'' ⟩∘⟨refl ⟩
      ((α⇐ ∘ α⇐) ∘ id ⊗₁ id ⊗₁ iso'₁ (C , d) ∘ id ⊗₁ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ (refl⟩∘⟨ ⟺ ((_ M.⊗-) .Functor.homomorphism)) ⟩∘⟨refl ⟩
      ((α⇐ ∘ α⇐) ∘ id ⊗₁ (id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ ⟺ pentagon' ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐) ∘ id ⊗₁ (id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ assoc²' ⟩∘⟨refl ⟩
      (α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐ ∘ id ⊗₁ (id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ ⟺ ((_ M.⊗-) .Functor.homomorphism)) ⟩∘⟨refl ⟩
      (α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ assoc²' ⟩
      α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (B , ⟦ C ⟧ d)) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ refl⟩∘⟨ ⟺ assoc ⟩
      α⇐ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (α⇐ ∘ id ⊗₁ iso'₁ (C , d) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ refl⟩⊗⟨ ⟺ assoc) ⟩∘⟨refl ⟩
      α⇐ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ iso'₁ (C , d)) ∘ iso'₁ (B , ⟦ C ⟧ d))) ∘ iso'₁ (A , ⟦ B ⟧ (⟦ C ⟧ d)) ∎

  natural₁ : ∀ d → Natural (appʳ F1 d) (appʳ F2 d) (λ c → iso'₁ (c , d))
  natural₁ d id = natural-id _
  natural₁ d (g ∘ f) = natural-∘ _ g f (natural₁ d g) (natural₁ d f)
  natural₁ d (_⊗₁_ {A} {B} {C} {D} f g) = natural-⊗ d f g (natural₁ (⟦ C ⟧ d) f) (natural₁ d g)
  natural₁ d λ⇒ = natural-λ⇒
  natural₁ d λ⇐ = natural-λ⇐
  natural₁ d ρ⇒ = natural-ρ⇒
  natural₁ d ρ⇐ = natural-ρ⇐
  natural₁ d α⇒ = natural-α⇒
  natural₁ d α⇐ = natural-α⇐

  opaque
    unfolding iso'₁
    ⟦⟧≅⊗ : NaturalIsomorphism (ι ∘F ⟦_⟧F) (FM.⊗ ∘F (F.id ⁂ ι))
    ⟦⟧≅⊗ = pointwise-iso iso' natural
      where
        natural : ∀ {X Y} → (f : P [ X , Y ])
                → FreeMonoidal [ iso'₁ Y ∘ Functor.₁ (ι ∘F ⟦_⟧F) f ≈ Functor.₁ (FM.⊗ ∘F (F.id ⁂ ι)) f ∘ iso'₁ X ]
        natural = natural-components (ι ∘F ⟦_⟧F) (FM.⊗ ∘F (F.id ⁂ ι)) iso'₁ natural₁
          (λ c → Discrete-NaturalD {F = appˡ (ι ∘F ⟦_⟧F) c} {appˡ (FM.⊗ ∘F (F.id ⁂ ι)) c} (λ d → iso'₁ (c , d)))

  open import Categories.Functor.Construction.Constant
  open import Categories.Morphism.Properties
  open import Categories.Category.Product.Properties

  import Categories.Morphism.Reasoning as MR
  import Relation.Binary.Reasoning.Setoid as SetoidR

  -×_ : {C D : Category 0ℓ 0ℓ 0ℓ} → D .Category.Obj → Functor C (Product C D)
  -×_ {C} {D} d = F.id ※ const d

  ⁂-× : {C D E : Category 0ℓ 0ℓ 0ℓ} → (G : Functor D E) → (d : D .Category.Obj)
      → NaturalIsomorphism ((F.id {C = C} ⁂ G) ∘F -× d) (-× Functor.F₀ G d)
  ⁂-× G d = begin
    (F.id ⁂ G) ∘F -× d ≈⟨ ⁂-※ _ _ F.id G ⟩
    ((F.id ∘F F.id) ※ (G ∘F const d)) ≈⟨ NI.unitorˡ ※ⁿⁱ NI.refl ⟩
    (F.id ※ (G ∘F const d)) ≈⟨ NI.refl ※ⁿⁱ ∘F-const d G ⟩
    (F.id ※ (const (Functor.F₀ G d))) ≈⟨ NI.refl ⟩
    -× Functor.F₀ G d ∎
    where open SetoidR (Functor-NI-setoid _ _)

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

import Data.Vec as V
open import Data.Fin using (Fin)

module Solver (C : MonoidalCategory 0ℓ 0ℓ 0ℓ)
              {n} (vars : V.Vec (C .MonoidalCategory.Obj) n) where
  open MonoidalCategory
  open FreeMonoidal (Fin n) public
  open CoherenceThm (Fin n) hiding (⟦_⟧₁)
  open Free {C = C .U} {C .monoidal} (V.lookup vars)

  opaque
    solveM : ∀ {X Y} → (f g : FreeMonoidal [ X , Y ]) → (C .U) [ ⟦ f ⟧₁ ≈ ⟦ g ⟧₁ ]
    solveM f g = Functor.F-resp-≈ freeFunctor (all-Comm f g)
  {-# INJECTIVE_FOR_INFERENCE solveM #-}
