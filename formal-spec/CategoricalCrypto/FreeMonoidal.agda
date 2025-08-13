{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.FreeMonoidal where

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

module FreeMonoidal (X : Set) where
  infix  4 _≈Term_
  infixr 9 _∘_
  infixr 10 _⊗₀_ _⊗₁_

  data ObjTerm : Set where
    unit : ObjTerm
    _⊗₀_ : ObjTerm → ObjTerm → ObjTerm
    Var : X → ObjTerm

  private variable A B C D E F : ObjTerm

  data HomTerm : ObjTerm → ObjTerm → Set where
    id : HomTerm A A
    _∘_ : HomTerm B C → HomTerm A B → HomTerm A C
    _⊗₁_ : HomTerm A B → HomTerm C D → HomTerm (A ⊗₀ C) (B ⊗₀ D)
    λ⇒ : HomTerm (unit ⊗₀ A) A
    λ⇐ : HomTerm A (unit ⊗₀ A)
    ρ⇒ : HomTerm (A ⊗₀ unit) A
    ρ⇐ : HomTerm A (A ⊗₀ unit)
    α⇒ : HomTerm ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
    α⇐ : HomTerm (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)

  data _≈Term_ : HomTerm A B → HomTerm A B → Set where
    idˡ : ∀ {f : HomTerm A B} → id ∘ f ≈Term f
    idʳ : ∀ {f : HomTerm A B} → f ∘ id ≈Term f
    assoc : ∀ {f : HomTerm A B} {g : HomTerm B C} {h : HomTerm C D}
          → (h ∘ g) ∘ f ≈Term h ∘ (g ∘ f)
    ∘-resp-≈ : ∀ {f h : HomTerm B C} {g i : HomTerm A B}
             → f ≈Term h → g ≈Term i → f ∘ g ≈Term h ∘ i
    ≈-Term-refl : ∀ {f : HomTerm A B} → f ≈Term f
    ≈-Term-sym : ∀ {f g : HomTerm A B} → f ≈Term g → g ≈Term f
    ≈-Term-trans : ∀ {f g h : HomTerm A B} → f ≈Term g → g ≈Term h → f ≈Term h
    id⊗id≈id : id ⊗₁ id ≈Term id {A ⊗₀ B}
    ⊗-resp-≈ : ∀ {f f' : HomTerm A B} {g g' : HomTerm C D}
             → f ≈Term f' → g ≈Term g' → f ⊗₁ g ≈Term f' ⊗₁ g'
    ⊗-∘-dist : {f : HomTerm A B} {g : HomTerm B C} {f' : HomTerm D E} {g' : HomTerm E F}
             → (g ∘ f) ⊗₁ (g' ∘ f') ≈Term g ⊗₁ g' ∘ f ⊗₁ f'
    λ⇐∘λ⇒≈id : λ⇐ ∘ (λ⇒ {A}) ≈Term id
    λ⇒∘λ⇐≈id : λ⇒ ∘ (λ⇐ {A}) ≈Term id
    ρ⇐∘ρ⇒≈id : ρ⇐ ∘ (ρ⇒ {A}) ≈Term id
    ρ⇒∘ρ⇐≈id : ρ⇒ ∘ (ρ⇐ {A}) ≈Term id
    α⇐∘α⇒≈id : α⇐ ∘ (α⇒ {A} {B} {C}) ≈Term id
    α⇒∘α⇐≈id : α⇒ ∘ (α⇐ {A} {B} {C}) ≈Term id
    λ⇒∘id⊗f≈f∘λ⇒ : {f : HomTerm A B} → λ⇒ ∘ id ⊗₁ f ≈Term f ∘ λ⇒
    ρ⇒∘f⊗id≈f∘ρ⇒ : {f : HomTerm A B} → ρ⇒ ∘ f ⊗₁ id ≈Term f ∘ ρ⇒
    α-comm : {f : HomTerm A B} {g : HomTerm C D} {h : HomTerm E F}
           → α⇒ ∘ (f ⊗₁ g) ⊗₁ h ≈Term f ⊗₁ g ⊗₁ h ∘ α⇒
    triangle : id ⊗₁ λ⇒ ∘ (α⇒ {A} {unit} {B}) ≈Term ρ⇒ ⊗₁ id
    pentagon : id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id ≈Term α⇒ ∘ (α⇒ {A ⊗₀ B} {C} {D})

  FreeMonoidal : Category ℓ0 ℓ0 ℓ0
  FreeMonoidal = categoryHelper record
    { Obj       = ObjTerm
    ; _⇒_       = HomTerm
    ; _≈_       = _≈Term_
    ; id        = id
    ; _∘_       = _∘_
    ; assoc     = assoc
    ; identityˡ = idˡ
    ; identityʳ = idʳ
    ; equiv     = record { refl = ≈-Term-refl ; sym = ≈-Term-sym ; trans = ≈-Term-trans }
    ; ∘-resp-≈  = ∘-resp-≈
    }

  Monoidal-FreeMonoidal : Monoidal FreeMonoidal
  Monoidal-FreeMonoidal = monoidalHelper FreeMonoidal record
    { ⊗               = record
        { F₀           = uncurry _⊗₀_
        ; F₁           = uncurry _⊗₁_
        ; identity     = id⊗id≈id
        ; homomorphism = ⊗-∘-dist
        ; F-resp-≈     = uncurry ⊗-resp-≈
        }
    ; unit            = unit
    ; unitorˡ         = record { from = λ⇒ ; to = λ⇐ ; iso = record { isoˡ = λ⇐∘λ⇒≈id ; isoʳ = λ⇒∘λ⇐≈id } }
    ; unitorʳ         = record { from = ρ⇒ ; to = ρ⇐ ; iso = record { isoˡ = ρ⇐∘ρ⇒≈id ; isoʳ = ρ⇒∘ρ⇐≈id } }
    ; associator      = record { from = α⇒ ; to = α⇐ ; iso = record { isoˡ = α⇐∘α⇒≈id ; isoʳ = α⇒∘α⇐≈id } }
    ; unitorˡ-commute = λ⇒∘id⊗f≈f∘λ⇒
    ; unitorʳ-commute = ρ⇒∘f⊗id≈f∘ρ⇒
    ; assoc-commute   = α-comm
    ; triangle        = triangle
    ; pentagon        = pentagon
    }

  open Commutation FreeMonoidal

module Free {X : Set} {C : Category 0ℓ 0ℓ 0ℓ} {Monoidal-C : Monoidal C} (value : X → C .Category.Obj) where
  open Category
  open FreeMonoidal X

  private
    module C where
      open Category C public
      open Monoidal Monoidal-C public
      open import Categories.Category.Monoidal.Utilities Monoidal-C
      open Shorthands public

    module ⊗ where
      open Functor C.⊗ public

  CM FreeMonoidalM : MonoidalCategory 0ℓ 0ℓ 0ℓ
  CM = record { U = C ; monoidal = Monoidal-C }
  FreeMonoidalM = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

  ⟦_⟧₀ : FreeMonoidal .Obj → C .Obj
  ⟦ unit ⟧₀ = C.unit
  ⟦ x ⊗₀ x₁ ⟧₀ = ⟦ x ⟧₀ C.⊗₀ ⟦ x₁ ⟧₀
  ⟦ Var x ⟧₀ = value x

  ⟦_⟧₁ : ∀ {A B} → FreeMonoidal [ A , B ] → C [ ⟦ A ⟧₀ , ⟦ B ⟧₀ ]
  ⟦ id ⟧₁ = C.id
  ⟦ f ∘ f₁ ⟧₁ = ⟦ f ⟧₁ C.∘ ⟦ f₁ ⟧₁
  ⟦ f ⊗₁ f₁ ⟧₁ = ⟦ f ⟧₁ C.⊗₁ ⟦ f₁ ⟧₁
  ⟦ λ⇒ ⟧₁ = C.λ⇒
  ⟦ λ⇐ ⟧₁ = C.λ⇐
  ⟦ ρ⇒ ⟧₁ = C.ρ⇒
  ⟦ ρ⇐ ⟧₁ = C.ρ⇐
  ⟦ α⇒ ⟧₁ = C.α⇒
  ⟦ α⇐ ⟧₁ = C.α⇐

  ⟦⟧-resp-≈ : ∀ {A B} {f g : FreeMonoidal [ A , B ]} → FreeMonoidal [ f ≈ g ] → C [ ⟦ f ⟧₁ ≈ ⟦ g ⟧₁ ]
  ⟦⟧-resp-≈ idˡ                 = C.identityˡ
  ⟦⟧-resp-≈ idʳ                 = C.identityʳ
  ⟦⟧-resp-≈ assoc               = C.assoc
  ⟦⟧-resp-≈ (∘-resp-≈ h h')     = C.∘-resp-≈ (⟦⟧-resp-≈ h) (⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ ≈-Term-refl         = C.Equiv.refl
  ⟦⟧-resp-≈ (≈-Term-sym h)      = C.Equiv.sym (⟦⟧-resp-≈ h)
  ⟦⟧-resp-≈ (≈-Term-trans h h') = C.Equiv.trans (⟦⟧-resp-≈ h) (⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ id⊗id≈id            = ⊗.identity
  ⟦⟧-resp-≈ (⊗-resp-≈ h h')     = ⊗.F-resp-≈ (⟦⟧-resp-≈ h , ⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ ⊗-∘-dist            = ⊗.homomorphism
  ⟦⟧-resp-≈ λ⇐∘λ⇒≈id            = C.unitorˡ.isoˡ
  ⟦⟧-resp-≈ λ⇒∘λ⇐≈id            = C.unitorˡ.isoʳ
  ⟦⟧-resp-≈ ρ⇐∘ρ⇒≈id            = C.unitorʳ.isoˡ
  ⟦⟧-resp-≈ ρ⇒∘ρ⇐≈id            = C.unitorʳ.isoʳ
  ⟦⟧-resp-≈ α⇐∘α⇒≈id            = C.associator.isoˡ
  ⟦⟧-resp-≈ α⇒∘α⇐≈id            = C.associator.isoʳ
  ⟦⟧-resp-≈ λ⇒∘id⊗f≈f∘λ⇒        = C.unitorˡ-commute-from
  ⟦⟧-resp-≈ ρ⇒∘f⊗id≈f∘ρ⇒        = C.unitorʳ-commute-from
  ⟦⟧-resp-≈ α-comm              = C.assoc-commute-from
  ⟦⟧-resp-≈ triangle            = C.triangle
  ⟦⟧-resp-≈ pentagon            = C.pentagon

  freeFunctor : Functor FreeMonoidal C
  freeFunctor = record
    { F₀ = ⟦_⟧₀
    ; F₁ = ⟦_⟧₁
    ; identity = begin C.id ∎
    ; homomorphism = λ {_} {_} {_} {f} {g} → begin ⟦ FreeMonoidal [ g ∘ f ] ⟧₁ ∎
    ; F-resp-≈ = ⟦⟧-resp-≈
    }
    where open Category.HomReasoning C

  open import Categories.Functor.Monoidal

  isMonoidal-freeFunctor : IsMonoidalFunctor FreeMonoidalM CM freeFunctor
  isMonoidal-freeFunctor = record
    { ε = C.id
    ; ⊗-homo = ntHelper record
      { η       = λ _ → C.id
      ; commute = λ _ → C.identityˡ ○ ⟺ C.identityʳ
      }
    ; associativity = begin
      C.α⇒ C.∘ C.id C.∘ C.id C.⊗₁ C.id ≈⟨ refl⟩∘⟨ (C.identityˡ ○ C.⊗.identity) ⟩
      C.α⇒ C.∘ C.id ≈⟨ C.identityʳ ⟩
      C.α⇒ ≈⟨ C.identityˡ ⟨
      C.id C.∘ C.α⇒ ≈⟨ refl⟩∘⟨ C.identityˡ ⟨
      C.id C.∘ C.id C.∘ C.α⇒ ≈⟨ refl⟩∘⟨ C.⊗.identity ⟩∘⟨refl ⟨
      C.id C.∘ C.id C.⊗₁ C.id C.∘ C.α⇒ ∎
    ; unitaryˡ = begin
      C.λ⇒ C.∘ C.id C.∘ C.id C.⊗₁ C.id
        ≈⟨ refl⟩∘⟨ (C.identityˡ ○ C.⊗.identity) ⟩
      C.λ⇒ C.∘ C.id
        ≈⟨ C.identityʳ ⟩
      C.λ⇒ ∎
    ; unitaryʳ = begin
      C.ρ⇒ C.∘ C.id C.∘ C.id C.⊗₁ C.id
        ≈⟨ refl⟩∘⟨ (C.identityˡ ○ C.⊗.identity) ⟩
      C.ρ⇒ C.∘ C.id
        ≈⟨ C.identityʳ ⟩
      C.ρ⇒ ∎
    }
    where open Category.HomReasoning C
