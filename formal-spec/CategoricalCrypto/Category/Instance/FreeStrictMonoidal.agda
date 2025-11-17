--{-# OPTIONS --safe #-}
module CategoricalCrypto.Category.Instance.FreeStrictMonoidal where

--------------------------------------------------------------------------------
-- Various free strict monoidal categories. The intended interface to this
-- file is further below, the `FreeMonoidalData` type and
-- `FreeMonoidal` module.
--------------------------------------------------------------------------------

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Properties
open import Categories.Category.Monoidal.Symmetric
import Categories.Morphism as Morphism
open import Categories.Functor hiding (id)
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
import Categories.Category.Construction.Core as Core
import Categories.Morphism.Reasoning
open import Categories.Functor.Bifunctor
import Categories.Category.Monoidal.Reasoning as MonReasoning

open import Function hiding (id; _∘_)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as ℕ
open import Data.List
open import Data.List.Properties
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary hiding (Symmetric)
open import Relation.Nullary
open import Data.Sum

open import CategoricalCrypto.FreeMonoidal using (Variant; _≤_; FreeMonoidalData; Symm)

module Het where
  import Relation.Binary.HeterogeneousEquality as H

  ≡-subst₂-removable : ∀ {A B : Set} (_∼_ : A → B → Set) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : x ∼ u) →
                      subst₂ _∼_ eq₁ eq₂ z H.≅ z
  ≡-subst₂-removable _ refl refl z = H.refl
  open H public

open import CategoricalCrypto.NaturalTransformationHelper

module FreeMonoidalHelper (v : Variant) (X : Set) where
  infixr 10 _⊗₀_

  opaque

    ObjTerm : Set
    ObjTerm = List X

    private variable A A' A₁ A₂ B B' B₁ B₂ C C' C₁ C₂ D E F : ObjTerm

    _⊗₀_ : ObjTerm → ObjTerm → ObjTerm
    _⊗₀_ = _++_
    ⊗₀-assoc : ∀ {A} {B} {C} → (A ⊗₀ B) ⊗₀ C ≡ A ⊗₀ B ⊗₀ C
    ⊗₀-assoc {A} {B} {C} = ++-assoc A B C

    unit : ObjTerm
    unit = []

    Var : X → ObjTerm
    Var x = Data.List.[ x ]

    A⊗₀unit≡A : ∀ {A} → A ⊗₀ unit ≡ A
    A⊗₀unit≡A = ++-identityʳ _

    unit⊗₀A≡A : ∀ {A} → unit ⊗₀ A ≡ A
    unit⊗₀A≡A = ++-identityˡ _

  module Mor (mor : ObjTerm → ObjTerm → Set) where
    infix  4 _≈Term_
    infixr 9 _∘_
    infixr 10 _⊗₁_

    data HomTerm : ObjTerm → ObjTerm → Set where
      var : mor A B → HomTerm A B
      id : HomTerm A A
      _∘_ : HomTerm B C → HomTerm A B → HomTerm A C
      _⊗₁_ : HomTerm A B → HomTerm C D → HomTerm (A ⊗₀ C) (B ⊗₀ D)
      λ⇒ : HomTerm (unit ⊗₀ A) A
      λ⇐ : HomTerm A (unit ⊗₀ A)
      ρ⇒ : HomTerm (A ⊗₀ unit) A
      ρ⇐ : HomTerm A (A ⊗₀ unit)
      α⇒ : HomTerm ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
      α⇐ : HomTerm (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
      σ : ⦃ Symm ≤ v ⦄ → HomTerm (A ⊗₀ B) (B ⊗₀ A)

    private variable f f' g g' h i : HomTerm A B

    data _≈Term_ : HomTerm A B → HomTerm A B → Set where
      idˡ : id ∘ f ≈Term f
      idʳ : f ∘ id ≈Term f
      assoc : (h ∘ g) ∘ f ≈Term h ∘ (g ∘ f)
      ∘-resp-≈ : f ≈Term h → g ≈Term i → f ∘ g ≈Term h ∘ i
      ≈-Term-refl : f ≈Term f
      ≈-Term-sym : f ≈Term g → g ≈Term f
      ≈-Term-trans : f ≈Term g → g ≈Term h → f ≈Term h
      id⊗id≈id : id ⊗₁ id ≈Term id {A ⊗₀ B}
      ⊗-resp-≈ : f ≈Term f' → g ≈Term g' → f ⊗₁ g ≈Term f' ⊗₁ g'
      ⊗-∘-dist : (g ∘ f) ⊗₁ (g' ∘ f') ≈Term g ⊗₁ g' ∘ f ⊗₁ f'
      λ⇐∘λ⇒≈id : λ⇐ ∘ (λ⇒ {A}) ≈Term id
      λ⇒∘λ⇐≈id : λ⇒ ∘ (λ⇐ {A}) ≈Term id
      ρ⇐∘ρ⇒≈id : ρ⇐ ∘ (ρ⇒ {A}) ≈Term id
      ρ⇒∘ρ⇐≈id : ρ⇒ ∘ (ρ⇐ {A}) ≈Term id
      α⇐∘α⇒≈id : α⇐ ∘ (α⇒ {A} {B} {C}) ≈Term id
      α⇒∘α⇐≈id : α⇒ ∘ (α⇐ {A} {B} {C}) ≈Term id
      λ⇒∘id⊗f≈f∘λ⇒ : λ⇒ ∘ id ⊗₁ f ≈Term f ∘ λ⇒
      ρ⇒∘f⊗id≈f∘ρ⇒ : ρ⇒ ∘ f ⊗₁ id ≈Term f ∘ ρ⇒
      α-comm : α⇒ ∘ (f ⊗₁ g) ⊗₁ h ≈Term f ⊗₁ g ⊗₁ h ∘ α⇒
      triangle : id ⊗₁ λ⇒ ∘ (α⇒ {A} {unit} {B}) ≈Term ρ⇒ ⊗₁ id
      pentagon : id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id ≈Term α⇒ ∘ (α⇒ {A ⊗₀ B} {C} {D})
      σ∘σ≈id : ⦃ _ : Symm ≤ v ⦄ → σ ∘ σ ≈Term id {A ⊗₀ B}
      σ∘[f⊗g]≈[g⊗f]∘σ : ⦃ _ : Symm ≤ v ⦄ {f : HomTerm A B} {g : HomTerm C D} → σ ∘ (f ⊗₁ g) ≈Term (g ⊗₁ f) ∘ σ
      hexagon : ⦃ _ : Symm ≤ v ⦄ → id ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ id ≈Term α⇒ ∘ σ ∘ α⇒ {A} {B} {C}
      -- TODO: add strict equalities

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

    module _ ⦃ _ : Symm ≤ v ⦄ where
      open import Categories.Morphism FreeMonoidal

      σ-iso : A ⊗₀ B ≅ B ⊗₀ A
      σ-iso = record { from = σ ; to = σ ; iso = record { isoˡ = σ∘σ≈id ; isoʳ = σ∘σ≈id } }

      Symmetric-Monoidal : Symmetric Monoidal-FreeMonoidal
      Symmetric-Monoidal = symmetricHelper Monoidal-FreeMonoidal record
        { braiding    = pointwise-iso (λ _ → σ-iso) λ where (f , g) → σ∘[f⊗g]≈[g⊗f]∘σ
        ; commutative = σ∘σ≈id
        ; hexagon     = hexagon
        }


    -- [σ, id ⊗ f ⊗ id, σ, id ⊗ g ⊗ id, σ, ..., σ]


    open import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix
    open import Data.List.Relation.Binary.Prefix.Homogeneous.Properties as Properties
    open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise)


    infix 4 _≼_
    opaque
      unfolding ObjTerm
      _≼_ : ObjTerm → ObjTerm → Set
      _≼_ = Prefix.Prefix _≡_

      ≼-IsPartialOrder-ty : Set
      ≼-IsPartialOrder-ty = IsPartialOrder (Pointwise _≡_) _≼_
      ≼-IsPartialOrder' : ≼-IsPartialOrder-ty
      ≼-IsPartialOrder' = Properties.isPartialOrder ≡.isPartialOrder

    postulate X≼X⊗Y : ∀ {X Y} → X ≼ X ⊗₀ Y
              prefix-remainder : ∀ {X Y} → X ≼ Y → ∃[ Z ] X ⊗₀ Z ≡ Y
              ⊗-cancelˡ : ∀ X {Y Z} → X ⊗₀ Y ≡ X ⊗₀ Z → Y ≡ Z
              ≼-IsPartialOrder : IsPartialOrder _≡_ _≼_ -- Pointwise _≡_ ⇔ _≡_

    ↑' : ∀ {X Y Z} → X ⊗₀ Y ≼ Z → ObjTerm
    ↑' X⊗Y≼Z = proj₁ (prefix-remainder X⊗Y≼Z)

    ↑ : ∀ {X Y Z} → (h : X ⊗₀ Y ≼ Z) → (X ⊗₀ Y) ⊗₀ ↑' h ≡ Z
    ↑ X⊗Y≼Z = proj₂ (prefix-remainder X⊗Y≼Z)

    data HomTermⁿ : ObjTerm → ObjTerm → Set where
      [] : HomTermⁿ A A
      id_⊗_∷_ : (offset : B₁ ⊗₀ B₂ ≼ B) → mor B₂ C₂
               → HomTermⁿ A B → HomTermⁿ A (B₁ ⊗₀ C₂ ⊗₀ (↑' offset))

    _∘ⁿ_ : HomTermⁿ B C → HomTermⁿ A B → HomTermⁿ A C
    [] ∘ⁿ f = f
    (id A ⊗ h ∷ g) ∘ⁿ f = id A ⊗ h ∷ (g ∘ⁿ f)

    module Setup {X Y Z} (f : mor B₂ Y) (g : mor C₂ Z)
        (C₁⊗C₂≼X : C₁ ⊗₀ C₂ ≼ X) (B₁⊗B₂≼C₁ : B₁ ⊗₀ B₂ ≼ C₁) where

      open import Relation.Binary.Reasoning.PartialOrder record
        { isPartialOrder = ≼-IsPartialOrder }

      R R' : ObjTerm
      R = proj₁ (prefix-remainder B₁⊗B₂≼C₁)
      R' = B₁ ⊗₀ Y ⊗₀ R

      B₁⊗B₂≼X : B₁ ⊗₀ B₂ ≼ X
      B₁⊗B₂≼X = begin
        B₁ ⊗₀ B₂
          ≤⟨ B₁⊗B₂≼C₁ ⟩
        C₁
          ≤⟨ X≼X⊗Y ⟩
        C₁ ⊗₀ C₂
          ≤⟨ C₁⊗C₂≼X ⟩
        X ∎

      B₃ = ↑' B₁⊗B₂≼X
      C₃ = ↑' C₁⊗C₂≼X

      B₃-eq : B₃ ≡ R ⊗₀ C₂ ⊗₀ C₃
      B₃-eq = ⊗-cancelˡ (B₁ ⊗₀ B₂) $ begin-equality
        (B₁ ⊗₀ B₂) ⊗₀ B₃
          ≡⟨ ↑ B₁⊗B₂≼X ⟩
        X
          ≡⟨ ↑ C₁⊗C₂≼X ⟨
        (C₁ ⊗₀ C₂) ⊗₀ C₃
          ≡⟨ ⊗₀-assoc ⟩
        C₁ ⊗₀ C₂ ⊗₀ C₃
          ≡⟨ cong (λ ∙ → ∙ ⊗₀ C₂ ⊗₀ C₃) (↑ B₁⊗B₂≼C₁) ⟨
        ((B₁ ⊗₀ B₂) ⊗₀ R) ⊗₀ C₂ ⊗₀ C₃
          ≡⟨ ⊗₀-assoc ⟩
        (B₁ ⊗₀ B₂) ⊗₀ (R ⊗₀ C₂ ⊗₀ C₃) ∎

      B₁⊗B₂≼X₁ : B₁ ⊗₀ B₂ ≼ C₁ ⊗₀ Z ⊗₀ C₃
      B₁⊗B₂≼X₁ = begin
        B₁ ⊗₀ B₂
          ≤⟨ B₁⊗B₂≼C₁ ⟩
        C₁
          ≤⟨ X≼X⊗Y ⟩
        C₁ ⊗₀ Z ⊗₀ C₃ ∎

      R'⊗C₂≼X₂ : R' ⊗₀ C₂ ≼ B₁ ⊗₀ Y ⊗₀ B₃
      R'⊗C₂≼X₂ = begin
        (B₁ ⊗₀ Y ⊗₀ R) ⊗₀ C₂
          ≡⟨ ⊗₀-assoc ⟩
        B₁ ⊗₀ (Y ⊗₀ R) ⊗₀ C₂
          ≡⟨ cong (B₁ ⊗₀_) ⊗₀-assoc ⟩
        B₁ ⊗₀ Y ⊗₀ R ⊗₀ C₂
          ≤⟨ X≼X⊗Y ⟩
        (B₁ ⊗₀ (Y ⊗₀ (R ⊗₀ C₂))) ⊗₀ C₃
          ≡⟨ ⊗₀-assoc ⟩
        B₁ ⊗₀ (Y ⊗₀ (R ⊗₀ C₂)) ⊗₀ C₃
          ≡⟨ cong (B₁ ⊗₀_) ⊗₀-assoc ⟩
        B₁ ⊗₀ Y ⊗₀ (R ⊗₀ C₂) ⊗₀ C₃
          ≡⟨ cong (λ ∙ → B₁ ⊗₀ Y ⊗₀ ∙) ⊗₀-assoc ⟩
        B₁ ⊗₀ Y ⊗₀ R ⊗₀ C₂ ⊗₀ C₃
          ≡⟨ cong (λ ∙ → B₁ ⊗₀ Y ⊗₀ ∙) B₃-eq ⟨
        B₁ ⊗₀ Y ⊗₀ B₃ ∎

    -- we'd like to have both arguments of the same type, but it's not quite obvious how to have `redʳ` compatible with that
    data _→ʳ_ : HomTermⁿ A B → HomTermⁿ C D → Set where

      redʳ : ∀ {X Y Z} (f : mor B₂ Y) (g : mor C₂ Z)
        (C₁⊗C₂≼X : C₁ ⊗₀ C₂ ≼ X) (B₁⊗B₂≼C₁ : B₁ ⊗₀ B₂ ≼ C₁)
        → let open Setup f g C₁⊗C₂≼X B₁⊗B₂≼C₁
        in (id B₁⊗B₂≼X₁ ⊗ f ∷ id C₁⊗C₂≼X ⊗ g ∷ [])
        →ʳ (id R'⊗C₂≼X₂ ⊗ g ∷ id B₁⊗B₂≼X ⊗ f ∷ [])

    data _→ʳ*_ : HomTermⁿ A B → HomTermⁿ A B → Set where
      →ʳ*-refl : {f : HomTermⁿ B C} → f →ʳ* f
      →ʳ*-trans : {f g h : HomTermⁿ A B} → f →ʳ* g → g →ʳ* h → f →ʳ* h
      →ʳ*-→ʳ : {f g : HomTermⁿ A B} → f →ʳ g → f →ʳ* g
      →ʳ*-∘ : {f f' : HomTermⁿ B C} {g g' : HomTermⁿ A B}
        → f →ʳ* f' → g →ʳ* g' → (f ∘ⁿ g) →ʳ* (f' ∘ⁿ g')
