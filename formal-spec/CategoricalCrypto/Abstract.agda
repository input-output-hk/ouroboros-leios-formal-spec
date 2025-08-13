{-# OPTIONS --no-require-unique-meta-solutions #-}
module CategoricalCrypto.Abstract where

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Functor hiding (id)
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Monad.Graded
open import Categories.Morphism
open import Categories.NaturalTransformation hiding (id)
open import Categories.Category.Monoidal.Properties

open import Categories.Category.Instance.Sets

open import Categories.Tactic.Category

open import Data.Product
open import Data.Fin

open import Data.Vec using (_∷_; [])
open import CategoricalCrypto.MonoidalCoherence

record UC-model : Set₁ where
  field C : Category ℓ0 ℓ0 ℓ0
        I : MonoidalCategory ℓ0 ℓ0 ℓ0
        M : GradedMonad I C
        ℰ : Presheaf C (Sets ℓ0)

module _ (C : Category ℓ0 ℓ0 ℓ0) (I : MonoidalCategory ℓ0 ℓ0 ℓ0) (M : GradedKleisliTriple I C) where
  open Category hiding (∘-resp-≈ˡ; identityʳ; assoc)
  open Category C using () renaming (id to idC; _∘_ to _∘C_)
  open MonoidalCategory hiding (_⊗₀_; _⊗₁_; -⊗_; _⊗-; ∘-resp-≈ˡ)
  open MonoidalCategory I using (∘-resp-≈ˡ; _⊗₀_; _⊗₁_; -⊗_; _⊗-) renaming (id to idI; _∘_ to _∘I_)
  open Functor
  open NaturalTransformation
  open GradedKleisliTriple M
  open import Categories.Category.Monoidal.Utilities (I .monoidal)
  open Shorthands

  GradedKleisli : Category ℓ0 ℓ0 ℓ0
  GradedKleisli = categoryHelper record
    { Obj       = I .Obj × C .Obj
    ; _⇒_       = λ where (i , c) (j , d) → ∃[ k ] (C [ c , T₀ k d ]) × (I .U [ i ⊗₀ k , j ])
    ; _≈_       = λ where
      {ai , _} (i , f , α) (j , g , β) →
        Σ[ φ ∈ I .U [ i , j ] ] C [ sub φ ∘C f ≈ g ] × I .U [ β ∘I (₁ (ai ⊗-) φ) ≈ α ]
    ; id        = I .unit , return , ρ⇒
    ; _∘_       = λ where
      (j , g , β) (i , f , α) → i ⊗₀ j , μ i j ∘C T₁ i g ∘C f , β ∘I (₁ (-⊗ j) α) ∘I α⇐
    ; assoc     = {!!}
    ; identityˡ = λ where
      {ai , _} {_} {i , f , α} →
          ρ⇒
        , ((let open Category.HomReasoning C in begin
            sub ρ⇒ ∘C μ i (I .unit) ∘C T₁ i return ∘C f
              ≈⟨ solve C ⟩
            (sub ρ⇒ ∘C μ i (I .unit) ∘C T₁ i return) ∘C f
              ≈⟨ μ-identityʳ ⟩∘⟨refl ⟩
            idC ∘C f
              ≈⟨ solve C ⟩
            f ∎))
        , (let open MonoidalCategory.HomReasoning I in begin
            α ∘I (₁ (ai ⊗-) ρ⇒)
              ≈⟨ refl⟩∘⟨ (let module S = Solver I (ai ∷ i ∷ []) in
                 S.solveM {Y = S.Var (# 0) S.⊗₀ S.Var (# 1)} (S.id S.⊗₁ S.ρ⇒) (S.ρ⇒ S.∘ S.α⇐)) ⟩
            α ∘I (ρ⇒ ∘I α⇐)
              ≈⟨ solve (I .U) ⟩
            (α ∘I ρ⇒) ∘I α⇐
              ≈⟨ unitorʳ-commute-from I ⟩∘⟨refl ⟨
            (ρ⇒ ∘I (₁ (-⊗ I .unit) α)) ∘I α⇐
              ≈⟨ solve (I .U) ⟩
            ρ⇒ ∘I (₁ (-⊗ I .unit) α) ∘I α⇐ ∎)

            -- α ∘I (₁ (ai ⊗-) ρ⇒)
            --   ≈⟨ refl⟩∘⟨ identityʳ I ⟨
            -- α ∘I (₁ (ai ⊗-) ρ⇒ ∘I idI)
            --   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoʳ (I .associator) ⟨
            -- α ∘I ((₁ (ai ⊗-) ρ⇒) ∘I α⇒ ∘I α⇐)
            --   ≈⟨ refl⟩∘⟨ assoc I ⟨
            -- α ∘I (((₁ (ai ⊗-) ρ⇒) ∘I α⇒) ∘I α⇐)
            --   ≈⟨ refl⟩∘⟨ coherence₂ (I .monoidal) ⟩∘⟨refl ⟩
            -- α ∘I (ρ⇒ ∘I α⇐)
            --   ≈⟨ solve (I .U) ⟩
            -- (α ∘I ρ⇒) ∘I α⇐
            --   ≈⟨ unitorʳ-commute-from I ⟩∘⟨refl ⟨
            -- (ρ⇒ ∘I (₁ (-⊗ I .unit) α)) ∘I α⇐
            --   ≈⟨ solve (I .U) ⟩
            -- ρ⇒ ∘I (₁ (-⊗ I .unit) α) ∘I α⇐ ∎)
    ; identityʳ = {!Solver.solveM!}
    ; equiv     = {!!}
    ; ∘-resp-≈  = {!!}
    }
