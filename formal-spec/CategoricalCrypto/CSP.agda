{-# OPTIONS --type-in-type --no-positivity-check --no-require-unique-meta-solutions #-}

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; [_]; _⊓_)
open import abstract-set-theory.FiniteSetTheory

import Data.List as L
open import CategoricalCrypto.SFunM {M = ℙ_}
open import Class.Monad.Ext
open import Data.List
open import Data.List.Relation.Unary.Any

module CategoricalCrypto.CSP where

postulate instance
  Monad-ℙ : Monad ℙ_
  F-Laws-ℙ : FunctorLaws ℙ_ ⦃ Applicative.super (Monad.super Monad-ℙ) ⦄
  M-Laws-ℙ : MonadLaws ℙ_
  Extensional-ℙ : ExtensionalMonad ℙ_
  Comm-ℙ : CommutativeMonad ℙ_

postulate
  instantiate : {A B : Type} → (List A → ℙ (List B)) → SFunᵉ A B

data Process (A : Type) (✓ : A) : Type where
  STOP SKIP : Process A ✓
  _➔_ : A → Process A ✓ → Process A ✓
  _□_ _⊓_ : Process A ✓ → Process A ✓ → Process A ✓
  _∥⦅_⦆_ : Process A ✓ → (A → Type) → Process A ✓ → Process A ✓
  fix : (Process A ✓ → Process A ✓) → Process A ✓
  _-_ : Process A ✓ → (A → Type) → Process A ✓

module _ {A : Type} {✓ : A} where

  _∥ᵗ⦅_⦆_ : List A → (A → Type) → List A → List (List A)
  l ∥ᵗ⦅ A ⦆ l' = {!!}

  {-# TERMINATING #-}
  [0⋯] : List ℕ
  [0⋯] = [ 0 ] ++ L.map suc [0⋯]

  appN : {A : Type} → ℕ → (A → A) → A → A
  appN zero f a = a
  appN (suc n) f a = f (appN n f a)

  {-# TERMINATING #-}
  ⟦_⟧ : Process A ✓ → List (List A)
  ⟦ STOP ⟧ = [ [] ]
  ⟦ SKIP ⟧ = [] ∷ [ ✓ ] ∷ []
  ⟦ a ➔ P ⟧ = [ [] ] ++ L.map (λ t → a ∷ t) ⟦ P ⟧
  ⟦ P □ Q ⟧ = ⟦ P ⟧ ++ ⟦ Q ⟧
  ⟦ P ⊓ Q ⟧ = ⟦ P ⟧ ++ ⟦ Q ⟧
  ⟦ P ∥⦅ A ⦆ Q ⟧ = L.concatMap (λ s → L.concatMap (λ t → s ∥ᵗ⦅ A ⦆ t) ⟦ Q ⟧) ⟦ P ⟧
  ⟦ fix F ⟧ = L.concatMap (λ n → ⟦ appN n F STOP ⟧) [0⋯]
  ⟦ P - A ⟧ = L.map (λ t → filter {P = A} {!!} t) ⟦ P ⟧

  toMachine : Process A ✓ → SFunᵉ ⊥ A
  toMachine P = instantiate (λ where [] → fromList ⟦ P ⟧)

  module Example (a : A) where
    P : Process A ✓
    P = SKIP □ (a ➔ SKIP)

    ex1 : List (List A)
    ex1 = {!take 10 ⟦ P ⟧!} -- C-c C-n to show the trace

    ex2 : a ∷ ✓ ∷ [] ∈ˡ ⟦ P ⟧
    ex2 = there (there (there (there (here refl))))
