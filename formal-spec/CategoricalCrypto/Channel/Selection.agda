{-# OPTIONS --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel.Selection where

open import CategoricalCrypto.Channel.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary 
open import Function
open import Meta.Prelude
open import Meta.Init

open import Data.List

open import Reflection.AST.Term
open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI

open import Class.Functor.Instances
open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances hiding (_ᵗ)
open import Class.Traversable

infix 4 _[_]⇒[_]ᵍ_

infix 10 _ᵗ
infix 9 _⊗R
infix 8 L⊗_
infix 8 ¬¬_

data _[_]⇒[_]ᵍ_ : Channel → Mode → Mode → Channel → Set₁ where 
  ϵ : ∀ {m A} → A [ m ]⇒[ m ]ᵍ A
  _⊗R : ∀ {m m' A B C} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ]ᵍ B ⊗ C
  L⊗_ : ∀ {m m' A B C} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ]ᵍ C ⊗ B
  _ᵗ : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ ¬ₘ m' ]ᵍ B ᵀ
  ¬¬_ : ∀ {m A B} → A [ m ]⇒[ m ]ᵍ B → A [ m ]⇒[ ¬ₘ ¬ₘ m ]ᵍ B

liftᵍ : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ] B
liftᵍ ϵ = ⇒-refl
liftᵍ (x ⊗R) = liftᵍ x ⇒ₜ ⊗-right-intro
liftᵍ (L⊗ x) = liftᵍ x ⇒ₜ ⊗-left-intro
liftᵍ (x ᵗ) = liftᵍ x ⇒ₜ ⇒-transpose
liftᵍ (¬¬_ {m} x) rewrite ¬ₘ-idempotent {m} = liftᵍ x

_↑ = liftᵍ

_↑ᵢ_ = liftᵍ {In}

_↑ₒ_ = liftᵍ {Out}

infix 7 _↑ _↑ᵢ_ _↑ₒ_

instance _ = Functor-M ⦃ Class.Monad.Monad-TC ⦄

A : Channel
A = ℕ ⇿ ⊤

B : Channel
B = ⊥ ⇿ Bool

x = quoteTerm (A [ In ]⇒[ Out ]ᵍ A ⊗ B)

y = quoteTerm (A [ Out ]⇒[ ¬ₘ ¬ₘ Out ]ᵍ A)

z = quoteTerm (A [ In ]⇒[ In ] A)

{-# NON_TERMINATING #-}
test : Term → TC Term
test (_ ∙⟦ A ∣ m ∣ m' ∣ B ⟧) with A ≟ B | m ≟ m'
test (_ ∙⟦ A ∣ m ∣ .m ∣ .A ⟧) | yes refl | yes refl = do
  mQ ← unquoteTC m
  AQ ← unquoteTC A
  return $ quoteTerm (ϵ {mQ} {AQ})
test (f ∙⟦ A ∣ m ∣ quote ¬ₘ_ ∙⟦ quote ¬ₘ_ ∙⟦ m' ⟧ ⟧ ∣ B ⟧) | _ | _ = do
  rec ← test (f ∙⟦ A ∣ m ∣ m' ∣ B ⟧)
  return $ quote ¬¬_ ∙⟦ rec ⟧
test (f ∙⟦ A ∣ m ∣ _ ∙⟦ m' ⟧ ∣ _ ∙⟦ B ⟧ ⟧) | _ | _ = do
  rec ← test (f ∙⟦ A ∣ m ∣ m' ∣ B ⟧)
  return $ quote _ᵗ ∙⟦ rec ⟧
test (f ∙⟦ A ∣ m ∣ _ ∙⟦ m' ⟧ ∣ _ ∙⟦ B ∣ C ⟧ ⟧) | _ | _ = do
  {!!}
test _ | _ | _ = error1 "Bad term shape"
test _ = error1 "Bad term shape"

applyConstrToUnknowns : Name → Type → Term
applyConstrToUnknowns n = con n ∘ map (\{ (arg i _) → arg i unknown }) ∘ argTys

-- No Maximum depth. Infinite recursion in monad

{-# TERMINATING #-}
tryConstrs' : ITactic
tryConstrs' = do
  inj₁ goal ← reader TCEnv.goal
    where inj₂ _ → error1 "Goal is not a term!"
  goalTy ← inferType goal
  constrs ← getConstrsForType $ quoteTerm _[_]⇒[_]ᵍ_
  let holedConstrs = map (uncurry applyConstrToUnknowns) constrs
  try
    (Data.List.map
      (λ constr → do
        t ← local
          (λ env → record env { reconstruction = true })
          (checkType constr goalTy)
        unify goal t
        traverse
          (λ t' → runWithHole t' tryConstrs')
          (findMetas t)
        return tt)
      holedConstrs)
    (error1 "No constructors were able to solve the goal!")

module _ ⦃ _ : TCOptions ⦄ where
  macro
    tryConstrs = initTac tryConstrs'
