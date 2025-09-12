{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel.Selection where

open import CategoricalCrypto.Channel.Core
open import Relation.Binary.PropositionalEquality
open import Function

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
  ¬¬_ : ∀ {m A B} → A [ m ]⇒[ ¬ₘ (¬ₘ m) ]ᵍ B → A [ m ]⇒[ m ]ᵍ B

lift : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ] B
lift ϵ = ⇒-refl
lift (x ⊗R) = lift x ⇒ₜ ⊗-right-intro
lift (L⊗ x) = lift x ⇒ₜ ⊗-left-intro
lift (x ᵗ) = lift x ⇒ₜ ⇒-transpose
lift (¬¬ x) = lift x ⇒ₜ ⇒-double-negate

_↑ = lift

_↑ᵢ_ = lift {In}

_↑ₒ_ = lift {Out}

infix 7 _↑ _↑ᵢ_ _↑ₒ_
