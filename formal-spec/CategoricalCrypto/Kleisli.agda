{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Kleisli where

open import CategoricalCrypto.Channel
open import Relation.Binary.PropositionalEquality
open import Function

---------------------------------------
-- Common (A ⊗ (B ⊗ Adv) ᵀ) pattern --
-------------------------------------------------------------------------------------
-- When building Kleisli machines and relying on an adversarial channel, the       --
-- above pattern often arises, thus we provide helpers to select channels from     --
-- it. Adv is the adversary channels, and A and B honest channels.                 --
-------------------------------------------------------------------------------------

honestChannelA : ∀ {m A B Adv} → A [ m ]⇒[ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelA = ⊗-right-intro

honestChannelB : ∀ {m A B Adv} → B [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelB = ⇒-transpose ⇒ₜ ⊗-right-intro ⇒ₜ ⊗-ᵀ-factor ⇒ₜ ⊗-left-intro

adversarialChannel : ∀ {m A B Adv} → Adv [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
adversarialChannel = ⇒-transpose ⇒ₜ ⊗-left-intro ⇒ₜ ⊗-ᵀ-factor ⇒ₜ ⊗-left-intro

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

-- Other approaches :
-- 1. remove ¬¬ but it requires to case split on the mode
-- 2. have lift take m' and m'' and an implicit proof that m' ≡ m''

lift : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ] B
lift ϵ = ⇒-refl
lift (x ⊗R) = lift x ⇒ₜ ⊗-right-intro
lift (L⊗ x) = lift x ⇒ₜ ⊗-left-intro
lift (x ᵗ) = lift x ⇒ₜ ⇒-transpose
lift (¬¬ x) = lift x ⇒ₜ ⇒-double-negate

_|ₗ = lift

infix 7 _|ₗ

honestChannelA' : ∀ {m A B Adv} → A [ m ]⇒[ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelA' = ϵ ⊗R |ₗ

honestChannelB' : ∀ {m A B Adv} → B [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelB' = L⊗ (ϵ ⊗R) ᵗ |ₗ

adversarialChannel' : ∀ {m A B Adv} → Adv [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
adversarialChannel' = L⊗ (L⊗ ϵ) ᵗ |ₗ

multiple : ∀ {m A B} → A [ m ]⇒[ m ] A ⊗ (A ⊗ B)
multiple = ϵ ⊗R |ₗ

multiple-negates : ∀ {m A B} → A [ m ]⇒[ ¬ₘ m ] ((((A ᵀ ⊗ B) ᵀ ⊗ B) ᵀ ⊗ B) ᵀ ⊗ B) ᵀ
multiple-negates = ((¬¬ (((¬¬ (ϵ ᵗ ⊗R) ᵗ) ⊗R) ᵗ ⊗R) ᵗ) ⊗R) ᵗ |ₗ

test : ∀ {m A B C D E} → E [ m ]⇒[ m ] A ⊗ ((B ⊗ E ⊗ D) ᵀ ⊗ C) ᵀ ⊗ (A ⊗ B)
test = L⊗ (¬¬ ((L⊗ ϵ ⊗R) ᵗ ⊗R) ᵗ) ⊗R |ₗ
