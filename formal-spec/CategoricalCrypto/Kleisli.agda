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

data _[_]⇒[_]ᵍ_ : Channel → Mode → Mode → Channel → Set₁ where 
  E : ∀ {m A} → A [ m ]⇒[ m ]ᵍ A
  R : ∀ {m m' A B C} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ]ᵍ B ⊗ C
  L : ∀ {m m' A B C} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ]ᵍ C ⊗ B
  T : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ ¬ₘ m' ]ᵍ B ᵀ
  N : ∀ {m A B} → A [ m ]⇒[ ¬ₘ (¬ₘ m) ]ᵍ B → A [ m ]⇒[ m ]ᵍ B

lift : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ] B
lift E = ⇒-refl
lift (R p) = lift p ⇒ₜ ⊗-right-intro
lift (L p) = lift p ⇒ₜ ⊗-left-intro
lift (T p) = lift p ⇒ₜ ⇒-transpose
lift (N p) = lift p ⇒ₜ ⇒-double-negate

honestChannelA' : ∀ {m A B Adv} → A [ m ]⇒[ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelA' = lift (R E)

honestChannelB' : ∀ {m A B Adv} → B [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelB' = lift (L (T (R E)))

adversarialChannel' : ∀ {m A B Adv} → Adv [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
adversarialChannel' = lift (L (T (L E)))

multiple : ∀ {m A B} → A [ m ]⇒[ m ] A ⊗ (A ⊗ B)
multiple = lift (L (R E)) -- (R E)

multiple-negates : ∀ {m A B} → A [ m ]⇒[ ¬ₘ m ] ((((A ᵀ ⊗ B) ᵀ ⊗ B) ᵀ ⊗ B) ᵀ ⊗ B) ᵀ
multiple-negates = lift (T (R (N (T (R (T (R (N (T (R (T E)))))))))))

test : ∀ {m A B C D E} → E [ m ]⇒[ m ] A ⊗ ((B ⊗ (E ⊗ D)) ᵀ ⊗ C) ᵀ ⊗ (A ⊗ B)
test = lift (N (L (R (T (R (T (L (R E))))))))
-- test {Out} = lift (L (R (T (R (T (L (R E)))))))
-- test {In} = lift (L (R (T (R (T (L (R E)))))))
