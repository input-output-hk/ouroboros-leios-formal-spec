{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Kleisli where

open import CategoricalCrypto.Channel

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
