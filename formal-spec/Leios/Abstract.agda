{-# OPTIONS --safe #-}

module Leios.Abstract where

open import Leios.Prelude

record LeiosAbstract : Type₁ where
  field Tx : Type
        ⦃ DecEq-Tx ⦄ : DecEq Tx
        PoolID : Type
        ⦃ DecEq-PoolID ⦄ : DecEq PoolID
        BodyHash VrfPf PrivKey Sig Hash : Type -- these could have been byte strings, but this is safer
        ⦃ DecEq-Hash ⦄ : DecEq Hash
        ⦃ DecEq-VrfPf ⦄ : DecEq VrfPf
        ⦃ DecEq-Sig ⦄ : DecEq Sig
        Vote : Type
        ⦃ DecEq-Vote ⦄ : DecEq Vote
        vote : PrivKey → Hash → Vote
        sign : PrivKey → Hash → Sig
        ⦃ Hashable-Txs ⦄ : Hashable (List Tx) Hash
        L : ℕ
        ⦃ NonZero-L ⦄ : NonZero L
