{-# OPTIONS --safe #-}

open import Leios.Prelude
open import CategoricalCrypto

-- | Typeclass for machines that behave like a blockchain
--
-- Parameterised over the type of participants (producers).  At use sites,
-- `Participant` is typically instantiated to `Fin n` where `n` is the number
-- of nodes.
module Blockchain.IsBlockchain (Participant : Type) where

data BlockChainInfo (Block : Type) : Type where
  Chain : BlockChainInfo Block
  Slot  : BlockChainInfo Block

bciQueryType : ∀ {Block : Type} → BlockChainInfo Block → Type
bciQueryType {Block = Block} Chain = List Block
bciQueryType                 Slot  = ℕ

record IsBlockchain (Block : Type) {A B : Channel} (m : Machine A B) : Type₂ where
  field
    isConstrained : IsConstrained m (bciQueryType {Block})
    isPure        : IsPure isConstrained
    producer      : Block → Participant
    slotOf        : Block → ℕ
