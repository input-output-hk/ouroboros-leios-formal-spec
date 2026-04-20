{-# OPTIONS --safe #-}

open import Leios.Prelude
open import CategoricalCrypto

-- | Generic "the machine answers blockchain queries and blocks carry
-- producer/slot metadata" witness.
--
-- Parameterised over the block type and the type of participants (producers).
-- At use sites, `Participant` is typically instantiated to `Fin n` where
-- `n` is the number of nodes.
module Blockchain.IsBlockchain (Block : Type) (Participant : Type) where

-- | Type of things we can query from a honest node
data BlockChainInfo : Type where
  Chain : BlockChainInfo
  Slot  : BlockChainInfo

-- | Type for responses given a specific query
bciQueryType : BlockChainInfo → Type
bciQueryType Chain = List Block
bciQueryType Slot  = ℕ

record IsBlockchain {A B : Channel} (m : Machine A B) : Type₂ where
  field
    isConstrained : IsConstrained m bciQueryType
    isPure        : IsPure isConstrained
    producer      : Block → Participant
    slotOf        : Block → ℕ
