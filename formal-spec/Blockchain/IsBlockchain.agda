{-# OPTIONS --safe #-}

open import Leios.Prelude
open import CategoricalCrypto

-- | Typeclass for machines that behave like a blockchain
--
-- The queries and their answer types are shared by every instance; only the
-- record is parameterised over the type of participants (producers), at use
-- sites typically `Fin n` for `n` nodes.  Were the queries parameterised too,
-- a base layer and the deployment built on it would ask different questions.
module Blockchain.IsBlockchain where

data BlockChainInfo (Block : Type) : Type where
  Chain : BlockChainInfo Block
  Slot  : BlockChainInfo Block

bciQueryType : ∀ {Block : Type} → BlockChainInfo Block → Type
bciQueryType {Block = Block} Chain = List Block
bciQueryType                 Slot  = ℕ

record IsBlockchain (Participant Block : Type) {A B : Channel} (m : Machine A B) : Type₂ where
  field
    isConstrained : IsConstrained m (bciQueryType {Block})
    isPure        : IsPure isConstrained
    producer      : Block → Participant
    slotOf        : Block → ℕ
