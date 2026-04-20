{-# OPTIONS --safe #-}

open import Leios.Prelude
open import CategoricalCrypto

-- | Generic "the machine answers blockchain queries and blocks carry
-- producer/slot metadata" witness.
--
-- Parameterised over the block type and the type of participants (producers).
-- At use sites, `Participant` is typically instantiated to `Fin n` where
-- `n` is the number of nodes.
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

-- | Compatibility witness relating two `IsBlockchain` instances over the same
-- participant type but different block types.
record IsBlockchain-compatible
  {BlockBase BlockExt : Type}
  {Abase Bbase : Channel} {mbase : Machine Abase Bbase}
  {Aext  Bext  : Channel} {mext  : Machine Aext  Bext}
  (base : IsBlockchain BlockBase mbase)
  (ext  : IsBlockchain BlockExt  mext)
  : Type where
  private
    module IB-base = IsBlockchain base
    module IB-ext  = IsBlockchain ext
  field
    getBaseBlock      : BlockExt → BlockBase
    getBaseBlock-inj  : Injective _≡_ _≡_ getBaseBlock
    producer-compat   : ∀ b → IB-ext.producer b ≡ IB-base.producer (getBaseBlock b)
    slotOf-compat     : ∀ b → IB-ext.slotOf   b ≡ IB-base.slotOf   (getBaseBlock b)
