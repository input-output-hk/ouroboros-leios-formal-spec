{-# OPTIONS --safe #-}

open import Leios.Prelude
open import CategoricalCrypto
import Relation.Binary.HeterogeneousEquality as H

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

-- The same question, asked of a different block type.  `BlockChainInfo` does
-- not depend on its block type, so this is a re-tagging; it is named because
-- an extension and its base layer ask the same questions of different blocks.
baseQ : ∀ {Block₁ Block₂ : Type} → BlockChainInfo Block₁ → BlockChainInfo Block₂
baseQ Chain = Chain
baseQ Slot  = Slot

-- An answer read through a block-level projection: blocks are mapped, slots
-- are untouched.  Shared, so that an extension and its instantiation cannot
-- give two definitions that differ only up to a case split.
mapAnswer : ∀ {Block₁ Block₂ : Type} (f : Block₁ → Block₂)
            (bci : BlockChainInfo Block₁)
          → bciQueryType bci → bciQueryType (baseQ {Block₂ = Block₂} bci)
mapAnswer f Chain = map f
mapAnswer _ Slot  = λ s → s

record IsBlockchain (Participant Block : Type) {A B : Channel} (m : Machine A B) : Type₂ where
  field
    isConstrained : IsConstrained m (bciQueryType {Block})
    isPure        : IsPure isConstrained
    producer      : Block → Participant
    slotOf        : Block → ℕ

-- Moving a query across a machine equality.  Matched here, in isolation: an
-- inline `with` on the same witness desynchronises from the definitions that
-- case on it (`base-all-nodes`, `single-protocol`, …), which is ill-typed.
query-≡ᴹ : ∀ {Participant Block : Type} {A B C D}
           {m : Machine A B} {m' : Machine C D}
           (e : m ≡ᴹ m') (ib : IsBlockchain Participant Block m')
           (bci : BlockChainInfo Block) (s : Machine.State m)
  → proj₁ (IsConstrained.queryCompute
             (IsBlockchain.isConstrained
               (≡ᴹ-subst (IsBlockchain Participant Block) (≡ᴹ-sym e) ib)) bci s)
  ≡ proj₁ (IsConstrained.queryCompute
             (IsBlockchain.isConstrained ib) bci (state-subst e s))
query-≡ᴹ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } ib bci s = refl
