{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)
open import Leios.Config
open import CategoricalCrypto hiding (id; _∘_)

module Leios.Safety where

-- Elements we are allowed to query from a BlockChain
data BlockChainInfo (Block : Type) : Type where
  chain : BlockChainInfo Block
  slot  : BlockChainInfo Block

bciQueryType : ∀ {Block} → BlockChainInfo Block → Type
bciQueryType {Block} chain = List Block
bciQueryType         slot  = ℕ

record IsBlockchain
  {A B   : Channel}
  (Block : Type)
  (m     : Machine A B) : Type where

  open Channel
  open Machine m renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
  
  module m = Machine m

  field queryI        : BlockChainInfo Block → B .outType
        queryO        : {bci : BlockChainInfo Block} → bciQueryType bci → B .inType
        queryCompute  : (bci : BlockChainInfo Block) → m.State → bciQueryType bci
        correctness   : {bci : BlockChainInfo Block} {s : m.State} →
          s -⟦ L⊗ ϵ ↑ᵢ queryI bci / just (L⊗ ϵ ↑ₒ queryO (queryCompute bci s)) ⟧ᵐ⇀ s

module _
  {A B : Channel}
  (m   : Machine A B) where
  
  open Machine m using () renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
  open Channel (A ⊗ B ᵀ)

  module m = Machine m

  data Trace : m.State → m.State → Type where
    []        : ∀ {s} → Trace s s
    _∷⟨_,_,_⟩ : ∀ {s s' s''} → Trace s s' → (i : inType) → (o : Maybe outType) → s' -⟦ i / o ⟧ᵐ⇀ s'' → Trace s s''

module _
  (n                   : ℕ) -- Number of involved parties
  (Block               : Type) -- Types of blocks 
  (IO Adv NAdv Network : Channel) -- Communication channels 
  (HonestSpec          : Machine Network (IO ⊗ Adv)) -- Spec machine
  (nodesF              : Fin n → Machine Network (IO ⊗ Adv)) -- Node machines 
  (honestNodes         : ℙ (Fin n)) -- Nodes behaving like the honest spec 
  (honest-Node         : ∀ {p} → p ∈ honestNodes → nodesF p ≡ HonestSpec) 
  (IsBlockchain-Node   : ∀ {p} → p ∈ honestNodes → IsBlockchain Block (nodesF p))
  (Net                 : Machine I (n ⨂ⁿ Network ⊗ NAdv)) -- The whole network
    where

  nodes : Machine (n ⨂ⁿ Network) (n ⨂ⁿ IO ⊗ n ⨂ⁿ Adv)
  nodes = ⨂ᴷ nodesF

  network : Machine I (n ⨂ⁿ IO ⊗ (NAdv ⊗ n ⨂ⁿ Adv))
  network = nodes ∘ᴷ Net

  module network = Machine network

  query : (bci : BlockChainInfo Block)
          {p : Fin n}
          → network.State
          → p ∈ honestNodes
          → bciQueryType bci
  query bci {p} ((_ , (s , tt)) , tt) honest-p = queryCompute bci (⨂ᴷ-sub-state p s)
    where open IsBlockchain (IsBlockchain-Node honest-p)

  getChain = query chain
  getSlot = query slot

  safety : ℕ → ℕ → Type
  safety k Δ = (p p'       : Fin n)
               (honest-p   : p ∈ honestNodes)
               (honest-p'  : p' ∈ honestNodes)
               (init final : network.State)
               (tr         : Trace network init final)
               -- for all traces that reach `Δ` slots into the future
               → getSlot init honest-p + Δ ≤ getSlot final honest-p
               -- all honest nodes have `chain` as a prefix
               → prune k (getChain init honest-p) ≼ getChain final honest-p'

