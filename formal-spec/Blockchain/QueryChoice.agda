{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id; _∘_)
import Blockchain.IsBlockchain as IsBC

-- | Why the chain and slot lemmas are assumptions and not theorems.
--
-- `Blockchain.Safety.Deployment.getChain` reads a chain out of a state by
-- asking the node through its `IsBlockchain` structure.  That structure is
-- DATA, not a property: a machine does not determine it.  Below is one
-- machine carrying two `IsBlockchain` structures that report different chains
-- from the same state.
--
-- `IsExtension` relates an ext node to its base node as MACHINES and says
-- nothing about their `IsBlockchain` structures, so no chain lemma can follow
-- from `IsExtension` alone: the two sides of the square are free to disagree,
-- exactly as the two interfaces here do.
module Blockchain.QueryChoice where

open IsBC using (BlockChainInfo; bciQueryType; IsBlockchain)
open IsBC.BlockChainInfo
open Channel

-- A channel with two ways to ask for a chain, and one for a slot.  Both chain
-- questions are always answered; they just give different answers.
data QT : Mode → Type where
  askA askB askS : QT Out
  chain          : List ⊤ → QT In
  slot           : ℕ → QT In

C : Channel
C = simpleChannel QT

qin : QT Out → inType (I ⊗ᵀ C)
qin x = L⊗ ϵ ᵗ¹ ↑ₒ x

qout : QT In → outType (I ⊗ᵀ C)
qout y = L⊗ ϵ ᵗ¹ ↑ᵢ y

opaque
  unfolding _⊗₀_

  route : inType (I ⊗ᵀ C) → Maybe (outType (I ⊗ᵀ C))
  route (inj₂ askA) = just (qout (chain []))
  route (inj₂ askB) = just (qout (chain (tt ∷ [])))
  route (inj₂ askS) = just (qout (slot 0))

  route-A : route (qin askA) ≡ just (qout (chain []))
  route-A = refl

  route-B : route (qin askB) ≡ just (qout (chain (tt ∷ [])))
  route-B = refl

  route-S : route (qin askS) ≡ just (qout (slot 0))
  route-S = refl

-- The machine.  `FunctionMachine route` has `State = ⊤` and step relation
-- `route i ≡ o`, so correctness, completeness and purity are all immediate.
M : Machine I C
M = FunctionMachine route

-- Answers travel on the one `QT In` shape, whichever question was asked.
ansOf : ∀ {q} → bciQueryType {Block = ⊤} q → QT In
ansOf {Chain} bs = chain bs
ansOf {Slot}  n  = slot n

-- Two interfaces over that one machine, differing only in which question
-- they ask for `Chain`.
module Interface
  (ask : BlockChainInfo ⊤ → QT Out)
  (ans : (q : BlockChainInfo ⊤) → bciQueryType {Block = ⊤} q)
  (routes : ∀ q → route (qin (ask q)) ≡ just (qout (ansOf {q} (ans q))))
  where

  isConstrained : IsConstrained M (bciQueryType {Block = ⊤})
  isConstrained = record
    { queryI       = λ q → qin (ask q)
    ; queryO       = λ {q} r → qout (ansOf {q} r)
    ; correctness  = λ {q} st → ans q , trans (sym st) (routes q)
    ; completeness = λ {q} → _ , tt , routes q
    }

  isBlockchain : IsBlockchain ⊤ ⊤ M
  isBlockchain = record
    { isConstrained = isConstrained
    ; isPure        = λ _ _ → refl
    ; producer      = λ _ → tt
    ; slotOf        = λ _ → 0
    }

private
  viaA viaB : BlockChainInfo ⊤ → QT Out
  viaA Chain = askA
  viaA Slot  = askS
  viaB Chain = askB
  viaB Slot  = askS

  ansA ansB : (q : BlockChainInfo ⊤) → bciQueryType {Block = ⊤} q
  ansA Chain = []
  ansA Slot  = 0
  ansB Chain = tt ∷ []
  ansB Slot  = 0

  routesA : ∀ q → route (qin (viaA q)) ≡ just (qout (ansOf {q} (ansA q)))
  routesA Chain = route-A
  routesA Slot  = route-S

  routesB : ∀ q → route (qin (viaB q)) ≡ just (qout (ansOf {q} (ansB q)))
  routesB Chain = route-B
  routesB Slot  = route-S

module A = Interface viaA ansA routesA
module B = Interface viaB ansB routesB

-- Both are `IsBlockchain` structures for the very same machine `M` …
blockchainA blockchainB : IsBlockchain ⊤ ⊤ M
blockchainA = A.isBlockchain
blockchainB = B.isBlockchain

-- … and from the same state they report different chains.
chainA : proj₁ (IsConstrained.queryCompute A.isConstrained Chain tt) ≡ []
chainA = refl

chainB : proj₁ (IsConstrained.queryCompute B.isConstrained Chain tt) ≡ tt ∷ []
chainB = refl

interfaces-disagree :
  proj₁ (IsConstrained.queryCompute A.isConstrained Chain tt)
  ≢ proj₁ (IsConstrained.queryCompute B.isConstrained Chain tt)
interfaces-disagree ()

-- They agree on `Slot`, where they ask the same question: it is the CHOICE of
-- question, not the machine, that the answer depends on.
slots-agree :
  proj₁ (IsConstrained.queryCompute A.isConstrained Slot tt)
  ≡ proj₁ (IsConstrained.queryCompute B.isConstrained Slot tt)
slots-agree = refl
