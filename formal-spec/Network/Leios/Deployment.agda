{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Machine.Iso using (≅ᴹ-refl)

open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
import Blockchain.Safety.Transfer as Transfer
import Blockchain.Liveness.Transfer as LTransfer

-- The Leios deployment and its safety and liveness, transferred from the base
-- layer's.  The query interface of the base spec is the derived one of
-- `Network.Leios.Queries`; what remains hypothetical are the deployed node's
-- own query interface, the chain and slot lemmas relating the two through the
-- transfer, and the base layer's safety and liveness.
module Network.Leios.Deployment
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂)
  (ebOf : RankingBlock → Maybe EndorserBlock)
  (ebOf-correct : ∀ rb → HashCorrectB rb (ebOf rb))
    where

open import Network.Leios         ⋯ params k HashCorrectB HashCorrect-irrel hash-unique ebOf ebOf-correct
open import Network.Leios.Queries ⋯ params k HashCorrectB HashCorrect-irrel hash-unique ebOf ebOf-correct
open import Leios.Linear ⋯ params
open Types params hiding (Network)
open BaseAbstract B' using (BaseAdv)

import Network.DelayedDiffuse numberOfParties Message k as DD

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗₀ AdvF p)) honest-Nodes
  (honest-Node : {p : Participant} → p ∈ honest-Nodes → nodesF p ≡ᴹ Leios1)
  (honest-IOF  : {p : Participant} → p ∈ honest-Nodes → IOF p ≡ ExtIO)
  (honest-AdvF : {p : Participant} → p ∈ honest-Nodes → AdvF p ≡ BaseAdv ⊗₀ Adv)
  (base-party : Fin B.n → Participant)
    where

  -- Both blockchain interfaces are derived, not assumed: the base layer's
  -- queries are relayed down to `spec` through the network adapter, and to
  -- the deployed node through the multiplexer on the query port.
  IsBlockchain-base : IsBC.IsBlockchain Participant RankingBlock spec
  IsBlockchain-base = IsBlockchain-spec base-party

  IsBlockchain-Leios : IsBC.IsBlockchain Participant LeiosBlock Leios1
  IsBlockchain-Leios = IsBlockchain-Leios1 base-party

  safetyS : Deployment LeiosBlock
  safetyS = record
    { n                   = numberOfParties
    ; Network             = _
    ; spec                = record
        { IO                = _
        ; Adv               = _
        ; honest-node-spec  = Leios1
        ; spec-IsBlockchain = IsBlockchain-Leios
        }
    ; NAdv                = _
    ; IOF                 = IOF
    ; AdvF                = AdvF
    ; all-nodes           = nodesF
    ; honest-nodes        = honest-Nodes
    ; honest-nodes-≡-spec = honest-Node
    ; honest-IOF          = honest-IOF
    ; honest-AdvF         = honest-AdvF
    ; network             = DD.Network
    }

  module S = Deployment safetyS

  base-spec : Spec RankingBlock S.n S.Network
  base-spec = record
    { IO                = _
    ; Adv               = _
    ; honest-node-spec  = spec
    ; spec-IsBlockchain = IsBlockchain-base
    }

  extension : IsExtension base-spec (Deployment.spec safetyS)
  extension = record
    { AdvL             = Adv
    ; ext-Adv≡base-Adv⊗AdvL = refl
    ; ext-layer        = ext-spec
    ; is-extension     = ≅ᴹ-refl
    ; getBaseBlock     = LeiosBlock.rb
    ; getBaseBlock-inj = LeiosBlock-Injective
    ; query-compat     = node-compat
    }

  private
    module Tr = Transfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec extension
    module TrM = Tr.Main

  -- The chain and slot lemmas are no longer hypotheses: they are discharged
  -- in `Blockchain.Safety.Transfer` from `query-compat` and the sub-state
  -- transport.  What is left to assume is the base layer's own safety and
  -- liveness.
  leiosSafety : Deployment.safety Tr.base k → S.safety k
  leiosSafety = TrM.transfer k

  private
    module LTr = LTransfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec extension (λ _ → refl) (λ _ → refl)
    module LTrM = LTr.Main

  leiosHCG : ∀ τ → LTr.BL.hcg τ → LTr.EL.hcg τ
  leiosHCG τ = LTrM.hcg-transfer τ

  leios∃CQ : ∀ T → LTr.BL.∃cq T → LTr.EL.∃cq T
  leios∃CQ T = LTrM.∃cq-transfer T
