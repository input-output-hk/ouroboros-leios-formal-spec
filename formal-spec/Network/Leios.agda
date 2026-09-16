{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Iso using (≅ᴹ-refl)

open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
import Blockchain.Safety.Transfer as Transfer
import Blockchain.Liveness.Transfer as LTransfer

open import Data.Product.Properties

module Network.Leios
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂)
    where

open import Leios.Linear ⋯ params
open Types params hiding (Network)

open import Leios.NetworkShim ⋯ params
open BaseAbstract B'

LeiosMsg = FFDA.Header ⊎ FFDA.Body
Message  = LeiosMsg ⊎ BaseMsg

import Network.DelayedDiffuse numberOfParties Message k as DD

-- multiplexing the network for the base & leios functionality
-- this is somewhat awkward because we require a strict order on
-- the messages going through it
module NetTranslate where
  record State : Type where
    field inBuffer  : Maybe (List LeiosMsg)
          outBuffer : Maybe (List BaseMsg)

  private variable s : State

  data WithState_receive_return_newState_ : MachineType DD.M (Network ⊗₀ BaseNetwork) State where

    Receive : ∀ {l} → let (leios , base) = partitionSumsWith proj₂ l in
      WithState record { inBuffer = nothing ; outBuffer = nothing }
      receive ϵ ⊗R ↑ᵢ DD.Deliver l
      return just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ base)
      newState record { inBuffer = just leios ; outBuffer = nothing }

    SendB : ∀ {m leios} →
      WithState record { inBuffer = just leios ; outBuffer = nothing }
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ m
      return just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ Activate leios)
      newState record { inBuffer = nothing ; outBuffer = just m }

    SendL : ∀ {m m'} →
      WithState record { inBuffer = nothing ; outBuffer = just m }
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ Done m'
      return just (ϵ ⊗R ↑ₒ DD.Diffuse (map inj₂ m ++ map inj₁ m'))
      newState record { inBuffer = nothing ; outBuffer = nothing }

NetTranslate : Machine DD.M (Network ⊗₀ BaseNetwork)
NetTranslate .Machine.State   = _
NetTranslate .Machine.stepRel = NetTranslate.WithState_receive_return_newState_

-- The base functionality as seen through the multiplexed network
spec : Machine DD.M ((Network ⊗₀ BaseIO) ⊗₀ BaseAdv)
spec = ⊗-assoc⃖ CC.∘ (CC.id ⊗₁ B.m) CC.∘ NetTranslate

-- The extension layer, with `Adv` as its adversary channel
ext-spec : Machine (Network ⊗₀ BaseIO) (IO ⊗₀ Adv)
ext-spec = LinearLeios CC.∘ (Shim ⊗₁ CC.id)

-- The node as deployed: the extension layer stacked on the base spec. Its
-- adversary channel is the base functionality's, `BaseAdv`, next to
-- `LinearLeios`'s own, `Adv`
Leios1 : Machine DD.M (IO ⊗₀ BaseAdv ⊗₀ Adv)
Leios1 = ext-spec ∘ᴷ spec

-- the optional EB is the one determined by the RB, _not_ the one announced by it
record LeiosBlock : Type where
  field rb : RankingBlock
        eb : Maybe EndorserBlock
        correct : HashCorrectB rb eb

hash-unique' : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
  → (hc₁ : HashCorrectB rb eb₁) → (hc₂ : HashCorrectB rb eb₂) → (eb₁ , hc₁) ≡ (eb₂ , hc₂)
hash-unique' rb eb₁ eb₂ hc₁ hc₂ =
  Σ-≡,≡→≡ (hash-unique rb eb₁ eb₂ hc₁ hc₂ , HashCorrect-irrel _ _ _ _)

LeiosBlock-Injective : Injective _≡_ _≡_ LeiosBlock.rb
LeiosBlock-Injective
  {record { rb = rb ; eb = eb₁ ; correct = correct₁ }}
  {record { rb = rb ; eb = eb₂ ; correct = correct₂ }} refl =
  subst (λ (eb , correct) → _ ≡ record { rb = rb ; eb = eb ; correct = correct })
    (hash-unique' rb eb₁ eb₂ correct₁ correct₂) refl

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗₀ AdvF p)) honest-Nodes
  (honest-Node : {p : Participant} → p ∈ honest-Nodes → nodesF p ≡ᴹ Leios1)
  (honest-IOF  : {p : Participant} → p ∈ honest-Nodes → IOF p ≡ IO)
  (honest-AdvF : {p : Participant} → p ∈ honest-Nodes → AdvF p ≡ BaseAdv ⊗₀ Adv)
  (isConstrained-Leios : IsConstrained Leios1 (IsBC.bciQueryType Participant {Block = LeiosBlock}))
  (isPure-Leios        : IsPure isConstrained-Leios)
  (IsBlockchain-base : IsBC.IsBlockchain Participant RankingBlock spec)
    where

  private
    module IBB = IsBC.IsBlockchain IsBlockchain-base

  IsBlockchain-Leios : IsBC.IsBlockchain Participant LeiosBlock Leios1
  IsBlockchain-Leios = record
    { isConstrained = isConstrained-Leios
    ; isPure        = isPure-Leios
    ; producer      = λ b → IBB.producer (LeiosBlock.rb b)
    ; slotOf        = λ b → IBB.slotOf   (LeiosBlock.rb b)
    }

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
    }

  private
    module Tr = Transfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec extension
    module TrM = Tr.Main

  leiosSafety : (∀ {A} (E : Deployment.Environment safetyS A) → TrM.ChainLemma-ty E)
              → Deployment.safety Tr.base k → S.safety k
  leiosSafety = TrM.transfer k

  private
    module LTr = LTransfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec extension (λ _ → refl) (λ _ → refl)
    module LTrM = LTr.Main

  leiosHCG : (∀ {A} (E : S.Environment A) → LTrM.TrM.ChainLemma-ty E)
           → (∀ {A} (E : S.Environment A) → LTrM.SlotLemma-ty E)
           → ∀ τ → LTr.BL.hcg τ → LTr.EL.hcg τ
  leiosHCG CL SL τ = LTrM.hcg-transfer τ CL SL

  leios∃CQ : (∀ {A} (E : S.Environment A) → LTrM.TrM.ChainLemma-ty E)
           → (∀ {A} (E : S.Environment A) → LTrM.SlotLemma-ty E)
           → ∀ T → LTr.BL.∃cq T → LTr.EL.∃cq T
  leios∃CQ CL SL T = LTrM.∃cq-transfer T CL SL
