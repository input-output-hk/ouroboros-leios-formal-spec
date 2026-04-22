{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
open import CategoricalCrypto.Channel.Selection

open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
open import Leios.ChannelCat
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
  (cc : ChannelCat) (let open ChannelCat cc)
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

Leios1 : Machine DD.M (IO ⊗₀ ((I ⊗₀ I ⊗₀ BaseAdv) ⊗₀ Adv))
Leios1 = LinearLeios ∘ᴷ (liftᴷ Shim ⊗ᴷ B.m) ∘ᴷ liftᴷ NetTranslate

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

spec : Machine DD.M ((Network ⊗₀ BaseIO) ⊗₀ (I ⊗₀ I ⊗₀ BaseAdv))
spec = (idᴷ ⊗ᴷ B.m) ∘ᴷ liftᴷ NetTranslate

ext-spec : Machine (Network ⊗₀ BaseIO) (IO ⊗₀ I)
ext-spec = subst (λ x → Machine (Network ⊗₀ BaseIO) (IO ⊗₀ x)) eq body
  where
    eq : (I ⊗₀ I) ⊗₀ I ≡ I
    eq = trans ⊗-identityʳ ⊗-identityʳ
    body : Machine (Network ⊗₀ BaseIO) (IO ⊗₀ ((I ⊗₀ I) ⊗₀ I))
    body = LinearLeios ∘ᴷ (liftᴷ Shim ⊗ᴷ idᴷ)

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗₀ AdvF p)) honestNodes
  (honest-Node : {p : Participant} → p ∈ honestNodes → nodesF p ≡ᴹ Leios1)
  (isConstrained-Leios : IsConstrained Leios1 (IsBC.bciQueryType Participant {Block = LeiosBlock}))
  (isPure-Leios        : IsPure isConstrained-Leios)
  (IsBlockchain-base : IsBC.IsBlockchain Participant RankingBlock spec)
  (is-extension-eq :
    idᴷ ∘ᴷ Leios1 ≡ subst (λ A → Machine DD.M (IO ⊗₀ (A ⊗₀ I))) (sym ⊗-identityʳ) (ext-spec ∘ᴷ spec))
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

  safetyS : Safety LeiosBlock
  safetyS = record
    { n          = numberOfParties
    ; Network    = _
    ; spec       = record
        { IO                = _
        ; Adv               = _
        ; honest-node-spec  = Leios1
        ; spec-IsBlockchain = IsBlockchain-Leios
        }
    ; deployment = record
        { NAdv                = _
        ; IOF                 = IOF
        ; AdvF                = AdvF
        ; all-nodes           = nodesF
        ; honest-nodes        = honestNodes
        ; honest-nodes-≡-spec = honest-Node
        ; network             = DD.Network
        }
    }

  module S = Safety safetyS

  base-spec : Spec RankingBlock S.n S.Network
  base-spec = record
    { IO                = _
    ; Adv               = _
    ; honest-node-spec  = spec
    ; spec-IsBlockchain = IsBlockchain-base
    }

  extension : IsExtension base-spec (Safety.spec safetyS)
  extension = record
    { ext-Adv≡base-Adv = ⊗-identityʳ
    ; ext-layer        = ext-spec
    ; is-extension     = is-extension-eq
    ; getBaseBlock     = LeiosBlock.rb
    ; getBaseBlock-inj = LeiosBlock-Injective
    }

  private
    module Tr = Transfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec cc extension
    module TrM = Tr.Main

  leiosSafety : (∀ {A} (E : Safety.Environment safetyS A) → TrM.ChainLemma-ty E)
              → Safety.safety Tr.base k → S.safety k
  leiosSafety = TrM.transfer k

  private
    module LTr = LTransfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec cc extension (λ _ → refl) (λ _ → refl)
    module LTrM = LTr.Main

  leiosHCG : (∀ {A} (E : S.Environment A) → LTrM.TrM.ChainLemma-ty E)
           → (∀ {A} (E : S.Environment A) → LTrM.SlotLemma-ty E)
           → ∀ τ → LTr.BL.hcg τ → LTr.EL.hcg τ
  leiosHCG CL SL τ = LTrM.hcg-transfer τ CL SL

  leios∃CQ : (∀ {A} (E : S.Environment A) → LTrM.TrM.ChainLemma-ty E)
           → (∀ {A} (E : S.Environment A) → LTrM.SlotLemma-ty E)
           → ∀ T → LTr.BL.∃cq T → LTr.EL.∃cq T
  leios∃CQ CL SL T = LTrM.∃cq-transfer T CL SL
