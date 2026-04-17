{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
open import CategoricalCrypto.Channel.Selection
import CategoricalCrypto as CC

open import Blockchain.Safety
open import Leios.ChannelCat
import Blockchain.Safety.Transfer as Transfer

module Network.Leios
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂) where

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

open import Data.Product.Properties

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
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗₀ AdvF p)) honestNodes
  (honest-Node : {p : Participant} → p ∈ honestNodes → nodesF p ≡ᴹ Leios1)
  (cc : ChannelCat) (let open ChannelCat cc)
  (IsBlockchain-Leios : IsBlockchain LeiosBlock Leios1)
  where

  module LS {Block : Type} (Leios-IsBlockchain : IsBlockchain Block Leios1) where
    honest-node-spec = Leios1
    spec-IsBlockchain = Leios-IsBlockchain
    all-nodes = nodesF
    honest-nodes = honestNodes
    network = DD.Network
    honest-nodes-≡-spec = honest-Node

  safetyS : Safety LeiosBlock
  safetyS = record { LS IsBlockchain-Leios }

  module S = Safety safetyS

  spec : Machine S.Network ((Network ⊗₀ BaseIO) ⊗₀ (I ⊗₀ I ⊗₀ BaseAdv))
  spec = (idᴷ ⊗ᴷ B.m) ∘ᴷ liftᴷ NetTranslate

  ext-spec : Machine (Network ⊗₀ BaseIO) (IO ⊗₀ I)
  ext-spec = subst (λ x → Machine (Network ⊗₀ BaseIO) (IO ⊗₀ x)) eq body
    where
      eq : (I ⊗₀ I) ⊗₀ I ≡ I
      eq = trans ⊗-identityʳ ⊗-identityʳ
      body : Machine (Network ⊗₀ BaseIO) (IO ⊗₀ ((I ⊗₀ I) ⊗₀ I))
      body = LinearLeios ∘ᴷ (liftᴷ Shim ⊗ᴷ idᴷ)

  module _ (IsBlockchain-spec : IsBlockchain RankingBlock spec) where

    private
      module Tr = Transfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
        LeiosBlock.rb LeiosBlock-Injective
        safetyS
        cc
        (Network ⊗₀ BaseIO) (I ⊗₀ I ⊗₀ BaseAdv)
        spec IsBlockchain-spec
        ⊗-identityʳ
        ext-spec

    single-protocol-≡-ty : Type₁
    single-protocol-≡-ty = ∀ p → idᴷ ∘ᴷ S.all-nodes p ≡ Tr.extPart p ∘ᴷ Tr.base-all-nodes p

    module _ (single-protocol-≡ : single-protocol-≡-ty) where
      private module TrM = Tr.Main single-protocol-≡

      leiosSafety : (∀ {A} (E : Safety.Environment safetyS A) → TrM.ChainLemma-ty E)
                  → Safety.safety Tr.base k → Safety.safety safetyS k
      leiosSafety = TrM.transfer k
