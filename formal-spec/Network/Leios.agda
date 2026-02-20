{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; module L)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
open import CategoricalCrypto.Channel.Selection

open import Leios.Safety

module Network.Leios (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (Lhdr Lvote Ldiff : ℕ)
  (splitTxs : List Tx → List Tx × List Tx)
  (validityCheckTime : EndorserBlock → ℕ) (Participants : ℕ) (Δ : ℕ) where

open import Leios.Linear ⋯ params Lhdr Lvote Ldiff splitTxs validityCheckTime
open Types params hiding (Network)

open import Leios.NetworkShim ⋯ params Lhdr Lvote Ldiff splitTxs validityCheckTime
open BaseAbstract B'

LeiosMsg = FFDA.Header ⊎ FFDA.Body
Message  = LeiosMsg ⊎ BaseMsg

import Network.DelayedDiffuse Participants Message Δ as DD

-- multiplexing the network for the base & leios functionality
-- this is somewhat awkward because we require a strict order on
-- the messages going through it
module NetTranslate where
  record State : Type where
    field inBuffer  : Maybe (List LeiosMsg)
          outBuffer : Maybe (List BaseMsg)

  private variable s : State

  data WithState_receive_return_newState_ : MachineType DD.M (Network ⊗ BaseNetwork) State where

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

NetTranslate : Machine DD.M (Network ⊗ BaseNetwork)
NetTranslate .Machine.State   = _
NetTranslate .Machine.stepRel = NetTranslate.WithState_receive_return_newState_

Leios1 : Machine DD.M (IO ⊗ ((I ⊗ BaseAdv) ⊗ Adv))
Leios1 = LinearLeios ∘ᴷ (liftᴷ Shim ⊗ᴷ B.m) ∘ NetTranslate

LeiosBlock = RankingBlock × Maybe EndorserBlock

IsBlockchain-Leios : IsBlockchain LeiosBlock Leios1
IsBlockchain-Leios = {!!}

IsBlockchain-Praos : IsBlockchain RankingBlock Leios1
IsBlockchain-Praos = {!!}

module _ nodesF honestNodes
  (honest-Node : {p : Fin Participants} → p ∈ honestNodes → nodesF p ≡ Leios1)
  where
  module S = Safety LeiosBlock Leios1 IsBlockchain-Leios nodesF honestNodes honest-Node DD.Network

  module P where
    open Safety RankingBlock Leios1 IsBlockchain-Praos nodesF honestNodes honest-Node DD.Network using (getChain; getSlot) public

  module L where
    open S using (getChain; getSlot) public

  LPSlotLemma : ∀ {s} → {p : Fin Participants} → (p-honest : p ∈ honestNodes)
    → P.getSlot s p-honest ≡ L.getSlot s p-honest
  LPSlotLemma = {!!}

  LPChainLemma : ∀ {s} → {p : Fin Participants} → (p-honest : p ∈ honestNodes)
    → P.getChain s p-honest ≡ map proj₁ (L.getChain s p-honest)
  LPChainLemma = {!!}

  EBHashesCorrect : List LeiosBlock → Type
  EBHashesCorrect = {!!}

  HashCollision : List LeiosBlock → List LeiosBlock → Type
  HashCollision = {!!}

  rbsDetermineEBs : (c₁ c₂ : List LeiosBlock) → map proj₁ c₁ ≡ map proj₁ c₂ → c₁ ≡ c₂ -- TODO: this only hold if there aren't any hash collisions
  rbsDetermineEBs = {!!}

  getChain-ebHashesCorrect : ∀ {s} → {p : Fin Participants} → (p-honest : p ∈ honestNodes)
    → EBHashesCorrect (L.getChain s p-honest)
  getChain-ebHashesCorrect = {!!}

  LeiosSafety : Type
  LeiosSafety = S.safety Δ Δ

  PraosSafety : Type
  PraosSafety = safetyBase _ _ BM {!!} honestNodes {!!} {!!} Δ Δ {!!}

  leiosSafety : LeiosSafety
  leiosSafety p p' honest-p honest-p' init final tr P = {!safetyBase _ _ BM!}
