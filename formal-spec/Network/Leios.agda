{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
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

module _ nodesF honestNodes
  (honest-Node : {p : Fin Participants} → p ∈ honestNodes → nodesF p ≡ Leios1)
  (honest-IsBlockchain : {p : Fin Participants} → p ∈ honestNodes → IsBlockchain Block (nodesF p))
  where
  LeiosSafety : Type
  LeiosSafety = safety Block Leios1
    nodesF honestNodes honest-Node honest-IsBlockchain DD.Network Δ Δ
