open import Leios.Prelude hiding (id; _⊗_)
open import Leios.Abstract

open import CategoricalCrypto renaming (_∘_ to _∘'_)
open import Leios.Config

open import Network.BasicBroadcast using (NetworkT; RcvMessage; SndMessage; Activate)

module Network.Leios where

module SingleNode (params : Params) (let open Params params) where

  open import Leios.Defaults params using (d-Abstract; d-SpecStructure; FFDBuffers; SimpleFFD)
  open import Leios.Blocks d-Abstract
  open import Leios.Short d-SpecStructure params
  open import Leios.FFD

  open Types params
  open LeiosAbstract d-Abstract

  addToInbox : NetworkMessage → FFDBuffers → FFDBuffers
  addToInbox (inj₁ ib)  b              = record b { inIBs = ib ∷ FFDBuffers.inIBs b }
  addToInbox (inj₂ (inj₁ eb)) b        = record b { inEBs = eb ∷ FFDBuffers.inEBs b }
  addToInbox (inj₂ (inj₂ (inj₁ vt))) b = record b { inVTs = vt ∷ FFDBuffers.inVTs b }
  addToInbox (inj₂ (inj₂ (inj₂ rb))) b = b

  collectOutbox : FFDBuffers → FFDBuffers × List NetworkMessage
  collectOutbox b = let open FFDBuffers b in
      record b { outIBs = [] ; outEBs = [] ; outVTs = [] }
    , map inj₁ outIBs ++ map (inj₂ ∘ inj₁) outEBs ++ map (inj₂ ∘ inj₂ ∘ inj₁) outVTs

  data WithState_receive_return_newState_ : MachineType Network (FFD ⊗ BaseC) FFDBuffers where

      ReceiveNetwork : ∀ {m s}
        → WithState s
          receive (rcvˡ (-, RcvMessage m))
          return nothing
          newState (addToInbox m s)

      LeiosStep : ∀ {s i o s'}
        → let b , outbox = collectOutbox s' in SimpleFFD s i o s'
        → WithState s
          receive rcvˡ (-, Activate)
          return just (sndˡ (-, SndMessage outbox))
          newState b

  Node : Machine Network (IO ⊗ Adv)
  Node = ShortLeios ∘' MkMachine FFDBuffers WithState_receive_return_newState_

module MultiNode (networkParams : NetworkParams) (let open NetworkParams networkParams)
  (winning-slotsF : Fin numberOfParties → ℙ (BlockType × ℕ))
  where

  open import Data.Fin

  paramsF : Fin numberOfParties → Params
  paramsF k = record { networkParams = networkParams
                     ; sutId = k
                     ; winning-slots = winning-slotsF k }

  -- TODO: refactor so we don't need this
  zeroParams : Params
  zeroParams = paramsF (fromℕ< (>-nonZero⁻¹ numberOfParties))

  -- Technically, all these channel families are identical. Maybe this can be refactored?

  module _ (k : Fin numberOfParties) where

    open import Leios.Defaults (paramsF k) using (d-SpecStructure)
    open import Leios.Short d-SpecStructure (paramsF k)
    open Types (paramsF k)

    NetworkF : Channel
    NetworkF = Network

    IOF : Channel
    IOF = IO

    AdvF : Channel
    AdvF = Adv

    NodeF : Machine NetworkF (IOF ⊗ AdvF)
    NodeF = SingleNode.Node (paramsF k)

  open import Leios.Defaults zeroParams using (d-SpecStructure)
  open import Leios.Short d-SpecStructure zeroParams
  open Types zeroParams

  constNetworkF : Fin numberOfParties → Channel
  constNetworkF _ = Network

  NetworkF≡constNetworkF : ∀ {k} → NetworkF k ≡ constNetworkF k
  NetworkF≡constNetworkF = refl

  NetworkMessage-const : ∀ {k₁ k₂} → NetworkF k₁ ≡ NetworkF k₂
  NetworkMessage-const = refl

  -- network consisting only of honest nodes

  honestNodes : Machine (⨂ NetworkF) (⨂ IOF ⊗ ⨂ AdvF)
  honestNodes = ⨂ᴷ NodeF

  honestNodes' : Machine (⨂ constNetworkF) (⨂ IOF ⊗ ⨂ AdvF)
  honestNodes' = subst (λ c → Machine c (⨂ IOF ⊗ ⨂ AdvF))
                       (⨂≡ (λ k → NetworkF≡constNetworkF {k})) honestNodes

  open Network.BasicBroadcast numberOfParties NetworkMessage
    renaming (A to NetAdv; Network to NetFunctionality)

  honestNetwork : Machine I (⨂ IOF ⊗ (NetAdv ⊗ ⨂ AdvF))
  honestNetwork = honestNodes' ∘ᴷ NetFunctionality
