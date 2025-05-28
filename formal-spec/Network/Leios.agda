open import Leios.Prelude hiding (id; _⊗_)
open import Leios.Abstract

open import CategoricalCrypto hiding (_∘_)
open import Leios.Config

open import Network.BasicBroadcast using (NetworkT; RcvMessage; SndMessage; Activate)

module Network.Leios where

module Types (params : Params) where

  open Params params
  open import Leios.Defaults params using (d-Abstract; d-SpecStructure; FFDBuffers)
  open import Leios.Blocks d-Abstract
  open LeiosAbstract d-Abstract

  Participant : Type
  Participant = Fin numberOfParties

  NetworkMessage : Type
  NetworkMessage = InputBlock ⊎ EndorserBlock ⊎ List Vote

  addToInbox : NetworkMessage → FFDBuffers → FFDBuffers
  addToInbox       (inj₁ ib)  b = record b { inIBs = ib ∷ FFDBuffers.inIBs b }
  addToInbox (inj₂ (inj₁ eb)) b = record b { inEBs = eb ∷ FFDBuffers.inEBs b }
  addToInbox (inj₂ (inj₂ vt)) b = record b { inVTs = vt ∷ FFDBuffers.inVTs b }

  collectOutbox : FFDBuffers → FFDBuffers × List NetworkMessage
  collectOutbox b = let open FFDBuffers b in
      record b { outIBs = [] ; outEBs = [] ; outVTs = [] }
    , map inj₁ outIBs ++ map (inj₂ ∘ inj₁) outEBs ++ map (inj₂ ∘ inj₂) outVTs

  Network : Channel
  Network = simpleChannel' (NetworkT numberOfParties NetworkMessage)

  data IOT : ChannelDir → Type where
    SubmitTxs : List Tx → IOT In
    FetchLdgI : IOT In
    FetchLdgO : List Tx → IOT Out

  -- mempool
  IO : Channel
  IO = simpleChannel' IOT ᵀ

  Adv : Channel
  Adv = I

module SingleNode (params : Params) where

  open Params params
  open import Leios.Defaults params using (d-Abstract; d-SpecStructure; FFDBuffers)
  open import Leios.Blocks d-Abstract
  open import Leios.Short d-SpecStructure
  open LeiosAbstract d-Abstract
  open Types params
  open LeiosState

  data Receive_withState_return_ : MachineType Network (IO ⊗ Adv) LeiosState where
    ReceiveNetwork : ∀ {m s}
      → Receive honestOutputI (-, RcvMessage m)
        withState s
        return ( record s { FFDState = addToInbox m (FFDState s) }
               , nothing )

    LeiosStep : ∀ {s s'} → let b , outbox = collectOutbox (FFDState s')
      in just s -⟦ SLOT / EMPTY ⟧⇀ s'
      → Receive (honestOutputI (-, Activate))
        withState s
        return ( record s' { FFDState = b }
               , just (honestInputO (-, SndMessage outbox)))

    InputTxs : ∀ {s s' txs}
      → just s -⟦ SUBMIT (inj₂ txs) / EMPTY ⟧⇀ s'
      → Receive honestInputI (-, SubmitTxs txs)
        withState s
        return (s' , nothing)

    FetchLedger : ∀ {s s' txs}
      → just s -⟦ FTCH-LDG / FTCH-LDG txs ⟧⇀ s'
      → Receive honestInputI (-, FetchLdgI)
        withState s
        return (s' , just (honestOutputO (-, FetchLdgO txs)))

  Node : Machine Network (IO ⊗ Adv)
  Node = MkMachine LeiosState Receive_withState_return_

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

  open Types zeroParams

  -- Technically, all these channel families are identical. Maybe this can be refactored?

  constNetworkF : Fin numberOfParties → Channel
  constNetworkF _ = Network

  NetworkF : Fin numberOfParties → Channel
  NetworkF k = Types.Network (paramsF k)

  NetworkF≡constNetworkF : ∀ {k} → NetworkF k ≡ constNetworkF k
  NetworkF≡constNetworkF = refl

  NetworkMessage-const : ∀ {k₁ k₂} → NetworkF k₁ ≡ NetworkF k₂
  NetworkMessage-const = refl

  IOF : Fin numberOfParties → Channel
  IOF k = Types.IO (paramsF k)

  AdvF : Fin numberOfParties → Channel
  AdvF k = Types.Adv (paramsF k)

  NodeF : (k : Fin numberOfParties) → Machine (NetworkF k) (IOF k ⊗ AdvF k)
  NodeF k = SingleNode.Node (paramsF k)

  -- network consisting only of honest nodes

  honestNodes : Machine (⨂ NetworkF) (⨂ IOF ⊗ ⨂ AdvF)
  honestNodes = ⨂ᴷ NodeF

  honestNodes' : Machine (⨂ constNetworkF) (⨂ IOF ⊗ ⨂ AdvF)
  honestNodes' = subst (λ c → Machine c (⨂ IOF ⊗ ⨂ AdvF))
                       (⨂≡ (λ {k} → NetworkF≡constNetworkF {k})) honestNodes

  open Network.BasicBroadcast numberOfParties NetworkMessage
    renaming (A to NetAdv; Network to NetFunctionality)

  honestNetwork : Machine I (⨂ IOF ⊗ (NetAdv ⊗ ⨂ AdvF))
  honestNetwork = honestNodes' ∘ᴷ NetFunctionality
