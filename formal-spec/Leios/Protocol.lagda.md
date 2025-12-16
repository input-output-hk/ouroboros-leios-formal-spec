## Leios.Protocol

This module defines the core Leios protocol state machine, including:
- Input/output message types
- Protocol state representation and operations
- Block and transaction validation
- State transition logic for processing headers and block bodies
  The protocol integrates header/body diffusion with the underlying base protocol.
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.FFD
open import Leios.SpecStructure

module Leios.Protocol (⋯ : SpecStructure) (let open SpecStructure ⋯) (SlotUpkeep : Type) (StageUpkeep : Type) where

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open GenFFD
```
High level structure:
<pre>
                                       Linear Leios
                                       /         |
+-------------------------------------+          |
| Header Diffusion     Body Diffusion |          |
+-------------------------------------+       Base Protocol
                                       \      /
                                       Network
</pre>
```agda
data LeiosInput : Type where
  INIT     : VTy → LeiosInput
  SUBMIT   : EndorserBlock ⊎ List Tx → LeiosInput
  FFD-OUT  : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract) → LeiosInput
  SLOT     : LeiosInput
  FTCH-LDG : LeiosInput

data LeiosOutput : Type where
  FTCH-LDG : List Tx → LeiosOutput
  FFD-IN   : FFDAbstract.Input ffdAbstract → LeiosOutput
  EMPTY    : LeiosOutput

record LeiosState : Type where
  field V            : VTy
        SD           : StakeDistr
        RBs          : List RankingBlock
        ToPropose    : List Tx
        {- EBs': EBs together with the slot in which we received them
        -}
        EBs'         : List (ℕ × EndorserBlock)
        VotedEBs     : List Hash
        Vs           : List (List Vote)
        slot         : ℕ
        Upkeep       : List SlotUpkeep
        Upkeep-Stage : ℙ StageUpkeep
        votingState  : VotingState
        PubKeys      : List PubKey

  -- ideally we'd require a non-empty list, but this also works for now
  currentRB : RankingBlock
  currentRB = maybe (λ x → x) (record { txs = [] ; announcedEB = nothing ; ebCert = nothing })
                (head RBs)

  EBs : List EndorserBlock
  EBs = map proj₂ EBs'

  lookupEB : EBRef → Maybe EndorserBlock
  lookupEB r = find (λ b → getEBRef b ≟ r) EBs

  lookupTxs : EndorserBlock → List Tx
  lookupTxs eb = let open EndorserBlockOSig eb in txs

  lookupTxsC : Hash → List Tx
  lookupTxsC c = maybe lookupTxs [] $ lookupEB c

  Ledger : List Tx
  Ledger = flip L.concatMap RBs
    (λ rb → RankingBlock.txs rb L.++ maybe lookupTxsC [] (getEBHash <$> (RankingBlock.ebCert rb)))

  needsUpkeep : SlotUpkeep → Type
  needsUpkeep = _∉ˡ Upkeep

  needsUpkeep-Stage : StageUpkeep → Set
  needsUpkeep-Stage = _∉ Upkeep-Stage

  Dec-needsUpkeep-Stage : ∀ {u : StageUpkeep} → ⦃ DecEq StageUpkeep ⦄ → needsUpkeep-Stage u ⁇
  Dec-needsUpkeep-Stage {u} .dec = ¬? (u ∈? Upkeep-Stage)

  -- Produces a Vote certified block
  ebsWithCert : List (EndorserBlock × EBCert)
  ebsWithCert = mapMaybe getCert EBs
    where
      getCert : EndorserBlock → Maybe (EndorserBlock × EBCert)
      getCert eb = case ¿ isVoteCertified votingState eb ¿ of λ where
        (yes p) → just (eb , getEBCert p)
        (no ¬p) → nothing

addUpkeep : LeiosState → SlotUpkeep → LeiosState
addUpkeep s u = let open LeiosState s in record s { Upkeep = u ∷ Upkeep }
{-# INJECTIVE_FOR_INFERENCE addUpkeep #-}

addUpkeep-Stage : LeiosState → StageUpkeep → LeiosState
addUpkeep-Stage s u = let open LeiosState s in record s { Upkeep-Stage = Upkeep-Stage ∪ ❴ u ❵ }

initLeiosState : VTy → StakeDistr → List PubKey → LeiosState
initLeiosState V SD pks = record
  { V            = V
  ; SD           = SD
  ; RBs          = []
  ; ToPropose    = []
  ; EBs'         = []
  ; VotedEBs     = []
  ; Vs           = []
  ; slot         = initSlot V
  ; Upkeep       = []
  ; Upkeep-Stage = ∅
  ; votingState  = initVotingState
  ; PubKeys      = pks
  }

stake' : PoolID → LeiosState → ℕ
stake' pid record { SD = SD } = TotalMap.lookup SD pid

stake'' : PubKey → LeiosState → ℕ
stake'' pk = stake' (poolID pk)

stake : LeiosState → ℕ
stake = stake' id

lookupPubKeyAndStake : ∀ {B} → ⦃ _ : IsBlock B ⦄ → LeiosState → B → Maybe (PubKey × ℕ)
lookupPubKeyAndStake s b =
  L.head $
    L.map (λ pk → (pk , stake'' pk s)) $
      L.filter (λ pk → producerID b ≟ poolID pk) (LeiosState.PubKeys s)

module _ (s : LeiosState)  where

  record ebValid (eb : EndorserBlock) (pk : PubKey) (st : ℕ) : Type where
    field lotteryPfValid : verify pk (slotNumber eb) st (lotteryPf eb)
          signatureValid : verifySig pk (signature eb)
    -- TODO
    -- ibRefsValid : ?
    -- ebRefsValid : ?

  ebValid? : (eb : EndorserBlock) (pk : PubKey) (st : ℕ) → Dec (ebValid eb pk st)
  ebValid? h pk st
    with verify? pk (slotNumber h) st (lotteryPf h)
  ... | no ¬p = no (¬p ∘ ebValid.lotteryPfValid)
  ... | yes p
    with verifySig? pk (signature h)
  ... | yes q = yes (record { lotteryPfValid = p ; signatureValid = q })
  ... | no ¬q = no (¬q ∘ ebValid.signatureValid)

  -- TODO
  record vsValid (vs : List Vote) : Type where

  vsValid? : (vs : List Vote) → Dec (vsValid vs)
  vsValid? _ = yes record {}

  headerValid : Header → Type
  headerValid (ebHeader h)
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ebValid h pk (stake'' pk s)
  ... | nothing = ⊥
  headerValid (vtHeader h) = vsValid h

  headerValid? : (h : Header) → Dec (headerValid h)
  headerValid? (ebHeader h)
    with lookupPubKeyAndStake s h
  ... | just (pk , pid) = ebValid? h pk (stake'' pk s)
  ... | nothing = no λ x → x
  headerValid? (vtHeader h) = vsValid? h

  bodyValid : Body → Type
  bodyValid _ = ⊤

  bodyValid? : (b : Body) → Dec (bodyValid b)
  bodyValid? _ = yes tt

  opaque
    isValid : Header ⊎ Body → Type
    isValid (inj₁ h) = headerValid h
    isValid (inj₂ b) = bodyValid b

    isValid? : ∀ (x : Header ⊎ Body) → Dec (isValid x)
    isValid? (inj₁ h) = headerValid? h
    isValid? (inj₂ b) = bodyValid? b

module _ (s : LeiosState) where

  open LeiosState s

  {- Update the LeiosState upon receiving a message (a header or body) -}
  upd : Header ⊎ Body → LeiosState
  upd (inj₁ (ebHeader eb)) = record s { EBs' = (slot , eb) ∷ EBs' }
  upd (inj₁ (vtHeader vs)) = record s { Vs = vs ∷ Vs }
  upd (inj₂ _)             = s

module _ {s s'} where
  open LeiosState s'

  upd-preserves-Upkeep : ∀ {x} → LeiosState.Upkeep s ≡ LeiosState.Upkeep s'
                               → LeiosState.Upkeep s ≡ LeiosState.Upkeep (upd s' x)
  upd-preserves-Upkeep {inj₁ (ebHeader x)} refl = refl
  upd-preserves-Upkeep {inj₁ (vtHeader x)} refl = refl
  upd-preserves-Upkeep {inj₂ _} refl            = refl

infix 25 _↑_
_↑_ : LeiosState → List (Header ⊎ Body) → LeiosState
_↑_ = foldr (flip upd)

↑-preserves-Upkeep : ∀ {s x} → LeiosState.Upkeep s ≡ LeiosState.Upkeep (s ↑ x)
↑-preserves-Upkeep {x = []} = refl
↑-preserves-Upkeep {s = s} {x = x ∷ x₁} =
  upd-preserves-Upkeep {s = s} {x = x} (↑-preserves-Upkeep {x = x₁})

open import Leios.Abstract

open import CategoricalCrypto hiding (_∘_)
open import Leios.Config

open import Network.BasicBroadcast using (NetworkT; RcvMessage; SndMessage; Activate)

module Types (params : Params) (let open Params params) where

  Participant : Type
  Participant = Fin numberOfParties

  NetworkMessage : Type
  NetworkMessage = EndorserBlock ⊎ List Vote ⊎ RankingBlock

  Network : Channel
  Network = simpleChannel (NetworkT numberOfParties NetworkMessage)

  data IOT : Mode → Type where
    SubmitTxs : List Tx → IOT In
    FetchLdgI : IOT In
    FetchLdgO : List Tx → IOT Out

  -- mempool
  IO : Channel
  IO = simpleChannel IOT ᵀ

  Adv : Channel
  Adv = I

  module FFDA = FFDAbstract ffdAbstract

  data FFDT : Mode → Type where
    FFD-OUT : List (FFDA.Header ⊎ FFDA.Body) → FFDT Out
    FFD-IN  : FFDA.Input → FFDT In
    SLOT    : FFDT Out
    FTCH    : FFDT Out

  FFD : Channel
  FFD = simpleChannel FFDT ᵀ

  data BaseT : Mode → Type where
    FTCH-LDG : BaseT In
    SUBMIT   : RankingBlock → BaseT In
    BASE-LDG : List RankingBlock → BaseT Out

  BaseC : Channel
  BaseC = simpleChannel BaseT ᵀ
```
