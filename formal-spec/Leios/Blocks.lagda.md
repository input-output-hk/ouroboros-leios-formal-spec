## Leios.Blocks

This module defines the block structures used in the Leios protocol.
It provides implementations for Endorser Blocks, Votes,
and defines a Freshest First Delivery (FFD) for Leios Blocks.
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
open import Leios.Prelude
open import Leios.Abstract
open import Leios.FFD
open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Leios.Blocks (a : LeiosAbstract) (let open LeiosAbstract a) where

-- IsBlock typeclass (could do a closed-world approach instead)
-- Q: should votes have an instance of this class?
record IsBlock (B : Type) : Type where
  field slotNumber : B → ℕ
        producerID : B → PoolID
        lotteryPf  : B → VrfPf
        signature  : B → Sig

  infix 4 _∈ᴮ_

  _∈ᴮ_ : B → ℙ ℕ → Type
  b ∈ᴮ X = slotNumber b ∈ X

  areEquivocated : B → B → Type
  areEquivocated b b' = b ≢ b'
                      × slotNumber b ≡ slotNumber b'
                      × producerID b ≡ producerID b'

open IsBlock ⦃...⦄ public

EBRef = Hash
```
### Endorser Blocks
```agda
record EndorserBlockOSig (sig : Type) : Type where
  field slotNumber : ℕ
        producerID : PoolID
        lotteryPf  : VrfPf
        txs        : List Tx
        signature  : sig

EndorserBlock    = EndorserBlockOSig Sig
PreEndorserBlock = EndorserBlockOSig ⊤

instance
  Hashable-EndorserBlock : ⦃ Hashable PreEndorserBlock Hash ⦄ → Hashable EndorserBlock Hash
  Hashable-EndorserBlock .hash b = hash {T = PreEndorserBlock}
    record { EndorserBlockOSig b hiding (signature) ; signature = _ }

  IsBlock-EndorserBlock : IsBlock EndorserBlock
  IsBlock-EndorserBlock = record { EndorserBlockOSig }

unquoteDecl DecEq-EndorserBlockOSig = derive-DecEq ((quote EndorserBlockOSig , DecEq-EndorserBlockOSig) ∷ [])

mkEB : ⦃ Hashable PreEndorserBlock Hash ⦄ → ℕ → PoolID → VrfPf → PrivKey → List Tx → EndorserBlock
mkEB slot id π pKey txs = record { signature = sign pKey (hash b) ; EndorserBlockOSig b }
  where
    b : PreEndorserBlock
    b = record { slotNumber = slot
               ; producerID = id
               ; lotteryPf  = π
               ; txs        = txs
               ; signature  = _
               }

getEBRef : ⦃ Hashable PreEndorserBlock Hash ⦄ → EndorserBlock → EBRef
getEBRef = hash
```
### FFD for Leios Blocks
```agda
module GenFFD ⦃ _ : IsBlock (List Vote) ⦄ where
  data Header : Type where
    ebHeader : EndorserBlock → Header
    vtHeader : List Vote → Header

  Body = ⊤

  unquoteDecl DecEq-Header =
    derive-DecEq ((quote Header , DecEq-Header) ∷ [])

  ID : Type
  ID = ℕ × PoolID

  match : Header → Body → Type
  match _ _ = ⊥

  -- can we express uniqueness wrt pipelines as a property?
  msgID : Header → ID
  msgID (ebHeader h) = (slotNumber h , producerID h)
  msgID (vtHeader  h) = (slotNumber h , producerID h)

ffdAbstract : ⦃ _ : IsBlock (List Vote) ⦄ → FFDAbstract
ffdAbstract = record { GenFFD }
```
