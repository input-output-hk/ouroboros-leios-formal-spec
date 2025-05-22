{-# OPTIONS --safe #-}

{- Module: Leios.Blocks
   
   This module defines the block structures used in the Leios protocol.
   It provides implementations for Input Blocks, Endorser Blocks, Votes, 
   and defines a Freshest First Delivery (FFD) for Leios Blocks.
-}

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

open IsBlock ⦃...⦄ public

IBRef = Hash
EBRef = Hash

--------------------------------------------------------------------------------
-- Input Blocks
--------------------------------------------------------------------------------

record IBHeaderOSig (sig : Type) : Type where
  field slotNumber : ℕ
        producerID : PoolID
        lotteryPf  : VrfPf
        bodyHash   : Hash
        signature  : sig

IBHeader    = IBHeaderOSig Sig
PreIBHeader = IBHeaderOSig ⊤

record IBBody : Type where
  field txs : List Tx

record InputBlock : Type where
  field header : IBHeader
        body   : IBBody

  open IBHeaderOSig header public

unquoteDecl DecEq-IBBody DecEq-IBHeaderOSig DecEq-InputBlock =
  derive-DecEq (
      (quote IBBody , DecEq-IBBody)
    ∷ (quote IBHeaderOSig , DecEq-IBHeaderOSig)
    ∷ (quote InputBlock , DecEq-InputBlock) ∷ [])

instance
  IsBlock-IBHeader : IsBlock IBHeader
  IsBlock-IBHeader = record { IBHeaderOSig }

  Hashable-IBBody : Hashable IBBody Hash
  Hashable-IBBody .hash b = hash (b .IBBody.txs)

  Hashable-IBHeader : ⦃ Hashable PreIBHeader Hash ⦄ → Hashable IBHeader Hash
  Hashable-IBHeader .hash b = hash {T = PreIBHeader}
    record { IBHeaderOSig b hiding (signature) ; signature = _ }

  IsBlock-InputBlock : IsBlock InputBlock
  IsBlock-InputBlock = record { InputBlock }

mkIBHeader : ⦃ Hashable PreIBHeader Hash ⦄ → ℕ → PoolID → VrfPf → PrivKey → List Tx → IBHeader
mkIBHeader slot id π pKey txs = record { signature = sign pKey (hash h) ; IBHeaderOSig h }
  where
    h : IBHeaderOSig ⊤
    h = record { slotNumber = slot
               ; producerID = id
               ; lotteryPf  = π
               ; bodyHash   = hash txs
               ; signature  = _
               }

getIBRef : ⦃ Hashable PreIBHeader Hash ⦄ → InputBlock → IBRef
getIBRef = hash ∘ InputBlock.header

--------------------------------------------------------------------------------
-- Endorser Blocks
--------------------------------------------------------------------------------

record EndorserBlockOSig (sig : Type) : Type where
  field slotNumber : ℕ
        producerID : PoolID
        lotteryPf  : VrfPf
        ibRefs     : List IBRef
        ebRefs     : List EBRef
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

mkEB : ⦃ Hashable PreEndorserBlock Hash ⦄ → ℕ → PoolID → VrfPf → PrivKey → List IBRef → List EBRef → EndorserBlock
mkEB slot id π pKey LI LE = record { signature = sign pKey (hash b) ; EndorserBlockOSig b }
  where
    b : PreEndorserBlock
    b = record { slotNumber = slot
               ; producerID = id
               ; lotteryPf  = π
               ; ibRefs     = LI
               ; ebRefs     = LE
               ; signature  = _
               }

getEBRef : ⦃ Hashable PreEndorserBlock Hash ⦄ → EndorserBlock → EBRef
getEBRef = hash

--------------------------------------------------------------------------------
-- Votes
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- FFD for Leios Blocks
--------------------------------------------------------------------------------

module GenFFD ⦃ _ : IsBlock (List Vote) ⦄ where
  data Header : Type where
    ibHeader : IBHeader → Header
    ebHeader : EndorserBlock → Header
    vtHeader : List Vote → Header

  data Body : Type where
    ibBody : IBBody → Body

  unquoteDecl DecEq-Header DecEq-Body =
    derive-DecEq ((quote Header , DecEq-Header) ∷ (quote Body , DecEq-Body) ∷ [])

  ID : Type
  ID = ℕ × PoolID

  matchIB : IBHeader → IBBody → Type
  matchIB h b = bodyHash ≡ hash b
    where open IBHeaderOSig h; open IBBody b

  matchIB? :  ∀ (h : IBHeader) → (b : IBBody) → Dec (matchIB h b)
  matchIB? h b = bodyHash ≟ hash b
    where open IBHeaderOSig h; open IBBody b

  match : Header → Body → Type
  match (ibHeader h) (ibBody b) = matchIB h b
  match _ _ = ⊥

  -- can we express uniqueness wrt pipelines as a property?
  msgID : Header → ID
  msgID (ibHeader h) = (slotNumber h , producerID h)
  msgID (ebHeader h) = (slotNumber h , producerID h) -- NOTE: this isn't in the paper
  msgID (vtHeader  h) = (slotNumber h , producerID h) -- NOTE: this isn't in the paper

ffdAbstract : ⦃ _ : IsBlock (List Vote) ⦄ → FFDAbstract
ffdAbstract = record { GenFFD }
