{-# OPTIONS --safe #-}

{- Module: Leios.Base
   
   This module defines core components for the base layer of Leios protocol.
   It includes stake distribution, ranking blocks, and base layer abstractions.
-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.VRF

module Leios.Base (a : LeiosAbstract) (open LeiosAbstract a) (vrf' : LeiosVRF a)
  (let open LeiosVRF vrf') where

open import Leios.Blocks a using (EndorserBlock)

StakeDistr : Type
StakeDistr = TotalMap PoolID ℕ

RankingBlock : Type
RankingBlock = These EndorserBlock (List Tx)

record BaseAbstract : Type₁ where
  field Cert : Type
        VTy : Type
        initSlot : VTy → ℕ
        V-chkCerts : List PubKey → EndorserBlock × Cert → Bool

  data Input : Type where
    INIT   : (EndorserBlock × Cert → Bool) → Input
    SUBMIT : RankingBlock → Input
    FTCH-LDG : Input

  data Output : Type where
    STAKE : StakeDistr → Output
    EMPTY : Output
    BASE-LDG : List RankingBlock → Output

  record Functionality : Type₁ where
    field State : Type
          _-⟦_/_⟧⇀_ : State → Input → Output → State → Type
          ⦃ Dec-_-⟦_/_⟧⇀_ ⦄ : {s : State} → {i : Input} → {o : Output} → {s' : State} → (s -⟦ i / o ⟧⇀ s') ⁇
          SUBMIT-total : ∀ {s b} → ∃[ s' ] s -⟦ SUBMIT b / EMPTY ⟧⇀ s'
          FTCH-total : ∀ {s} → ∃[ r ] (∃[ s' ] (s -⟦ FTCH-LDG / BASE-LDG r ⟧⇀ s'))

    open Input public
    open Output public
