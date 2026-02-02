## Leios.Base

This module defines core components for the base layer of Leios protocol.
It includes stake distribution, ranking blocks, and base layer abstractions.
<!--
```agda
-- {-# OPTIONS --safe #-}
```
-->
```agda
open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.VRF

open import CategoricalCrypto hiding (id; _∘_)

module Leios.Base (a : LeiosAbstract) (open LeiosAbstract a) (vrf' : LeiosVRF a)
  (let open LeiosVRF vrf') where

open import Leios.Blocks a using (EndorserBlock; EBRef)

StakeDistr : Type
StakeDistr = TotalMap PoolID ℕ

record RankingBlock : Type where
  field txs : List Tx
        announcedEB : Maybe Hash
        ebCert : Maybe EBCert

record BaseAbstract : Type₁ where
  field Cert : Type
        VTy : Type
        initSlot : VTy → ℕ
        V-chkCerts : List PubKey → EndorserBlock × Cert → Bool
        BaseNetwork BaseAdv : Channel
```
Type family for communicating with the base functionality.

The base layer can produce three types of outputs:
- Stake distribution information
- Empty response (no meaningful output)
- Base layer ledger contents
```agda
  data BaseIOF : Mode → Type where
```
INIT: Initialize the base layer with a certificate validation function.

Parameters:
- (EndorserBlock × Cert → Bool): A validation function that checks
  whether an endorser block and certificate pair is valid.
  Returns True if the pair is valid, False otherwise.
```agda
    INIT   : (EndorserBlock × Cert → Bool) → BaseIOF Out
```
SUBMIT: Submit a ranking block to the base layer for processing.

Parameters:
- RankingBlock: A ranking block containing either an endorser block,
  a list of transactions, or both (using the These type constructor).
  This represents new content to be added to the ledger.
```agda
    SUBMIT : RankingBlock → BaseIOF Out
```
FTCH-LDG: Request to fetch the current ledger state.

This input has no parameters and is used to query the current
state of the base layer ledger.
```agda
    FTCH-LDG : BaseIOF Out
```
The base layer can produce three types of outputs:
- Stake distribution information
- Empty response (no meaningful output)
- Base layer ledger contents

STAKE: Output containing the current stake distribution.

Parameters:
- StakeDistr: A total map from pool identifiers to their stake amounts (ℕ).
  This represents how stake is distributed across different pools
  in the system.
```agda
    STAKE : StakeDistr → BaseIOF In
```
EMPTY: Empty output indicating no meaningful result.

This output is used when an operation completes successfully
but produces no data that needs to be returned to the caller.
```agda
    EMPTY : BaseIOF In
```
BASE-LDG: Output containing the base layer ledger contents.

Parameters:
- List RankingBlock: A list of ranking blocks that constitute
  the current state of the base layer ledger. Each ranking block
  may contain endorser blocks, transactions, or both.
```agda
    BASE-LDG : List RankingBlock → BaseIOF In
```
```agda
  open import Leios.Safety
  open import Data.Fin.Base using (_↑ˡ_)

  BaseIO = simpleChannel BaseIOF

  record BaseMachine : Type₁ where
    field m              : Machine BaseNetwork (BaseIO ⊗ BaseAdv)
          IsBlockchain-m : IsBlockchain RankingBlock m
          -- TODO: how do we do this?
          -- SUBMIT-fun : IsFunction m (SUBMIT b) EMPTY
          -- FTCH-pfun : IsPureFunction m FTCH-LDG (BASE-LDG r)
    open Machine m renaming (stepRel to _-⟦_/_⟧⇀_) public

  data IsLeft {A : Set} {B : Set} : A ⊎ B → Set where
    isLeft : ∀ {x} → IsLeft (inj₁ x)

  module _
    (numberOfParties    : ℕ)
    (NAdv               : Channel)
    (honestSpec         : BaseMachine)
    (allNodes           : Fin numberOfParties → Machine BaseNetwork (BaseIO ⊗ BaseAdv))
    (honestNodes        : ℙ (Fin numberOfParties))
    (honest≡spec        : ∀ {p} → p ∈ honestNodes → allNodes p ≡ BaseMachine.m honestSpec)
    (honestIsBlockchain : ∀ {p} → p ∈ honestNodes → IsBlockchain RankingBlock (allNodes p))
    (Net                : Machine I (numberOfParties ⨂ⁿ BaseNetwork ⊗ NAdv))
    (k                  : ℕ)
    (Δ                  : ℕ)    
    where
    
    postulate
      HonestStakeMajority : Type

    safetyBase : Type 
    safetyBase = safety
          numberOfParties
          RankingBlock
          BaseIO
          BaseAdv
          NAdv 
          BaseNetwork
          (BaseMachine.m honestSpec)
          allNodes
          honestNodes
          honest≡spec
          honestIsBlockchain
          Net
          k
          Δ
```
