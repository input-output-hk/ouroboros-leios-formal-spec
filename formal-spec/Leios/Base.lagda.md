## Leios.Base

This module defines core components for the base layer of Leios protocol.
It includes stake distribution, ranking blocks, and base layer abstractions.
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.VRF

open import CategoricalCrypto hiding (id; _∘_)

module Leios.Base
  (a    : LeiosAbstract) (open LeiosAbstract a) 
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  where

open import Leios.Blocks a using (EndorserBlock; EBRef)

StakeDistr : Type
StakeDistr = TotalMap PoolID ℕ

record RankingBlock : Type where
  field txs         : List Tx
        announcedEB : Maybe Hash
        ebCert      : Maybe EBCert
        slot        : ℕ

record BaseAbstract : Type₁ where
  field Cert        : Type
        VTy         : Type
        initSlot    : VTy → ℕ
        V-chkCerts  : List PubKey → EndorserBlock × Cert → Bool
        BaseAdv     : Channel
        BaseMsg     : Type
        ⦃ DecEq-BaseMsg ⦄ : DecEq BaseMsg

  BaseNetwork = simpleChannel (λ _ → List BaseMsg)
```
Type family for communicating with the base functionality.
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
FTCH-SLOT: Request to fetch the current slot.

This input has no parameters and is used to query the current
slot of the base layer ledger.
```agda
    FTCH-SLOT : BaseIOF Out
```
The base layer can produce four types of outputs:
- Stake distribution information
- Empty response (no meaningful output)
- Base layer ledger contents
- Curreent slot of the base layer

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
SLOT: Output containing the current slot.

Parameters:
- ℕ: the current slot of the base machine. Should always be greater
or equal than the slot of the last processed block
```agda
    SLOT : ℕ → BaseIOF In
```

```agda
  open import Leios.Safety RankingBlock
  open import Data.Fin.Base using (_↑ˡ_)

  BaseIO = simpleChannel BaseIOF

  record BaseMachine : Type₂ where
    field m             : Machine BaseNetwork (BaseIO ⊗ BaseAdv)
          is-blockchain : IsBlockchain m

    open Machine m renaming (stepRel to _-⟦_/_⟧⇀_) public

--   module _
--     (numberOfParties     : ℕ)
--     (NAdv                : Channel)
--     (honestSpec          : BaseMachine)
--     (IOF AdvF : Fin numberOfParties → Channel)
--     (allNodes            : (p : Fin numberOfParties) → Machine BaseNetwork (IOF p ⊗ AdvF p))
--     (honestNodes         : ℙ (Fin numberOfParties))
--     (honest≡spec         : ∀ {p} → p ∈ honestNodes → allNodes p ≡ᴹ BaseMachine.m honestSpec)
--     (Net                 : Machine I (numberOfParties ⨂ⁿ BaseNetwork ⊗ NAdv))
--     (k                   : ℕ)
--     (Δ                   : ℕ)
--     (HonestStakeMajority : Type)
--     where

--     safetyBase : Type₁
--     safetyBase = Safety.safety
--           (BaseMachine.m honestSpec)
--           (BaseMachine.is-blockchain honestSpec)
--           IOF AdvF
--           allNodes
--           honestNodes
--           honest≡spec
--           Net
--           k
--           Δ
-- ```
