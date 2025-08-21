## Trace verification examples

```agda
open import Prelude.Result
open import Leios.Prelude hiding (id)
open import Leios.Config

module Leios.Linear.Trace.Verifier.Test where
```
```agda
module _ where

  private
```
Parameters are as follows
```agda
    params : Params
    params =
      record
        { networkParams =
            record
              { numberOfParties = 2
              ; stakeDistribution =
                  let open FunTot (completeFin 2) (maximalFin 2)
                  in Fun⇒TotalMap (const 100000000)
              ; stageLength = 2
              ; ledgerQuality = 0
              ; lateIBInclusion = false
              }
        ; sutId = fzero
        ; winning-slots = fromList $
            (EB , 1) ∷ (VT , 1) ∷
            (EB , 2) ∷ (VT , 2) ∷
            (EB , 3) ∷ (VT , 3) ∷
            (EB , 4) ∷ (VT , 4) ∷
            (EB , 5) ∷ (VT , 5) ∷
                       (VT , 6) ∷
            (EB , 7) ∷ (VT , 7) ∷
            (EB , 8) ∷ (VT , 8) ∷
            []
      }

    Lvote = 2
    Ldiff = 0
```
```agda
    open import Leios.Linear.Trace.Verifier params Lvote Ldiff

    open Params params
    open Types params

    opaque
      unfolding List-Model
```
Initial state
```agda
      s₀ : LeiosState
      s₀ = initLeiosState tt stakeDistribution ((fzero , tt) ∷ (fsuc fzero , tt) ∷ [])
```
Check a simple trace
```agda
{-
      test₁ : IsOk $ verifyTrace (
                     (Slot-Action 0 , FFDT.FFD-OUT [])
                   ∷ (Base₁-Action 0 , FFDT.SLOT)
               --    ∷ (No-EB-Role-Action 0 , FFDT.SLOT)
                   ∷ []) s₀
      test₁ = _
-}      
```
### Linear Leios
```agda
module _ where

  private

    params : Params
    params =
      record
        { networkParams =
            record
              { numberOfParties = 2
              ; stakeDistribution =
                  let open FunTot (completeFin 2) (maximalFin 2)
                  in Fun⇒TotalMap (const 100000000)
              ; stageLength = 2
              ; ledgerQuality = 0
              ; lateIBInclusion = false
              }
        ; sutId = fzero
        ; winning-slots = fromList $
          (EB , 100) ∷ (VT , 100) ∷        
          (EB , 101) ∷ (VT , 101) ∷
          (EB , 102) ∷ (VT , 102) ∷
          (EB , 103) ∷ (VT , 103) ∷
          (EB , 104) ∷ (VT , 104) ∷
          (EB , 105) ∷ (VT , 105) ∷
                       (VT , 106) ∷
          (EB , 107) ∷ (VT , 107) ∷
          (EB , 108) ∷ (VT , 108) ∷
          []
      }

    Lvote = 2
    Ldiff = 0

    open Params params
    open import Leios.Linear.Trace.Verifier params Lvote Ldiff
    open Types params

    opaque
      unfolding List-Model
```
Starting at slot 100
```agda
      s₁₀₀ : LeiosState
      s₁₀₀ = record s₀ { slot = 100 }
        where
          s₀ : LeiosState
          s₀ = initLeiosState tt stakeDistribution ((fzero , tt) ∷ (fsuc fzero , tt) ∷ [])
```
Checking trace
```agda
      test₂ : IsOk (verifyTrace (L.reverse $
```
#### Slot 100, Stage 50
```agda
              --  (EB-Role-Action 100 {!!} , FFDT.SLOT)
              -- ∷ (VT-Role-Action 100 {!!} , FFDT.SLOT)
               (Base₂-Action    100 , FFDT.SLOT)
              -- ∷ (Slot-Action    100 , FFDT.FFD-OUT [])
```
#### Slot 101, Stage 50
```agda
--              ∷ (Base₂-Action  101    , FFDT.SLOT)
--              ∷ (Slot-Action    101    , FFDT.FFD-OUT [])
              ∷ []) s₁₀₀)
      test₂ = tt
```
