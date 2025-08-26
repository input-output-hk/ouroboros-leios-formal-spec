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
          (EB , 100) ∷

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
      eb : EndorserBlock
      eb = mkEB 100 id tt (EB , tt) (0 ∷ 1 ∷ 2 ∷ []) [] []

      mkRB : LeiosState → RankingBlock
      mkRB s = record
                 { txs = []
                 ; announcedEB = hash <$> toProposeEB s tt
                 ; ebCert = nothing
                 }

      s₁₀₀ : LeiosState
      s₁₀₀ = record s₀
               { slot = 100
               ; ToPropose = 0 ∷ 1 ∷ 2 ∷ []
               ; EBs' = (90 , eb) ∷ []
               }
        where
          s₀ : LeiosState
          s₀ = initLeiosState tt stakeDistribution ((fzero , tt) ∷ (fsuc fzero , tt) ∷ [])
```
Checking trace
```agda
      test₂ : IsOk (verifyTrace (L.reverse $
```
#### Slot 100
```agda
                     (EB-Role-Action    100 eb , inj₁ SLOT)
                   ∷ (Base₂-Action      100    , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 100    , inj₁ SLOT)
                   ∷ (Slot₂-Action      100    , inj₂ (BASE-LDG [ mkRB s₁₀₀ ]))
                   ∷ (Slot₁-Action      100    , inj₁ (FFD-OUT []))
```
#### Slot 101
```agda
                   ∷ (Base₂-Action      101    , inj₁ SLOT)
                   ∷ (No-EB-Role-Action 101    , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 101    , inj₁ SLOT)
                   ∷ (Slot₁-Action      101    , inj₁ (FFD-OUT []))
                   ∷ []) s₁₀₀)
      test₂ = _
```
