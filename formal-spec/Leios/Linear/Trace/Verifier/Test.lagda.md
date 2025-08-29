## Trace verification examples
<!--
```agda
open import Prelude.Result
open import Leios.Prelude hiding (id)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)

module Leios.Linear.Trace.Verifier.Test where
```
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

    Lhdr = 0
    Lvote = 2
    Ldiff = 0

    open Params params
    open import Leios.Linear.Trace.Verifier params
    open GenFFD

    splitTxs : List Tx → List Tx × List Tx
    splitTxs l = [] , l

    validityCheckTime : EndorserBlock → ℕ
    validityCheckTime eb = 0

    open Defaults Lhdr Lvote Ldiff splitTxs validityCheckTime
    open Types params

    opaque
      unfolding List-Model
```
Starting at slot 100
```agda
      s₁₀₀ : LeiosState
      s₁₀₀ = record s₀
               { slot = 100
               ; ToPropose = 0 ∷ 1 ∷ 2 ∷ []
               ; EBs' = []
               }
        where
          s₀ : LeiosState
          s₀ = initLeiosState tt stakeDistribution ((fzero , tt) ∷ (fsuc fzero , tt) ∷ [])

      mkRB : LeiosState → RankingBlock
      mkRB s = record
                 { txs = []
                 ; announcedEB = hash <$> toProposeEB s tt
                 ; ebCert = nothing
                 }
```
Checking a simple trace
```agda
      test₁ : IsOk (verifyTrace (L.reverse $
```
#### Slot 100
```agda
                     (EB-Role-Action    100 (mkEB 100 id tt (EB , tt) (0 ∷ 1 ∷ 2 ∷ []) [] []) , inj₁ SLOT)
                   ∷ (Base₁-Action      100 , inj₂ (inj₂ (SubmitTxs (3 ∷ 4 ∷ 5 ∷ []))))
                   ∷ (Base₂-Action      100 , inj₁ SLOT)
                   ∷ (Slot₂-Action      100 , inj₂ (inj₁ (BASE-LDG [ mkRB s₁₀₀ ])))
                   ∷ (No-VT-Role-Action 100 , inj₁ SLOT)
                   ∷ (Slot₁-Action      100 , inj₁ (FFD-OUT []))
```
#### Slot 101
```agda
                   ∷ (Base₂-Action      101 , inj₁ SLOT)
                   ∷ (No-EB-Role-Action 101 , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 101 , inj₁ SLOT)
                   ∷ (Slot₂-Action      101 , inj₂ (inj₁ (BASE-LDG [ record { txs = [] ; announcedEB = just (hash $ mkEB 100 (fsuc fzero) tt (EB , tt) (0 ∷ []) [] []) ; ebCert = nothing } ])))
                   ∷ (Slot₁-Action      101 , inj₁ (FFD-OUT (inj₁ (ebHeader (mkEB 100 (fsuc fzero) tt (EB , tt) (0 ∷ []) [] [])) ∷ [])))
```
#### Slot 102
```agda
                   ∷ (Base₂-Action      102 , inj₁ SLOT)
                   ∷ (EB-Role-Action    102 (mkEB 102 id tt (EB , tt) (3 ∷ 4 ∷ 5 ∷ []) [] []) , inj₁ SLOT)
              --     ∷ (VT-Role-Action    102 (mkEB 100 (fsuc fzero) tt (EB , tt) (0 ∷ []) [] []) , inj₁ SLOT) -- 101 < 100 + 2
              --     ∷ (Slot₁-Action      102 , inj₁ (FFD-OUT []))
                   ∷ []) s₁₀₀)
      test₁ = _
```
