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

          (EB , 102) ∷
                       (VT , 106) ∷
          (EB , 107) ∷ (VT , 107) ∷
          (EB , 108) ∷ (VT , 108) ∷
          []
      }

    Lhdr = 2
    Lvote = 2
    Ldiff = 0

    open Params params
    open import Leios.Linear.Trace.Verifier params
    open GenFFD

    splitTxs : List Tx → List Tx × List Tx
    splitTxs l = [] , l

    validityCheckTime : EndorserBlock → ℕ
    validityCheckTime eb = 6

    open Defaults Lhdr Lvote Ldiff splitTxs validityCheckTime
    open Types params

    opaque
      unfolding List-Model
```
Starting at slot 100
```agda
      eb₀ eb₁ eb₂ : EndorserBlock
      eb₀ = mkEB 102 id tt (EB , tt) (3 ∷ 4 ∷ 5 ∷ []) [] []
      eb₁ = mkEB 100 (fsuc fzero) tt (EB , tt) (6 ∷ []) [] []
      eb₂ = mkEB 100 id tt (EB , tt) (0 ∷ 1 ∷ 2 ∷ []) [] []

      rb₀ rb₁ : RankingBlock
      rb₀ = record { txs = 3 ∷ 4 ∷ 5 ∷ [] ; announcedEB = nothing ; ebCert = nothing }
      rb₁ = record { txs = [] ; announcedEB = just (hash eb₁) ; ebCert = nothing }

      verify-eb₀-hash : hash eb₀ ≡ 3 ∷ 4 ∷ 5 ∷ []
      verify-eb₀-hash = refl

      verify-eb₁-hash : hash eb₁ ≡ 6 ∷ []
      verify-eb₁-hash = refl

      s₁₀₀ : LeiosState
      s₁₀₀ = record s₀
               { slot = 100
               ; ToPropose = 0 ∷ 1 ∷ 2 ∷ []
               ; PubKeys = (fzero , tt) ∷ (fsuc fzero , tt) ∷ []
               }
        where
          s₀ : LeiosState
          s₀ = initLeiosState tt stakeDistribution ((fzero , tt) ∷ (fsuc fzero , tt) ∷ [])

```
Checking a simple trace
```agda
      test₁ : IsOk (verifyTrace (L.reverse $
```
#### Slot 100
```agda
                     (EB-Role-Action    100 eb₂ , inj₁ SLOT)
                   ∷ (Base₁-Action      100 , inj₂ (inj₂ (SubmitTxs (3 ∷ 4 ∷ 5 ∷ []))))
                   ∷ (Base₂-Action      100 , inj₁ SLOT)
                   ∷ (Slot₂-Action      100 , inj₂ (inj₁ (BASE-LDG [ rb₀ ])))
                   ∷ (No-VT-Role-Action 100 , inj₁ SLOT)
                   ∷ (Slot₁-Action      100 , inj₁ (FFD-OUT []))
```
#### Slot 101
```agda
                   ∷ (Base₂-Action      101 , inj₁ SLOT)
                   ∷ (No-EB-Role-Action 101 , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 101 , inj₁ SLOT)
                   ∷ (Slot₂-Action      101 , inj₂ (inj₁ (BASE-LDG [ rb₁ ])))
                   ∷ (Slot₁-Action      101 , inj₁ (FFD-OUT (inj₁ (ebHeader eb₁) ∷ [])))
```
#### Slot 102
```agda
                   ∷ (Base₂-Action      102 , inj₁ SLOT)
                   ∷ (EB-Role-Action    102 eb₀ , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 102 , inj₁ SLOT)
                   ∷ (Slot₁-Action      102 , inj₁ (FFD-OUT []))
```
#### Slot 103
```agda
                   ∷ (Base₂-Action      103 , inj₁ SLOT)
                   ∷ (No-EB-Role-Action 103 , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 103 , inj₁ SLOT)
                   ∷ (Slot₁-Action      103 , inj₁ (FFD-OUT []))
```
#### Slot 104
```agda
                   ∷ (Base₂-Action      104 , inj₁ SLOT)
                   ∷ (No-EB-Role-Action 104 , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 104 , inj₁ SLOT)
                   ∷ (Slot₁-Action      104 , inj₁ (FFD-OUT []))
```
#### Slot 105
```agda
                   ∷ (Base₂-Action      105 , inj₁ SLOT)
                   ∷ (No-EB-Role-Action 105 , inj₁ SLOT)
                   ∷ (No-VT-Role-Action 105 , inj₁ SLOT)
                   ∷ (Slot₁-Action      105 , inj₁ (FFD-OUT []))
```
#### Slot 106
```agda
                   ∷ (Base₂-Action      106 , inj₁ SLOT)
                   ∷ (No-EB-Role-Action 106 , inj₁ SLOT)
                   ∷ (VT-Role-Action    106 eb₁ 102 , inj₁ SLOT)
                   ∷ (Slot₁-Action      106 , inj₁ (FFD-OUT []))
                   ∷ []) s₁₀₀)
      test₁ = _
```
