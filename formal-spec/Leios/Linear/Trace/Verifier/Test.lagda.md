## Trace verification examples
<!--
```agda
open import Prelude.Result
open import Leios.Prelude hiding (id)
open import Leios.Config
open import Leios.SpecStructure using (SpecStructure)
```
-->
```agda
module Leios.Linear.Trace.Verifier.Test where
private
```
#### Params
A test setup requires parameters, which are bundled in the `Params` record.
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
        (EB , 100) ∷ (VT , 100) ∷
        (EB , 102) ∷ (VT , 102) ∷
                     (VT , 106) ∷
        (EB , 107) ∷ (VT , 107) ∷
        (EB , 108) ∷ (VT , 108) ∷
        []
    }
```
#### Additional Linear Leios parameters
Linear Leios has the following three protocol parameters
```agda
  Lhdr = 2
  Lvote = 2
  Ldiff = 0
```
#### SpecStructure
In order to build a test trace, an implementation for the `SpecStructure` needs to be specified.
For the test trace, we rely on the implementation provided in `Leios.Defaults`.
```agda
  -- TODO: why does Hashable-EndorserBlock not work instead of hpe...?
  open import Leios.Defaults params using (d-SpecStructure; hpe)
  open SpecStructure d-SpecStructure hiding (Hashable-EndorserBlock)
```
#### TraceVerifier
```agda
  splitTxs : List Tx → List Tx × List Tx
  splitTxs l = [] , l

  validityCheckTime : EndorserBlock → ℕ
  validityCheckTime eb = 6

  open import Leios.Linear.Trace.Verifier d-SpecStructure params Lhdr Lvote Ldiff splitTxs validityCheckTime
```
<!--
```agda
  open Params params
  open Types params
  open GenFFD

  opaque
    unfolding List-Model
    unfolding isValid?
```
-->
EndorserBlocks that will be used in the test trace
```agda
    eb₀ eb₁ eb₂ : EndorserBlock
    eb₀ = mkEB 102 id tt (EB , tt) (3 ∷ 4 ∷ 5 ∷ []) [] []
    eb₁ = mkEB 100 (fsuc fzero) tt (EB , tt) (6 ∷ []) [] []
    eb₂ = mkEB 100 id tt (EB , tt) (0 ∷ 1 ∷ 2 ∷ []) [] []
```
Checking `hash` of EndorserBlocks
```agda
    verify-eb₀-hash : hash eb₀ ≡ 3 ∷ 4 ∷ 5 ∷ []
    verify-eb₀-hash = refl

    verify-eb₁-hash : hash eb₁ ≡ 6 ∷ []
    verify-eb₁-hash = refl

    verify-eb₂-hash : hash eb₂ ≡ 0 ∷ 1 ∷ 2 ∷ []
    verify-eb₂-hash = refl
```
RankingBlocks that will be used in the test trace
```agda
    rb₀ rb₁ rb₂ : RankingBlock
    rb₀ = record { txs = 3 ∷ 4 ∷ 5 ∷ [] ; announcedEB = nothing ; ebCert = nothing }
    rb₁ = record { txs = [] ; announcedEB = just (hash eb₁) ; ebCert = nothing }
    rb₂ = record { txs = [] ; announcedEB = nothing ; ebCert = just (6 ∷ []) }
```
Starting at slot 100
```agda
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
### Verify a test trace
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
```
#### Slot 107
```agda
                 ∷ (Base₂-Action      107 , inj₁ SLOT)
                 ∷ (Slot₂-Action      107 , inj₂ (inj₁ (BASE-LDG [ rb₂ ])))
                 ∷ []) s₁₀₀)
    test₁ = _
```
