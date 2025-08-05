## Trace verification examples

```agda
open import Prelude.Result
open import Leios.Prelude hiding (id)
open import Leios.Config

module Leios.Short.Trace.Verifier.Test where
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
            (IB , 1) ∷ (EB , 1) ∷ (VT , 1) ∷
            (IB , 2) ∷ (EB , 2) ∷ (VT , 2) ∷
            (IB , 3) ∷ (EB , 3) ∷ (VT , 3) ∷
            (IB , 4) ∷ (EB , 4) ∷ (VT , 4) ∷
            (IB , 5) ∷ (EB , 5) ∷ (VT , 5) ∷
                                  (VT , 6) ∷
            (IB , 7) ∷ (EB , 7) ∷ (VT , 7) ∷
            (IB , 8) ∷ (EB , 8) ∷ (VT , 8) ∷
            []
      }
```
```agda
    open Params params
    open import Leios.Short.Trace.Verifier params
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
      test₁ : IsOk $ verifyTrace (
                     (Slot-Action 0 , FFDT.FFD-OUT [])
                   ∷ (Base₂b-Action 0 , FFDT.SLOT)
                   ∷ (No-IB-Role-Action 0 , FFDT.SLOT)
                   ∷ []) s₀
      test₁ = _
```
Check IB validity
```agda
      test-valid-ib : Bool
      test-valid-ib =
        let h = record { slotNumber = 1
                       ; producerID = fsuc fzero
                       ; lotteryPf = tt
                       ; bodyHash = 0 ∷ 1 ∷ 2 ∷ []
                       ; signature = tt
                       }
            b = record { txs = 0 ∷ 1 ∷ 2 ∷ [] }
            ib = record { header = h ; body = b }
            pks = L.zip (completeFinL numberOfParties) (L.replicate numberOfParties tt)
            s = initLeiosState tt stakeDistribution pks
        in isYes (ibValid? s ib)

      _ : test-valid-ib ≡ true
      _ = refl
```
### Short Leios
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
          (IB , 101) ∷ (EB , 101) ∷ (VT , 101) ∷
          (IB , 102) ∷ (EB , 102) ∷ (VT , 102) ∷
          (IB , 103) ∷ (EB , 103) ∷ (VT , 103) ∷
          (IB , 104) ∷ (EB , 104) ∷ (VT , 104) ∷
          (IB , 105) ∷ (EB , 105) ∷ (VT , 105) ∷
                                    (VT , 106) ∷
          (IB , 107) ∷ (EB , 107) ∷ (VT , 107) ∷
          (IB , 108) ∷ (EB , 108) ∷ (VT , 108) ∷
          []
      }

    open Params params
    open import Leios.Short.Trace.Verifier params
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
                (No-IB-Role-Action 100 , FFDT.SLOT)
              ∷ (No-EB-Role-Action 100 , FFDT.SLOT)
              ∷ (No-VT-Role-Action 100 , FFDT.SLOT)
              ∷ (Base₂b-Action     100 , FFDT.SLOT)
              ∷ (Slot-Action       100 , FFDT.FFD-OUT [])
```
#### Slot 101, Stage 50
```agda
              ∷ (IB-Role-Action 101    , FFDT.SLOT)
              ∷ (Base₂b-Action  101    , FFDT.SLOT)
              ∷ (Slot-Action    101    , FFDT.FFD-OUT [])
```
#### Slot 102, Stage 51
```agda
              ∷ (IB-Role-Action 102    , FFDT.SLOT)
              ∷ (EB-Role-Action 102 [] [] , FFDT.SLOT)
              ∷ (VT-Role-Action 102    , FFDT.SLOT)
              ∷ (Base₂b-Action  102    , FFDT.SLOT)
              ∷ (Slot-Action    102    , FFDT.FFD-OUT (
                    inj₁ (GenFFD.ibHeader $
                          record { slotNumber = 101
                                 ; producerID = fsuc fzero
                                 ; lotteryPf = tt
                                 ; bodyHash = 0 ∷ 1 ∷ 2 ∷ []
                                 ; signature = tt
                                 })
                  ∷ inj₂ (GenFFD.ibBody $
                          record { txs = 0 ∷ 1 ∷ 2 ∷ [] })
                  ∷ [])
                )
```
#### Slot 103, Stage 51
```agda
              ∷ (IB-Role-Action 103    , FFDT.SLOT)
              ∷ (Base₂b-Action  103    , FFDT.SLOT)
              ∷ (Slot-Action    103    , FFDT.FFD-OUT (
                    inj₁ (GenFFD.ibHeader $
                          record { slotNumber = 102
                                 ; producerID = fsuc fzero
                                 ; lotteryPf = tt
                                 ; bodyHash = 3 ∷ 4 ∷ 5 ∷ []
                                 ; signature = tt
                                 })
                  ∷ inj₂ (GenFFD.ibBody $
                          record { txs = 3 ∷ 4 ∷ 5 ∷ [] })
                  ∷ [])
              )
```
#### Slot 104, Stage 52
```agda
              ∷ (IB-Role-Action 104    , FFDT.SLOT)
              ∷ (EB-Role-Action 104 [] [] , FFDT.SLOT)
              ∷ (VT-Role-Action 104    , FFDT.SLOT)
              ∷ (Base₂b-Action  104    , FFDT.SLOT)
              ∷ (Slot-Action    104    , FFDT.FFD-OUT [])
```
#### Slot 105, Stage 52
```agda
              ∷ (IB-Role-Action 105    , FFDT.SLOT)
              ∷ (Base₂b-Action  105    , FFDT.SLOT)
              ∷ (Slot-Action    105    , FFDT.FFD-OUT [])
```
#### Slot 106, Stage 53
```agda
              ∷ (No-IB-Role-Action 106 , FFDT.SLOT)
              ∷ (No-EB-Role-Action 106 , FFDT.SLOT)
              ∷ (VT-Role-Action    106 , FFDT.SLOT)
              ∷ (Base₂b-Action     106 , FFDT.SLOT)
              ∷ (Slot-Action       106 , FFDT.FFD-OUT [])
```
#### Slot 107, Stage 53
```agda
              ∷ (IB-Role-Action 107    , FFDT.SLOT)
              ∷ (Base₂b-Action  107    , FFDT.SLOT)
              ∷ (Slot-Action    107    , FFDT.FFD-OUT [])
```
#### Slot 108, Stage 54
```agda
              ∷ (IB-Role-Action 108    , FFDT.SLOT)
              ∷ (EB-Role-Action 108 ((3 ∷ 4 ∷ 5 ∷ []) ∷ []) [] , FFDT.SLOT)
              ∷ (VT-Role-Action 108    , FFDT.SLOT)
              ∷ (Base₂b-Action  108    , FFDT.SLOT)
              ∷ (Slot-Action    108    , FFDT.FFD-OUT [])
              ∷ []) s₁₀₀)
      test₂ = _
```
### Full Short Leios
* η > 0
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
              ; ledgerQuality = 10
              ; lateIBInclusion = false
              }
        ; sutId = fzero
        ; winning-slots = fromList $
          (IB , 101) ∷ (EB , 101) ∷ (VT , 101) ∷
          (IB , 102) ∷ (EB , 102) ∷ (VT , 102) ∷
          (IB , 103) ∷ (EB , 103) ∷ (VT , 103) ∷
          (IB , 104) ∷ (EB , 104) ∷ (VT , 104) ∷
          (IB , 105) ∷ (EB , 105) ∷ (VT , 105) ∷
                                    (VT , 106) ∷
          (IB , 107) ∷ (EB , 107) ∷ (VT , 107) ∷
          (IB , 108) ∷ (EB , 108) ∷ (VT , 108) ∷
          (IB , 109) ∷ (EB , 109) ∷ (VT , 109) ∷
          (IB , 110) ∷ (EB , 110) ∷ (VT , 110) ∷
          (IB , 111) ∷ (EB , 111) ∷ (VT , 111) ∷
          (IB , 112)              ∷ (VT , 112) ∷
          (IB , 113)              ∷ (VT , 113) ∷
          (IB , 114)              ∷ (VT , 114) ∷
          []
      }
```
```agda
    open Params params
    open import Leios.Short.Trace.Verifier params
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
      test : IsOk (verifyTrace (L.reverse $
```
#### Slot 100, Stage 50
```agda
                (No-IB-Role-Action 100 , FFDT.SLOT)
              ∷ (No-EB-Role-Action 100 , FFDT.SLOT)
              ∷ (No-VT-Role-Action 100 , FFDT.SLOT)
              ∷ (Base₂b-Action     100 , FFDT.SLOT)
              ∷ (Slot-Action       100 , FFDT.FFD-OUT [])
```
#### Slot 101
```agda
              ∷ (IB-Role-Action 101    , FFDT.SLOT)
              ∷ (Base₂b-Action  101    , FFDT.SLOT)
              ∷ (Slot-Action    101    , FFDT.FFD-OUT [])
```
#### Slot 102, Stage 51
The Leios state is updated by
* IB created in slot 101 by the other party
* EB created in slot 96 by the other party
```agda
              ∷ (IB-Role-Action 102    , FFDT.SLOT)
              ∷ (EB-Role-Action 102 [] [] , FFDT.SLOT)
              ∷ (VT-Role-Action 102    , FFDT.SLOT)
              ∷ (Base₂b-Action  102    , FFDT.SLOT)
              ∷ (Slot-Action    102    , FFDT.FFD-OUT (
                    inj₁ (GenFFD.ibHeader $
                          record { slotNumber = 101
                                 ; producerID = fsuc fzero
                                 ; lotteryPf = tt
                                 ; bodyHash = 0 ∷ 1 ∷ 2 ∷ []
                                 ; signature = tt
                                 })
                  ∷ inj₂ (GenFFD.ibBody $
                          record { txs = 0 ∷ 1 ∷ 2 ∷ [] })
                  ∷ inj₁ (GenFFD.ebHeader $
                          record { slotNumber = 96
                                 ; producerID = fsuc fzero
                                 ; lotteryPf = tt
                                 ; ibRefs = (10 ∷ 20 ∷ []) ∷ []
                                 ; ebRefs = []
                                 ; signature = tt
                                 })
                  ∷ [])
                )
```
#### Slot 103
The Leios state is updated by
* IB created in slot 102 by the other party
```agda
              ∷ (IB-Role-Action 103    , FFDT.SLOT)
              ∷ (Base₂b-Action  103    , FFDT.SLOT)
              ∷ (Slot-Action    103    , FFDT.FFD-OUT (
                    inj₁ (GenFFD.ibHeader $
                          record { slotNumber = 102
                                 ; producerID = fsuc fzero
                                 ; lotteryPf = tt
                                 ; bodyHash = 3 ∷ 4 ∷ 5 ∷ []
                                 ; signature = tt
                                 })
                  ∷ inj₂ (GenFFD.ibBody $
                          record { txs = 3 ∷ 4 ∷ 5 ∷ [] })
                  ∷ [])
                )
```
#### Slot 104, Stage 52
* EB created references EB created in slot 96 by the other party
```agda
              ∷ (IB-Role-Action 104    , FFDT.SLOT)
              ∷ (EB-Role-Action 104 []
                 (record { slotNumber = 96
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; ibRefs = (10 ∷ 20 ∷ []) ∷ []
                         ; ebRefs = []
                         ; signature = tt
                         } ∷ []) , FFDT.SLOT)
              ∷ (VT-Role-Action 104    , FFDT.SLOT)
              ∷ (Base₂b-Action  104    , FFDT.SLOT)
              ∷ (Slot-Action    104    , FFDT.FFD-OUT [])
```
#### Slot 105
```agda
              ∷ (IB-Role-Action 105    , FFDT.SLOT)
              ∷ (Base₂b-Action  105    , FFDT.SLOT)
              ∷ (Slot-Action    105    , FFDT.FFD-OUT [])
```
#### Slot 106, Stage 53
```agda
              ∷ (No-IB-Role-Action 106 , FFDT.SLOT)
              ∷ (No-EB-Role-Action 106 , FFDT.SLOT)
              ∷ (VT-Role-Action    106 , FFDT.SLOT)
              ∷ (Base₂b-Action     106 , FFDT.SLOT)
              ∷ (Slot-Action       106 , FFDT.FFD-OUT [])
```
#### Slot 107
The Leios state is updated by
* IB created in slot 105 by the other party
```agda
              ∷ (IB-Role-Action 107    , FFDT.SLOT)
              ∷ (Base₂b-Action  107    , FFDT.SLOT)
              ∷ (Slot-Action    107    , FFDT.FFD-OUT (
                    inj₁ (GenFFD.ibHeader $
                          record { slotNumber = 105
                                 ; producerID = fsuc fzero
                                 ; lotteryPf = tt
                                 ; bodyHash = 6 ∷ 7 ∷ []
                                 ; signature = tt
                                 })
                  ∷ inj₂ (GenFFD.ibBody $
                          record { txs = 6 ∷ 7 ∷ [] })
                  ∷ [])
                )
```
#### Slot 108, Stage 54
* EB created references EB created in slot 96 by the other party
* Receive EB created in slot 96 by the other party that references older EB
```agda
              ∷ (IB-Role-Action 108    , FFDT.SLOT)
              ∷ (EB-Role-Action 108 ((3 ∷ 4 ∷ 5 ∷ []) ∷ [])
                 (record { slotNumber = 96
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; ibRefs = (10 ∷ 20 ∷ []) ∷ []
                         ; ebRefs = []
                         ; signature = tt
                         } ∷ []) , FFDT.SLOT)
              ∷ (VT-Role-Action 108    , FFDT.SLOT)
              ∷ (Base₂b-Action  108    , FFDT.SLOT)
              ∷ (Slot-Action    108    , FFDT.FFD-OUT (
                    inj₁ (GenFFD.ebHeader $
                          record { slotNumber = 108
                                 ; producerID = fzero
                                 ; lotteryPf = tt
                                 ; ibRefs = (3 ∷ 4 ∷ 5 ∷ []) ∷ []
                                 ; ebRefs = (10 ∷ 20 ∷ []) ∷ []
                                 ; signature = tt
                                 })
                  ∷ [])
                )
```
#### Slot 109
```agda
              ∷ (IB-Role-Action 109    , FFDT.SLOT)
              ∷ (Base₂b-Action  109    , FFDT.SLOT)
              ∷ (Slot-Action    109    , FFDT.FFD-OUT [])
```
#### Slot 110, Stage 55
* Create EB referencing older EB
```agda
              ∷ (IB-Role-Action 110    , FFDT.SLOT)
              ∷ (EB-Role-Action 110 []
                 (record { slotNumber = 96
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; ibRefs = (10 ∷ 20 ∷ []) ∷ []
                         ; ebRefs = []
                         ; signature = tt
                         } ∷ []) , FFDT.SLOT)
              ∷ (VT-Role-Action 110    , FFDT.SLOT)
              ∷ (Base₂b-Action  110    , FFDT.SLOT)
              ∷ (Slot-Action    110    , FFDT.FFD-OUT [])
```
#### Slot 111
```agda
              ∷ (IB-Role-Action 111    , FFDT.SLOT)
              ∷ (Base₂b-Action  111    , FFDT.SLOT)
              ∷ (Slot-Action    111    , FFDT.FFD-OUT [])
```
#### Slot 112, Stage 56
* Send EB to underlying chain
```agda
              ∷ (IB-Role-Action 112    , FFDT.SLOT)
              ∷ (No-EB-Role-Action 112 , FFDT.SLOT)
              ∷ (VT-Role-Action 112    , FFDT.SLOT)
              ∷ (Base₂a-Action  112
                  record { slotNumber = 108
                         ; producerID = fzero
                         ; lotteryPf = tt
                         ; ibRefs = (3 ∷ 4 ∷ 5 ∷ []) ∷ []
                         ; ebRefs = (10 ∷ 20 ∷ []) ∷ []
                         ; signature = tt
                         }, FFDT.SLOT)
              ∷ (Slot-Action    112    , FFDT.FFD-OUT [])
```
#### Slot 113
* Send EB to underlying chain
```agda
              ∷ (IB-Role-Action 113    , FFDT.SLOT)
              ∷ (Base₂a-Action  113
                  record { slotNumber = 108
                         ; producerID = fzero
                         ; lotteryPf = tt
                         ; ibRefs = (3 ∷ 4 ∷ 5 ∷ []) ∷ []
                         ; ebRefs = (10 ∷ 20 ∷ []) ∷ []
                         ; signature = tt
                         }, FFDT.SLOT)
              ∷ (Slot-Action    113    , FFDT.FFD-OUT [])
```
#### Slot 114, Stage 57
```agda
              ∷ (IB-Role-Action 114    , FFDT.SLOT)
              ∷ (No-EB-Role-Action 114 , FFDT.SLOT)
              ∷ (VT-Role-Action 114    , FFDT.SLOT)
              ∷ (Base₂b-Action  114    , FFDT.SLOT)
              ∷ (Slot-Action    114    , FFDT.FFD-OUT [])
```
```agda
              ∷ []) s₁₀₀)
      test = _
```
