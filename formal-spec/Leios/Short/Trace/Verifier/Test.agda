open import Leios.Prelude hiding (id)
open import Leios.Config

module Leios.Short.Trace.Verifier.Test where

params : Params
params =
  record
    { numberOfParties = 2
    ; sutId = fzero
    ; stakeDistribution =
        let open FunTot (completeFin 2) (maximalFin 2)
        in Fun⇒TotalMap (const 100000000)
    ; stageLength = 2
    ; winning-slots = fromList $
        (IB , 1) ∷ (EB , 1) ∷ (VT , 1) ∷
        (IB , 2) ∷ (EB , 2) ∷ (VT , 2) ∷
        (IB , 3) ∷ (EB , 3) ∷ (VT , 3) ∷
        (IB , 4) ∷ (EB , 4) ∷ (VT , 4) ∷
        (IB , 5) ∷ (EB , 5) ∷ (VT , 5) ∷
                              (VT , 6) ∷
        (IB , 7) ∷ (EB , 7) ∷ (VT , 7) ∷
        (IB , 8) ∷ (EB , 8) ∷ (VT , 8) ∷
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

private
  opaque
    unfolding List-Model

    s₀ : LeiosState
    s₀ = initLeiosState tt stakeDistribution tt ((fzero , tt) ∷ (fsuc fzero , tt) ∷ [])

    test₁ : IsOk (verifyTrace (inj₁ (Slot-Action 0 , SLOT) ∷ inj₁ (Base₂b-Action 0 , SLOT) ∷ inj₁ (No-IB-Role-Action 0 , SLOT) ∷ []) s₀)
    test₁ = _

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
          s = initLeiosState tt stakeDistribution tt pks
      in isYes (ibValid? s ib)

    _ : test-valid-ib ≡ true
    _ = refl

    -- section of trace, slot 100 - 108

    s₁₀₀ : LeiosState
    s₁₀₀ = record s₀ { slot = 100 }

    test₂ : IsOk (verifyTrace (L.reverse $
            -- slot 100
              inj₁ (No-IB-Role-Action 100 , SLOT)
            ∷ inj₁ (No-EB-Role-Action 100 , SLOT)
            ∷ inj₁ (No-VT-Role-Action 100 , SLOT)
            ∷ inj₁ (Base₂b-Action     100 , SLOT)
            ∷ inj₁ (Slot-Action       100 , SLOT)
            -- slot 101
            ∷ inj₁ (IB-Role-Action 101    , SLOT)
            ∷ inj₁ (VT-Role-Action 101    , SLOT)
            ∷ inj₁ (Base₂b-Action  101    , SLOT)
            ∷ inj₁ (Slot-Action    101    , SLOT)
            -- slot 102
            ∷ inj₂ (IB-Recv-Update
                (record { header =
                  record { slotNumber = 101
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; bodyHash = 0 ∷ 1 ∷ 2 ∷ []
                         ; signature = tt
                         }
                        ; body = record { txs = 0 ∷ 1 ∷ 2 ∷ [] }}))
            ∷ inj₁ (IB-Role-Action 102    , SLOT)
            ∷ inj₁ (EB-Role-Action 102 [] , SLOT)
            ∷ inj₁ (VT-Role-Action 102    , SLOT)
            ∷ inj₁ (Base₂b-Action  102    , SLOT)
            ∷ inj₁ (Slot-Action    102    , SLOT)
            -- slot 103
            ∷ inj₂ (IB-Recv-Update
                (record { header =
                  record { slotNumber = 102
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; bodyHash = 3 ∷ 4 ∷ 5 ∷ []
                         ; signature = tt
                         }
                        ; body = record { txs = 3 ∷ 4 ∷ 5 ∷ [] }}))
            ∷ inj₁ (IB-Role-Action 103    , SLOT)
            ∷ inj₁ (VT-Role-Action 103    , SLOT)
            ∷ inj₁ (Base₂b-Action  103    , SLOT)
            ∷ inj₁ (Slot-Action    103    , SLOT)
            -- slot 104
            ∷ inj₁ (IB-Role-Action 104    , SLOT)
            ∷ inj₁ (EB-Role-Action 104 [] , SLOT)
            ∷ inj₁ (VT-Role-Action 104    , SLOT)
            ∷ inj₁ (Base₂b-Action  104    , SLOT)
            ∷ inj₁ (Slot-Action    104    , SLOT)
            -- slot 105
            ∷ inj₁ (IB-Role-Action 105    , SLOT)
            ∷ inj₁ (VT-Role-Action 105    , SLOT)
            ∷ inj₁ (Base₂b-Action  105    , SLOT)
            ∷ inj₁ (Slot-Action    105    , SLOT)
            -- slot 106
            ∷ inj₁ (No-IB-Role-Action 106 , SLOT)
            ∷ inj₁ (No-EB-Role-Action 106 , SLOT)
            ∷ inj₁ (VT-Role-Action    106 , SLOT)
            ∷ inj₁ (Base₂b-Action     106 , SLOT)
            ∷ inj₁ (Slot-Action       106 , SLOT)
            -- slot 107
            ∷ inj₁ (IB-Role-Action 107    , SLOT)
            ∷ inj₁ (VT-Role-Action 107    , SLOT)
            ∷ inj₁ (Base₂b-Action  107    , SLOT)
            ∷ inj₁ (Slot-Action    107    , SLOT)
            -- slot 108
            ∷ inj₁ (IB-Role-Action 108    , SLOT)
            ∷ inj₁ (EB-Role-Action 108 ((3 ∷ 4 ∷ 5 ∷ []) ∷ []) , SLOT)
            ∷ inj₁ (VT-Role-Action 108    , SLOT)
            ∷ inj₁ (Base₂b-Action  108    , SLOT)
            ∷ inj₁ (Slot-Action    108    , SLOT)
            ∷ []) s₁₀₀)
    test₂ = _
