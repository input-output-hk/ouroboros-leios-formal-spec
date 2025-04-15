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
    ; ib-slots = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 7 ∷ 8 ∷ []
    ; eb-slots = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 7 ∷ 8 ∷ []
    ; vt-slots = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []
    }

open Params params
open import Leios.Short.Trace.Verifier params

private
  opaque
    unfolding List-Model

    test₁ : Bool
    test₁ = ¿ ValidTrace (inj₁ (IB-Role-Action 0 , SLOT) ∷ []) ¿ᵇ

    _ : test₁ ≡ true
    _ = refl

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

    test₂ : Bool
    test₂ =
      let t = L.reverse $
            -- slot 0
              inj₁ (IB-Role-Action 0    , SLOT)
            ∷ inj₁ (EB-Role-Action 0 [] , SLOT)
            ∷ inj₁ (VT-Role-Action 0    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    0    , SLOT)
            -- slot 1
            ∷ inj₁ (IB-Role-Action 1    , SLOT)
            ∷ inj₁ (VT-Role-Action 1    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    1    , SLOT)
            -- slot 2
            ∷ inj₂ (IB-Recv-Update
                (record { header =
                  record { slotNumber = 1
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; bodyHash = 0 ∷ 1 ∷ 2 ∷ []
                         ; signature = tt
                         }
                        ; body = record { txs = 0 ∷ 1 ∷ 2 ∷ [] }}))
            ∷ inj₁ (IB-Role-Action 2    , SLOT)
            ∷ inj₁ (EB-Role-Action 2 [] , SLOT)
            ∷ inj₁ (VT-Role-Action 2    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    2    , SLOT)
            -- slot 3
            ∷ inj₂ (IB-Recv-Update
                (record { header =
                  record { slotNumber = 2
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; bodyHash = 3 ∷ 4 ∷ 5 ∷ []
                         ; signature = tt
                         }
                        ; body = record { txs = 3 ∷ 4 ∷ 5 ∷ [] }}))
            ∷ inj₁ (IB-Role-Action 3    , SLOT)
            ∷ inj₁ (VT-Role-Action 3    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    3    , SLOT)
            -- slot 4
            ∷ inj₁ (IB-Role-Action 4    , SLOT)
            ∷ inj₁ (EB-Role-Action 4 [] , SLOT)
            ∷ inj₁ (VT-Role-Action 4    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    4    , SLOT)
            -- slot 5
            ∷ inj₁ (IB-Role-Action 5    , SLOT)
            ∷ inj₁ (VT-Role-Action 5    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    5    , SLOT)
            -- slot 6
            ∷ inj₁ (No-IB-Role-Action   , SLOT)
            ∷ inj₁ (No-EB-Role-Action   , SLOT)
            ∷ inj₁ (VT-Role-Action 6    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    6    , SLOT)
            -- slot 7
            ∷ inj₁ (IB-Role-Action 7    , SLOT)
            ∷ inj₁ (VT-Role-Action 7    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    7    , SLOT)
            -- slot 8
            ∷ inj₁ (IB-Role-Action 8    , SLOT)
            ∷ inj₁ (EB-Role-Action 8 ((3 ∷ 4 ∷ 5 ∷ []) ∷ []) , SLOT)
            ∷ inj₁ (VT-Role-Action 8    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    8    , SLOT)
            ∷ []
      in ¿ ValidTrace t ¿ᵇ

    _ : test₂ ≡ true
    _ = refl
