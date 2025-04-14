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
    }

open import Leios.Short.Trace.Verifier params

private
  opaque
    unfolding List-Model

    test₁ : Bool
    test₁ = ¿ ValidTrace (inj₁ (IB-Role-Action 0 , SLOT) ∷ []) ¿ᵇ

    _ : test₁ ≡ true
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
            ∷ []
      in ¿ ValidTrace t ¿ᵇ

    _ : test₂ ≡ true
    _ = refl
