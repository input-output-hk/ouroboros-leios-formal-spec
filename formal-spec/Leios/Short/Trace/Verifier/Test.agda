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
    ; stageLength = 5
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
              inj₁ (IB-Role-Action 0    , SLOT)
            ∷ inj₁ (EB-Role-Action 0 [] , SLOT)
            ∷ inj₁ (VT-Role-Action 0    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    0    , SLOT)
            ∷ inj₁ (IB-Role-Action 1    , SLOT)
            ∷ inj₁ (VT-Role-Action 1    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    1    , SLOT)
            ∷ inj₂ (IB-Recv-Update
                (record { header =
                  record { slotNumber = 1
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; bodyHash = 0 ∷ 1 ∷ 2 ∷ []
                         ; signature = tt
                         }
                        ; body = record { txs = 0 ∷ 1 ∷ 2 ∷ [] }}))
            ∷ []
      in ¿ ValidTrace t ¿ᵇ

    _ : test₂ ≡ true
    _ = refl
