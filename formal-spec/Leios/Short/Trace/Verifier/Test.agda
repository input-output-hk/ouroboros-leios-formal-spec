open import Leios.Prelude hiding (id)

module Leios.Short.Trace.Verifier.Test where


numberOfParties : ℕ
numberOfParties = 2

SUT-id : Fin numberOfParties
SUT-id = fzero

open FunTot (completeFin numberOfParties) (maximalFin numberOfParties)

sd : TotalMap (Fin numberOfParties) ℕ
sd = Fun⇒TotalMap (const 100000000)

open import Leios.Short.Trace.Verifier numberOfParties SUT-id sd

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
            ∷ inj₁ (EB-Role-Action 1 [] , SLOT)
            ∷ inj₁ (VT-Role-Action 1    , SLOT)
            ∷ inj₁ (Base₂b-Action       , SLOT)
            ∷ inj₁ (Slot-Action    1    , SLOT)
            ∷ inj₂ (IB-Recv-Update
                (record { header =
                  record { slotNumber = 1
                         ; producerID = fsuc fzero
                         ; lotteryPf = tt
                         ; bodyHash = "0,1,2"
                         ; signature = tt
                         }
                        ; body = record { txs = 0 ∷ 1 ∷ 2 ∷ [] }}))
            ∷ []
      in ¿ ValidTrace t ¿ᵇ

    _ : test₂ ≡ true
    _ = refl
