open import Leios.Prelude hiding (id)

module Leios.Trace.Verifier.Test where

open import Leios.Trace.Verifier 2 fzero
open import Leios.Defaults 2 fzero

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
