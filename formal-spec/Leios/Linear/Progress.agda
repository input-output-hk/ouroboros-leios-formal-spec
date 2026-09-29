{-# OPTIONS --safe #-}

open import Leios.Config
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.SpecStructure

open import CategoricalCrypto hiding (id; _∘_; eval)
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Ext

open import Data.Nat.Properties
import Data.Maybe.Relation.Unary.All as Maybe

-- Progress for the bare Linear Leios node.  Safety and liveness are stated
-- as `Invariant`s, i.e. preservation along `Trace`s, so they say nothing
-- unless enough traces exist; `enough-traces` shows that from any state
-- whose slot upkeep is complete every future slot is reachable.  The
-- inputs (network messages, ledger, certificate answers) are chosen by the
-- trace, so this is a witness of progress, not a liveness argument for a
-- composite deployment.
module Leios.Linear.Progress (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params) where

open import Leios.Linear ⋯ params
open Types params

open LeiosState

private variable
  s s' : LeiosState

↝-slot : ∀ {i} → s ↝ (s' , i) → slot s' ≡ slot s
↝-slot (EB-Role _) = refl
↝-slot (VT-Role _) = refl

private
  allDone-of : ∀ s → Upkeep s ≡ VT-Role ∷ Base ∷ CertCheck ∷ EB-Role ∷ [] → allDone s
  allDone-of s eq = has s eq (here refl)
                  , has s eq (there (there (there (here refl))))
                  , has s eq (there (here refl))
                  , has s eq (there (there (here refl)))

  Base∉ : Base ∉ˡ EB-Role ∷ []
  Base∉ (here ())
  Base∉ (there ())

  CertCheck∉ : CertCheck ∉ˡ EB-Role ∷ []
  CertCheck∉ (here ())
  CertCheck∉ (there ())

  Base∉′ : Base ∉ˡ CertCheck ∷ EB-Role ∷ []
  Base∉′ (here ())
  Base∉′ (there p) = Base∉ p

  VT-Role∉ : VT-Role ∉ˡ Base ∷ CertCheck ∷ EB-Role ∷ []
  VT-Role∉ (here ())
  VT-Role∉ (there (here ()))
  VT-Role∉ (there (there (here ())))
  VT-Role∉ (there (there (there ())))

upkeep-step : ∀ s u → u ≢ Base → u ≢ CertCheck → needsUpkeep s u
            → ∃[ s' ] ∃[ o ] (s -⟦ ((ϵ ⊗R) ⊗R) ⊗R ↑ᵢ SLOT / o ⟧⇀ s')
                    × Upkeep s' ≡ u ∷ Upkeep s
                    × slot s' ≡ slot s
upkeep-step s u u≢Base u≢CertCheck nu with ¿ ∃[ s'×i ] (s ↝ s'×i × (u ∷ Upkeep s) ≡ Upkeep (proj₁ s'×i)) ¿
... | yes ((s' , inj₁ i) , st , eq) = s' , _ , Roles₁ st , sym eq , ↝-slot st
... | yes ((s' , inj₂ v) , st , eq) = s' , _ , Vote₁ st , sym eq , ↝-slot st
... | no ¬p                         = addUpkeep s u , _ , Roles₂ (¬p , nu , u≢Base , u≢CertCheck) , refl , refl

-- When the tip calls for a certificate, the trace answers `Base₃`'s query
-- with `CERT nothing`, which `Cert₁` accepts for any request.
base-step : ∀ s → Upkeep s ≡ EB-Role ∷ []
          → ∃[ s' ] Trace LinearLeios s s'
                  × Upkeep s' ≡ Base ∷ CertCheck ∷ EB-Role ∷ []
                  × slot s' ≡ slot s
base-step s eq with certRequest s in eqc
... | nothing =
  _ , ([] ∷ʳ⟨ _ , _ , Base₂ (needs s eq Base∉ , needs s eq CertCheck∉ , has s eq (here refl) , eqc) ⟩)
    , cong (λ l → Base ∷ CertCheck ∷ l) eq , refl
... | just eb =
  let s₁ = record (addUpkeep s CertCheck) { PendingQuery = just (hash eb) }
  in _ , (([] ∷ʳ⟨ _ , _ , Base₃ (needs s eq CertCheck∉ , has s eq (here refl) , eqc) ⟩)
            ∷ʳ⟨ _ , _ , Cert₁ {c = nothing}
                  (needs s₁ (cong (CertCheck ∷_) eq) Base∉′ , here refl , eqc , refl , Maybe.nothing) ⟩)
       , cong (λ l → Base ∷ CertCheck ∷ l) eq , refl

-- The EB role goes first, because `Base₂` and `Base₃` require it settled.
upkeep : ∀ s → Upkeep s ≡ []
       → ∃[ s' ] Trace LinearLeios s s' × allDone s' × slot s' ≡ slot s
upkeep s eq₀ =
  let s₃ , _ , st₃ , eq₃ , sl₃ = upkeep-step s EB-Role (λ ()) (λ ()) (needs s eq₀ λ ())
      s₄ , t₄ , eq₄ , sl₄ = base-step s₃ (trans eq₃ (cong (EB-Role ∷_) eq₀))

      s₅ , _ , st₅ , eq₅ , sl₅ = upkeep-step s₄ VT-Role (λ ()) (λ ()) (needs s₄ eq₄ VT-Role∉)
  in s₅
   , Trace-trans ([] ∷ʳ⟨ _ , _ , st₃ ⟩) (t₄ ∷ʳ⟨ _ , _ , st₅ ⟩)
   , allDone-of s₅ (trans eq₅ (cong (VT-Role ∷_) eq₄))
   , trans sl₅ (trans sl₄ sl₃)

slot-step : ∀ s msgs rbs → allDone s
          → ∃[ s' ] Trace LinearLeios s s' × Upkeep s' ≡ [] × slot s' ≡ suc (slot s)
slot-step s msgs rbs done =
  _ , (([] ∷ʳ⟨ _ , _ , Slot₁ {s = s} {msgs = msgs} done ⟩) ∷ʳ⟨ _ , _ , Slot₂ {rbs = rbs} ⟩) , refl , refl

tick : ∀ s msgs rbs → allDone s
     → ∃[ s' ] Trace LinearLeios s s' × allDone s' × slot s' ≡ suc (slot s)
tick s msgs rbs done =
  let s₂ , t₂ , up₂ , sl₂ = slot-step s msgs rbs done
      s' , t' , done' , sl' = upkeep s₂ up₂
  in s' , Trace-trans t₂ t' , done' , trans sl' sl₂

ticks : ∀ n s (msgsAt : ℕ → List (FFDA.Header ⊎ FFDA.Body)) (rbsAt : ℕ → List RankingBlock)
      → allDone s
      → ∃[ s' ] Trace LinearLeios s s' × allDone s' × slot s' ≡ n + slot s
ticks zero    s _      _     done = s , [] , done , refl
ticks (suc n) s msgsAt rbsAt done =
  let s₁ , t₁ , done₁ , sl₁ = tick s (msgsAt (slot s)) (rbsAt (slot s)) done
      s' , t' , done' , sl' = ticks n s₁ msgsAt rbsAt done₁
  in s' , Trace-trans t₁ t' , done' , trans sl' (trans (cong (n +_) sl₁) (+-suc n _))

enough-traces : ∀ s n → allDone s → ∃[ s' ] slot s + n ≡ slot s' × Trace LinearLeios s s'
enough-traces s n done =
  let s' , t , _ , eq = ticks n s (λ _ → []) (λ _ → []) done
  in s' , trans (+-comm (slot s) n) (sym eq) , t
