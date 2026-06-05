{-# OPTIONS --safe #-}

-- ============================================================================
-- A PARTIAL `TraceCat` instance at trace equivalence `_≈ᵗ_`.
--
-- Illustrative artifact (NOT wired into the proofs; kept out of the everything-
-- file).  It pins down exactly which `TraceCat` obligations categorical-crypto
-- already discharges, and which are still open — i.e. precisely what "fixing the
-- MachineCategory so we can use it here" must deliver.  Postulate-free and
-- `--safe`: the OPEN obligations are taken as module PARAMETERS (so this module
-- *is* the interface a `≈ᵗ`-based MachineCategory has to implement); the FILLED
-- ones are supplied from categorical-crypto in the body.
--
-- Why `_≈ᵗ_` and NOT the library `MachineCategory`:
--   * `MachineCategory`'s equality is `_≈ℰ_ : … → Type₁` — a universe too high
--     to even inhabit `TraceCat._≈_ : … → Type`; and being state-sensitive its
--     monoidal laws are FALSE there (they hold only via postulated MaybeHomLaws).
--   * trace equivalence `_≈ᵗ_ : … → Type` is the intended layer, state-agnostic,
--     so the laws are GENUINELY true once proven.
--
--   FILLED in the body — already in categorical-crypto:
--     _≈_, ≈-refl/sym/trans         — Machine.TraceEquiv  (proven)
--     σ, α⇒, α⇐, ρ⇒, ρ⇐, λ⇒, λ⇐     — Machine.Monoidal    (real forwarding machines)
--   PARAMETERS — the OPEN `≈ᵗ` obligations ("fix MachineCategory at ≈ᵗ"):
--     ∘-resp-≈, ⊗₁-resp-≈, ⨂ᴷ-cong-≈, ∘-identityˡ, assoc²γδ, env-absorb, and the
--     7 iso laws  — exactly `Machine.Monoidal.MonoidalLaws` + the protocol absorb,
--     all provable at `≈ᵗ` via one compositional lemma on `traces`.
--   PARAMETERS — genuinely new (no categorical source):
--     Reachable, ≈-Reachable        — observation semantics over traces.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto
import CategoricalCrypto as CC
open import CategoricalCrypto.Machine.TraceEquiv using (_≈ᵗ_; ≈ᵗ-refl; ≈ᵗ-sym; ≈ᵗ-trans)
import CategoricalCrypto.Machine.Monoidal as Mon
import Blockchain.Safety.TransferTrace as STT

module Blockchain.Safety.TraceCatPartial
  (n : ℕ)
  -- ── OPEN ≈ᵗ obligations: what a `≈ᵗ`-based MachineCategory must discharge
  (∘-resp-≈ᵗ : ∀ {A B C} {M M' : Machine B C} {N N' : Machine A B}
             → M ≈ᵗ M' → N ≈ᵗ N' → (M ∘ N) ≈ᵗ (M' ∘ N'))
  (⊗₁-resp-≈ᵗ : ∀ {A B C D} {M M' : Machine A B} {N N' : Machine C D}
             → M ≈ᵗ M' → N ≈ᵗ N' → (M ⊗₁ N) ≈ᵗ (M' ⊗₁ N'))
  (⨂ᴷ-cong-≈ᵗ : ∀ {m} {A B E : Fin m → Channel}
                {f g : (k : Fin m) → Machine (A k) (B k ⊗₀ E k)}
             → (∀ k → f k ≈ᵗ g k) → ⨂ᴷ f ≈ᵗ ⨂ᴷ g)
  (∘-identityˡᵗ : ∀ {A B} {M : Machine A B} → (id ∘ M) ≈ᵗ M)
  (assoc²γδᵗ : ∀ {A B C D E} {f : Machine A B} {g : Machine B C} {h : Machine C D} {i : Machine D E}
             → ((i ∘ h) ∘ (g ∘ f)) ≈ᵗ (i ∘ ((h ∘ g) ∘ f)))
  (env-absorbᵗ : ∀ {m} {A Network NAdv : Channel} {B E B' E' : Fin m → Channel}
       (Env   : Machine (⨂ B' ⊗₀ (NAdv ⊗₀ ⨂ E')) A)
       (extN  : (p : Fin m) → Machine Network (B' p ⊗₀ E' p))
       (lay   : (p : Fin m) → Machine (B p ⊗₀ E p) (B' p ⊗₀ E' p))
       (baseN : (p : Fin m) → Machine Network (B p ⊗₀ E p))
       (net   : Machine I (m ⨂ⁿ Network ⊗₀ NAdv))
       → (∀ p → extN p ≈ᵗ (lay p ∘ baseN p))
       → Σ[ Env' ∈ Machine (⨂ B ⊗₀ (NAdv ⊗₀ ⨂ E)) A ]
            ((Env ∘ CC._∘ᴷ_ (⨂ᴷ extN) net) ≈ᵗ (Env' ∘ CC._∘ᴷ_ (⨂ᴷ baseN) net)))
  (α-isoˡᵗ : ∀ {A B C} → (Mon.α⇒ {A} {B} {C} ∘ Mon.α⇐) ≈ᵗ id)
  (α-isoʳᵗ : ∀ {A B C} → (Mon.α⇐ {A} {B} {C} ∘ Mon.α⇒) ≈ᵗ id)
  (ρ-isoˡᵗ : ∀ {A}     → (Mon.ρ⇒ {A} ∘ Mon.ρ⇐) ≈ᵗ id)
  (ρ-isoʳᵗ : ∀ {A}     → (Mon.ρ⇐ {A} ∘ Mon.ρ⇒) ≈ᵗ id)
  (λ-isoˡᵗ : ∀ {A}     → (Mon.λ⇒ {A} ∘ Mon.λ⇐) ≈ᵗ id)
  (λ-isoʳᵗ : ∀ {A}     → (Mon.λ⇐ {A} ∘ Mon.λ⇒) ≈ᵗ id)
  (σ-isoᵗ  : ∀ {A B}   → (Mon.σ {A} {B} ∘ Mon.σ) ≈ᵗ id)
  -- ── genuinely new: observation semantics, no categorical source
  (Reachableᵗ   : ∀ {A} {Block : Type} → Machine I A → STT.Obs n Block → Type)
  (≈-Reachableᵗ : ∀ {A} {Block} {P Q : Machine I A} → P ≈ᵗ Q
                → ∀ {o : STT.Obs n Block} → Reachableᵗ P o → Reachableᵗ Q o)
  where

open STT n using (TraceCat)

partial-TraceCat : TraceCat
partial-TraceCat = record
  { _≈_         = _≈ᵗ_         -- ┐ FILLED — Machine.TraceEquiv
  ; ≈-refl      = ≈ᵗ-refl      -- │
  ; ≈-sym       = ≈ᵗ-sym       -- │
  ; ≈-trans     = ≈ᵗ-trans     -- ┘
  ; ∘-resp-≈    = ∘-resp-≈ᵗ    -- ┐ OPEN ≈ᵗ obligations
  ; ⊗₁-resp-≈   = ⊗₁-resp-≈ᵗ   -- │ (MonoidalLaws + absorb;
  ; ⨂ᴷ-cong-≈   = ⨂ᴷ-cong-≈ᵗ   -- │  the "fix" to discharge)
  ; ∘-identityˡ = ∘-identityˡᵗ -- │
  ; assoc²γδ    = assoc²γδᵗ    -- │
  ; env-absorb  = env-absorbᵗ  -- ┘
  ; σ           = Mon.σ        -- ┐ FILLED — Machine.Monoidal
  ; α⇒          = Mon.α⇒       -- │ (real forwarding machines)
  ; α⇐          = Mon.α⇐       -- │
  ; ρ⇒          = Mon.ρ⇒       -- │
  ; ρ⇐          = Mon.ρ⇐       -- │
  ; λ⇒          = Mon.λ⇒       -- │
  ; λ⇐          = Mon.λ⇐       -- ┘
  ; α-isoˡ      = α-isoˡᵗ      -- ┐ OPEN ≈ᵗ obligations
  ; α-isoʳ      = α-isoʳᵗ      -- │ (iso laws — false at ≈ℰ,
  ; ρ-isoˡ      = ρ-isoˡᵗ      -- │  true at ≈ᵗ)
  ; ρ-isoʳ      = ρ-isoʳᵗ      -- │
  ; λ-isoˡ      = λ-isoˡᵗ      -- │
  ; λ-isoʳ      = λ-isoʳᵗ      -- │
  ; σ-iso       = σ-isoᵗ       -- ┘
  ; Reachable   = Reachableᵗ   -- ┐ GENUINELY NEW
  ; ≈-Reachable = ≈-Reachableᵗ -- ┘ (observation semantics)
  }
