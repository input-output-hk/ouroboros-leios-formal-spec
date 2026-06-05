{-# OPTIONS --safe #-}

-- ============================================================================
-- Trace-equivalence rework of `Blockchain/Safety/Transfer.agda` (SKELETON).
--
-- The current transfer transports STATES and TRACES along a *propositional*
-- machine equality (`transProtocol : Ext.protocol E ≡ᴹ Base.protocol …`,
-- `state-subst`, `Trace-subst`). With the explicit Machine category the
-- morphism equivalence becomes TRACE EQUIVALENCE `_≈_`, which one cannot
-- `subst` along. So the property layer moves from `Machine.State` to
-- OBSERVATIONS (the chain/slot query outputs), and the single new transport
-- primitive `≈-Reachable` replaces `state-subst`/`Trace-subst`.
--
-- This file is a compiling --safe skeleton: the categorical-crypto deliverables
-- are isolated as the fields of `TraceCat` (no postulates, no holes — they are
-- the obligations the explicit category must discharge); the leios-side
-- `transfer` is then PROVEN from them + the existing list lemmas.
--
-- Provenance of names:
--   prune, _≼_, prune-map, map-≼, inj-map-≼   — Leios/Prelude.lagda.md
--   Spec                                       — Blockchain/Safety.agda
--   _∘_, _⊗₁_, id, Machine, Channel, I, _⊗₀_   — CategoricalCrypto
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
-- `α-isoˡ`/… are also names in `CategoricalCrypto.SFunM.Monoidal`; hide them so
-- the `TraceCat` field names below don't clash.
open import CategoricalCrypto hiding (_∘ᴷ_; α-isoˡ; α-isoʳ; ρ-isoˡ; ρ-isoʳ; λ-isoˡ; λ-isoʳ)
import CategoricalCrypto as CC
open import Blockchain.Safety using (Spec)

module Blockchain.Safety.TransferTrace (n : ℕ) where

-- ----------------------------------------------------------------------------
-- Observations: what a reachable state exposes through the queries.
-- (Replaces predicates over `Machine.State`.)  In the real port `chainOf`
-- would be indexed by honest parties only; all parties here for brevity.
-- ----------------------------------------------------------------------------

record Obs (Block : Type) : Type where
  field
    chainOf : Fin n → List Block
    clockOf : Fin n → ℕ           -- the party's CURRENT slot (cf. getSlot); used by liveness

open Obs

mapObs : ∀ {A B} → (A → B) → Obs A → Obs B
mapObs f o = record { chainOf = λ p → map f (chainOf o p) ; clockOf = clockOf o }

-- safety as a predicate on a single observation (was `safeState` on a State)
safeObs : ∀ {Block} → ℕ → Obs Block → Type
safeObs k o = (p p' : Fin n) → prune k (chainOf o p) ≼ chainOf o p'

-- ----------------------------------------------------------------------------
-- The deliverables of the explicit Machine category (what replaces ChannelCat
-- for this proof).  These are FIELDS = obligations, not assumptions baked into
-- the protocol: they mention only the categorical structure.
-- ----------------------------------------------------------------------------

record TraceCat : Type₂ where
  field
    -- trace equivalence on machines (replaces ≡ᴹ / ≡)
    _≈_     : ∀ {A B} → Machine A B → Machine A B → Type
    ≈-refl  : ∀ {A B} {M : Machine A B} → M ≈ M
    ≈-sym   : ∀ {A B} {M N : Machine A B} → M ≈ N → N ≈ M
    ≈-trans : ∀ {A B} {M N P : Machine A B} → M ≈ N → N ≈ P → M ≈ P
    -- congruences (needed downstream to DISCHARGE is-extension / ChainLemma)
    ∘-resp-≈  : ∀ {A B C} {M M' : Machine B C} {N N' : Machine A B}
              → M ≈ M' → N ≈ N' → (M ∘ N) ≈ (M' ∘ N')
    ⊗₁-resp-≈ : ∀ {A B C D} {M M' : Machine A B} {N N' : Machine C D}
              → M ≈ M' → N ≈ N' → (M ⊗₁ N) ≈ (M' ⊗₁ N')

    -- left identity at `≈` (the categorical law that is FALSE at `≈ℰ`/`≡ᴹ` by
    -- state-counting, but TRUE at trace equivalence; discharged by `MACHINE`).
    -- Used for the dishonest nodes in the `≈`-native `single-protocol`.
    ∘-identityˡ : ∀ {A B} {M : Machine A B} → (id ∘ M) ≈ M

    -- env-absorb: the protocol respects per-node factoring at `≈`.  Given each
    -- ext node factors as `lay ∘ baseN` (the `single-protocol-≈` consequence of
    -- `is-extension≈`), the ext-node protocol equals — up to `≈` — the base-node
    -- protocol under a transformed environment `Env'`.  THIS is the ⨂/network
    -- congruence `ChainLemmaDischarge` flags as "beyond the minimal TraceCat":
    -- discharged by `MACHINE` via the explicit category's constructive
    -- `insert-id`/`⨂-absorb-env` (decomposable into those + `⊗₁`-interchange +
    -- the `∘ᴷ` laws; packaged here as one obligation for the `≈-protocol` step).
    env-absorb : ∀ {n} {A Network NAdv : Channel} {B E B' E' : Fin n → Channel}
      (Env   : Machine (⨂ B' ⊗₀ (NAdv ⊗₀ ⨂ E')) A)
      (extN  : (p : Fin n) → Machine Network (B' p ⊗₀ E' p))
      (lay   : (p : Fin n) → Machine (B p ⊗₀ E p) (B' p ⊗₀ E' p))
      (baseN : (p : Fin n) → Machine Network (B p ⊗₀ E p))
      (net   : Machine I (n ⨂ⁿ Network ⊗₀ NAdv))
      → (∀ p → extN p ≈ (lay p ∘ baseN p))
      → Σ[ Env' ∈ Machine (⨂ B ⊗₀ (NAdv ⊗₀ ⨂ E)) A ]
           ((Env ∘ CC._∘ᴷ_ (⨂ᴷ extN) net) ≈ (Env' ∘ CC._∘ᴷ_ (⨂ᴷ baseN) net))

    -- congruence of the n-fold Kleisli tensor `⨂ᴷ` (used to lift the per-node
    -- `is-extension≈` over all parties in the `≈-protocol` derivation).  It is
    -- derivable from `∘-resp-≈`/`⊗₁-resp-≈` by induction, but kept as a field so
    -- the `≈-protocol` mechanisation needn't re-derive it.
    ⨂ᴷ-cong-≈ : ∀ {n} {A B E : Fin n → Channel}
                {f g : (k : Fin n) → Machine (A k) (B k ⊗₀ E k)}
              → (∀ k → f k ≈ g k) → ⨂ᴷ f ≈ ⨂ᴷ g

    -- associativity: the ≈-analogue of the `assoc²γδ` step at
    -- `Safety/Transfer.agda:115`.  Discharged by the explicit MACHINE category
    -- (`Leios.ChannelCat.MachineCat.assoc²γδ` = `Reasoning.assoc²γδ`); consumed
    -- by the `≈-protocol` derivation (ChainLemmaDischarge obligation (I)).
    assoc²γδ : ∀ {A B C D E} {f : Machine A B} {g : Machine B C} {h : Machine C D} {i : Machine D E}
             → ((i ∘ h) ∘ (g ∘ f)) ≈ (i ∘ ((h ∘ g) ∘ f))

    -- structure isomorphisms: morphisms + ≈-inverse laws (the ≈-analogue of the
    -- ChannelCat σ/α/λ/ρ fields, minus the FALSE propositional channel
    -- equalities ⊗-identityˡ/ʳ; supplied by the explicit category).
    σ  : ∀ {A B}   → Machine (A ⊗₀ B) (B ⊗₀ A)
    α⇒ : ∀ {A B C} → Machine ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
    α⇐ : ∀ {A B C} → Machine (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
    ρ⇒ : ∀ {A}     → Machine (A ⊗₀ I) A
    ρ⇐ : ∀ {A}     → Machine A (A ⊗₀ I)
    λ⇒ : ∀ {A}     → Machine (I ⊗₀ A) A
    λ⇐ : ∀ {A}     → Machine A (I ⊗₀ A)
    α-isoˡ : ∀ {A B C} → (α⇒ {A} {B} {C} ∘ α⇐) ≈ id
    α-isoʳ : ∀ {A B C} → (α⇐ {A} {B} {C} ∘ α⇒) ≈ id
    ρ-isoˡ : ∀ {A}     → (ρ⇒ {A} ∘ ρ⇐) ≈ id
    ρ-isoʳ : ∀ {A}     → (ρ⇐ {A} ∘ ρ⇒) ≈ id
    λ-isoˡ : ∀ {A}     → (λ⇒ {A} ∘ λ⇐) ≈ id
    λ-isoʳ : ∀ {A}     → (λ⇐ {A} ∘ λ⇒) ≈ id
    σ-iso  : ∀ {A B}   → (σ {A} {B} ∘ σ) ≈ id

    -- "observation o is exposed at some reachable state of the closed machine P"
    Reachable : ∀ {A} {Block : Type} → Machine I A → Obs Block → Type
    -- THE new transport primitive (replaces state-subst / Trace-subst):
    -- trace-equivalent closed machines expose the same reachable observations.
    ≈-Reachable : ∀ {A} {Block} {P Q : Machine I A} → P ≈ Q
                → ∀ {o : Obs Block} → Reachable P o → Reachable Q o

module Transfer (tc : TraceCat) where
  open TraceCat tc

  -- iso in the Machine category (replaces the propositional `E.Adv ≡ B.Adv`)
  record _≅_ (A B : Channel) : Type₁ where
    field
      to      : Machine A B
      from    : Machine B A
      to-from : (to ∘ from) ≈ id
      from-to : (from ∘ to) ≈ id

  -- --------------------------------------------------------------------------
  -- Reworked IsExtension: no `subst`, no `idᴷ` padding, no propositional
  -- channel equality.  cf. Blockchain/Safety.agda:73.
  -- --------------------------------------------------------------------------
  record IsExtension≈ {BlockBase BlockExt : Type} {Network : Channel}
                      (base-spec : Spec BlockBase n Network)
                      (ext-spec  : Spec BlockExt  n Network) : Type₁ where
    private module B = Spec base-spec
            module E = Spec ext-spec
    field
      ext-layer        : Machine B.IO E.IO
      getBaseBlock     : BlockExt → BlockBase
      getBaseBlock-inj : Injective _≡_ _≡_ getBaseBlock
      adv-iso          : E.Adv ≅ B.Adv
      -- honest ext node ≈ EB-layer ∘ Praos node, up to trace equivalence
      is-extension     :
        E.honest-node-spec ≈ ((ext-layer ⊗₁ _≅_.from adv-iso) ∘ B.honest-node-spec)

  -- --------------------------------------------------------------------------
  -- Trace-based safety + the reworked ChainLemma and transfer.
  -- --------------------------------------------------------------------------

  -- was: `safety k = ∀ E → Invariant (protocol E) (safeState k E)`
  Safe : ∀ {A} {Block : Type} → ℕ → Machine I A → Type
  Safe {Block = Block} k P = ∀ {o : Obs Block} → Reachable P o → safeObs k o

  -- ChainLemma, recast: a trace equivalence between the ext protocol and the
  -- derived base protocol, plus the getBaseBlock-projection of observations.
  -- (The `≈` component is what `≈-Reachable` consumes to build the projection
  -- when this is discharged for a concrete deployment.)
  ChainLemma : ∀ {A} {BlockExt BlockBase : Type}
               (gB : BlockExt → BlockBase) (Pₑ P-b : Machine I A) → Type
  ChainLemma gB Pₑ P-b =
      (Pₑ ≈ P-b)
    × (∀ {o} → Reachable Pₑ o → Reachable P-b (mapObs gB o))

  -- The transfer itself: PROVEN, reusing prune-map / inj-map-≼.  Note it uses
  -- only the projection field of ChainLemma — `≈` enters when DISCHARGING
  -- ChainLemma (via ≈-Reachable), not here.  cf. Safety/Transfer.agda:156.
  transfer : ∀ {A} {BlockExt BlockBase : Type} {gB : BlockExt → BlockBase} {k}
             {Pₑ P-b : Machine I A}
           → Injective _≡_ _≡_ gB
           → ChainLemma gB Pₑ P-b
           → Safe k P-b
           → Safe k Pₑ
  transfer {gB = gB} {k = k} gB-inj (_ , proj) baseSafe {o} reach p p' =
    inj-map-≼ gB-inj
      (subst (λ x → x ≼ map gB (chainOf o p'))
             (prune-map {k = k} {f = gB} {l = chainOf o p})
             (baseSafe (proj reach) p p'))
