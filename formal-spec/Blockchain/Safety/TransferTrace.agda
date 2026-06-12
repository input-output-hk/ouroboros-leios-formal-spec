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
-- The machine equivalence is the hom equality `_≅ᴹ_` of the library's
-- `MachineCategory` (a proven, postulate-free category).  The categorical
-- facts the proofs rely on are either fields of that category or OPEN
-- obligations taken as module
-- parameters by their consumers (`Reachable` here and in the discharge
-- modules, `≈-Reachable` in `ChainLemmaDischarge`, `env-absorb` in
-- `ProtocolEquiv`, the right-unitor inverse laws in `Network/Leios`); the
-- leios-side `transfer` is PROVEN from them + the existing list lemmas.
--
-- Provenance of names:
--   prune, _≼_, prune-map, map-≼, inj-map-≼   — Leios/Prelude.lagda.md
--   Spec                                       — Blockchain/Safety.agda
--   _∘_, _⊗₁_, id, Machine, Channel, I, _⊗₀_   — CategoricalCrypto
--   _≅ᴹ_                                       — CategoricalCrypto.Machine.Iso
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (_∘ᴷ_)
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_)
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
-- Extension witnesses, at the machine isomorphism `_≅ᴹ_`.
-- ----------------------------------------------------------------------------

-- iso in the Machine category (replaces the propositional `E.Adv ≡ B.Adv`)
record _≅_ (A B : Channel) : Type₁ where
  field
    to      : Machine A B
    from    : Machine B A
    to-from : (to ∘ from) ≅ᴹ id
    from-to : (from ∘ to) ≅ᴹ id

-- Reworked IsExtension: no `subst`, no `idᴷ` padding, no propositional
-- channel equality.  cf. Blockchain/Safety.agda:73.
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
    -- honest ext node ≅ᴹ EB-layer ∘ Praos node
    is-extension     :
      E.honest-node-spec ≅ᴹ ((ext-layer ⊗₁ _≅_.from adv-iso) ∘ B.honest-node-spec)

-- ----------------------------------------------------------------------------
-- Trace-based safety + the reworked ChainLemma and transfer.  `Reachable` —
-- "observation o is exposed at some reachable state of the closed machine P"
-- — is the observation semantics, an OPEN obligation taken as a parameter.
-- ----------------------------------------------------------------------------

module Transfer
  (Reachable : ∀ {A} {Block : Type} → Machine I A → Obs Block → Type)
  where

  -- was: `safety k = ∀ E → Invariant (protocol E) (safeState k E)`
  Safe : ∀ {A} {Block : Type} → ℕ → Machine I A → Type
  Safe {Block = Block} k P = ∀ {o : Obs Block} → Reachable P o → safeObs k o

  -- ChainLemma, recast: a machine isomorphism between the ext protocol and the
  -- derived base protocol, plus the getBaseBlock-projection of observations.
  -- (The `≅ᴹ` component is what `≈-Reachable` consumes to build the projection
  -- when this is discharged for a concrete deployment.)
  ChainLemma : ∀ {A} {BlockExt BlockBase : Type}
               (gB : BlockExt → BlockBase) (Pₑ P-b : Machine I A) → Type
  ChainLemma gB Pₑ P-b =
      (Pₑ ≅ᴹ P-b)
    × (∀ {o} → Reachable Pₑ o → Reachable P-b (mapObs gB o))

  -- The transfer itself: PROVEN, reusing prune-map / inj-map-≼.  Note it uses
  -- only the projection field of ChainLemma — `≅ᴹ` enters when DISCHARGING
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
