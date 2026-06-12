{-# OPTIONS --safe #-}

-- ============================================================================
-- Mechanisation of ChainLemmaDischarge obligation (I): `≈-protocol`, at the
-- reworked `IsExtension≈` (trace-equivalence, `adv-iso` instead of the
-- propositional `E.Adv ≡ B.Adv`).
--
-- The protocol equivalence (at the machine isomorphism `_≅ᴹ_`) is assembled
-- from the per-node factoring `single-protocol-≈` (a consequence of
-- `is-extension≈`, proven WITHOUT channel injectivity) via the `env-absorb`
-- obligation — the ⨂/network congruence.  The category-level facts are read
-- directly off the library `MachineCategory` (hence the monad telescope); the
-- open obligations (`Reachable`/`≈-Reachable`, `env-absorb`) are module
-- parameters.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import Blockchain.Safety
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Ext
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_)
open import Categories.Category using (Category; module Category)
open import Class.Core
open import Class.Monad.Ext using (ExtensionalMonad; CommutativeMonad)
open import Class.Monad.Iterative using (IterativeMonad)
open import Class.Monad.OfRel using (MonadOfRel)
import Blockchain.Safety.TransferTrace as STT
import Blockchain.Safety.ChainLemmaDischarge as CLD

module Blockchain.Safety.ProtocolEquiv
  {BlockExt BlockBase : Type}
  (ext                : Deployment BlockExt)
  (let module Ext = Deployment ext)
  (base-spec          : Spec BlockBase Ext.n Ext.Network)
  {Mon : Type↑}
  ⦃ Monad-M       : Monad Mon            ⦄
  ⦃ M-Laws        : MonadLaws Mon        ⦄
  ⦃ M-Extensional : ExtensionalMonad Mon ⦄
  ⦃ M-Comm        : CommutativeMonad Mon ⦄
  ⦃ M-Iter        : IterativeMonad Mon   ⦄
  ⦃ M-OfRel       : MonadOfRel Mon       ⦄
  (Reachable   : ∀ {A} {Block : Type} → Machine I A → STT.Obs Ext.n Block → Type)
  (≈-Reachable : ∀ {A} {Block} {P Q : Machine I A} → P ≅ᴹ Q
               → ∀ {o : STT.Obs Ext.n Block} → Reachable P o → Reachable Q o)
  (env-absorb : ∀ {m} {A Net NAdv : Channel} {B E B' E' : Fin m → Channel}
       (Env   : Machine (⨂ B' ⊗₀ (NAdv ⊗₀ ⨂ E')) A)
       (extN  : (p : Fin m) → Machine Net (B' p ⊗₀ E' p))
       (lay   : (p : Fin m) → Machine (B p ⊗₀ E p) (B' p ⊗₀ E' p))
       (baseN : (p : Fin m) → Machine Net (B p ⊗₀ E p))
       (net   : Machine I (m ⨂ⁿ Net ⊗₀ NAdv))
       → (∀ p → extN p ≅ᴹ (lay p ∘ baseN p))
       → Σ[ Env' ∈ Machine (⨂ B ⊗₀ (NAdv ⊗₀ ⨂ E)) A ]
            ((Env ∘ CC._∘ᴷ_ (⨂ᴷ extN) net) ≅ᴹ (Env' ∘ CC._∘ᴷ_ (⨂ᴷ baseN) net)))
  (extension≈  : STT.IsExtension≈ Ext.n base-spec Ext.spec)
  where

module B  = Spec base-spec
module Tr = STT.Transfer Ext.n Reachable
open STT Ext.n using (Obs; mapObs; _≅_; IsExtension≈)
open _≅_
open IsExtension≈ extension≈
open Tr using (ChainLemma)
module CLD' = CLD Ext.n

-- The machine equivalence, read off the library category `MachineCategory`
-- (hom equality `_≅ᴹ_`).  Kept OPAQUE for performance: `with`-abstraction
-- normalizes goal types, and goals of shape `X ≈ Y` with a transparent
-- `_≈_ = _≅ᴹ_` normalize through the full machine composites
-- (`Typing.With` measured at ~22 min for this module).  A neutral `_≈_`
-- keeps those goals small; `≅ᴹ→≈`/`≈→≅ᴹ` mediate at the interfaces that are
-- stated at `_≅ᴹ_` (`is-extension`, `env-absorb`, `ChainLemmaDischarge`).
opaque
  _≈_ : ∀ {A B} → Machine A B → Machine A B → Type
  _≈_ = _≅ᴹ_

opaque
  unfolding _≈_

  ≅ᴹ→≈ : ∀ {A B} {M N : Machine A B} → M ≅ᴹ N → M ≈ N
  ≅ᴹ→≈ p = p

  ≈→≅ᴹ : ∀ {A B} {M N : Machine A B} → M ≈ N → M ≅ᴹ N
  ≈→≅ᴹ p = p

  ≈-refl : ∀ {A B} {M : Machine A B} → M ≈ M
  ≈-refl = Category.Equiv.refl MachineCategory

  ≈-sym : ∀ {A B} {M N : Machine A B} → M ≈ N → N ≈ M
  ≈-sym = Category.Equiv.sym MachineCategory

  ≈-trans : ∀ {A B} {M N P : Machine A B} → M ≈ N → N ≈ P → M ≈ P
  ≈-trans = Category.Equiv.trans MachineCategory

  ∘-identityˡ : ∀ {A B} {M : Machine A B} → (CC.id ∘ M) ≈ M
  ∘-identityˡ = Category.identityˡ MachineCategory

private
  subst-≡ᴹ : ∀ {x y : Channel} {A B : Channel → Channel} → (eq : x ≡ y)
    → (M : Machine (A x) (B x)) → subst (λ x → Machine (A x) (B x)) eq M ≡ᴹ M
  subst-≡ᴹ refl _ = ≡ᴹ-refl

  ≡→≈ : ∀ {A B} {M N : Machine A B} → M ≡ N → M ≈ N
  ≡→≈ refl = ≈-refl

  -- subst-congruence for the abstract ≈ (split on the equality)
  ≈-subst-cod : ∀ {C X Y} (eq : X ≡ Y) {M N : Machine C X}
              → M ≈ N → subst (Machine C) eq M ≈ subst (Machine C) eq N
  ≈-subst-cod refl p = p

  -- subst on a composite's codomain pushes onto the outer machine
  subst-∘-cod : ∀ {A C X Y} (eq : X ≡ Y) (L : Machine C X) (G : Machine A C)
              → subst (Machine A) eq (L ∘ G) ≡ (subst (Machine C) eq L) ∘ G
  subst-∘-cod refl _ _ = refl

-- ----------------------------------------------------------------------------
-- Restructured base deployment: honest nodes are the Praos nodes directly
-- (Adv stays `B.Adv`, bridged by `adv-iso`); no `subst`, no `idᴷ` padding.
-- ----------------------------------------------------------------------------

-- All case distinctions on party honesty are routed through Dec-indexed
-- helper functions sharing ONE decision value, instead of `with`-abstraction:
-- `with` normalizes the goal type to abstract the scrutinee, and goals here
-- contain machine composites whose normal forms are enormous (`Typing.With`
-- measured at ~22 min for this module).  Hand-written helper types avoid that
-- normalization entirely; the public wrappers restore the original interface.

base-IOF' base-AdvF' : (p : Fin Ext.n) → Dec (p ∈ Ext.honest-nodes) → Channel
base-IOF'  p (yes _) = B.IO
base-IOF'  p (no  _) = Ext.IOF p
base-AdvF' p (yes _) = B.Adv
base-AdvF' p (no  _) = Ext.AdvF p

base-IOF base-AdvF : Fin Ext.n → Channel
base-IOF  p = base-IOF'  p (p ∈? Ext.honest-nodes)
base-AdvF p = base-AdvF' p (p ∈? Ext.honest-nodes)

base-node' : (p : Fin Ext.n) (d : Dec (p ∈ Ext.honest-nodes))
           → Machine Ext.Network (base-IOF' p d ⊗₀ base-AdvF' p d)
base-node' p (yes _) = B.honest-node-spec
base-node' p (no  _) = Ext.all-nodes p

base-node : (p : Fin Ext.n) → Machine Ext.Network (base-IOF p ⊗₀ base-AdvF p)
base-node p = base-node' p (p ∈? Ext.honest-nodes)

-- the EB-layer + Adv bridge, coerced onto the per-party channels
layer' : (p : Fin Ext.n) (d : Dec (p ∈ Ext.honest-nodes))
       → Machine (base-IOF' p d ⊗₀ base-AdvF' p d) (Ext.IOF p ⊗₀ Ext.AdvF p)
layer' p (yes hp) = subst (Machine (B.IO ⊗₀ B.Adv))
                          (sym (cong₂ _⊗₀_ (Ext.honest-IOF≡ hp) (Ext.honest-AdvF≡ hp)))
                          (ext-layer ⊗₁ from adv-iso)
layer' p (no  _)  = CC.id

layer : (p : Fin Ext.n) → Machine (base-IOF p ⊗₀ base-AdvF p) (Ext.IOF p ⊗₀ Ext.AdvF p)
layer p = layer' p (p ∈? Ext.honest-nodes)

-- channel-matched per-node factoring at ≈ (NO `∘ᴷ-cong-≡ᴹ`, NO `⊗-injective`)
single-protocol-≈' : (p : Fin Ext.n) (d : Dec (p ∈ Ext.honest-nodes))
                   → Ext.all-nodes p ≈ (layer' p d ∘ base-node' p d)
single-protocol-≈' p (no  _)  = ≈-sym ∘-identityˡ
single-protocol-≈' p (yes hp) =
  ≈-trans (≡→≈ (≡ᴹ→≡ (≡ᴹ-trans (Ext.honest-nodes-≡-spec hp)
                                (≡ᴹ-sym (subst-≡ᴹ (sym cheq) Ext.honest-node-spec)))))
  (≈-trans (≈-subst-cod (sym cheq) (≅ᴹ→≈ is-extension))
           (≡→≈ (subst-∘-cod (sym cheq) (ext-layer ⊗₁ from adv-iso) B.honest-node-spec)))
  where cheq = cong₂ _⊗₀_ (Ext.honest-IOF≡ hp) (Ext.honest-AdvF≡ hp)

single-protocol-≈ : (p : Fin Ext.n) → Ext.all-nodes p ≈ (layer p ∘ base-node p)
single-protocol-≈ p = single-protocol-≈' p (p ∈? Ext.honest-nodes)

base-honest-≡-spec' : {p : Fin Ext.n} (d : Dec (p ∈ Ext.honest-nodes))
                    → p ∈ Ext.honest-nodes → base-node' p d ≡ᴹ B.honest-node-spec
base-honest-≡-spec' (yes _)  _  = ≡ᴹ-refl
base-honest-≡-spec' (no ¬hp) hp = contradiction hp ¬hp

base-honest-≡-spec : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-node p ≡ᴹ B.honest-node-spec
base-honest-≡-spec {p} = base-honest-≡-spec' (p ∈? Ext.honest-nodes)

base-honest-IOF≡' : {p : Fin Ext.n} (d : Dec (p ∈ Ext.honest-nodes))
                  → p ∈ Ext.honest-nodes → base-IOF' p d ≡ B.IO
base-honest-IOF≡' (yes _)  _  = refl
base-honest-IOF≡' (no ¬hp) hp = contradiction hp ¬hp

base-honest-IOF≡ : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-IOF p ≡ B.IO
base-honest-IOF≡ {p} = base-honest-IOF≡' (p ∈? Ext.honest-nodes)

base-honest-AdvF≡' : {p : Fin Ext.n} (d : Dec (p ∈ Ext.honest-nodes))
                   → p ∈ Ext.honest-nodes → base-AdvF' p d ≡ B.Adv
base-honest-AdvF≡' (yes _)  _  = refl
base-honest-AdvF≡' (no ¬hp) hp = contradiction hp ¬hp

base-honest-AdvF≡ : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-AdvF p ≡ B.Adv
base-honest-AdvF≡ {p} = base-honest-AdvF≡' (p ∈? Ext.honest-nodes)

base : Deployment BlockBase
base = record
  { n                   = Ext.n
  ; Network             = Ext.Network
  ; spec                = base-spec
  ; NAdv                = Ext.NAdv
  ; IOF                 = base-IOF
  ; AdvF                = base-AdvF
  ; all-nodes           = base-node
  ; honest-nodes        = Ext.honest-nodes
  ; honest-nodes-≡-spec = base-honest-≡-spec
  ; honest-IOF≡         = base-honest-IOF≡
  ; honest-AdvF≡        = base-honest-AdvF≡
  ; network             = Ext.network
  }

module Base = Deployment base

-- ----------------------------------------------------------------------------
-- Obligation (I): the protocol trace equivalence, via `env-absorb`.
-- ----------------------------------------------------------------------------

module _ {A : Channel} (E : Ext.Environment A) where

  private
    absorbed = env-absorb E Ext.all-nodes layer base-node Ext.network
                          (λ p → ≈→≅ᴹ (single-protocol-≈ p))

  transEnv : Base.Environment A
  transEnv = proj₁ absorbed

  ≈-protocol : Ext.protocol E ≈ Base.protocol transEnv
  ≈-protocol = ≅ᴹ→≈ (proj₂ absorbed)

  -- Wiring: feed `≈-protocol` into `ChainLemmaDischarge.chainLemma`, leaving
  -- only obligation (II) `reindex` (the block-level projection) abstract.
  chainLemma : (∀ {o : Obs BlockExt}
                 → Reachable (Base.protocol transEnv) o
                 → Reachable (Base.protocol transEnv) (mapObs getBaseBlock o))
             → ChainLemma getBaseBlock (Ext.protocol E) (Base.protocol transEnv)
  chainLemma reindex = CLD'.chainLemma Reachable ≈-Reachable getBaseBlock (≈→≅ᴹ ≈-protocol) reindex
