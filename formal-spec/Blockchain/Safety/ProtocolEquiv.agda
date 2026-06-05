{-# OPTIONS --safe #-}

-- ============================================================================
-- Mechanisation of ChainLemmaDischarge obligation (I): `≈-protocol`, at the
-- reworked `IsExtension≈` (trace-equivalence, `adv-iso` instead of the
-- propositional `E.Adv ≡ B.Adv`).
--
-- The protocol trace-equivalence is assembled from the per-node factoring
-- `single-protocol-≈` (a consequence of `is-extension≈`, proven WITHOUT channel
-- injectivity) via the `TraceCat.env-absorb` obligation — the ⨂/network
-- congruence discharged by the explicit MACHINE category.  Unlike the previous
-- `≡ᴹ`-based version, this needs NO `ChannelCat` (`∘ᴷ-cong-≡ᴹ`/`⊗-injective`).
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import Blockchain.Safety
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Ext
import Blockchain.Safety.TransferTrace as STT
import Blockchain.Safety.ChainLemmaDischarge as CLD

module Blockchain.Safety.ProtocolEquiv
  {BlockExt BlockBase : Type}
  (ext                : Deployment BlockExt)
  (let module Ext = Deployment ext)
  (base-spec          : Spec BlockBase Ext.n Ext.Network)
  (tc                 : STT.TraceCat Ext.n)
  (extension≈         : STT.Transfer.IsExtension≈ Ext.n tc base-spec Ext.spec)
  where

module B  = Spec base-spec
module Tr = STT.Transfer Ext.n tc
open Tr._≅_
open Tr.IsExtension≈ extension≈
open STT Ext.n using (Obs; mapObs)
open STT.TraceCat tc using (_≈_; ≈-refl; ≈-sym; ≈-trans; ∘-identityˡ; env-absorb; Reachable)
open Tr using (ChainLemma)
module CLD' = CLD Ext.n

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

base-IOF base-AdvF : Fin Ext.n → Channel
base-IOF  p = case p ∈? Ext.honest-nodes of λ where (yes _) → B.IO  ; (no _) → Ext.IOF p
base-AdvF p = case p ∈? Ext.honest-nodes of λ where (yes _) → B.Adv ; (no _) → Ext.AdvF p

base-node : (p : Fin Ext.n) → Machine Ext.Network (base-IOF p ⊗₀ base-AdvF p)
base-node p with p ∈? Ext.honest-nodes
... | yes _ = B.honest-node-spec
... | no  _ = Ext.all-nodes p

-- the EB-layer + Adv bridge, coerced onto the per-party channels
layer : (p : Fin Ext.n) → Machine (base-IOF p ⊗₀ base-AdvF p) (Ext.IOF p ⊗₀ Ext.AdvF p)
layer p with p ∈? Ext.honest-nodes
... | yes hp = subst (Machine (B.IO ⊗₀ B.Adv))
                     (sym (cong₂ _⊗₀_ (Ext.honest-IOF≡ hp) (Ext.honest-AdvF≡ hp)))
                     (ext-layer ⊗₁ from adv-iso)
... | no  _  = CC.id

-- channel-matched per-node factoring at ≈ (NO `∘ᴷ-cong-≡ᴹ`, NO `⊗-injective`)
single-protocol-≈ : (p : Fin Ext.n) → Ext.all-nodes p ≈ (layer p ∘ base-node p)
single-protocol-≈ p with p ∈? Ext.honest-nodes
... | no  _  = ≈-sym ∘-identityˡ
... | yes hp =
  ≈-trans (≡→≈ (≡ᴹ→≡ (≡ᴹ-trans (Ext.honest-nodes-≡-spec hp)
                                (≡ᴹ-sym (subst-≡ᴹ (sym cheq) Ext.honest-node-spec)))))
  (≈-trans (≈-subst-cod (sym cheq) is-extension)
           (≡→≈ (subst-∘-cod (sym cheq) (ext-layer ⊗₁ from adv-iso) B.honest-node-spec)))
  where cheq = cong₂ _⊗₀_ (Ext.honest-IOF≡ hp) (Ext.honest-AdvF≡ hp)

base-honest-≡-spec : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-node p ≡ᴹ B.honest-node-spec
base-honest-≡-spec {p} hp with p ∈? Ext.honest-nodes
... | yes _  = ≡ᴹ-refl
... | no ¬hp = contradiction hp ¬hp

base-honest-IOF≡ : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-IOF p ≡ B.IO
base-honest-IOF≡ {p} hp with p ∈? Ext.honest-nodes
... | yes _  = refl
... | no ¬hp = contradiction hp ¬hp

base-honest-AdvF≡ : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-AdvF p ≡ B.Adv
base-honest-AdvF≡ {p} hp with p ∈? Ext.honest-nodes
... | yes _  = refl
... | no ¬hp = contradiction hp ¬hp

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
    absorbed = env-absorb E Ext.all-nodes layer base-node Ext.network single-protocol-≈

  transEnv : Base.Environment A
  transEnv = proj₁ absorbed

  ≈-protocol : Ext.protocol E ≈ Base.protocol transEnv
  ≈-protocol = proj₂ absorbed

  -- Wiring: feed `≈-protocol` into `ChainLemmaDischarge.chainLemma`, leaving
  -- only obligation (II) `reindex` (the block-level projection) abstract.
  chainLemma : (∀ {o : Obs BlockExt}
                 → Reachable (Base.protocol transEnv) o
                 → Reachable (Base.protocol transEnv) (mapObs getBaseBlock o))
             → ChainLemma getBaseBlock (Ext.protocol E) (Base.protocol transEnv)
  chainLemma reindex = CLD'.chainLemma tc getBaseBlock ≈-protocol reindex
