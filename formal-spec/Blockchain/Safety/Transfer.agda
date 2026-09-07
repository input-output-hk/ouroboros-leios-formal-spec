{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
open import CategoricalCrypto.Machine.NAry
  using (⨂-reshape-env-helper; ⨂-absorb-env-helper; unit-∘ᴷ; ⨂-reshape-env; ⨂-absorb-env)

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Ext
open import CategoricalCrypto.Machine.Iso
  using (_≅ᴹ_; ≅ᴹ-refl; ≅ᴹ-sym; ≅ᴹ-trans; ∘-resp-≅ᴹ; ∘-identityˡ-≅ᴹ)
open import CategoricalCrypto.Machine.Monoidal using (⊗₁-id)

import Relation.Binary.Reasoning.PartialOrder
open import Relation.Binary using (Poset)

-- | Generic safety transfer.
--
-- Given an ext `Deployment` and an `IsExtension` witness (the base-side spec,
-- channel/layer equipment, and block-level projection), safety of the
-- derived base `Deployment` implies safety of the ext `Deployment`.
--
-- The protocol correspondence is now a machine ISOMORPHISM (`_≅ᴹ_`, a
-- bisimulation) rather than propositional machine equality.  Structurally the
-- proof is unchanged: `transState`/`transTrace` still push a state and a run
-- from the ext protocol to the base protocol, only now via the iso's `to` and
-- `Trace-map` instead of `subst`.  The component-wise channel facts about
-- honest nodes that the old `ChannelCat` extracted by ⊗-injectivity — which is
-- what made it inconsistent — are fields of `Deployment` (`honest-IOF`,
-- `honest-AdvF`).
--
-- The extension layer has its own adversary channel (`IsExtension.AdvL`), so
-- an ext node's adversary channel splits into its base node's and its
-- layer's.  The derived base deployment therefore has per-party adversary
-- channels (`base-AdvF`), and the environment is rewired with a per-party
-- forwarder (`unpad`) reassembling the ext channel.
module Blockchain.Safety.Transfer
  {BlockExt BlockBase : Type}
  (ext                : Deployment BlockExt)
  (let module Ext = Deployment ext)
  (base-spec          : Spec BlockBase Ext.n Ext.Network)
  (extension          : IsExtension base-spec Ext.spec)
  where

module B = Spec base-spec
open IsExtension extension

-- The honest nodes' channels, from the deployment.  The adversary channel is
-- read on the base side: the base spec's next to the extension layer's.
honest-IOF : ∀ {p} → p ∈ Ext.honest-nodes → Ext.IOF p ≡ Ext.IO
honest-IOF = Ext.honest-IOF

honest-AdvF : ∀ {p} → p ∈ Ext.honest-nodes → Ext.AdvF p ≡ B.Adv ⊗₀ AdvL
honest-AdvF hp = trans (Ext.honest-AdvF hp) ext-Adv≡base-Adv⊗AdvL

-- The base deployment's channels: the base spec's for honest parties, the ext
-- deployment's for the rest, whose nodes are kept as they are.
base-IOF : Fin Ext.n → Channel
base-IOF p = case p ∈? Ext.honest-nodes of λ where
  (yes _) → B.IO
  (no  _) → Ext.IOF p

base-AdvF : Fin Ext.n → Channel
base-AdvF p = case p ∈? Ext.honest-nodes of λ where
  (yes _) → B.Adv
  (no  _) → Ext.AdvF p

-- The extension layer's adversary channel, per party: `AdvL` for honest
-- parties, the unit for the rest, whose layer is `idᴷ`.
extAdv : Fin Ext.n → Channel
extAdv p = case p ∈? Ext.honest-nodes of λ where
  (yes _) → AdvL
  (no  _) → I

base-all-nodes : (p : Fin Ext.n) → Machine Ext.Network (base-IOF p ⊗₀ base-AdvF p)
base-all-nodes p with p ∈? Ext.honest-nodes
... | yes _ = B.honest-node-spec
... | no  _ = Ext.all-nodes p

base-honest-≡-spec : {p : Fin Ext.n} → p ∈ Ext.honest-nodes
                   → base-all-nodes p ≡ᴹ B.honest-node-spec
base-honest-≡-spec {p} hp with p ∈? Ext.honest-nodes
... | yes _   = ≡ᴹ-refl
... | no  ¬hp = contradiction hp ¬hp

base-honest-IOF : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-IOF p ≡ B.IO
base-honest-IOF {p} hp with p ∈? Ext.honest-nodes
... | yes _   = refl
... | no  ¬hp = contradiction hp ¬hp

base-honest-AdvF : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → base-AdvF p ≡ B.Adv
base-honest-AdvF {p} hp with p ∈? Ext.honest-nodes
... | yes _   = refl
... | no  ¬hp = contradiction hp ¬hp

extPart : (p : Fin Ext.n) → Machine (base-IOF p) (Ext.IOF p ⊗₀ extAdv p)
extPart p with p ∈? Ext.honest-nodes
... | yes hp = subst (λ x → Machine B.IO (x ⊗₀ AdvL)) (sym (honest-IOF hp)) ext-layer
... | no  _  = idᴷ

-- Reassembling an ext node's adversary channel from its base node's and its
-- layer's: a renaming for honest parties, the right unitor for the rest.
unpad : (p : Fin Ext.n) → Machine (base-AdvF p ⊗₀ extAdv p) (Ext.AdvF p)
unpad p with p ∈? Ext.honest-nodes
... | yes hp = subst (Machine (B.Adv ⊗₀ AdvL)) (sym (honest-AdvF hp)) CC.id
... | no  _  = ρ⇒

base : Deployment BlockBase
base = record
  { n                   = Ext.n
  ; Network             = Ext.Network
  ; spec                = base-spec
  ; NAdv                = Ext.NAdv
  ; IOF                 = base-IOF
  ; AdvF                = base-AdvF
  ; all-nodes           = base-all-nodes
  ; honest-nodes        = Ext.honest-nodes
  ; honest-nodes-≡-spec = base-honest-≡-spec
  ; honest-IOF          = base-honest-IOF
  ; honest-AdvF         = base-honest-AdvF
  ; network             = Ext.network
  }

module Base = Deployment base

private
  subst-≡ᴹ : ∀ {x y : Channel} {A B : Channel → Channel} → (eq : x ≡ y)
    → (M : Machine (A x) (B x)) → subst (λ x → Machine (A x) (B x)) eq M ≡ᴹ M
  subst-≡ᴹ refl _ = ≡ᴹ-refl

  -- The honest case of `single-protocol`, over channel variables so that the
  -- two channel equalities can be matched on.
  single-honest : ∀ {X Y} (eX : X ≡ Ext.IO) (eY : Y ≡ B.Adv ⊗₀ AdvL)
    (N : Machine Ext.Network (X ⊗₀ Y))
    → N ≡ᴹ (ext-layer ∘ᴷ B.honest-node-spec)
    → ((CC.id ⊗₁ subst (Machine (B.Adv ⊗₀ AdvL)) (sym eY) CC.id)
        CC.∘ (subst (λ x → Machine B.IO (x ⊗₀ AdvL)) (sym eX) ext-layer ∘ᴷ B.honest-node-spec))
      ≅ᴹ N
  single-honest refl refl N eq =
    ≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl)
    (≅ᴹ-trans ∘-identityˡ-≅ᴹ (≡ᴹ→≅ᴹ (≡ᴹ-sym eq)))

-- Each ext node is its extension layer stacked on its base node, once the
-- adversary channel is reassembled.  Honest parties by `is-extension`, the
-- rest by the unit law of `_∘ᴷ_`.
single-protocol : ∀ p
  → ((CC.id ⊗₁ unpad p) CC.∘ (extPart p ∘ᴷ base-all-nodes p)) ≅ᴹ Ext.all-nodes p
single-protocol p with p ∈? Ext.honest-nodes
... | no  _  = unit-∘ᴷ (Ext.all-nodes p)
... | yes hp = single-honest (honest-IOF hp) (honest-AdvF hp) (Ext.all-nodes p)
  (≡ᴹ-trans (Ext.honest-nodes-≡-spec hp)
  (≡ᴹ-trans (≡→≡ᴹ is-extension)
            (subst-≡ᴹ-out (sym ext-Adv≡base-Adv⊗AdvL) _)))

module Main where

  module _ {A : Channel} (E : Ext.Environment A) where

    -- Reassembling the ext deployment's channels from the base deployment's
    -- and the extension layers': a structure isomorphism.
    transId : Machine
      ((⨂ Ext.IOF ⊗₀ ⨂ extAdv) ⊗₀ (Ext.NAdv ⊗₀ ⨂ base-AdvF))
      (⨂ Ext.IOF ⊗₀ (Ext.NAdv ⊗₀ ⨂ Ext.AdvF))
    transId = ⨂-reshape-env-helper {n = Ext.n} {E₂' = λ p → base-AdvF p ⊗₀ extAdv p} {E₂ = Ext.AdvF} unpad
         CC.∘ ⨂-absorb-env-helper {E = Ext.NAdv} Ext.IOF {E₁ = base-AdvF} {E₂ = extAdv}

    transEnv : Base.Environment A
    transEnv = E CC.∘ transId CC.∘ ⨂ᴷ extPart ⊗₁ CC.id

    -- Was: a propositional `_≡ᴹ_`, proven from the `ChannelCat` equations.
    -- The shape of the chain is identical; every step is now a theorem
    -- (`CategoricalCrypto.Machine.Iso`, `CategoricalCrypto.Machine.NAry`).
    --
    -- Opaque on purpose.  While `insert-id`/`⨂-absorb-env` were record fields
    -- of a module parameter, `transState` below was a rigid term and
    -- `transState E ?s ≟ transState E s` solved by first-order unification;
    -- as theorems they unfold, and the unifier then has to compare two
    -- normal forms of the whole isomorphism instead.  Nothing downstream needs
    -- to see inside.
    opaque
      transProtocol : Ext.protocol E ≅ᴹ Base.protocol transEnv
      transProtocol =
        ≅ᴹ-trans (⨂-reshape-env Ext.all-nodes (λ p → extPart p ∘ᴷ base-all-nodes p)
                                unpad single-protocol Ext.network E)
        (≅ᴹ-trans (⨂-absorb-env extPart base-all-nodes Ext.network
                                (E CC.∘ ⨂-reshape-env-helper {n = Ext.n}
                                          {E₂' = λ p → base-AdvF p ⊗₀ extAdv p} {E₂ = Ext.AdvF} unpad))
                  (∘-resp-≅ᴹ assoc²γδ-≅ᴹ ≅ᴹ-refl))

    transState : Machine.State (Ext.protocol E) → Machine.State (Base.protocol transEnv)
    transState = _≅ᴹ_.to transProtocol

    transTrace : {s₁ s₂ : Machine.State (Ext.protocol E)} → Trace (Ext.protocol E) s₁ s₂
      → Trace (Base.protocol transEnv) (transState s₁) (transState s₂)
    transTrace = Trace-map transProtocol

  ChainLemma-ty : ∀ {A : Channel} → Ext.Environment A → Type
  ChainLemma-ty {A} E = ∀ {p : Fin Ext.n} {s} (p-honest : p ∈ Ext.honest-nodes)
    → Base.getChain (transEnv E) (transState E s) p-honest
    ≡ map getBaseBlock (Ext.getChain E s p-honest)

  module ≼-Reasoning {A} = Relation.Binary.Reasoning.PartialOrder (Poset-≼ {A})

  module _ {A : Channel} (E : Ext.Environment A) (CL : ChainLemma-ty E) (s : Machine.State (Ext.protocol E)) where
    open ≼-Reasoning

    private
      inj-≼ : {l₁ l₂ : List BlockExt}
            → map getBaseBlock l₁ ≼ map getBaseBlock l₂ → l₁ ≼ l₂
      inj-≼ = inj-map-≼ getBaseBlock-inj

    safeState-ext⇒base : (k : ℕ) → Ext.safeState k E s → Base.safeState k (transEnv E) (transState E s)
    safeState-ext⇒base k safe hp hp' = begin
        prune k (Base.getChain (transEnv E) (transState E s) hp)   ≡⟨ cong (prune k) (CL hp) ⟩
        prune k (map getBaseBlock (Ext.getChain E s hp))           ≡⟨ prune-map {k = k} ⟩
        map getBaseBlock (prune k (Ext.getChain E s hp))           ≤⟨ map-≼ (safe hp hp') ⟩
        map getBaseBlock (Ext.getChain E s hp')                    ≡⟨ CL hp' ⟨
        Base.getChain (transEnv E) (transState E s) hp'            ∎

    safeState-base⇒ext : (k : ℕ) → Base.safeState k (transEnv E) (transState E s) → Ext.safeState k E s
    safeState-base⇒ext k safe hp hp' = inj-≼ $ begin
        map getBaseBlock (prune k (Ext.getChain E s hp))           ≡⟨ prune-map {k = k} ⟨
        prune k (map getBaseBlock (Ext.getChain E s hp))           ≡⟨ cong (prune k) (CL hp) ⟨
        prune k (Base.getChain (transEnv E) (transState E s) hp)   ≤⟨ safe hp hp' ⟩
        Base.getChain (transEnv E) (transState E s) hp'            ≡⟨ CL hp' ⟩
        map getBaseBlock (Ext.getChain E s hp')                    ∎

  transfer : (k : ℕ)
           → (∀ {A} (E : Ext.Environment A) → ChainLemma-ty E)
           → Base.safety k → Ext.safety k
  transfer k CL baseSafety E init final trace safeInit =
    safeState-base⇒ext E (CL E) final k
      (baseSafety (transEnv E) (transState E init) (transState E final)
                  (transTrace E trace)
                  (safeState-ext⇒base E (CL E) init k safeInit))
