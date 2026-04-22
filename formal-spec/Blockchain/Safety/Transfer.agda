{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
open import Leios.ChannelCat

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC

import Relation.Binary.HeterogeneousEquality as H
import Relation.Binary.Reasoning.PartialOrder
open import Relation.Binary using (Poset)

-- | Generic safety transfer.
--
-- Given an ext `Safety` and an `IsExtension` witness (the base-side spec,
-- channel/layer equipment, and block-level projection), safety of the
-- derived base `Safety` implies safety of the ext `Safety`.
module Blockchain.Safety.Transfer
  {BlockExt BlockBase : Type}
  (ext                : Safety BlockExt)
  (let module Ext = Safety ext)
  (base-spec          : Spec BlockBase Ext.n Ext.Network)
  (cc                 : ChannelCat)
  (extension          : IsExtension base-spec (Safety.spec ext))
  where

module B = Spec base-spec
open IsExtension extension
open ChannelCat cc

-- On honest nodes, the per-participant channels agree with the ext spec's
-- `IO`/`Adv` channels.  Derived from `Ext.honest-nodes-≡-spec`.
honest-IOF : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → Ext.IOF p ≡ Ext.IO
honest-IOF hp = ⊗-injectiveˡ (_≡ᴹ_.B≡D (Ext.honest-nodes-≡-spec hp))

honest-AdvF : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → Ext.AdvF p ≡ B.Adv
honest-AdvF hp = trans (⊗-injectiveʳ (_≡ᴹ_.B≡D (Ext.honest-nodes-≡-spec hp))) ext-Adv≡base-Adv

-- Per-participant base IO channel: `B.IO` on honest nodes, else ext IOF.
base-IOF : Fin Ext.n → Channel
base-IOF p = case p ∈? Ext.honest-nodes of λ where
  (yes _) → B.IO
  (no  _) → Ext.IOF p

-- Honest nodes are replaced by `B.honest-node-spec`; dishonest nodes are unchanged.
base-all-nodes : (p : Fin Ext.n) → Machine Ext.Network (base-IOF p ⊗₀ Ext.AdvF p)
base-all-nodes p with p ∈? Ext.honest-nodes
... | yes hp = subst (λ x → Machine Ext.Network (B.IO ⊗₀ x)) (sym (honest-AdvF hp)) B.honest-node-spec
... | no  _  = Ext.all-nodes p

private
  subst-≡ᴹ : ∀ {x y : Channel} {A B : Channel → Channel} → (eq : x ≡ y)
    → (M : Machine (A x) (B x)) → subst (λ x → Machine (A x) (B x)) eq M ≡ᴹ M
  subst-≡ᴹ refl _ = ≡ᴹ-refl

base-honest-≡-spec : {p : Fin Ext.n} → p ∈ Ext.honest-nodes
                   → base-all-nodes p ≡ᴹ B.honest-node-spec
base-honest-≡-spec {p} hp with p ∈? Ext.honest-nodes
... | yes hp' = subst-≡ᴹ (sym (honest-AdvF hp')) B.honest-node-spec
... | no ¬hp  = contradiction hp ¬hp

-- Derived per-participant extension piece: honest nodes get `ext-layer`
-- (transported from `Ext.IO` to `Ext.IOF p`), dishonest nodes get identity
-- (with `base-IOF p` definitionally `Ext.IOF p`).
extPart : (p : Fin Ext.n) → Machine (base-IOF p) (Ext.IOF p ⊗₀ I)
extPart p with p ∈? Ext.honest-nodes
... | yes hp = subst (λ x → Machine B.IO (x ⊗₀ I)) (sym (honest-IOF hp)) ext-layer
... | no  _  = idᴷ

-- The derived base `Deployment` (over `base-spec`).
base-deployment : Deployment base-spec
base-deployment = record
  { NAdv                = Ext.NAdv
  ; IOF                 = base-IOF
  ; AdvF                = Ext.AdvF
  ; all-nodes           = base-all-nodes
  ; honest-nodes        = Ext.honest-nodes
  ; honest-nodes-≡-spec = base-honest-≡-spec
  ; network             = Ext.network
  }

-- The derived base `Safety` record.
base : Safety BlockBase
base = record
  { n          = Ext.n
  ; Network    = Ext.Network
  ; spec       = base-spec
  ; deployment = base-deployment
  }

module Base = Safety base

private
  -- Transitivity of `_≡ᴹ_`.
  ≡ᴹ-trans : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
             {M₁ : Machine A₁ B₁} {M₂ : Machine A₂ B₂} {M₃ : Machine A₃ B₃}
           → M₁ ≡ᴹ M₂ → M₂ ≡ᴹ M₃ → M₁ ≡ᴹ M₃
  ≡ᴹ-trans record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
           record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
    = ≡ᴹ-refl

  -- When both sides already have the same type, `_≡ᴹ_` collapses to `_≡_`.
  ≡ᴹ→≡ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ᴹ M₂ → M₁ ≡ M₂
  ≡ᴹ→≡ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } = refl

  -- Inclusion `_≡_ → _≡ᴹ_` at matching types.
  ≡→≡ᴹ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ M₂ → M₁ ≡ᴹ M₂
  ≡→≡ᴹ refl = ≡ᴹ-refl

  -- `subst` along a channel equality preserves the machine up to `_≡ᴹ_`
  -- (variant of `subst-≡ᴹ` where the channel equation affects only the
  -- output type).
  subst-≡ᴹ-out : ∀ {x y} {A : Channel} {B : Channel → Channel}
               → (eq : x ≡ y) (M : Machine A (B x))
               → subst (λ c → Machine A (B c)) eq M ≡ᴹ M
  subst-≡ᴹ-out refl _ = ≡ᴹ-refl

  -- `idᴷ` instantiated at different (but propositionally equal) channels
  -- are `_≡ᴹ_`.
  idᴷ-cong-≡ᴹ : ∀ {A B} → A ≡ B → _≡ᴹ_ (idᴷ {A = A}) (idᴷ {A = B})
  idᴷ-cong-≡ᴹ refl = ≡ᴹ-refl

-- Every ext node factors as `extPart p ∘ᴷ base-all-nodes p`.  For honest
-- nodes this follows from `is-extension` via `∘ᴷ-cong-≡ᴹ` (a ChannelCat
-- axiom); for dishonest nodes both sides definitionally reduce to the
-- same `idᴷ ∘ᴷ Ext.all-nodes p`.
single-protocol-≡ : ∀ p → idᴷ ∘ᴷ Ext.all-nodes p ≡ extPart p ∘ᴷ base-all-nodes p
single-protocol-≡ p with p ∈? Ext.honest-nodes
... | no ¬hp = refl
... | yes hp = ≡ᴹ→≡
  (≡ᴹ-trans (∘ᴷ-cong-≡ᴹ (idᴷ-cong-≡ᴹ (honest-IOF hp))
                        (Ext.honest-nodes-≡-spec hp))
  (≡ᴹ-trans (≡→≡ᴹ is-extension)
  (≡ᴹ-trans (subst-≡ᴹ-out (sym ext-Adv≡base-Adv) _)
            (∘ᴷ-cong-≡ᴹ (≡ᴹ-sym (subst-≡ᴹ (sym (honest-IOF hp)) ext-layer))
                        (≡ᴹ-sym (subst-≡ᴹ (sym (honest-AdvF hp)) B.honest-node-spec))))))

module Main where

  -- | Translation from extended protocols to base protocols.
  module _ {A : Channel} (E : Ext.Environment A) where

    -- this is a structure isomorphism
    transId : Machine
      ((⨂ Ext.IOF ⊗₀ (⨂_ {n = Ext.n} (const I))) ⊗₀ (Ext.NAdv ⊗₀ ⨂ Ext.AdvF))
      (⨂ Ext.IOF ⊗₀ (Ext.NAdv ⊗₀ ⨂ Ext.AdvF))
    transId = insert-id-helper Ext.AdvF ∘ (⨂-absorb-env-helper Ext.IOF)

    -- This is `E`, but we absorb the `extPart` part of each participant.
    transEnv : Base.Environment A
    transEnv = E ∘ transId ∘ ⨂ᴷ extPart ⊗₁ CC.id

    transProtocol : Ext.protocol E ≡ᴹ Base.protocol transEnv
    transProtocol = flip (subst (Ext.protocol E ≡ᴹ_)) ≡ᴹ-refl $
      E ∘ (Ext.nodes ∘ᴷ Ext.network) ≡⟨ insert-id Ext.all-nodes Ext.network E ⟩
      (E ∘ insert-id-helper Ext.AdvF) ∘ (⨂ᴷ (λ p → idᴷ ∘ᴷ Ext.all-nodes p) ∘ᴷ Ext.network)
        ≡⟨ cong (λ x → (E ∘ insert-id-helper Ext.AdvF) ∘ x ∘ᴷ Ext.network) (⨂ᴷ-cong single-protocol-≡) ⟩
      (E ∘ insert-id-helper Ext.AdvF) ∘ (⨂ᴷ (λ p → extPart p ∘ᴷ base-all-nodes p) ∘ᴷ Ext.network)
        ≡⟨ ⨂-absorb-env extPart base-all-nodes Ext.network (E ∘ insert-id-helper Ext.AdvF) ⟩
      ((E ∘ insert-id-helper Ext.AdvF) ∘ (⨂-absorb-env-helper Ext.IOF) ∘ ⨂ᴷ extPart ⊗₁ CC.id) ∘ ((⨂ᴷ base-all-nodes) ∘ᴷ Ext.network)
        ≡⟨ cong (_∘ (Base.nodes ∘ᴷ Ext.network)) (assoc²γδ {g = ⨂-absorb-env-helper Ext.IOF} {h = insert-id-helper Ext.AdvF}) ⟩
      (E ∘ transId ∘ ⨂ᴷ extPart ⊗₁ CC.id) ∘ (Base.nodes ∘ᴷ Base.network) ∎
      where
        open ≡-Reasoning

    transState : Machine.State (Ext.protocol E) → Machine.State (Base.protocol transEnv)
    transState = state-subst transProtocol

    transTrace : {s₁ s₂ : Machine.State (Ext.protocol E)} → Trace (Ext.protocol E) s₁ s₂
      → Trace (Base.protocol transEnv) (transState s₁) (transState s₂)
    transTrace = Trace-subst transProtocol

  -- | Chain lemma: the base chain is the `getBaseBlock`-projection of the ext chain.
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
