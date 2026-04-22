{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
open import Leios.ChannelCat

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Ext

import Relation.Binary.Reasoning.PartialOrder
open import Relation.Binary using (Poset)

-- | Generic safety transfer.
--
-- Given an ext `Deployment` and an `IsExtension` witness (the base-side spec,
-- channel/layer equipment, and block-level projection), safety of the
-- derived base `Deployment` implies safety of the ext `Deployment`.
module Blockchain.Safety.Transfer
  {BlockExt BlockBase : Type}
  (ext                : Deployment BlockExt)
  (let module Ext = Deployment ext)
  (base-spec          : Spec BlockBase Ext.n Ext.Network)
  (cc                 : ChannelCat)
  (extension          : IsExtension base-spec Ext.spec)
  where

module B = Spec base-spec
open IsExtension extension
open ChannelCat cc

honest-IOF : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → Ext.IOF p ≡ Ext.IO
honest-IOF hp = ⊗-injectiveˡ (_≡ᴹ_.B≡D (Ext.honest-nodes-≡-spec hp))

honest-AdvF : {p : Fin Ext.n} → p ∈ Ext.honest-nodes → Ext.AdvF p ≡ B.Adv
honest-AdvF hp = trans (⊗-injectiveʳ (_≡ᴹ_.B≡D (Ext.honest-nodes-≡-spec hp))) ext-Adv≡base-Adv

base-IOF : Fin Ext.n → Channel
base-IOF p = case p ∈? Ext.honest-nodes of λ where
  (yes _) → B.IO
  (no  _) → Ext.IOF p

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

extPart : (p : Fin Ext.n) → Machine (base-IOF p) (Ext.IOF p ⊗₀ I)
extPart p with p ∈? Ext.honest-nodes
... | yes hp = subst (λ x → Machine B.IO (x ⊗₀ I)) (sym (honest-IOF hp)) ext-layer
... | no  _  = idᴷ

base : Deployment BlockBase
base = record
  { n                   = Ext.n
  ; Network             = Ext.Network
  ; spec                = base-spec
  ; NAdv                = Ext.NAdv
  ; IOF                 = base-IOF
  ; AdvF                = Ext.AdvF
  ; all-nodes           = base-all-nodes
  ; honest-nodes        = Ext.honest-nodes
  ; honest-nodes-≡-spec = base-honest-≡-spec
  ; network             = Ext.network
  }

module Base = Deployment base

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

  module _ {A : Channel} (E : Ext.Environment A) where

    -- this is a structure isomorphism
    transId : Machine
      ((⨂ Ext.IOF ⊗₀ (⨂_ {n = Ext.n} (const I))) ⊗₀ (Ext.NAdv ⊗₀ ⨂ Ext.AdvF))
      (⨂ Ext.IOF ⊗₀ (Ext.NAdv ⊗₀ ⨂ Ext.AdvF))
    transId = insert-id-helper Ext.AdvF ∘ (⨂-absorb-env-helper Ext.IOF)

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
