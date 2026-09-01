{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_)
open import CategoricalCrypto.IsoExt

module Leios.ChannelCat where

private variable A B C D E E₁ E₂ E₃ : Channel

-- ============================================================================
-- The former `ChannelCat` was INCONSISTENT.  Kept here, renamed, with the
-- proof — so the record cannot be reintroduced by accident.
--
--   ⊗-identityˡ : I ⊗₀ A ≡ A        ⊗-identityʳ : A ⊗₀ I ≡ A
--
-- together give `I ⊗₀ A ≡ A ⊗₀ I`, and `⊗-injectiveˡ` then collapses that to
-- `I ≡ A` for EVERY channel `A`.  Instantiating at `A = ⊤ ⇿ ⊤` gives `⊥ ≡ ⊤`.
--
-- Everything proved under a `ChannelCatPostulates` hypothesis is therefore
-- vacuous: the hypothesis is uninhabitable, so the implication says nothing.
-- ============================================================================

record ChannelCatPostulates : Type₁ where
  field
    ⊗-injectiveˡ : A ⊗₀ B ≡ C ⊗₀ D → A ≡ C
    ⊗-identityˡ  : I ⊗₀ A ≡ A
    ⊗-identityʳ  : A ⊗₀ I ≡ A

channelCatPostulates-inconsistent : ChannelCatPostulates → ⊥
channelCatPostulates-inconsistent cc = subst Channel.inType (sym I≡⊤) tt
  where
    open ChannelCatPostulates cc

    I≡⊤ : I ≡ (⊤ ⇿ ⊤)
    I≡⊤ = ⊗-injectiveˡ (trans (⊗-identityˡ {A = ⊤ ⇿ ⊤}) (sym (⊗-identityʳ {A = ⊤ ⇿ ⊤})))

-- ============================================================================
-- The structural machines the transfer needs.  All of these were fields of the
-- old record; every one of them is an ordinary definition, built by the
-- channel-forwarding solver exactly as `Machine.Core` builds `⊗-assoc`,
-- `⊗-symₘ` and `idᴷ`.
-- ============================================================================

ρ⇒ : Machine (A ⊗₀ I) A
ρ⇒ = TotalFunctionMachine' ⊗-right-neutral ⊗-right-intro

ρ⇐ : Machine A (A ⊗₀ I)
ρ⇐ = TotalFunctionMachine' ⊗-right-intro ⊗-right-neutral

λ⇒ : Machine (I ⊗₀ A) A
λ⇒ = TotalFunctionMachine' ⊗-left-neutral ⊗-left-intro

σ : Machine (A ⊗₀ B) (B ⊗₀ A)
σ = ⊗-symₘ

α⇒ : Machine ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
α⇒ = ⊗-assoc

α⇐ : Machine (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
α⇐ = ⊗-assoc⃖

insert-id-helper : ∀ {n} (C : Fin n → Channel)
  → Machine (A ⊗₀ B ⊗₀ (⨂ (λ k → C k ⊗₀ I))) (A ⊗₀ B ⊗₀ (⨂ C))
insert-id-helper {n = n} _ = CC.id ⊗₁ CC.id ⊗₁ ⨂₁ {n = n} (λ _ → ρ⇒)

-- ============================================================================
-- What actually remains as an assumption.
--
-- The old record had ~30 fields; the ∘/⊗ laws are now theorems
-- (`CategoricalCrypto.Machine.Iso`, `CategoricalCrypto.IsoExt`), the structural
-- machines are definitions (above), and the two channel-injectivity fields —
-- the inconsistent ones — become explicit parameters of the transfer, where a
-- uniform deployment discharges them with `refl`.
--
-- These two are the genuine content: rewiring a ⨂ of per-node machines past
-- the environment.  Both are stated at `_≅ᴹ_` (a bisimulation) rather than
-- propositional machine equality, so unlike their predecessors they are, at
-- least, satisfiable.
-- ============================================================================

record ChannelCat : Type₁ where
  field
    -- The one unit law that survives, needed only to identify an adversary
    -- channel `A ⊗₀ I` with `A` (`Network.Leios`'s `ext-Adv≡base-Adv`).
    --
    -- On its own this is merely UNPROVABLE, not absurd: it is `X ⊎ ⊥ ≡ X`,
    -- which holds in a univalent model.  What made the old record inconsistent
    -- was asserting it alongside `⊗-injectiveˡ` — the two are incompatible,
    -- since a unit law is precisely a failure of injectivity.  Only one of them
    -- may be assumed, and this is the one that is actually used.
    ⊗-identityʳ : A ⊗₀ I ≡ A

    ⨂-absorb-env-helper : ∀ {n} (D : Fin n → Channel) {E₁ E₂ : Fin n → Channel}
      → Machine ((⨂ D ⊗₀ ⨂ E₂) ⊗₀ E ⊗₀ (⨂ E₁)) ((⨂ D) ⊗₀ E ⊗₀ (⨂ (λ k → E₁ k ⊗₀ E₂ k)))

    insert-id : ∀ {n} {E₁} {B C E₂ : Fin n → Channel}
      → (f : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k)) (g : Machine A (⨂ B ⊗₀ E₁))
      → (α : Machine (⨂ C ⊗₀ E₁ ⊗₀ ⨂ E₂) D)
      → (α CC.∘ (⨂ᴷ f ∘ᴷ g))
        ≅ᴹ ((α CC.∘ insert-id-helper E₂) CC.∘ (⨂ᴷ (λ k → idᴷ ∘ᴷ f k) ∘ᴷ g))

    ⨂-absorb-env : ∀ {n} {B C D E₁ E₂ : Fin n → Channel} {F : Channel}
      (f : (k : Fin n) → Machine (C k) (D k ⊗₀ E₂ k))
      (g : (k : Fin n) → Machine (B k) (C k ⊗₀ E₁ k))
      (h : Machine A (⨂ B ⊗₀ E))
      (α : Machine (⨂ D ⊗₀ E ⊗₀ ⨂ (λ k → E₁ k ⊗₀ E₂ k)) F)
      → (α CC.∘ (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h))
        ≅ᴹ ((α CC.∘ (⨂-absorb-env-helper D) CC.∘ (⨂ᴷ f ⊗₁ CC.id)) CC.∘ (⨂ᴷ g ∘ᴷ h))
