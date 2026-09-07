{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_)
open import CategoricalCrypto.IsoExt
open import Tactic.Defaults

module Leios.ChannelCat where

private variable A B C D E E₁ E₂ E₃ : Channel

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

-- The middle-four interchange on channels.  Exposed rather than hidden inside
-- `⨂-zip`, because discharging the `⨂-absorb-env` law needs to name it
-- (see `Leios.ChannelCat.Monoidal`).
mid4 : ∀ {P Q R S} → Machine ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
mid4 = TotalFunctionMachine' ⇒-solver ⇒-solver

-- The n-ary interchange ("zip"): two parallel ⨂s of channels become one ⨂ of
-- pairs.  This is the only part of `⨂-absorb-env-helper` below that needs
-- induction — everything else is a fixed permutation of four channel atoms,
-- which `⇒-solver` builds.  At each step the head channels are pulled together
-- and the tails are zipped recursively.
⨂-zip : ∀ {n} {F₁ F₂ : Fin n → Channel}
      → Machine (⨂ F₁ ⊗₀ ⨂ F₂) (⨂ (λ k → F₁ k ⊗₀ F₂ k))
⨂-zip {zero}            = λ⇒
⨂-zip {suc n} {F₁} {F₂} =
  (CC.id ⊗₁ ⨂-zip {n} {λ k → F₁ (fsuc k)} {λ k → F₂ (fsuc k)}) ∘ mid4

-- The permutation half of `⨂-absorb-env-helper`, at its natural generality.
-- Exposed rather than hidden in a `where`, because discharging the
-- `⨂-absorb-env` law needs to reason about it (see `Leios.ChannelCat.Monoidal`).
absorb-regroup : ∀ {X Y Z W} → Machine ((X ⊗₀ Y) ⊗₀ (W ⊗₀ Z)) (X ⊗₀ (W ⊗₀ (Z ⊗₀ Y)))
absorb-regroup = TotalFunctionMachine' ⇒-solver ⇒-solver

-- Rewiring the per-node environment channels past the shared environment `E`:
-- the `⨂ E₂` that composition strands on the left is carried across and zipped
-- onto the `⨂ E₁` on the right.  A four-atom permutation, then `⨂-zip`.
⨂-absorb-env-helper : ∀ {n} {E : Channel} (D : Fin n → Channel) {E₁ E₂ : Fin n → Channel}
  → Machine ((⨂ D ⊗₀ ⨂ E₂) ⊗₀ E ⊗₀ (⨂ E₁)) ((⨂ D) ⊗₀ E ⊗₀ (⨂ (λ k → E₁ k ⊗₀ E₂ k)))
⨂-absorb-env-helper {n} {E} D {E₁} {E₂} =
  (CC.id ⊗₁ CC.id ⊗₁ ⨂-zip {n} {E₁} {E₂}) ∘ absorb-regroup

-- ============================================================================
-- What actually remains as an assumption.
--
-- The old record had ~30 fields; the ∘/⊗ laws are now theorems
-- (`CategoricalCrypto.Machine.Iso`, `CategoricalCrypto.IsoExt`), the structural
-- machines are definitions (above), and the two channel-injectivity fields —
-- the inconsistent ones — become explicit parameters of the transfer, where a
-- uniform deployment discharges them with `refl`.
--
-- The unit law `A ⊗₀ I ≡ A` is gone too.  It is unprovable in `--safe` Agda
-- (it is `X ⊎ ⊥ ≡ X`, which needs univalence), and it was only ever used to
-- `subst` a machine along a channel equality.  `Network.Leios` composes with
-- the right unitor `ρ⇒` above instead, so the channels it used to reconcile
-- are now definitionally equal and `ext-Adv≡base-Adv` is `refl`.
--
-- `⨂-absorb-env-helper` is gone as well.  It was never a proposition, only a
-- machine, so it just had to be built: a four-atom permutation from
-- `⇒-solver`, then the n-ary interchange `⨂-zip` above.
--
-- What is left is the genuine content, and it is genuinely two laws: rewiring
-- a ⨂ of per-node machines past the environment really does change the state
-- space, so an equation is needed, not a definition.  Both are stated at
-- `_≅ᴹ_` (a bisimulation) rather than propositional machine equality, so
-- unlike their predecessors they are, at least, satisfiable.
-- ============================================================================

record ChannelCat : Type₁ where
  field
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
