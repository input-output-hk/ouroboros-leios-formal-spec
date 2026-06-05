{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)

open import CategoricalCrypto hiding (id)
open import Categories.Category
open import Categories.Category.Helper
import Categories.Morphism.Reasoning
import Categories.GConstruction as GC

open import Class.Core
open import Class.Monad.Ext using (ExtensionalMonad; CommutativeMonad)
open import Class.Monad.Iterative using (IterativeMonad)
open import Class.Monad.OfRel using (MonadOfRel)

open import CategoricalCrypto.Machine.Category

module Leios.ChannelCat where

private variable A B C D E E₁ E₂ : Channel

-- This module exposes only `MachineCat`: the explicit library `MachineCategory`
-- plus the `TransferTrace.TraceCat` obligations discharged from it.  The former
-- `ChannelCat` record — the propositional `≡`/`≡ᴹ` machine-law bundle the
-- retired `Transfer.agda` consumed — has been removed; the trace-equivalence
-- rework states its obligations in `TransferTrace.TraceCat` instead, and the
-- `IsExtension≈` migration removed the last record consumers.

-- The library's `MachineCategory` is parameterised over a monad `M` with
-- seven instance laws and four law bundles.
module MachineCat
  {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ F-Laws        : FunctorLaws M      ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄
  ⦃ M-Comm        : CommutativeMonad M ⦄
  ⦃ M-Iter        : IterativeMonad M   ⦄
  ⦃ M-OfRel       : MonadOfRel M       ⦄
  (trLaws  : SFunᵉ-TraceLaws)
  (coh     : GC.GCoherence SFunᵉ-Category SFunᵉ-monoidal SFunᵉ-traced)
  (extLaws : ExtLaws trLaws coh)
  (mhLaws  : MaybeHomLaws trLaws coh extLaws)
  where

  MACHINE : Category (sucˡ zeroˡ) (sucˡ zeroˡ) (sucˡ zeroˡ)
  MACHINE = MachineCategory trLaws coh extLaws mhLaws

  module M = Categories.Morphism.Reasoning MACHINE
  open Category MACHINE using (_≈_)

  -- The `assoc²γδ` obligation of `TransferTrace.TraceCat` follows from the
  -- category structure of `MACHINE` (it is exactly `Reasoning.assoc²γδ`), at the
  -- category's observational equality `_≈ℰ_`.
  assoc²γδ : {f : Machine A B} {g : Machine B C} {h : Machine C D} {i : Machine D E}
    → ((i ∘ h) ∘ (g ∘ f)) ≈ (i ∘ ((h ∘ g) ∘ f))
  assoc²γδ = M.assoc²γδ

  -- The equivalence + congruence obligations of `TransferTrace.TraceCat`,
  -- discharged from `MACHINE` (a `Category`). These replace the propositional
  -- `≡`/`≡ᴹ` machine equalities the old `Transfer.agda` relies on. The
  -- remaining `TraceCat` obligations (`⊗₁-resp-≈`, the structure-iso laws,
  -- and `Reachable`/`≈-Reachable`) are NOT category-level and are not
  -- dischargeable from `MACHINE` alone.
  ≈-refl : {M₀ : Machine A B} → M₀ ≈ M₀
  ≈-refl = Category.Equiv.refl MACHINE

  ≈-sym : {M₀ N₀ : Machine A B} → M₀ ≈ N₀ → N₀ ≈ M₀
  ≈-sym = Category.Equiv.sym MACHINE

  ≈-trans : {M₀ N₀ P₀ : Machine A B} → M₀ ≈ N₀ → N₀ ≈ P₀ → M₀ ≈ P₀
  ≈-trans = Category.Equiv.trans MACHINE

  ∘-resp-≈ : {M₀ M₀' : Machine B C} {N₀ N₀' : Machine A B}
           → M₀ ≈ M₀' → N₀ ≈ N₀' → (M₀ ∘ N₀) ≈ (M₀' ∘ N₀')
  ∘-resp-≈ = Category.∘-resp-≈ MACHINE
