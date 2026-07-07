{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import Categories.Category
open import Categories.Category.Helper
import Categories.Morphism.Reasoning

module Leios.ChannelCat where

private variable A B C D E E₁ E₂ E₃ : Channel

record ChannelCat : Type₁ where
  field
    ⊗-injectiveˡ : A ⊗₀ B ≡ C ⊗₀ D → A ≡ C
    ⊗-injectiveʳ : A ⊗₀ B ≡ C ⊗₀ D → B ≡ D
    ⊗-identityˡ : I ⊗₀ A ≡ A
    ⊗-identityʳ : A ⊗₀ I ≡ A
    I-helper : ∀ {n} → (⨂_ {n} (const I)) ≡ I
    ∘-assoc : {M₁ : Machine C D} {M₂ : Machine B C} {M₃ : Machine A B} → (M₁ ∘ M₂) ∘ M₃ ≡ M₁ ∘ M₂ ∘ M₃
    idᴹ : Machine A A
    _∘ᴹ_ : Machine B C → Machine A B → Machine A C
    ∘ᴹ-assoc : {M₃ : Machine A B} {M₂ : Machine B C} {M₁ : Machine C D}
      → (M₁ ∘ᴹ M₂) ∘ᴹ M₃ ≡ M₁ ∘ᴹ (M₂ ∘ᴹ M₃)
    ∘ᴹ-identityˡ : {f : Machine A B} → (idᴹ ∘ᴹ f) ≡ f
    ∘ᴹ-identityʳ : {f : Machine A B} → (f ∘ᴹ idᴹ) ≡ f
    ∘ᴹ-resp-≡ : {f h : Machine B C} {g i : Machine A B} → f ≡ h → g ≡ i → (f ∘ᴹ g) ≡ (h ∘ᴹ i)

    assoc²γδ : {f : Machine A B} {g : Machine B C} {h : Machine C D} {i : Machine D E}
      → (i ∘ h) ∘ (g ∘ f) ≡ i ∘ ((h ∘ g) ∘ f)
    σ : Machine (A ⊗₀ B) (B ⊗₀ A)
    α⇒ : Machine ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
    α⇐ : Machine (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
    λ⇒ : Machine (I ⊗₀ A) A
    ρ⇒ : Machine (A ⊗₀ I) A
    ρ⇐ : Machine A (A ⊗₀ I)

    ⨂ᴷ-⊗-∘ : ∀ {n} {f : Fin n → Machine B C} {g : Fin n → Machine E₁ E₂} {h : Fin n → Machine A (B ⊗₀ E₁)}
      → ⨂ᴷ (λ k → (f k ⊗₁ g k) ∘ h k) ≡ ((⨂₁ f) ⊗₁ ⨂₁ g) ∘ ⨂ᴷ h

    ∘ᴷ-assoc : {M₁ : Machine C (D ⊗₀ E₃)} {M₂ : Machine B (C ⊗₀ E₂)} {M₃ : Machine A (B ⊗₀ E₁)}
      → (M₁ ∘ᴷ M₂) ∘ᴷ M₃ ≡ (CC.id ⊗₁ α⇒) ∘ (M₁ ∘ᴷ M₂ ∘ᴷ M₃)

    ∘ᴷ-assoc' : {M₁ : Machine C (D ⊗₀ E₃)} {M₂ : Machine B (C ⊗₀ E₂)} {M₃ : Machine A (B ⊗₀ E₁)}
      → M₁ ∘ᴷ M₂ ∘ᴷ M₃ ≡ (CC.id ⊗₁ α⇐) ∘ ((M₁ ∘ᴷ M₂) ∘ᴷ M₃)

    ⨂-⊗-swap : {n : ℕ} {F₁ F₂ : Fin n → Channel} → Machine ((⨂ F₁) ⊗₀ (⨂ F₂)) (⨂ (λ k → F₁ k ⊗₀ F₂ k))

    ⨂-⊗-swap' : {n : ℕ} {F₁ F₂ : Fin n → Channel} → Machine (⨂ (λ k → F₁ k ⊗₀ F₂ k)) ((⨂ F₁) ⊗₀ (⨂ F₂))

    ⨂ᴷ-∘ᴷ-⨂ᴷ : ∀ {n} {f : Fin n → Machine A (B ⊗₀ E₁)} {g : Fin n → Machine B (C ⊗₀ E₂)}
      → ⨂ᴷ (λ k → g k ∘ᴷ f k) ≡ (CC.id ⊗₁ (⨂-⊗-swap {n = n} {F₁ = const E₁} {F₂ = const E₂})) ∘ (⨂ᴷ g ∘ᴷ ⨂ᴷ f)

    ⨂ᴷ-∘ᴷ-⨂ᴷ' : ∀ {n} {f : Fin n → Machine A (B ⊗₀ E₁)} {g : Fin n → Machine B (C ⊗₀ E₂)}
      → (⨂ᴷ g ∘ᴷ ⨂ᴷ f) ≡ (CC.id ⊗₁ (⨂-⊗-swap' {n = n} {F₁ = const E₁} {F₂ = const E₂})) ∘ ⨂ᴷ (λ k → g k ∘ᴷ f k)

    liftᴷ-∘ᴷ : {f : Machine A (B ⊗₀ E₁)} {g : Machine B (C ⊗₀ E₂)}
      → liftᴷ g ∘ᴷ f ≡ ((CC.id ⊗₁ ρ⇐) ∘ α⇐ ∘ (CC.id ⊗₁ σ)) ∘ (g ∘ᴷ f)

    ⨂-absorb-env-helper : ∀ {n} (D : Fin n → Channel) {E₁ E₂ : Fin n → Channel}
      → Machine ((⨂ D ⊗₀ ⨂ E₂) ⊗₀ E ⊗₀ (⨂ E₁)) ((⨂ D) ⊗₀ E ⊗₀ (⨂ (λ k → E₁ k ⊗₀ E₂ k)))

    ⨂-absorb-env : ∀ {n} {B C D E₁ E₂ : Fin n → Channel} {F : Channel}
      (f : (k : Fin n) → Machine (C k) (D k ⊗₀ E₂ k)) (g : (k : Fin n) → Machine (B k) (C k ⊗₀ E₁ k)) (h : Machine A (⨂ B ⊗₀ E))
      (α : Machine (⨂ D ⊗₀ E ⊗₀ ⨂ (λ k → E₁ k ⊗₀ E₂ k)) F)
      → α ∘ (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h) ≡ (α ∘ (⨂-absorb-env-helper D) ∘ ⨂ᴷ f ⊗₁ CC.id) ∘ (⨂ᴷ g ∘ᴷ h)

    ⨂ᴷ-cong : ∀ {n} {A B E : Fin n → Channel} {f g : (k : Fin n) → Machine (A k) (B k ⊗₀ E k)}
      → (∀ k → f k ≡ g k) → ⨂ᴷ f ≡ ⨂ᴷ g

    ⨂-cong : ∀ {n} {A B : Fin n → Channel} → (∀ k → A k ≡ B k) → Machine (⨂ A) (⨂ B)

    -- Congruence of Kleisli composition under heterogeneous machine equality.
    ∘ᴷ-cong-≡ᴹ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂ E₁₁ E₁₂ E₂₁ E₂₂}
                  {M : Machine B₁ (C₁ ⊗₀ E₂₁)} {M' : Machine B₂ (C₂ ⊗₀ E₂₂)}
                  {N : Machine A₁ (B₁ ⊗₀ E₁₁)} {N' : Machine A₂ (B₂ ⊗₀ E₁₂)}
                → M ≡ᴹ M' → N ≡ᴹ N' → (M ∘ᴷ N) ≡ᴹ (M' ∘ᴷ N')

  insert-id-helper : ∀ {n} (C : Fin n → Channel)
    → Machine (A ⊗₀ B ⊗₀ (⨂ (λ k → C k ⊗₀ I))) (A ⊗₀ B ⊗₀ (⨂ C))
  insert-id-helper {n = n} _ = CC.id ⊗₁ CC.id ⊗₁ ⨂₁ {n = n} (λ _ → ρ⇒)

  field
    insert-id : ∀ {n} {E₁} {B C E₂ : Fin n → Channel}
      → (f : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k)) (g : Machine A (⨂ B ⊗₀ E₁))
      → (α : Machine (⨂ C ⊗₀ E₁ ⊗₀ ⨂ E₂) D)
      → α ∘ (⨂ᴷ f ∘ᴷ g) ≡ (α ∘ insert-id-helper E₂) ∘ (⨂ᴷ (λ k → idᴷ ∘ᴷ f k) ∘ᴷ g)

  MACHINE : Category (sucˡ zeroˡ) (sucˡ zeroˡ) (sucˡ zeroˡ)
  MACHINE = categoryHelper record
    { Obj = Channel
    ; _⇒_ = Machine
    ; _≈_ = _≡_
    ; id = idᴹ
    ; _∘_ = _∘ᴹ_
    ; assoc = ∘ᴹ-assoc
    ; identityˡ = ∘ᴹ-identityˡ
    ; identityʳ = ∘ᴹ-identityʳ
    ; equiv = record { refl = refl ; sym = sym ; trans = trans }
    ; ∘-resp-≈ = ∘ᴹ-resp-≡
    }

  module M = Categories.Morphism.Reasoning MACHINE

  ⊗-identityʳ-helper : B ≡ I → Machine A C → Machine (A ⊗₀ B) C
  ⊗-identityʳ-helper {A = A} refl M = M ∘ subst (λ x → Machine x A) (sym ⊗-identityʳ) CategoricalCrypto.id

  ⊗ᴷ-⊗ : {M₁ : Machine A (B ⊗₀ E₁)} {M₂ : Machine C (D ⊗₀ E₂)}
    → ∃[ π ] M₁ ⊗ᴷ M₂ ≡ π ∘ M₁ ⊗₁ M₂
  ⊗ᴷ-⊗ = -, refl

  -- this is a structure iso
  ⊗ᴷ-⊗₁ : Machine ((A ⊗₀ B) ⊗₀ C ⊗₀ D) ((A ⊗₀ C) ⊗₀ B ⊗₀ D)
  ⊗ᴷ-⊗₁ = proj₁ (⊗ᴷ-⊗ {M₁ = CategoricalCrypto.id} {CategoricalCrypto.id})
