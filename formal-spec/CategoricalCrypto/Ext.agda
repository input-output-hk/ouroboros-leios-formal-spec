{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)
open import CategoricalCrypto hiding (id; _∘_)
import Relation.Binary.HeterogeneousEquality as H

open import Data.Maybe.Properties using (just-injective)

module CategoricalCrypto.Ext where

≡ᴹ-trans : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
           {M₁ : Machine A₁ B₁} {M₂ : Machine A₂ B₂} {M₃ : Machine A₃ B₃}
         → M₁ ≡ᴹ M₂ → M₂ ≡ᴹ M₃ → M₁ ≡ᴹ M₃
≡ᴹ-trans record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
         record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }
  = ≡ᴹ-refl

≡ᴹ→≡ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ᴹ M₂ → M₁ ≡ M₂
≡ᴹ→≡ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } = refl

≡→≡ᴹ : ∀ {A B} {M₁ M₂ : Machine A B} → M₁ ≡ M₂ → M₁ ≡ᴹ M₂
≡→≡ᴹ refl = ≡ᴹ-refl

subst-≡ᴹ-out : ∀ {x y} {A : Channel} {B : Channel → Channel}
             → (eq : x ≡ y) (M : Machine A (B x))
             → subst (λ c → Machine A (B c)) eq M ≡ᴹ M
subst-≡ᴹ-out refl _ = ≡ᴹ-refl

idᴷ-cong-≡ᴹ : ∀ {A B} → A ≡ B → _≡ᴹ_ (idᴷ {A = A}) (idᴷ {A = B})
idᴷ-cong-≡ᴹ refl = ≡ᴹ-refl

-- | The answer `queryCompute` computes is the one its completeness witness
-- carries, provided answers are determined by the message that reports them.
--
-- `queryCompute` reads its answer off `correctness` applied to the witness
-- `completeness` supplies, so the answer is pinned only as far as `queryO` is
-- injective.  Nothing about the machine's step relation is needed: both the
-- hypothesis and `correctness` speak about the SAME witness, so two answering
-- steps never have to be compared.
queryCompute-answer : ∀ {A B} {m : Machine A B} {Query : Type} {QueryReturnType : Query → Type}
  (ic : IsConstrained m QueryReturnType)
  (let open IsConstrained ic)
  → (∀ {q} {r r' : QueryReturnType q} → queryO r ≡ queryO r' → r ≡ r')
  → ∀ {q s r} → proj₁ (completeness {q} {s}) ≡ queryO {q} r
  → proj₁ (queryCompute q s) ≡ r
queryCompute-answer ic qO-inj {q} {s} eq =
  qO-inj (trans (sym (just-injective (proj₂ (correctness (proj₂ (proj₂ (completeness {q} {s}))))))) eq)
  where open IsConstrained ic
