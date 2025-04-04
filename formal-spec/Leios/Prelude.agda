{-# OPTIONS --safe #-}

module Leios.Prelude where

open import abstract-set-theory.FiniteSetTheory public
open import abstract-set-theory.Prelude public
open import Data.List using (upTo)

open import Class.HasAdd public
open import Class.HasOrder public
open import Class.Hashable public
open import Prelude.InferenceRules public

module T where
  open import Data.These public
open T public using (These; this; that)

module L where
  open import Data.List public
open L public using (List; []; _∷_; _++_; catMaybes; head; length; sum; and; or; any)

module A where
  open import Data.List.Relation.Unary.Any public
open A public using (here; there)

module N where
  open import Data.Nat public
  open import Data.Nat.Properties public
open N public using (ℕ; zero; suc)

module F where
  open import Data.Fin public
  open import Data.Fin.Properties public
open F public using (Fin; toℕ; #_) renaming (zero to fzero; suc to fsuc)

fromTo : ℕ → ℕ → List ℕ
fromTo m n = map (_+ m) (upTo (n ∸ m))

slice : (L : ℕ) → ⦃ NonZero L ⦄ → ℕ → ℕ → ℙ ℕ
slice L s x = fromList (fromTo s' (s' + (L ∸ 1)))
  where s' = ((s / L) ∸ x) * L -- equivalent to the formula in the paper

filter : {A : Set} → (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → List A → List A
filter P = L.filter ¿ P ¿¹

instance
  IsSet-List : {A : Set} → IsSet (List A) A
  IsSet-List .toSet A = fromList A

open import Data.List.Relation.Unary.Any
open Properties

finite⇒A≡∅⊎∃a∈A : {X : Type} → {A : ℙ X} → finite A → (A ≡ᵉ ∅) ⊎ Σ[ a ∈ X ] a ∈ A
finite⇒A≡∅⊎∃a∈A ([]    , h) = inj₁ (∅-least (λ a∈A → ⊥-elim (case Equivalence.to h a∈A of λ ())))
finite⇒A≡∅⊎∃a∈A (x ∷ _ , h) = inj₂ (x , Equivalence.from h (here refl))

completeFin : ∀ (n : ℕ) → ℙ (Fin n)
completeFin zero = ∅
completeFin (ℕ.suc n) = singleton (F.fromℕ n) ∪ mapˢ F.inject₁ (completeFin n)

m≤n∧n≤m⇒m≡n : ∀ {n m : ℕ} → n N.≤ m → m N.≤ n → m ≡ n
m≤n∧n≤m⇒m≡n z≤n z≤n = refl
m≤n∧n≤m⇒m≡n (s≤s n≤m) (s≤s m≤n) = cong N.suc (m≤n∧n≤m⇒m≡n n≤m m≤n)

toℕ-fromℕ : ∀ {n} {a : Fin (N.suc n)} → toℕ a ≡ n → a ≡ F.fromℕ n
toℕ-fromℕ {zero} {fzero} x = refl
toℕ-fromℕ {N.suc n} {fsuc a} x = cong fsuc (toℕ-fromℕ {n} {a} (N.suc-injective x))

open Equivalence

maximalFin : ∀ (n : ℕ) → isMaximal (completeFin n)
maximalFin (ℕ.suc n) {a} with toℕ a N.<? n
... | yes p =
  let n≢toℕ = ≢-sym (N.<⇒≢ p)
      fn = F.lower₁ a n≢toℕ
      fn≡a = F.inject₁-lower₁ a n≢toℕ
  in (to ∈-∪) (inj₂ ((to ∈-map) (fn , (sym fn≡a , maximalFin n))))
... | no ¬p with a F.≟ F.fromℕ n
... | yes q = (to ∈-∪) (inj₁ ((to ∈-singleton) q))
... | no ¬q =
  let n≢toℕ = N.≰⇒> ¬p
      a<sucn = F.toℕ<n a
  in ⊥-elim $ (¬q ∘ toℕ-fromℕ) (N.suc-injective (m≤n∧n≤m⇒m≡n n≢toℕ a<sucn))
