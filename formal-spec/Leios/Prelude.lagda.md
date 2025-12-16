## Leios.Prelude
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
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

module N where
  open import Data.Nat public
  open import Data.Nat.Properties public
open N public using (ℕ; zero; suc)

module F where
  open import Data.Fin public
  open import Data.Fin.Patterns public
  open import Data.Fin.Properties public
open F public using (Fin; toℕ; #_; 0F) renaming (zero to fzero; suc to fsuc)

module L where
  open import Data.List public
open L public using (List; []; _∷_; _++_; catMaybes; head; length; sum; and; or; any)

module Any where
  open import Data.List.Relation.Unary.Any public
open Any public using (here; there)

module All where
  open import Data.List.Relation.Unary.All public

open import Data.List.Relation.Unary.Unique.DecPropositional N._≟_ using (Unique) public
```
```agda
filter : {A : Set} → (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → List A → List A
filter P = L.filter ¿ P ¿¹

instance
  IsSet-List : {A : Set} → IsSet (List A) A
  IsSet-List .toSet A = fromList A

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

record Listable (A : Type) : Type where
  field
    listing  : ℙ A
    complete : ∀ {a : A} → a ∈ listing

totalDec : ∀ {A B : Type} → ⦃ DecEq A ⦄ → ⦃ Listable A ⦄ → {R : Rel A B} → Dec (total R)
totalDec {A} {B} {R} with all? (_∈? dom R)
... | yes p = yes λ {a} → p {a} ((Listable.complete it) {a})
... | no ¬p = no λ x → ¬p λ {a} _ → x {a}

instance
  total? : ∀ {A B : Type} → ⦃ DecEq A ⦄ → ⦃ Listable A ⦄ → {R : Rel A B} → ({a : A} → a ∈ dom R) ⁇
  total? = ⁇ totalDec

  Listable-Fin : ∀ {n} → Listable (Fin n)
  Listable-Fin {zero} = record { listing = ∅ ; complete = λ {a} → ⊥-elim $ (Inverse.to F.0↔⊥) a }
  Listable-Fin {suc n} =
    let record { listing = l ; complete = c } = Listable-Fin {n}
    in record
         { listing = singleton (F.fromℕ n) ∪ mapˢ F.inject₁ l
         ; complete = complete
         }
       where
         complete : ∀ {a} → a ∈ singleton (F.fromℕ n) ∪ mapˢ F.inject₁ (let record { listing = l } = Listable-Fin {n} in l)
         complete {a} with F.toℕ a N.<? n
         ... | yes p =
           let record { listing = l ; complete = c } = Listable-Fin {n}
               n≢toℕ = ≢-sym (N.<⇒≢ p)
               fn = F.lower₁ a n≢toℕ
               fn≡a = F.inject₁-lower₁ a n≢toℕ
           in (Equivalence.to ∈-∪) (inj₂ ((Equivalence.to ∈-map) (fn , (sym fn≡a , c))))
         ... | no ¬p with a F.≟ F.fromℕ n
         ... | yes q = (Equivalence.to ∈-∪) (inj₁ ((Equivalence.to ∈-singleton) q))
         ... | no ¬q =
           let n≢toℕ = N.≰⇒> ¬p
               a<sucn = F.toℕ<n a
           in ⊥-elim $ (¬q ∘ toℕ-fromℕ) (N.suc-injective (m≤n∧n≤m⇒m≡n n≢toℕ a<sucn))

completeFinL : ∀ (n : ℕ) → List (Fin n)
completeFinL zero = []
completeFinL (ℕ.suc n) = F.fromℕ n ∷ L.map F.inject₁ (completeFinL n)
```
