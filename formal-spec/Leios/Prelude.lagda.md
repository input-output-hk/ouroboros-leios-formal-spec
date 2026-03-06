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
private variable
  A B : Type
  l₁ l₂ : List A

filter : (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → List A → List A
filter P = L.filter ¿ P ¿¹

instance
  IsSet-List : IsSet (List A) A
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

totalDec : ⦃ DecEq A ⦄ → ⦃ Listable A ⦄ → {R : Rel A B} → Dec (total R)
totalDec {A} {B} {R} with all? (_∈? dom R)
... | yes p = yes λ {a} → p {a} ((Listable.complete it) {a})
... | no ¬p = no λ x → ¬p λ {a} _ → x {a}

instance
  total? : ⦃ DecEq A ⦄ → ⦃ Listable A ⦄ → {R : Rel A B} → ({a : A} → a ∈ dom R) ⁇
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

prune : {A : Type} → ℕ → List A → List A
prune k l = take (length l ∸ k) l

open import Relation.Binary hiding (_⇔_)
open import Data.List.Properties
import Relation.Binary.PropositionalEquality

module _ {A : Type} where
  _≼_ : List A → List A → Type
  l₁ ≼ l = ∃[ l₂ ] l₁ ++ l₂ ≡ l

  _≼′_ : List A → List A → Type
  l₁ ≼′ l₂ = ∃[ n ] l₁ ≡ take n l₂

  IsPreorder-≼ : IsPreorder _≡_ _≼_
  IsPreorder-≼ = record
    { isEquivalence = record { Relation.Binary.PropositionalEquality }
    ; reflexive = λ where refl → [] , ++-identityʳ _
    ; trans = λ where (l₁ , refl) (l₂ , refl) → l₁ ++ l₂ , sym (++-assoc _ l₁ l₂)
    }

  IsPartialOrder-≼ : IsPartialOrder _≡_ _≼_
  IsPartialOrder-≼ = record
    { isPreorder = IsPreorder-≼
    ; antisym = λ where {i} (l₁ , refl) (l₂ , eq₂) → let
        l₁++l₂≡[] = ++-identityʳ-unique i (trans (sym eq₂) (++-assoc i l₁ l₂))
        l₁≡[] = ++-conicalˡ l₁ l₂ l₁++l₂≡[]
        in subst (λ x → i ≡ i ++ x) (sym l₁≡[]) (sym (++-identityʳ _))
    }

  Poset-≼ : Poset _ _ _
  Poset-≼ = record
    { Carrier = List A
    ; _≈_ = _≡_
    ; _≤_ = _≼_
    ; isPartialOrder = IsPartialOrder-≼ }

map-≼ : {f : A → B} → l₁ ≼ l₂ → map f l₁ ≼ map f l₂
map-≼ {l₁ = l₁} {l₂} {f} (l , eq) = -, trans (sym (map-++ f l₁ l)) (cong (map f) eq)

take-++ˡ : take (length l₁) (l₁ ++ l₂) ≡ l₁
take-++ˡ {l₁ = []}     = refl
take-++ˡ {l₁ = a ∷ l₁} = cong (a ∷_) take-++ˡ

≼⇔≼′ : (l₁ ≼ l₂) ⇔ (l₁ ≼′ l₂)
≼⇔≼′ {l₁ = l₁} {l₂} = mk⇔
  (λ where (l , refl) → length l₁ , sym take-++ˡ)
  (λ where (k , refl) → drop k l₂ , take++drop≡id k l₂)

inj-map-≼ : {f : A → B} → Injective _≡_ _≡_ f
  → map f l₁ ≼ map f l₂ → l₁ ≼ l₂
inj-map-≼ inj fl₁≼fl₂ = case to ≼⇔≼′ fl₁≼fl₂ of λ where
    (k , eq) → from ≼⇔≼′ (k , map-injective inj (trans eq (take-map k _)))
  where open Equivalence

prune-map : ∀ {k} {f : A → B} {l : List A}
  → prune k (map f l) ≡ map f (prune k l)
prune-map {k = k} {f} {l} =
  trans (cong (λ n → take (n ∸ k) (map f l)) (length-map f l)) (take-map (length l ∸ k) l)

```
