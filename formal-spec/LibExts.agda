{-# OPTIONS --safe #-}

module LibExts where

open import Data.Vec
open import Relation.Binary.PropositionalEquality

take-++ : ∀ {m n} {a} {A : Set a} {as : Vec A n} {as' : Vec A m} → take n (as ++ as') ≡ as
take-++ {as = []} = refl
take-++ {as = _ ∷ _} = cong (_ ∷_) take-++

case_of-≡_ : ∀ {ℓ ℓ₁} {A : Set ℓ} {B : Set ℓ₁} → (a : A) → ((a' : A) → a ≡ a' → B) → B
case a of-≡ f = f a refl
