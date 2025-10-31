{-# OPTIONS --safe #-}
module CategoricalCrypto.SFun where

open import Level renaming (zero to ℓ0)

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; ⊤; ⊥; Functor; Bifunctor; [_]; head; tail; _++_; take)
import abstract-set-theory.Prelude as P
open import Data.Vec hiding (init)
open import Data.Nat using (_+_)
open import Relation.Binary

-- M = id, Maybe, Powerset (relation), Giry (probability)
-- SFunType A B S = S × A → M (S × B)
SFunType : Type → Type → Type → Type
SFunType A B S = S × A → S × B

-- explicit state
record SFunᵉ (A B : Type) : Type₁ where
  field
    State : Type
    init  : State
    fun   : SFunType A B State

private variable A B C D State : Type
                 m n : ℕ

trace : SFunType A B State → State → Vec A n → Vec B n
trace f s [] = []
trace f s (a ∷ as) = let (s , b) = f (s , a) in b ∷ trace f s as

take-trace : ∀ {f : SFunType A B State} {s} {as : Vec A (n + m)}
           → take n (trace f s as) ≡ trace f s (take n as)
take-trace {n = zero} = refl
take-trace {n = suc _} {as = _ ∷ _} = cong (_ ∷_) take-trace

-- implicit state
record SFunⁱ (A B : Type) : Type where
  field
    fun : Vec A n → Vec B n
    take-fun : ∀ {as : Vec A (m + n)} → take m (fun as) ≡ fun (take m as)

  fun₁ : A → B
  fun₁ a = head (fun [ a ])

  -- the function on traces after making one fixed step
  apply₁ : A → SFunⁱ A B
  apply₁ a = record { fun = λ as → tail (fun (a ∷ as)) ; take-fun = prop  }
    where
      open ≡-Reasoning

      tail[a]≡[] : ∀ {a} {A : Set a} {v : Vec A 1} → tail v ≡ []
      tail[a]≡[] {v = _ ∷ []} = refl
      
      prop : {m n : ℕ} {a : A} {as : Vec A (m + n)} → take m (tail (fun (a ∷ as))) ≡ tail (fun (a ∷ take m as))
      prop {zero} {a = a} {as} =
        begin
          take zero (tail (fun (a ∷ as))) ≡⟨⟩
          [] ≡⟨ tail[a]≡[] {v = fun (a ∷ [])} ⟨
          tail (fun (a ∷ [])) ≡⟨⟩
          tail (fun (a ∷ take zero as)) ∎ 
      prop {ℕ.suc m} = {!!}


module _ where
  open SFunⁱ
  fun-∷ : ∀ {f : SFunⁱ A B} {a} {as : Vec A n} → fun f (a ∷ as) ≡ fun₁ f a ∷ fun (apply₁ f a) as
  fun-∷ = {!!}

eval : SFunᵉ A B → SFunⁱ A B
eval f = let open SFunᵉ f in record { fun = trace fun init ; take-fun = take-trace }

resume : SFunⁱ A B → SFunᵉ A B
resume f = record
  { init = f
  ; fun = λ where (g , a) → SFunⁱ.apply₁ g a , SFunⁱ.fun₁ g a
  }

_≈ⁱ_ : SFunⁱ A B → SFunⁱ A B → Type
f ≈ⁱ g = let open SFunⁱ in ∀ {n} → fun f {n} ≗ fun g {n}

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
f ≈ᵉ g = eval f ≈ⁱ eval g

eval∘resume≡id : ∀ {f : SFunⁱ A B} → eval (resume f) ≈ⁱ f
eval∘resume≡id {f = f} [] with SFunⁱ.fun f []
... | [] = refl
eval∘resume≡id {f = f} (a ∷ as) = begin
  head (fun f (a ∷ [])) ∷ fun (eval (resume (apply₁ f a))) as
    ≡⟨ cong (_ ∷_) (eval∘resume≡id as) ⟩
  fun₁ f a ∷ fun (apply₁ f a) as
    ≡⟨ sym (fun-∷ {f = f}) ⟩
  fun f (a ∷ as) ∎
  where open ≡-Reasoning
        open SFunⁱ

resume∘eval≡id : ∀ {f : SFunᵉ A B} → resume (eval f) ≈ᵉ f
resume∘eval≡id {f = f} {n} = eval∘resume≡id {f = eval f}

IsEquivalence-≈ⁱ : IsEquivalence (_≈ⁱ_ {A} {B})
IsEquivalence-≈ⁱ = {!!}

IsEquivalence-≈ᵉ : IsEquivalence (_≈ᵉ_ {A} {B})
IsEquivalence-≈ᵉ = {!!}

SFunⁱ-Setoid : (A B : Type) → Setoid ℓ0 ℓ0
SFunⁱ-Setoid A B = record { Carrier = SFunⁱ A B ; _≈_ = _≈ⁱ_ ; isEquivalence = IsEquivalence-≈ⁱ }

SFunᵉ-Setoid : (A B : Type) → Setoid (sucˡ ℓ0) ℓ0
SFunᵉ-Setoid A B = record { Carrier = SFunᵉ A B ; _≈_ = _≈ᵉ_ ; isEquivalence = IsEquivalence-≈ᵉ }

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

Inverse-resume-eval : Inverse (SFunⁱ-Setoid A B) (SFunᵉ-Setoid A B)
Inverse-resume-eval {A} {B} = record { to = resume ; from = eval ; Go }
  where
    open SetoidReasoning (SFunⁱ-Setoid A B)
    module Go where
      to-cong : Congruent _≈ⁱ_ _≈ᵉ_ resume
      to-cong {x} {y} x≈y = begin
        eval (resume x) ≈⟨ eval∘resume≡id ⟩ x ≈⟨ x≈y ⟩ y ≈⟨ eval∘resume≡id ⟨ eval (resume y) ∎
      from-cong : Congruent _≈ᵉ_ _≈ⁱ_ eval
      from-cong f≈g = f≈g
      inverse : Inverseᵇ _≈ⁱ_ _≈ᵉ_ resume eval
      inverse = (λ {x} {y} y≈eval[x] → begin
                 eval (resume y)
                   ≈⟨ from-cong (to-cong y≈eval[x]) ⟩
                 eval (resume (eval x))
                   ≈⟨ resume∘eval≡id ⟩
                 eval x ∎)
              , λ {x} {y} y≈resume[x] → begin
                  eval y
                    ≈⟨ from-cong y≈resume[x] ⟩
                  eval (resume x)
                    ≈⟨ eval∘resume≡id ⟩
                  x ∎
