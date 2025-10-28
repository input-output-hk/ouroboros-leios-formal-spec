{-# OPTIONS --safe #-}
module CategoricalCrypto.SFun where

open import Level renaming (zero to ℓ0)

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; ⊤; ⊥; Functor; Bifunctor; [_]; head; tail; _++_; take)
import abstract-set-theory.Prelude as P
open import Data.Vec hiding (init)
open import Data.Nat using (_+_)

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
  apply₁ a = record { fun = λ as → tail (fun (a ∷ as)) ; take-fun = {!!} }

eval : SFunᵉ A B → SFunⁱ A B
eval f = let open SFunᵉ f in record { fun = trace fun init ; take-fun = take-trace }

resume : SFunⁱ A B → SFunᵉ A B
resume f = record
  { init = f
  ; fun = λ where (g , a) → SFunⁱ.apply₁ g a , SFunⁱ.fun₁ g a
  }

_≈ⁱ_ : SFunⁱ A B → SFunⁱ A B → Type
f ≈ⁱ g = let open SFunⁱ in ∀ {n} → fun f {n} ≗ fun g {n}

open SFunⁱ
≈ⁱ-ind : ∀ {f g : SFunⁱ A B} a → fun₁ f a ≡ fun₁ g a → apply₁ f a ≈ⁱ apply₁ g a → f ≈ⁱ g
≈ⁱ-ind = {!!}

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
f ≈ᵉ g = eval f ≈ⁱ eval g

resume∘eval≡id : ∀ {f : SFunᵉ A B} → resume (eval f) ≈ᵉ f
resume∘eval≡id {f = f} {n} as = {!!}
