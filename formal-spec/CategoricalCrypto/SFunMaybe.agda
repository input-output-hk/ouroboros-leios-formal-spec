{-# OPTIONS --safe #-}
module CategoricalCrypto.SFunMaybe where

open import Level renaming (zero to ℓ0)

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; ⊤; ⊥; Functor; Bifunctor; [_]; head; tail; _++_; take ; drop)
import abstract-set-theory.Prelude as P
open import Data.Vec hiding (init)
open import Data.Vec.Properties
open import Data.Nat using (_+_)
open import Data.Nat.Properties
open import Data.Maybe as Maybe using (map)
open import Relation.Binary
open import Categories.Category
open import Categories.Category.Helper
import Relation.Binary.HeterogeneousEquality as H

-- M = id, Maybe, Powerset (relation), Giry (probability)
-- SFunType A B S = S × A → M (S × B)
SFunType : Type → Type → Type → Type
SFunType A B S = S × A → Maybe (S × B)

-- explicit state
record SFunᵉ (A B : Type) : Type₁ where
  field
    State : Type
    init  : State
    fun   : SFunType A B State

private variable A B C D State : Type

trace : ∀ {n} → SFunType A B State → State → Vec A n → Vec (Maybe B) n
trace _ _ [] = []
trace f s (a ∷ as) with f (s , a)
... | nothing       = nothing ∷ trace f s  as
... | just (s' , b) = just b  ∷ trace f s' as
  
take-trace : ∀ {m n} {f : SFunType A B State} {s} {as : Vec A (n + m)}
           → take n (trace f s as) ≡ trace f s (take n as)
take-trace {n = zero} = refl
take-trace {n = suc _} {f} {s} {a ∷ _} with f (s , a)
... | just _  = cong (just _  ∷_) take-trace
... | nothing = cong (nothing ∷_) take-trace

-- implicit state
record SFunⁱ (A B : Type) : Type where

  constructor SF

  field
    fun : ∀ {n} → Vec A n → Vec (Maybe B) n
    take-fun : ∀ {m n} {as : Vec A (m + n)} → take m (fun as) ≡ fun (take m as)

  fun₁ : A → Maybe B
  fun₁ a = head (fun [ a ])

  take-tail : {m n : ℕ} {a : A} {as : Vec A (m + n)} → take m (tail (fun (a ∷ as))) ≡ tail (fun (a ∷ take m as))
  take-tail {m} {a = a} {as} = begin
    take m (tail (fun (a ∷ as)))         ≡⟨ take-suc {v = fun (a ∷ as)} ⟩
    tail (take (ℕ.suc m) (fun (a ∷ as))) ≡⟨ cong tail take-fun ⟩
    tail (fun (take (ℕ.suc m) (a ∷ as))) ≡⟨⟩
    tail (fun (a ∷ take m as))           ∎
    where
      open ≡-Reasoning
      take-suc : ∀ {m n} {v : Vec (Maybe B) (ℕ.suc (m + n))} → take m (tail v) ≡ tail (take (ℕ.suc m) v)
      take-suc {v = _ ∷ _} = refl

  tail-fun : {n : ℕ} {a : A} {as : Vec A (n + 0)} → fun as H.≅ tail (fun (a ∷ as))
  tail-fun {n} {a} {as} = let open H.≅-Reasoning in begin
    fun as                       ≅⟨ {!!} ⟩
    take n (fun as) ≅⟨ {!!} ⟩
    tail (fun (a ∷ take n as)) ≅⟨ {!!} ⟩
    tail (fun (a ∷ as))          ∎

  -- the function on traces after making one fixed step
  apply₁ : A → SFunⁱ A B
  apply₁ a = record { fun = λ as → tail (fun (a ∷ as)) ; take-fun = take-tail }
  
module _ where
  open SFunⁱ
  open ≡-Reasoning

  take₁ : ∀ {A : Type} {n} {as : Vec A (ℕ.suc n)} → head (take 1 as) ≡ head as 
  take₁ {as = _ ∷ _} = refl

  head-tail : ∀ {A : Type} {n} {as : Vec A (ℕ.suc n)} {y} → y ≡ head as → as ≡ y ∷ tail as
  head-tail {as = _ ∷ _} refl = refl

  fun-∷ : ∀ {n} {f : SFunⁱ A B} {a} {as : Vec A n} → fun f (a ∷ as) ≡ fun₁ f a ∷ fun (apply₁ f a) as
  fun-∷ {f = f} {a} {as} = head-tail $ begin
    fun₁ f a                       ≡⟨⟩
    head (fun f (a ∷ []))          ≡⟨ take₁ {as = fun f (a ∷ [])} ⟨
    head (take 1 (fun f (a ∷ []))) ≡⟨ cong head (take-fun f) ⟩
    head (fun f (take 1 (a ∷ []))) ≡⟨⟩
    head (fun f (take 1 (a ∷ as))) ≡⟨ cong head (take-fun f) ⟨
    head (take 1 (fun f (a ∷ as))) ≡⟨ take₁ {as = fun f (a ∷ as)} ⟩
    head (fun f (a ∷ as))          ∎
    
eval : SFunᵉ A B → SFunⁱ A B
eval f = let open SFunᵉ f in record { fun = trace fun init ; take-fun = take-trace }

resume : SFunⁱ A B → SFunᵉ A B
resume f = record
  { init = f
  ; fun = λ where (g , a) → P.map (SFunⁱ.apply₁ g a ,_) (SFunⁱ.fun₁ g a)
  }

_≈ⁱ_ : SFunⁱ A B → SFunⁱ A B → Type
f ≈ⁱ g = let open SFunⁱ in ∀ {n} → fun f {n} ≗ fun g {n}

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
f ≈ᵉ g = eval f ≈ⁱ eval g

eval∘resume≡id : ∀ {f : SFunⁱ A B} → eval (resume f) ≈ⁱ f
eval∘resume≡id {f = f} [] with SFunⁱ.fun f []
... | [] = refl
eval∘resume≡id {f = f} (a ∷ as) with SFunⁱ.fun₁ f a in fa≡
... | just x = trans (cong₂ _∷_ (sym fa≡) (eval∘resume≡id as)) (sym (fun-∷ {f = f}))
... | nothing = trans (cong₂ _∷_ (sym fa≡) (trans (eval∘resume≡id as) {!!})) (sym (fun-∷ {f = f}))

resume∘eval≡id : ∀ {f : SFunᵉ A B} → resume (eval f) ≈ᵉ f
resume∘eval≡id {f = f} {n} = eval∘resume≡id {f = eval f}
