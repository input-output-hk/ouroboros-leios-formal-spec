{-# OPTIONS --safe #-}
module CategoricalCrypto.SFun where

open import Level renaming (zero to ℓ0)

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; ⊤; ⊥; Functor; Bifunctor; [_]; head; tail; _++_; take)
import abstract-set-theory.Prelude as P
open import Data.Vec hiding (init)
open import Data.Nat using (_+_)
open import Relation.Binary
open import Categories.Category
open import Categories.Category.Helper

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

trace : ∀ {n} → SFunType A B State → State → Vec A n → Vec B n
trace f s [] = []
trace f s (a ∷ as) = let (s , b) = f (s , a) in b ∷ trace f s as

take-trace : ∀ {m n } {f : SFunType A B State} {s} {as : Vec A (n + m)}
           → take n (trace f s as) ≡ trace f s (take n as)
take-trace {n = zero} = refl
take-trace {n = suc _} {as = _ ∷ _} = cong (_ ∷_) take-trace

-- implicit state
record SFunⁱ (A B : Type) : Type where

  constructor SF

  field
    fun : ∀ {n} → Vec A n → Vec B n
    take-fun : ∀ {m n} {as : Vec A (m + n)} → take m (fun as) ≡ fun (take m as)

  fun₁ : A → B
  fun₁ a = head (fun [ a ])
  
  take-tail : {m n : ℕ} {a : A} {as : Vec A (m + n)} → take m (tail (fun (a ∷ as))) ≡ tail (fun (a ∷ take m as))
  take-tail {m} {a = a} {as} = begin
    take m (tail (fun (a ∷ as)))         ≡⟨ take-suc {v = fun (a ∷ as)} ⟩
    tail (take (ℕ.suc m) (fun (a ∷ as))) ≡⟨ cong tail take-fun ⟩
    tail (fun (take (ℕ.suc m) (a ∷ as))) ≡⟨⟩
    tail (fun (a ∷ take m as))           ∎
    where
      open ≡-Reasoning
      take-suc : ∀ {m n} {v : Vec B (ℕ.suc (m + n))} → take m (tail v) ≡ tail (take (ℕ.suc m) v)
      take-suc {v = _ ∷ _} = refl
        
  -- the function on traces after making one fixed step
  apply₁ : A → SFunⁱ A B
  apply₁ a = record { fun = λ as → tail (fun (a ∷ as)) ; take-fun = take-tail  }

idⁱ : SFunⁱ A A
idⁱ = SF P.id refl

_∘ⁱ_ : ∀ {A B C} → SFunⁱ B C → SFunⁱ A B → SFunⁱ A C
_∘ⁱ_ (SF fun take-fun) (SF fun₁ take-fun₁) = SF (fun P.∘ fun₁) (trans take-fun (cong fun take-fun₁))

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
  head (fun f (a ∷ [])) ∷ fun (eval (resume (apply₁ f a))) as ≡⟨ cong (_ ∷_) (eval∘resume≡id as) ⟩
  fun₁ f a ∷ fun (apply₁ f a) as                              ≡⟨ sym (fun-∷ {f = f}) ⟩
  fun f (a ∷ as)                                              ∎
  where open ≡-Reasoning
        open SFunⁱ

resume∘eval≡id : ∀ {f : SFunᵉ A B} → resume (eval f) ≈ᵉ f
resume∘eval≡id {f = f} {n} = eval∘resume≡id {f = eval f}

IsEquivalence-≈ⁱ : IsEquivalence (_≈ⁱ_ {A} {B})
IsEquivalence-≈ⁱ = record
  { refl = λ _ → refl
  ; sym = λ x x₁ → sym (x x₁)
  ; trans = λ x x₁ x₂ → trans (x x₂) (x₁ x₂) }

IsEquivalence-≈ᵉ : IsEquivalence (_≈ᵉ_ {A} {B})
IsEquivalence-≈ᵉ = record
  { refl = λ _ → refl
  ; sym = λ x x₁ → sym (x x₁)
  ; trans = λ x x₁ x₂ → trans (x x₂) (x₁ x₂) }

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
        eval (resume x) ≈⟨ eval∘resume≡id ⟩
        x               ≈⟨ x≈y ⟩
        y               ≈⟨ eval∘resume≡id ⟨
        eval (resume y) ∎
      from-cong : Congruent _≈ᵉ_ _≈ⁱ_ eval
      from-cong f≈g = f≈g
      inverse : Inverseᵇ _≈ⁱ_ _≈ᵉ_ resume eval
      inverse = (λ {x} {y} y≈eval[x] → begin
        eval (resume y)        ≈⟨ from-cong (to-cong y≈eval[x]) ⟩
        eval (resume (eval x)) ≈⟨ resume∘eval≡id ⟩
        eval x                 ∎)
              , λ {x} {y} y≈resume[x] → begin
        eval y          ≈⟨ from-cong y≈resume[x] ⟩
        eval (resume x) ≈⟨ eval∘resume≡id ⟩
        x               ∎

sFunCategory : Category _ _ _
sFunCategory = categoryHelper $ record
  { Obj = Type
  ; _⇒_ = SFunⁱ
  ; _≈_ = _≈ⁱ_
  ; id = idⁱ
  ; _∘_ = _∘ⁱ_
  ; assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  ; equiv = IsEquivalence-≈ⁱ
  ; ∘-resp-≈ = λ { {h = SF fun _} {SF fun₁ _} f≈ⁱh g≈ⁱi {n} v → trans (f≈ⁱh (fun₁ v)) (cong fun (g≈ⁱi v)) }
  }
