{-# OPTIONS --safe #-}

module CategoricalCrypto.SFunMaybe where

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import LibExts
open import abstract-set-theory.Prelude hiding ([_]; head; tail; _++_; take)
open import Categories.Category
open import Categories.Category.Helper
open import Class.Functor
open import Class.Monad
open import Data.Vec hiding (init)
open import Relation.Binary

SFunType : Type → Type → Type → Type
SFunType A B S = S × A → Maybe (S × B)

-- explicit state
record SFunᵉ (A B : Type) : Type₁ where
  constructor SFᵉ

  field
    State : Type
    init  : State
    fun   : SFunType A B State

private variable A B C D State : Type

Trace : Type → Type → Type
Trace A B = ∀ {n} → Vec A n → Maybe (Vec B n)

trace : SFunType A B State → State → Trace A B
trace _ _ [] = just []
trace f s (a ∷ as) = do
  (s' , b) ← f (s , a)
  rec ← trace f s' as
  return (b ∷ rec)

Preserving : ∀ {A B : Type} → Trace A B → Type
Preserving {A} {B} t =
  ∀ {m n : ℕ}
    {as  : Vec A (n +ℕ m)}
    {bs  : Vec B (n +ℕ m)}
  → t as ≡ just bs
  → t (take n as) ≡ just (take n bs)

Unitary : ∀ {A B : Type} → Trace A B → Type
Unitary t = t [] ≡ just []

trace-preserving :
  ∀ {f : SFunType A B State}
    {s : State}
  → Preserving (trace f s)
trace-preserving {n = zero} _ = refl
trace-preserving {f = f} {s} {n = suc n} {a ∷ as} p with f (s , a)
... | just (s' , b') with trace f s' as in q
... | just bs' with p
... | refl = cong (_>>= (\rec → just (b' ∷ rec))) (trace-preserving q)

trace-unitary :
  ∀ {f : SFunType A B State}
    {s : State}
  → Unitary (trace f s)  
trace-unitary = refl

-- implicit state
record SFunⁱ (A B : Type) : Type where

  constructor SFⁱ

  field
    fun      : Trace A B
    fun-pres : Preserving fun
    fun-unit : Unitary fun

  fun-single : A → Maybe B
  fun-single = fmap head ∘ fun ∘ [_]

  fun-nothing :
    ∀ {m n : ℕ}
      {as  : Vec A n}
      {as' : Vec A m}
    → fun as ≡ nothing
    → fun (as ++ as') ≡ nothing
  fun-nothing {n = n} {as} {as'} p with fun (as ++ as') in q
  ... | nothing = refl
  ... | just _ with fun-pres {n = n} q
  ... | r with take-++ {as = as} {as'}
  ... | s rewrite s | p with r
  ... | ()

  apply₁ : ∀ {a bs} → fun [ a ] ≡ just bs → SFunⁱ A B
  apply₁ {a = a} {b ∷ []} p =
    record
      { fun = fun'
      ; fun-pres = fun-pres'
      ; fun-unit = cong (fmap tail) p
      }
    where
      fun' : Trace A B
      fun' = fmap tail ∘ fun ∘ (a ∷_)

      fun-pres' : Preserving fun'
      fun-pres' {n = n} {as} q with (fun (a ∷ as)) in r
      ... | just (_ ∷ _) with q
      ... | refl rewrite fun-pres {n = suc n} r = refl

idⁱ : SFunⁱ A A
idⁱ = SFⁱ just (λ where refl → refl) refl

_∘ⁱ_ : ∀ {A B C} → SFunⁱ B C → SFunⁱ A B → SFunⁱ A C
_∘ⁱ_ (SFⁱ fun fun-pres fun-unit) (SFⁱ fun₁ fun-pres₁ fun-unit₁) =
  SFⁱ funⁱ fun-pres-∘ⁱ fun-unitⁱ
   where
     funⁱ : Trace _ _ 
     funⁱ = (_>>= fun) ∘ fun₁

     fun-pres-∘ⁱ : Preserving funⁱ 
     fun-pres-∘ⁱ {n = n} {as} p with fun₁ as in q
     ... | just bs rewrite fun-pres₁ {n = n} q = fun-pres p

     fun-unitⁱ : Unitary funⁱ 
     fun-unitⁱ rewrite fun-unit₁ = fun-unit
    
fun-∷ :
  ∀ {n  : ℕ}
    {f  : SFunⁱ A B}
    {a  : A}
    {as : Vec A n}
    {b  : Vec B 1}
    (p  : SFunⁱ.fun f [ a ] ≡ just b)
  → SFunⁱ.fun f (a ∷ as) ≡ do
                       h ← SFunⁱ.fun-single f a
                       t ← SFunⁱ.fun (SFunⁱ.apply₁ f p) as
                       return (h ∷ t)
fun-∷ {f = f} {a} {as} {b ∷ []} p with SFunⁱ.fun f (a ∷ as) in q
... | nothing rewrite p = refl
... | just (b' ∷ bs') rewrite p with SFunⁱ.fun-pres f {n = 1} q
... | r with trans (sym r) p
... | refl = refl

eval : SFunᵉ A B → SFunⁱ A B
eval (SFᵉ _ init fun) = SFⁱ (trace fun init) trace-preserving refl

resume-fun : SFunType A B (SFunⁱ A B)
resume-fun (f , a) with SFunⁱ.fun f [ a ] in p
... | nothing = nothing
... | just (b ∷ []) = just (SFunⁱ.apply₁ f p , b)

resume : SFunⁱ A B → SFunᵉ A B
resume f = record
  { init = f
  ; fun = resume-fun
  }

_≈ⁱ_ : SFunⁱ A B → SFunⁱ A B → Type
f ≈ⁱ g = ∀ {n} → SFunⁱ.fun f {n} ≗ SFunⁱ.fun g {n}

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
f ≈ᵉ g = eval f ≈ⁱ eval g

eval∘resume≡id : ∀ {f : SFunⁱ A B} → eval (resume f) ≈ⁱ f
eval∘resume≡id = go
  where
    go : ∀ {f : SFunⁱ A B} {n} → (trace resume-fun f) {n} ≗ (SFunⁱ.fun f {n})
    go {f = f} {n} [] = sym (SFunⁱ.fun-unit f)
    go {f = f} {.suc n} (a ∷ as) = ? -- with SFunⁱ.fun f [ a ]
    -- ... | f[a] = {!!}

-- [] with SFunⁱ.fun f []
-- ... | [] = refl
-- eval∘resume≡id {f = f} (a ∷ as) = begin
--   head (fun f (a ∷ [])) ∷ fun (eval (resume (apply₁ f a))) as ≡⟨ cong (_ ∷_) (eval∘resume≡id as) ⟩
--   fun-single f a ∷ fun (apply₁ f a) as                              ≡⟨ sym (fun-∷ {f = f}) ⟩
--   fun f (a ∷ as)                                              ∎
--   where open ≡-Reasoning
--         open SFunⁱ

resume∘eval≡id : ∀ {f : SFunᵉ A B} → resume (eval f) ≈ᵉ f
resume∘eval≡id {f = f} = eval∘resume≡id {f = eval f}

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

SFunⁱ-Setoid : (A B : Type) → Setoid _ _
SFunⁱ-Setoid A B = record
  { Carrier = SFunⁱ A B
  ; _≈_ = _≈ⁱ_
  ; isEquivalence = IsEquivalence-≈ⁱ }

SFunᵉ-Setoid : (A B : Type) → Setoid (sucˡ _) _
SFunᵉ-Setoid A B = record
  { Carrier = SFunᵉ A B
  ; _≈_ = _≈ᵉ_
  ; isEquivalence = IsEquivalence-≈ᵉ }

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
  ; assoc = λ { {f = f} {g} {h} → associative' {f = f} {g} {h}}
  ; identityˡ = λ { {f = f} → identityˡ' {f = f}}
  ; identityʳ = λ _ → refl
  ; equiv = IsEquivalence-≈ⁱ
  ; ∘-resp-≈ = λ { {f = f} {h} {g} {i} → resp' {f = f} {h} {g} {i}}
  }
  where
    associative' : {A B C D : Type} {f : SFunⁱ A B} {g : SFunⁱ B C} {h : SFunⁱ C D} → ((h ∘ⁱ g) ∘ⁱ f) ≈ⁱ (h ∘ⁱ (g ∘ⁱ f))
    associative' {f = f} {g} {h} v with SFunⁱ.fun f v
    ... | just _ = refl
    ... | nothing = refl
    
    identityˡ' : {A B : Type} {f : SFunⁱ A B} → (idⁱ ∘ⁱ f) ≈ⁱ f
    identityˡ' {f = f} v with SFunⁱ.fun f v
    ... | just _ = refl
    ... | nothing = refl

    resp' : ∀ {A} {B} {C} {f h : SFunⁱ B C} {g i : SFunⁱ A B} → f ≈ⁱ h → g ≈ⁱ i → (f ∘ⁱ g) ≈ⁱ (h ∘ⁱ i)
    resp' {g = g} {i} f≈ⁱh g≈ⁱi v with g≈ⁱi v
    ... | p with SFunⁱ.fun g v | SFunⁱ.fun i v
    ... | nothing | nothing = refl
    ... | just gs | just _ with p
    ... | refl = f≈ⁱh gs

