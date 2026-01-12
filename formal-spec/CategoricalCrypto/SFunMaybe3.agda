{-# OPTIONS --safe #-}
module CategoricalCrypto.SFunMaybe3 where

open import Level renaming (zero to ℓ0)

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; ⊤; ⊥; Functor; Bifunctor; [_]; head; tail; _++_; take)
import abstract-set-theory.Prelude as P
open import Data.Vec hiding (init)
open import Data.Nat using (_+_)
open import Relation.Binary
open import Categories.Category
open import Categories.Category.Helper
open import Class.Monad
open import Class.Functor
-- open import Data.Maybe using (just) renaming (map to mmap ; _>>=_ to _m>>=_)
open import Data.Maybe.Relation.Unary.Any hiding (just)

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

trace : ∀ {n} → SFunType A B State → State → Vec A n → Maybe (Vec B n)
trace _ _ [] = just []
trace f s (a ∷ as) = do
  (s' , b) ← f (s , a)
  rec ← trace f s' as
  return (b ∷ rec)

from-just' : ∀ {a} {A : Type a} {x : Maybe A} → Is-just x → ∃[ y ] x ≡ just y
from-just' {x = just x} _ = x , refl

take-n : ∀ {m n} {f : SFunType A B State} {s} {as : Vec A (n + m)} {bs}
  → trace f s as ≡ just bs
  → trace f s (take n as) ≡ just (take n bs)
take-n {m = m} {zero} _ = refl
take-n {m = m} {ℕ.suc n} {f} {s} {as = a ∷ as} {b ∷ bs} p with f (s , a)
... | just (s' , b') with trace f s' as in q
take-n {m = m} {ℕ.suc n} {f} {s} {a ∷ as} {b ∷ bs} refl | just (s' , b') | just x rewrite take-n {m = m} {n} {f} {s'} {as} {bs} q = refl

take-trace : ∀ {m n} {f : SFunType A B State} {s} {as : Vec A (n + m)}
  → Is-just (trace f s as)
  → fmap (take n) (trace f s as) ≡ {!!} -- trace f s (take n as)
take-trace p = {!!} -- with from-just' p
-- ... | _ , p' rewrite p' = {!!} -- sym (take-n p')

-- take-suc : ∀ {m n} {v : Vec B (ℕ.suc (m + n))} → take m (tail v) ≡ tail (take (ℕ.suc m) v)
-- take-suc {v = _ ∷ _} = refl

-- is-just-fmap : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {v : Maybe A} → Is-just (fmap f v) → Is-just v
-- is-just-fmap {v = just _} _ = Any.just tt

-- is-just->>= : ∀ {a b} {A : Set a} {B : Set b} {f : A → Maybe B} {v : Maybe A} → Is-just (v >>= f) → Is-just v
-- is-just->>= {v = just _} _ = Any.just tt

-- mfmap : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {mv : Maybe A} {g : A → B} {f : B → C}
--   → fmap f (fmap g mv) ≡ fmap (f P.∘ g) mv
-- mfmap {mv = just _} = refl
-- mfmap {mv = nothing} = refl

-- -- implicit state
-- record SFunⁱ (A B : Type) : Type where

--   constructor SF

--   field
--     fun : ∀ {n} → Vec A n → Maybe (Vec B n)
--     take-fun : ∀ {m n} {as : Vec A (m + n)} → Is-just (fun as) → fmap (take m) (fun as) ≡ fun (take m as)

--   fun₁ : A → Maybe B
--   fun₁ a = fmap head (fun [ a ])
  
--   take-tail : {m n : ℕ} {a : A} {as : Vec A (m + n)}
--     → Is-just (fun (a ∷ as))
--     → fmap (take m P.∘ tail) (fun (a ∷ as)) ≡ fmap tail (fun (a ∷ take m as))
--   take-tail {m = m} p with take-fun {m = ℕ.suc m} p
--   ... | ≡fun with from-just' p
--   ... | bs , fun[a∷as]≡bs rewrite fun[a∷as]≡bs | take-suc {m = m} {v = bs} = cong (fmap tail) ≡fun

--   -- the function on traces after making one fixed step
--   apply₁ : A → SFunⁱ A B
--   apply₁ a = record
--     { fun = λ as → fmap tail (fun (a ∷ as))
--     ; take-fun = λ {m = m} {n} {as} x →
--       trans
--         (mfmap {mv = fun (a ∷ as)} {g = tail} {f = take m} )
--         (take-tail {m = m} (is-just-fmap {v = fun (a ∷ as)} x)) }

-- idⁱ : SFunⁱ A A
-- idⁱ = SF just (const refl)

-- _∘ⁱ_ : ∀ {A B C} → SFunⁱ B C → SFunⁱ A B → SFunⁱ A C
-- _∘ⁱ_ {A} {B} {C} (SF fun take-fun) (SF fun₁ take-fun₁) =
--   SF
--     ((_>>= fun) P.∘ fun₁)
--     λ {m = m} {as = as} p → trans (aux as) (cong (_>>= fun) (take-fun₁ {m = m} (is-just->>= p)))
--   where
--     aux : ∀ {m} {n} (w : Vec A (m +ℕ n)) → fmap (take m) (fun₁ w >>= fun) ≡ (fmap (take m) (fun₁ w) >>= fun)
--     aux w with fun₁ w in p
--     ... | just x = take-fun {!!}
--     ... | nothing = refl

-- module _ where
--   open SFunⁱ
--   open ≡-Reasoning

--   take₁ : ∀ {A : Type} {n} {as : Vec A (ℕ.suc n)} → head (take 1 as) ≡ head as 
--   take₁ {as = _ ∷ _} = refl

--   head-tail : ∀ {A : Type} {n} {as : Vec A (ℕ.suc n)} {y} → y ≡ head as → as ≡ y ∷ tail as
--   head-tail {as = _ ∷ _} refl = refl

--   fun-∷ : ∀ {n} {f : SFunⁱ A B} {a} {as : Vec A n} → fun f (a ∷ as) ≡ fun₁ f a ∷ fun (apply₁ f a) as
--   fun-∷ {f = f} {a} {as} = head-tail $ begin
--     fun₁ f a                       ≡⟨⟩
--     head (fun f (a ∷ []))          ≡⟨ take₁ {as = fun f (a ∷ [])} ⟨
--     head (take 1 (fun f (a ∷ []))) ≡⟨ cong head (take-fun f) ⟩
--     head (fun f (take 1 (a ∷ []))) ≡⟨⟩
--     head (fun f (take 1 (a ∷ as))) ≡⟨ cong head (take-fun f) ⟨
--     head (take 1 (fun f (a ∷ as))) ≡⟨ take₁ {as = fun f (a ∷ as)} ⟩
--     head (fun f (a ∷ as))          ∎

-- eval : SFunᵉ A B → SFunⁱ A B
-- eval f = let open SFunᵉ f in record { fun = trace fun init ; take-fun = take-trace }

-- resume : SFunⁱ A B → SFunᵉ A B
-- resume f = record
--   { init = f
--   ; fun = λ where (g , a) → SFunⁱ.apply₁ g a , SFunⁱ.fun₁ g a
--   }

-- _≈ⁱ_ : SFunⁱ A B → SFunⁱ A B → Type
-- f ≈ⁱ g = let open SFunⁱ in ∀ {n} → fun f {n} ≗ fun g {n}

-- _≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
-- f ≈ᵉ g = eval f ≈ⁱ eval g

-- eval∘resume≡id : ∀ {f : SFunⁱ A B} → eval (resume f) ≈ⁱ f
-- eval∘resume≡id {f = f} [] with SFunⁱ.fun f []
-- ... | [] = refl
-- eval∘resume≡id {f = f} (a ∷ as) = begin
--   head (fun f (a ∷ [])) ∷ fun (eval (resume (apply₁ f a))) as ≡⟨ cong (_ ∷_) (eval∘resume≡id as) ⟩
--   fun₁ f a ∷ fun (apply₁ f a) as                              ≡⟨ sym (fun-∷ {f = f}) ⟩
--   fun f (a ∷ as)                                              ∎
--   where open ≡-Reasoning
--         open SFunⁱ

-- resume∘eval≡id : ∀ {f : SFunᵉ A B} → resume (eval f) ≈ᵉ f
-- resume∘eval≡id {f = f} {n} = eval∘resume≡id {f = eval f}

-- IsEquivalence-≈ⁱ : IsEquivalence (_≈ⁱ_ {A} {B})
-- IsEquivalence-≈ⁱ = record
--   { refl = λ _ → refl
--   ; sym = λ x x₁ → sym (x x₁)
--   ; trans = λ x x₁ x₂ → trans (x x₂) (x₁ x₂) }

-- IsEquivalence-≈ᵉ : IsEquivalence (_≈ᵉ_ {A} {B})
-- IsEquivalence-≈ᵉ = record
--   { refl = λ _ → refl
--   ; sym = λ x x₁ → sym (x x₁)
--   ; trans = λ x x₁ x₂ → trans (x x₂) (x₁ x₂) }

-- SFunⁱ-Setoid : (A B : Type) → Setoid ℓ0 ℓ0
-- SFunⁱ-Setoid A B = record { Carrier = SFunⁱ A B ; _≈_ = _≈ⁱ_ ; isEquivalence = IsEquivalence-≈ⁱ }

-- SFunᵉ-Setoid : (A B : Type) → Setoid (sucˡ ℓ0) ℓ0
-- SFunᵉ-Setoid A B = record { Carrier = SFunᵉ A B ; _≈_ = _≈ᵉ_ ; isEquivalence = IsEquivalence-≈ᵉ }

-- import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Inverse-resume-eval : Inverse (SFunⁱ-Setoid A B) (SFunᵉ-Setoid A B)
-- Inverse-resume-eval {A} {B} = record { to = resume ; from = eval ; Go }
--   where
--     open SetoidReasoning (SFunⁱ-Setoid A B)
--     module Go where
--       to-cong : Congruent _≈ⁱ_ _≈ᵉ_ resume
--       to-cong {x} {y} x≈y = begin
--         eval (resume x) ≈⟨ eval∘resume≡id ⟩
--         x               ≈⟨ x≈y ⟩
--         y               ≈⟨ eval∘resume≡id ⟨
--         eval (resume y) ∎
--       from-cong : Congruent _≈ᵉ_ _≈ⁱ_ eval
--       from-cong f≈g = f≈g
--       inverse : Inverseᵇ _≈ⁱ_ _≈ᵉ_ resume eval
--       inverse = (λ {x} {y} y≈eval[x] → begin
--         eval (resume y)        ≈⟨ from-cong (to-cong y≈eval[x]) ⟩
--         eval (resume (eval x)) ≈⟨ resume∘eval≡id ⟩
--         eval x                 ∎)
--               , λ {x} {y} y≈resume[x] → begin
--         eval y          ≈⟨ from-cong y≈resume[x] ⟩
--         eval (resume x) ≈⟨ eval∘resume≡id ⟩
--         x               ∎

-- sFunCategory : Category _ _ _
-- sFunCategory = categoryHelper $ record
--   { Obj = Type
--   ; _⇒_ = SFunⁱ
--   ; _≈_ = _≈ⁱ_
--   ; id = idⁱ
--   ; _∘_ = _∘ⁱ_
--   ; assoc = λ _ → refl
--   ; identityˡ = λ _ → refl
--   ; identityʳ = λ _ → refl
--   ; equiv = IsEquivalence-≈ⁱ
--   ; ∘-resp-≈ = λ { {h = SF fun _} {SF fun₁ _} f≈ⁱh g≈ⁱi {n} v → trans (f≈ⁱh (fun₁ v)) (cong fun (g≈ⁱi v)) }
--   }
