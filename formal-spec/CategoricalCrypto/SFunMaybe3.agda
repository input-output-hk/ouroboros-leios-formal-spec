{-# OPTIONS --safe #-}

module CategoricalCrypto.SFunMaybe3 where

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

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

-- to-just : ∀ {a} {A : Set a} {x : Maybe A} {y : A} → x ≡ just y → Is-just x
-- to-just refl = just tt

-- from-just' : ∀ {a} {A : Type a} {x : Maybe A} → Is-just x → ∃[ y ] x ≡ just y
-- from-just' {x = just x} _ = x , refl

-- from-nothing' : ∀ {a} {A : Type a} {x : Maybe A} → Is-nothing x → x ≡ nothing
-- from-nothing' {x = nothing} _ = refl
-- from-nothing' {x = just _} (just ())

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

-- trace-preserving : ∀ {m n} {f : SFunType A B State} {s} {as : Vec A (n +ℕ m)}
--   → Is-just (trace f s as)
--   → fmap {F = Maybe} (take n) (trace f s as) ≡ trace f s (take n as)
-- trace-preserving p with from-just' p
-- ... | _ , p' rewrite p' = sym (take-n p')

-- take-suc : ∀ {m n} {v : Vec B (suc (m +ℕ n))} → take m (tail v) ≡ tail (take (suc m) v)
-- take-suc {v = _ ∷ _} = refl

-- is-just-fmap : {f : A → B} {v : Maybe A} → Is-just (fmap f v) → Is-just v
-- is-just-fmap {v = just _} _ = Any.just tt

-- is-just->>=-l : {f : A → Maybe B} {v : Maybe A} → Is-just (v >>= f) → Is-just v
-- is-just->>=-l {v = just _} _ = Any.just tt

-- is-just->>=-r : {f : A → Maybe B} {v : Maybe A}
--   → (p : Is-just (v >>= f))
--   → let (v' , q) = from-just' $ is-just->>=-l {f = f} {v} p in Is-just (f v')
-- is-just->>=-r {v = just x} p = p

-- is-nothing->>=-r : ∀ {a b} {A : Set a} {B : Set b} (v : Maybe A) → Is-nothing {A = B} (v >>= \h → nothing)
-- is-nothing->>=-r (just _) = nothing
-- is-nothing->>=-r nothing = nothing

-- mfmap : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {mv : Maybe A} {g : A → B} {f : B → C}
--   → fmap f (fmap g mv) ≡ fmap (f P.∘ g) mv
-- mfmap {mv = just _} = refl
-- mfmap {mv = nothing} = refl

-- ij×in→⊥ : ∀ {a} {A : Set a} {v : Maybe A} → Is-just v × Is-nothing v → P.⊥
-- ij×in→⊥ {v = just _} (_ , (just ()))

-- ij⊎in : ∀ {a} {A : Set a} (v : Maybe A) → Is-just v ⊎ Is-nothing v
-- ij⊎in (just _) = inj₁ (just tt)
-- ij⊎in nothing = inj₂ nothing

take-++ : ∀ {m n} {a} {A : Set a} {as : Vec A n} {as' : Vec A m} → take n (as ++ as') ≡ as
take-++ {as = []} = refl
take-++ {as = x ∷ _} = cong (x ∷_) take-++

-- fmap-is-just : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {v : Maybe A} → Is-just v → Is-just (fmap f v)
-- fmap-is-just {v = just x} _ = just tt

-- is-just-≡ : ∀ {a} {A : Set a} {v w : Maybe A} → Is-just v → v ≡ w → Is-just w
-- is-just-≡ p refl = p

-- just-[]-≡ : ∀ {a} {A : Set a} {v w : A} → Maybe.just [ v ] ≡ just [ w ] → v ≡ w
-- just-[]-≡ refl = refl

-- implicit state
record SFunⁱ (A B : Type) : Type where

  constructor SFⁱ

  field
    fun      : Trace A B
    fun-pres : Preserving fun
    fun-unit : Unitary fun

  fun-single : A → Maybe B
  fun-single = fmap head ∘ fun ∘ [_]

  -- take-tail :
  --   ∀ {m n : ℕ}
  --     {a   : A}
  --     {b   : B}
  --     {as  : Vec A (n +ℕ m)}
  --     {bs  : Vec B (n +ℕ m)}
  --   → fun (a ∷ as) ≡ just (b ∷ bs)
  --   → fmap tail (fun (a ∷ take n as)) ≡ just (take n bs)
  -- take-tail {n = n} p rewrite fun-pres {n = suc n} p = refl
  
--   take-tail : {m n : ℕ} {a : A} {as : Vec A (m +ℕ n)}
--     → Is-just (fun (a ∷ as))
--     → fmap (take m P.∘ tail) (fun (a ∷ as)) ≡ fmap tail (fun (a ∷ take m as))
--   take-tail {m = m} p with fun-pres {m = suc m} p
--   ... | ≡fun with from-just' p
--   ... | bs , fun[a∷as]≡bs rewrite fun[a∷as]≡bs | take-suc {m = m} {v = bs} = cong (fmap tail) ≡fun

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

--   nothing-fun : ∀ {m n} {as : Vec A m} {as' : Vec A n} → Is-nothing (fun as) → Is-nothing (fun (as ++ as'))
--   nothing-fun {m = m} {n} {as} {as'} in[fun[as]] with ij⊎in (fun (as ++ as'))
--   ... | inj₁ ij[fun[as++as']] =
--     ⊥-elim (ij×in→⊥
--       (is-just-≡
--         (fmap-is-just ij[fun[as++as']])
--         (trans
--           (fun-pres {m = m} ij[fun[as++as']])
--           (cong fun (take-++ {m = m} {n} {as = as} {as'}))) ,
--       in[fun[as]]))
--   ... | inj₂ isNothing = isNothing

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

--   -- the function on traces after making one fixed step
--   apply₁ : {a : A} → Is-just (fun [ a ]) → SFunⁱ A B
--   apply₁ {a = a} ij with from-just' ij
--   ... | (a' ∷ [] , p) = record
--     { fun = λ as → fmap tail (fun (a ∷ as))
--     ; fun-pres = λ {m = m} {n} {as} x →
--       trans
--         (mfmap {mv = fun (a ∷ as)} {g = tail} {f = take m} )
--         (take-tail {m = m} (is-just-fmap {v = fun (a ∷ as)} x))
--     ; fun-unit = cong (fmap tail) p }
        

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

     -- fun-pres-∘ⁱ {m = m} {as = as} p with is-just->>=-l {f = fun} {v = fun₁ as} p in q
    -- ... | ijl rewrite sym (fun-pres₁ {m = m} {as = as} ijl) with from-just' ijl
    -- ... | fun₁as , fun₁as≡ rewrite fun₁as≡ = fun-pres (is-just->>=-r {f = fun} p)

     fun-unitⁱ : Unitary funⁱ 
     fun-unitⁱ rewrite fun-unit₁ = fun-unit
    

module _ where
  open SFunⁱ
--   open ≡-Reasoning

--   take₁ : ∀ {A : Type} {n} {as : Vec A (suc n)} → head (take 1 as) ≡ head as 
--   take₁ {as = _ ∷ _} = refl

--   head-tail : ∀ {A : Type} {n} {as : Vec A (suc n)} {y} → y ≡ head as → as ≡ y ∷ tail as
--   head-tail {as = _ ∷ _} refl = refl

  fun-∷ :
    ∀ {n  : ℕ}
      {f  : SFunⁱ A B}
      {a  : A}
      {as : Vec A n}
      {b  : Vec B 1}
      (p  : fun f [ a ] ≡ just b)
    → fun f (a ∷ as) ≡ do
                         h ← fun-single f a
                         t ← fun (apply₁ f p) as
                         return (h ∷ t)
  fun-∷ {f = f} {a} {as} {b ∷ []} p with fun f (a ∷ as) in q
  ... | nothing rewrite p = refl
  ... | just (b' ∷ bs') rewrite p with fun-pres f {n = 1} q
  ... | r with trans (sym r) p
  ... | refl = refl

--   fun-∷ {f = f} {a} {as} ij with from-just' ij
--   ... | (a' ∷ [] , r) with fun f (a ∷ as) in p
--   ... | nothing = sym (from-nothing' (is-nothing->>=-r (fmap head (fun f [ a ]))))
--   ... | just (b ∷ bs) with fun-pres f {m = 1} (to-just p)
--   ... | q rewrite p | r | sym q = cong just (cong (_∷ bs) (just-[]-≡ q))
  
eval : SFunᵉ A B → SFunⁱ A B
eval (SFᵉ _ init fun) = SFⁱ (trace fun init) trace-preserving refl

-- resume-fun : SFunType A B (SFunⁱ A B)
-- resume-fun (g , a) with SFunⁱ.fun-single g a in p
-- ... | just b = just (SFunⁱ.apply₁ g {a = a} (is-just-fmap (to-just {y = b} p)) , b)
-- ... | nothing = nothing

resume : SFunⁱ A B → SFunᵉ A B
resume f = record
  { init = f
  ; fun = resume-fun
  }
  where
    resume-fun : SFunType A B (SFunⁱ A B)
    resume-fun (g , a) with SFunⁱ.fun-single g a in p
    ... | nothing = nothing
    ... | just b with SFunⁱ.fun g [ a ] in q
    ... | just (b' ∷ []) with p
    ... | refl = just (SFunⁱ.apply₁ g {bs = [ b ]} q , b)
    
    -- just (SFunⁱ.apply₁ g {a = a} (is-just-fmap (to-just {y = b} p)) , b)

_≈ⁱ_ : SFunⁱ A B → SFunⁱ A B → Type
f ≈ⁱ g = let open SFunⁱ in ∀ {n} → fun f {n} ≗ fun g {n}

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
f ≈ᵉ g = eval f ≈ⁱ eval g

eval∘resume≡id : ∀ {f : SFunⁱ A B} → eval (resume f) ≈ⁱ f
eval∘resume≡id {f = f} [] = sym (SFunⁱ.fun-unit f)
eval∘resume≡id {f = f} (a ∷ as) with resume f in p
... | SFᵉ _ init fun with fun (init , a) in q
... | nothing = {!!}
... | just b = {!!}

-- -- [] with SFunⁱ.fun f []
-- -- ... | [] = refl
-- -- eval∘resume≡id {f = f} (a ∷ as) = begin
-- --   head (fun f (a ∷ [])) ∷ fun (eval (resume (apply₁ f a))) as ≡⟨ cong (_ ∷_) (eval∘resume≡id as) ⟩
-- --   fun-single f a ∷ fun (apply₁ f a) as                              ≡⟨ sym (fun-∷ {f = f}) ⟩
-- --   fun f (a ∷ as)                                              ∎
-- --   where open ≡-Reasoning
-- --         open SFunⁱ

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
  ; assoc = λ _ → {!!} -- refl
  ; identityˡ = λ _ → {!!} -- refl
  ; identityʳ = λ _ → refl
  ; equiv = IsEquivalence-≈ⁱ
  ; ∘-resp-≈ = λ { {h = SFⁱ fun _ _} {SFⁱ fun₁ _ _} f≈ⁱh g≈ⁱi {n} v → {!!} } -- trans (f≈ⁱh (fun₁ v)) (cong fun (g≈ⁱi v)) }
  }
