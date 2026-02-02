{-# OPTIONS --safe #-}

open import abstract-set-theory.Prelude
open import Class.Core
open import Categories.Category.Core
open import Categories.Category.Helper
open import Relation.Binary

open import Class.Monad.Ext
open import LibExt

import Relation.Binary.Construct.On as On
import Relation.Binary.Reasoning.Setoid as R-Setoid

module CategoricalCrypto.SFunM {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ F-Laws        : FunctorLaws M      ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄
  ⦃ M-Comm        : CommutativeMonad M ⦄
  where

SFunType : Type → Type → Type → Type
SFunType A B S = S × A → M (S × B)

record SFunᵉ (A B : Type) : Type₁ where
  field
    State : Type
    init  : State
    fun   : SFunType A B State

private variable A B C D State : Type

idᵉ : SFunᵉ A A
idᵉ = record
  { State = ⊤
  ; fun = λ (_ , a) → return (_ , a)
  }

_∘ᵉ'_ : ∀ {A B C State₁ State₂}
  → SFunType B C State₂
  → SFunType A B State₁
  → SFunType A C (State₂ × State₁)
_∘ᵉ'_ g f ((sg , sf) , a) = do
  (sf , b) ← f (sf , a)
  (sg , c) ← g (sg , b)
  return ((sg , sf) , c)

_∘ᵉ_ : ∀ {A B C}
  → SFunᵉ B C
  → SFunᵉ A B
  → SFunᵉ A C
_∘ᵉ_ g f = let module g = SFunᵉ g; module f = SFunᵉ f in record
  { State = g.State × f.State
  ; init  = g.init , f.init
  ; fun   = g.fun ∘ᵉ' f.fun
  } 

trace : SFunType A B State → State → List A → M (List B)
trace f s [] = return []
trace f s (a ∷ as) = do
  (s , b) ← f (s , a)
  bs ← trace f s as
  return (b ∷ bs)

eval : SFunᵉ A B → List A → M (List B)
eval f as = let open SFunᵉ f in trace fun init as

id-correct : ∀ {A} → return ≗ eval (idᵉ {A})
id-correct [] = refl
id-correct (a ∷ as) = begin
  return (a ∷ as)                                                        ≡⟨ sym >>=-identityˡ ⟩
  (return as >>= λ as → return (a ∷ as))                                 ≡⟨ id-correct as ⟩>>=⟨refl ⟩
  (trace (λ (_ , a) → return (tt , a)) tt as >>= λ as → return (a ∷ as)) ≡⟨ sym >>=-identityˡ ⟩
  eval idᵉ (a ∷ as) ∎
  where open ≡-Reasoning
  
trace-∘ : ∀ {StateG StateF sg sf} {g : SFunType B C StateG} {f : SFunType A B StateF}
  → trace g sg Kl-M.∘ trace f sf ≗ trace (g ∘ᵉ' f) (sg , sf)
trace-∘ {sg = sg} {sf} {g} {f} [] = begin
  (return [] >>= (λ x → return (trace g sg x)) >>= λ x → x)
    ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
  (return (return []) >>= λ x → x)
    ≡⟨ >>=-identityˡ ⟩
  return [] ∎
  where open ≡-Reasoning
trace-∘ {sg = sg} {sf} {g} {f} (a ∷ as) = begin
  (f (sf , a) >>=
    (λ (sf , b) → trace f sf as >>= λ bs → return (b ∷ bs)) >>=
    (λ x → return (trace g sg x)) >>=
    (λ x → x))
    ≡⟨ >>=-assoc (f (sf , a) >>= λ (sf , b) → trace f sf as >>= λ bs → return (b ∷ bs)) ⟩
  (f (sf , a) >>=
    (λ (sf , b) → trace f sf as >>= λ bs → return (b ∷ bs)) >>=
    (λ x → return (trace g sg x) >>=
    (λ x → x)))
    ≡⟨ refl⟩>>=⟨ (λ x → >>=-identityˡ) ⟩
  (f (sf , a) >>=
    (λ (sf , b) → trace f sf as >>= λ bs → return (b ∷ bs)) >>= trace g sg)
    ≡⟨ >>=-assoc (f (sf , a)) ⟩
  (f (sf , a) >>=
    (λ (sf , b) → (trace f sf as >>= λ bs → return (b ∷ bs)) >>= trace g sg))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → >>=-assoc _) ⟩
  (f (sf , a) >>=
    (λ (sf , b) → trace f sf as >>= λ bs → (return (b ∷ bs) >>= trace g sg)))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → refl⟩>>=⟨ λ bs → >>=-identityˡ) ⟩
  (f (sf , a) >>= λ (sf , b) → trace f sf as >>= λ bs → trace g sg (b ∷ bs))
    ≡⟨⟩
  (f (sf , a) >>= λ (sf , b) → trace f sf as >>= λ bs → g (sg , b) >>=
    λ (sg , c) → trace g sg bs >>= λ cs → return (c ∷ cs))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → >>=-comm-y _) ⟩
  (f (sf , a) >>= λ (sf , b) → g (sg , b) >>= λ (sg , c) →
    trace f sf as >>= λ bs → trace g sg bs >>= λ cs → return (c ∷ cs))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → refl⟩>>=⟨ λ (sg , c) → sym (>>=-assoc _)) ⟩
  (f (sf , a) >>= λ (sf , b) → g (sg , b) >>= λ (sg , c) →
    (trace f sf as >>= λ bs → trace g sg bs) >>= λ cs → return (c ∷ cs))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → refl⟩>>=⟨ λ (sg , c) → (refl⟩>>=⟨ λ bs → sym >>=-identityˡ) ⟩>>=⟨refl) ⟩
  (f (sf , a) >>= λ (sf , b) → g (sg , b) >>= λ (sg , c) →
    (trace f sf as >>= λ bs → (return (trace g sg bs) >>= λ x → x)) >>= λ cs → return (c ∷ cs))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → refl⟩>>=⟨ λ (sg , c) → sym (>>=-assoc _) ⟩>>=⟨refl) ⟩
  (f (sf , a) >>= λ (sf , b) → g (sg , b) >>= λ (sg , c) →
    (trace f sf as >>= return ∘ trace g sg >>= λ x → x) >>= λ cs → return (c ∷ cs))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → refl⟩>>=⟨ λ (sg , c) → trace-∘ as ⟩>>=⟨refl) ⟩
  (f (sf , a) >>= λ (sf , b) → g (sg , b) >>= λ (sg , c) →
    trace (g ∘ᵉ' f) (sg , sf) as >>= λ cs → return (c ∷ cs))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → refl⟩>>=⟨ λ (sg , c) → sym >>=-identityˡ) ⟩
  (f (sf , a) >>= λ (sf , b) → g (sg , b) >>= λ (sg , c) → return ((sg , sf) , c) >>=
    λ (s , c) → trace (g ∘ᵉ' f) s as >>= λ cs → return (c ∷ cs))
    ≡⟨ refl⟩>>=⟨ (λ (sf , b) → sym (>>=-assoc _)) ⟩
  (f (sf , a) >>= λ (sf , b) → (g (sg , b) >>= λ (sg , c) → return ((sg , sf) , c)) >>=
    λ (s , c) → trace (g ∘ᵉ' f) s as >>= λ cs → return (c ∷ cs))
    ≡⟨ sym (>>=-assoc (f (sf , a))) ⟩
  (f (sf , a) >>= (λ (sf , b) → g (sg , b) >>= λ (sg , c) → return ((sg , sf) , c)) >>=
    λ (s , c) → trace (g ∘ᵉ' f) s as >>= λ cs → return (c ∷ cs))
    ≡⟨⟩
  trace (g ∘ᵉ' f) (sg , sf) (a ∷ as) ∎
  where open ≡-Reasoning

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
_≈ᵉ_ = _≗_ on eval

assoc-∘ᵉ : {A B C D : Type} {f : SFunᵉ A B} {g : SFunᵉ B C} {h : SFunᵉ C D} → ((h ∘ᵉ g) ∘ᵉ f) ≈ᵉ (h ∘ᵉ (g ∘ᵉ f))
assoc-∘ᵉ {f = f} {g} {h} = begin
  eval ((h ∘ᵉ g) ∘ᵉ f)         ≈⟨ trace-∘ ⟨ 
  eval (h ∘ᵉ g) ∘ᵏ eval f      ≈⟨ ∘-resp-≈ (sym ∘ trace-∘) (λ _ → refl) ⟩
  (eval h ∘ᵏ eval g) ∘ᵏ eval f ≈⟨ assoc {f = eval f} ⟩
  eval h ∘ᵏ (eval g ∘ᵏ eval f) ≈⟨ ∘-resp-≈ (λ _ → refl) trace-∘ ⟩
  eval h ∘ᵏ eval (g ∘ᵉ f)      ≈⟨ trace-∘ ⟩
  eval (h ∘ᵉ (g ∘ᵉ f)) ∎
  where
    open Kl-M renaming (_∘_ to _∘ᵏ_)
    open R-Setoid ≗-setoid

identityˡ-∘ᵉ : {f : SFunᵉ A B} → (idᵉ ∘ᵉ f) ≈ᵉ f
identityˡ-∘ᵉ {f = f} = begin
  eval (idᵉ ∘ᵉ f)      ≈⟨ trace-∘ ⟨
  (eval idᵉ ∘ᵏ eval f) ≈⟨ ∘-resp-≈ (sym ∘ id-correct) (λ _ → refl) ⟩
  (idᵏ ∘ᵏ eval f)      ≈⟨ identityˡ ⟩ 
  eval f ∎
  where
    open Kl-M renaming (_∘_ to _∘ᵏ_ ; id to idᵏ)
    open R-Setoid ≗-setoid
    
identityʳ-∘ᵉ : {f : SFunᵉ A B} → (f ∘ᵉ idᵉ) ≈ᵉ f
identityʳ-∘ᵉ {f = f} = begin
  eval (f ∘ᵉ idᵉ)      ≈⟨ trace-∘ ⟨
  (eval f ∘ᵏ eval idᵉ) ≈⟨ ∘-resp-≈ (λ _ → refl) (sym ∘ id-correct) ⟩
  (eval f ∘ᵏ idᵏ)      ≈⟨ identityʳ ⟩ 
  eval f ∎
  where
    open Kl-M renaming (_∘_ to _∘ᵏ_ ; id to idᵏ)
    open R-Setoid ≗-setoid

∘ᵉ-resp-≈ᵉ : {A B C : Type} {f h : SFunᵉ B C} {g i : SFunᵉ A B} → f ≈ᵉ h → g ≈ᵉ i → (f ∘ᵉ g) ≈ᵉ (h ∘ᵉ i)
∘ᵉ-resp-≈ᵉ {f = f} {h} {g} {i} p q = begin
  eval (f ∘ᵉ g)      ≈⟨ trace-∘ ⟨
  (eval f ∘ᵏ eval g) ≈⟨ ∘-resp-≈ p (λ _ → refl) ⟩
  (eval h ∘ᵏ eval g) ≈⟨ ∘-resp-≈ (λ _ → refl) q ⟩
  (eval h ∘ᵏ eval i) ≈⟨ trace-∘ ⟩
  eval (h ∘ᵉ i) ∎
  where
    open Kl-M renaming (_∘_ to _∘ᵏ_ ; id to idᵏ)
    open R-Setoid ≗-setoid
    
SFunᵉ-Category : Category _ _ _
SFunᵉ-Category = categoryHelper record
  { Obj = Type
  ; _⇒_ = SFunᵉ
  ; _≈_ = _≈ᵉ_
  ; id = idᵉ
  ; _∘_ = _∘ᵉ_
  ; assoc = assoc-∘ᵉ
  ; identityˡ = identityˡ-∘ᵉ
  ; identityʳ = identityʳ-∘ᵉ
  ; equiv = On.isEquivalence eval IsEquivalence-≗
  ; ∘-resp-≈ = ∘ᵉ-resp-≈ᵉ
  }
