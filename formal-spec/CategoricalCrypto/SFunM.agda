{-# OPTIONS --safe #-}

open import abstract-set-theory.Prelude

open import Class.Core
open import Class.Functor
open import Class.Monad

import Categories.Monad as C
open import Categories.Category
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Instance.Sets
open import Categories.Category.SubCategory
open import Categories.Monad.Construction.Kleisli

open import Class.Monad.Ext

module CategoricalCrypto.SFunM {M : Type↑} ⦃ Monad-M : Monad M ⦄ ⦃ F-Laws : FunctorLaws M ⦄
  ⦃ M-Laws : MonadLaws M ⦄ ⦃ M-Extensional : ExtensionalMonad M ⦄ ⦃ M-Comm : CommutativeMonad M ⦄ where

-- relevant examples: M = id, Maybe, Powerset (relation), Giry (probability)
SFunType : Type → Type → Type → Type
SFunType A B S = S × A → M (S × B)

-- explicit state
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

_∘ᵉ'_ : ∀ {A B C State₁ State₂} → SFunType B C State₂ → SFunType A B State₁ → SFunType A C (State₂ × State₁)
_∘ᵉ'_ g f ((sg , sf) , a) = do
  (sf , b) ← f (sf , a)
  (sg , c) ← g (sg , b)
  return ((sg , sf) , c)

_∘ᵉ_ : ∀ {A B C} → SFunᵉ B C → SFunᵉ A B → SFunᵉ A C
_∘ᵉ_ g f = let module g = SFunᵉ g; module f = SFunᵉ f in record
  { State = g.State ×  f.State
  ; init  = g.init  ,  f.init
  ; fun   = g.fun  ∘ᵉ' f.fun
  } 

trace : SFunType A B State → State → List A → M (List B)
trace f s [] = return []
trace f s (a ∷ as) = do
  (s , b) ← f (s , a)
  bs ← trace f s as
  return (b ∷ bs)

eval : SFunᵉ A B → List A → M (List B)
eval f as = let open SFunᵉ f in trace fun init as

open ≡-Reasoning

id-correct : ∀ {A} → return ≗ eval (idᵉ {A})
id-correct [] = refl
id-correct (a ∷ as) = begin
  return (a ∷ as)
    ≡⟨ sym >>=-identityˡ ⟩
  (return as >>= λ as → return (a ∷ as))
    ≡⟨ id-correct as ⟩>>=⟨refl ⟩
  (trace (λ (_ , a) → return (tt , a)) tt as >>= λ as → return (a ∷ as))
    ≡⟨ sym >>=-identityˡ ⟩
  eval idᵉ (a ∷ as) ∎

trace-∘ : ∀ {StateG StateF sg sf} {g : SFunType B C StateG} {f : SFunType A B StateF}
  → trace g sg Kl-M.∘ trace f sf ≗ trace (g ∘ᵉ' f) (sg , sf)
trace-∘ {sg = sg} {sf} {g} {f} [] = begin
  (return [] >>= (λ x → return (trace g sg x)) >>= λ x → x)
    ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
  (return (return []) >>= λ x → x)
    ≡⟨ >>=-identityˡ ⟩
  return [] ∎
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

SFunᵉ-SubCat : SubCat Kl-M Type
SFunᵉ-SubCat = record
  { U    = List
  ; R    = λ f → ∃[ g ] f ≗ eval g
  ; Rid  = idᵉ , id-correct
  ; _∘R_ = λ where (g , gpf) (f , fpf) → g ∘ᵉ f , λ as → trans ((gpf Kl-M.HomReasoning.⟩∘⟨ fpf) as) (trace-∘ as)
  }

SFunᵉ-Category : Category _ _ _
SFunᵉ-Category = SubCategory Kl-M SFunᵉ-SubCat

module SFunᵉC = Category SFunᵉ-Category

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Relation.Binary.Construct.On as On

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
_≈ᵉ_ = _≗_ on eval

-- open import Function.Equality

IsEquivalence-≈ᵉ : IsEquivalence (_≈ᵉ_ {A} {B})
IsEquivalence-≈ᵉ {A} {B} = On.isEquivalence eval {!On.setoid (List A ⟶ M (List B)) eval !}

SFunᵉ-Setoid : Type → Type → Setoid _ _
SFunᵉ-Setoid A B = record
  { Carrier = SFunᵉ A B
  ; _≈_ = _≈ᵉ_
  ; isEquivalence = IsEquivalence-≈ᵉ
  }

iso : ∀ {A B} → Inverse (SFunᵉC.hom-setoid {A} {B}) (SFunᵉ-Setoid A B)
iso = {!On.setoid!} -- mk↔ {to = λ where (f , g , eq) → g} {from = λ g → (eval g , g , (λ _ → refl))}
  -- ((λ where refl → refl) , λ where {x = (f , g , pf)} refl → refl)
