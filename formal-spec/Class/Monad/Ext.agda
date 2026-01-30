{-# OPTIONS --safe #-}

open import abstract-set-theory.Prelude

open import Class.Core
open import Class.Monad
open import Class.Prelude using (Typeω)
open import Data.Product

module Class.Monad.Ext where

record ExtensionalMonad (M : Type↑) ⦃ Monad-M : Monad M ⦄ ⦃ _ : MonadLaws M ⦄ : Typeω where
  infixr 4 _⟩>>=⟨_ refl⟩>>=⟨_
  infixl 5 _⟩>>=⟨refl

  field _⟩>>=⟨_ : ∀ {a b} {A : Type a} {B : Type b} {x y : M A} {f g : A → M B}
                → x ≡ y → f ≗ g → (x >>= f) ≡ (y >>= g)

  refl⟩>>=⟨_ : ∀ {a b} {A : Type a} {B : Type b} {x : M A} {f g : A → M B} → f ≗ g → (x >>= f) ≡ (x >>= g)
  refl⟩>>=⟨_ = refl ⟩>>=⟨_

  _⟩>>=⟨refl : ∀ {a b} {A : Type a} {B : Type b} {x y : M A} {f : A → M B} → x ≡ y → (x >>= f) ≡ (y >>= f)
  _⟩>>=⟨refl = _⟩>>=⟨ λ _ → refl

open ExtensionalMonad ⦃...⦄ public

instance
  Extensional-Maybe : ExtensionalMonad Maybe
  Extensional-Maybe ._⟩>>=⟨_ {x = x} refl f≗g with x
  ... | just x  = f≗g x
  ... | nothing = refl

record CommutativeMonad (M : Type↑) ⦃ Monad-M : Monad M ⦄ ⦃ _ : MonadLaws M ⦄ : Typeω where
  field >>=-comm : ∀ {a b} {X : Type a} {Y : Type b} {x : M X} {y : M Y}
          → (x >>= λ x → y >>= λ y → return (x ,′ y)) ≡ (y >>= λ y → x >>= λ x → return (x , y))

  -- yoneda variant
  >>=-comm-y : ∀ ⦃ _ : ExtensionalMonad M ⦄ {X Y Z : Type} {x : M X} {y : M Y} (f : X → Y → M Z)
    → (x >>= λ x → y >>= λ y → f x y) ≡ (y >>= λ y → x >>= λ x → f x y)
  >>=-comm-y {x = x} {y} f = begin
    (x >>= λ x → y >>= λ y → f x y)
      ≡⟨ (refl⟩>>=⟨ λ x → refl⟩>>=⟨ λ y → sym >>=-identityˡ) ⟩
    (x >>= λ x → y >>= λ y → return (x ,′ y) >>= λ (x , y) → f x y)
      ≡⟨ refl⟩>>=⟨ (λ x → sym (>>=-assoc _)) ⟩
    (x >>= λ x → (y >>= λ y → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≡⟨ sym (>>=-assoc _) ⟩
    ((x >>= λ x → y >>= λ y → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≡⟨ >>=-comm ⟩>>=⟨refl ⟩
    ((y >>= λ y → x >>= λ x → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≡⟨ >>=-assoc _ ⟩
    (y >>= λ y → (x >>= λ x → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≡⟨ refl⟩>>=⟨ (λ y → >>=-assoc _) ⟩
    (y >>= λ y → x >>= λ x → return (x ,′ y) >>= λ (x , y) → f x y)
      ≡⟨ (refl⟩>>=⟨ λ y → refl⟩>>=⟨ λ x → >>=-identityˡ) ⟩
    (y >>= λ y → x >>= λ x → f x y) ∎
    where open ≡-Reasoning

open CommutativeMonad ⦃...⦄ public

instance
  Commutative-Maybe : CommutativeMonad Maybe
  Commutative-Maybe .>>=-comm {x = just  _} {just  _} = refl
  Commutative-Maybe .>>=-comm {x = just  _} {nothing} = refl
  Commutative-Maybe .>>=-comm {x = nothing} {just  _} = refl
  Commutative-Maybe .>>=-comm {x = nothing} {nothing} = refl


import Categories.Monad as C
open import Categories.Category
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Instance.Sets
open import Categories.Monad.Construction.Kleisli

module _ {M : Type↑} ⦃ Monad-M : Monad M ⦄ ⦃ F-Laws : FunctorLaws M ⦄
  ⦃ M-Laws : MonadLaws M ⦄ ⦃ M-Extensional : ExtensionalMonad M ⦄ where

  KleisliTriple-M : ∀ {a} → KleisliTriple (Sets a)
  KleisliTriple-M = record
    { F₀ = M
    ; unit = return
    ; extend = _=<<_
    ; identityʳ = λ _ → >>=-identityˡ
    ; identityˡ = >>=-identityʳ
    ; assoc = λ x → sym (>>=-assoc x)
    ; sym-assoc = λ x → >>=-assoc x
    ; extend-≈ = λ eq _ → refl⟩>>=⟨ eq
    }

  Monad′-M : ∀ {a} → C.Monad (Sets a)
  Monad′-M = Kleisli⇒Monad _ KleisliTriple-M

  Kl-M : ∀ {a} → Category _ a _
  Kl-M = Kleisli Monad′-M
  module Kl-M {a} = Category {ℓ = a} Kl-M
