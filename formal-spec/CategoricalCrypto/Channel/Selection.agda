{-# OPTIONS --safe --no-require-unique-meta-solutions #-}
{-# OPTIONS -v allTactics:100 #-}

module CategoricalCrypto.Channel.Selection where

open import CategoricalCrypto.Channel.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary 
open import Function
open import Meta.Prelude
open import Meta.Init
open import Data.Nat.Show

open import Data.List
open import Data.Sum

open import Reflection.AST.Term
open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI

open import Class.Functor.Instances
open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances hiding (_ᵗ)
open import Class.Traversable
open import Class.Functor
open import Class.Traversable

infix 4 _[_]⇒[_]ᵍ_

infix 10 _ᵗ¹ _ᵗ²
infix 9 _⊗R
infix 8 L⊗_

data _[_]⇒[_]ᵍ_ : Channel → Mode → Mode → Channel → Set₁ where 
  ϵ : ∀ {m A} → A [ m ]⇒[ m ]ᵍ A
  _⊗R : ∀ {m m' A B C} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ]ᵍ B ⊗ C
  L⊗_ : ∀ {m m' A B C} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ]ᵍ C ⊗ B
  _ᵗ¹ : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ ¬ₘ m' ]ᵍ B ᵀ
  _ᵗ² : ∀ {m m' A B} → A [ m ]⇒[ ¬ₘ m' ]ᵍ B → A [ m ]⇒[ m' ]ᵍ B ᵀ

instance _ = Functor-M ⦃ Class.Monad.Monad-TC ⦄

data LiftError : Set where
  MultipleSolutions : LiftError
  NoSolution : LiftError

liftConstr : TC ⊤
liftConstr = inDebugPath "Lift _[_]⇒[_]ᵍ_ tactic" $ do
  holeType ← goalTy
  ensureNoMetas holeType
  quote _[_]⇒[_]ᵍ_ ∙⟦ A ∣ m ∣ m' ∣ B ⟧ ← return holeType
    where _ → error ("Bad type shape1: " ∷ᵈ holeType ∷ᵈ [])
  inj₂ solution ← return $ handle-pattern A m m' B
    where
      (inj₁ NoSolution) → error1 "No solution found"
      (inj₁ MultipleSolutions) → error1 "Multiple solutions found"
  debugLog (solution ∷ᵈ [])
  unifyWithGoal solution
  where
    handle-pattern : Term → Term → Term → Term → LiftError ⊎ Term
    handle-pattern A m m' B with isYes (A ≟ B ×-dec m ≟ m')
    handle-pattern A m _ _ | true =
      inj₂ $ con (quote ϵ) (hArg m ∷ hArg A ∷ [])
    handle-pattern A m (quote ¬ₘ_ ∙⟦ m' ⟧) (quote _ᵀ ∙⟦ B ⟧) | false =
      map₂ (λ rec → con (quote _ᵗ¹) (vArg rec ∷ [])) $ handle-pattern A m m' B
    handle-pattern A m m' (quote _ᵀ ∙⟦ B ⟧) | false =
      map₂ (λ rec → con (quote _ᵗ²) (vArg rec ∷ [])) $ handle-pattern A m (quote ¬ₘ_ ∙⟦ m' ⟧) B      
    handle-pattern A m m' (quote _⊗_ ∙⟦ B ∣ C ⟧) | false =
      case (handle-pattern A m m' B) of λ where
        (inj₁ NoSolution) → map₂ (λ rec → con (quote L⊗_) (vArg rec ∷ [])) $ handle-pattern A m m' C
        (inj₁ MultipleSolutions) → inj₁ MultipleSolutions
        (inj₂ solution) → case (handle-pattern A m m' C) of λ where
          (inj₁ _) → inj₂ $ con (quote _⊗R) (vArg solution ∷ [])
          (inj₂ _) → inj₁ MultipleSolutions
    handle-pattern _ _ _ _ | false = inj₁ NoSolution

module _ ⦃ _ : TCOptions ⦄ where
  liftC = initTac liftConstr

-- open import Tactic.Defaults

instance
  defaultTCOptionsI = record
    { debug = record defaultDebugOptions
      { prefix = '┃'
      ; filter = Filter.⊤
      }
    ; fuel  = ("reduceDec/constrs" , 5) ∷ []
    }
    
liftᵍ : ∀ {m m' A B} {@(tactic liftC) p : A [ m ]⇒[ m' ]ᵍ B} → A [ m ]⇒[ m' ] B
liftᵍ {p = ϵ} = ⇒-refl
liftᵍ {p = x ⊗R} = liftᵍ {p = x} ⇒ₜ ⊗-right-intro
liftᵍ {p = L⊗ x} = liftᵍ {p = x} ⇒ₜ ⊗-left-intro
liftᵍ {p = x ᵗ¹} = liftᵍ {p = x} ⇒ₜ ⇒-transpose
liftᵍ {p = x ᵗ²} = liftᵍ {p = x} ⇒ₜ ⇒-transpose ⇒ₜ ⇒-double-negate

↑ = liftᵍ

_↑ᵢ_ : ∀ {m'} A {B} {@(tactic liftC) p : A [ In ]⇒[ m' ]ᵍ B} → A [ In ]⇒[ m' ] B
_↑ᵢ_ _ {p = p} = liftᵍ {p = p}

_↑ₒ_ : ∀ {m'} A {B} {@(tactic liftC) p : A [ Out ]⇒[ m' ]ᵍ B} → A [ Out ]⇒[ m' ] B
_↑ₒ_ _ {p = p} = liftᵍ {p = p}

infix 7 _↑ᵢ_ _↑ₒ_

test : ∀ {A B D m} → B [ m ]⇒[ m ] ((D ⊗ A) ᵀ ⊗ B) ᵀ ⊗ (B ⊗ D)
test = ↑ 
