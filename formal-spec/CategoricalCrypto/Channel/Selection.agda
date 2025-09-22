{-# OPTIONS --safe --no-require-unique-meta-solutions #-}
{-# OPTIONS -v allTactics:100 #-}

module CategoricalCrypto.Channel.Selection where

open import CategoricalCrypto.Channel.Core
open import Relation.Nullary 
open import Meta.Prelude
open import Meta.Init
open import Data.Sum
open import Reflection.AST.Term
open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI
open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadTC.Instances hiding (_ᵗ)

instance _ = Functor-M ⦃ Class.Monad.Monad-TC ⦄

data LiftError : Set where
  MultipleSolutions : LiftError
  NoSolution : LiftError

liftConstr : TC ⊤
liftConstr = inDebugPath "Auto _[_]⇒[_]_ tactic" $ do
  holeType ← goalTy
  ensureNoMetas holeType
  quote _[_]⇒[_]_ ∙⟦ A ∣ m ∣ m' ∣ B ⟧ ← return holeType
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
      inj₂ $ def (quote ⇒-refl) []
    handle-pattern A m (quote ¬ₘ_ ∙⟦ m' ⟧) (quote _ᵀ ∙⟦ B ⟧) | false =
      map₂ (quote ⇒-trans ∙⟦_∣ quote ⇒-transpose ∙ ⟧)
           (handle-pattern A m m' B)
    handle-pattern A m m' (quote _ᵀ ∙⟦ B ⟧) | false =
      map₂ (quote ⇒-trans ∙⟦_∣ quote ⇒-trans ∙⟦ quote ⇒-transpose ∙ ∣ quote ⇒-double-negate ∙ ⟧ ⟧)
           (handle-pattern A m (quote ¬ₘ_ ∙⟦ m' ⟧) B)    
    handle-pattern A m m' (quote _⊗_ ∙⟦ B ∣ C ⟧) | false =
      case (handle-pattern A m m' B) of λ where
        (inj₁ NoSolution) →
          map₂ (quote ⇒-trans ∙⟦_∣ quote ⊗-left-intro ∙ ⟧)
               (handle-pattern A m m' C)
        (inj₁ MultipleSolutions) → inj₁ MultipleSolutions
        (inj₂ solution) → case (handle-pattern A m m' C) of λ where
          (inj₁ _) → inj₂ $ quote ⇒-trans ∙⟦ solution ∣ quote ⊗-right-intro ∙ ⟧
          (inj₂ _) → inj₁ MultipleSolutions
    handle-pattern _ _ _ _ | false = inj₁ NoSolution

module _ ⦃ _ : TCOptions ⦄ where
  liftC = initTac liftConstr

instance
  defaultTCOptionsI = record
    { debug = record defaultDebugOptions
      { prefix = '┃'
      ; filter = Filter.⊤
      }
    ; fuel  = ("reduceDec/constrs" , 5) ∷ []
    }
    
liftᵍ : ∀ {m m' A B} {@(tactic liftC) p : A [ m ]⇒[ m' ] B} → A [ m ]⇒[ m' ] B
liftᵍ {p = p} = p

↑ = liftᵍ

_↑ᵢ_ : ∀ {m'} A {B} {@(tactic liftC) p : A [ In ]⇒[ m' ] B} → A [ In ]⇒[ m' ] B
_↑ᵢ_ _ {p = p} = liftᵍ {p = p}

_↑ₒ_ : ∀ {m'} A {B} {@(tactic liftC) p : A [ Out ]⇒[ m' ] B} → A [ Out ]⇒[ m' ] B
_↑ₒ_ _ {p = p} = liftᵍ {p = p}

infix 7 _↑ᵢ_ _↑ₒ_

test : ∀ {A B D m} → A [ m ]⇒[ m ] ((D ⊗ A) ᵀ ⊗ B) ᵀ ⊗ (B ⊗ D)
test = ↑
