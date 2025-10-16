{-# OPTIONS --safe --no-require-unique-meta-solutions #-}
{-# OPTIONS -v allTactics:100 #-}

module CategoricalCrypto.Channel.Selection where

open import CategoricalCrypto.Channel.Core
open import Relation.Nullary
open import Meta.Prelude
open import Meta.Init
open import Data.Sum hiding (reduce)
open import Data.List renaming (map to mapₗ)
open import Reflection.AST.Term
open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI
open import Class.Monad
open import Class.Functor
open import Class.MonadError.Instances
open import Class.MonadTC.Instances hiding (_ᵗ)

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

infix 7 _↑ _↑ᵢ_ _↑ₒ_

_↑ : ∀ {m m' A B} → A [ m ]⇒[ m' ]ᵍ B → A [ m ]⇒[ m' ] B
ϵ ↑ = ⇒-refl
(x ⊗R) ↑ = (x ↑) ⇒ₜ ⊗-right-intro
(L⊗ x) ↑ = (x ↑) ⇒ₜ ⊗-left-intro
(x ᵗ¹) ↑ = (x ↑) ⇒ₜ ⇒-negate-transpose-right
(x ᵗ²) ↑ = (x ↑) ⇒ₜ ⇒-negate-transpose-left

_↑ᵢ_ = _↑ {In}
_↑ₒ_ = _↑ {Out}

instance _ = Functor-M ⦃ Class.Monad.Monad-TC ⦄

⇒-solver-tactic' : TC ⊤
⇒-solver-tactic' = inDebugPath "Auto _[_]⇒[_]_ tactic" $ do
  holeType' ← goalTy
  ensureNoMetas holeType'
  let (args , holeType) = stripPis holeType'
  inContext args $ do
    quote _[_]⇒[_]_ ∙⟦ A ∣ m ∣ m' ∣ B ⟧ ← return holeType
      where _ → error ("Bad type shape: " ∷ᵈ holeType ∷ᵈ [])
    debugLog ("Attempting to find a solution for problem " ∷ᵈ holeType ∷ᵈ [])
    -- Reductions must happen on the mode to compute negations when the mode is
    -- actually known
    mN ← reduce m
    m'N ← reduce m'
    solution ← handle-pattern A mN m'N B
    debugLog ("Solution: " ∷ᵈ solution ∷ᵈ [])
    unifyWithGoal $ prependLams (mapₗ (\{(s , arg (arg-info v _) _) → (s , v)}) args) solution
  where
  handle-pattern : Term → Term → Term → Term → TC Term
  handle-pattern A m m' B
    with isYes (A ≟ B ×-dec m ≟ m')
  ... | true
    = return $ quote ⇒-refl ∙
  ... | false
  ------------------------
  -- Inspecting the LHS --
  ------------------------
    with A | m
  -- A ᵀ ᵀ [ m ]⇒[ m' ] B
  ... | quote _ᵀ ∙⟦ quote _ᵀ ∙⟦ A ⟧ ⟧ | _ = do
    rec ← handle-pattern A m m' B
    return $ quote _⇒ₜ_ ∙⟦ quote ⇒-double-transpose-left ∙ ∣ rec ⟧
  -- A [ ¬ₘ ¬ₘ m ]⇒[ m' ] B
  ... | _ | quote ¬ₘ_ ∙⟦ quote ¬ₘ_ ∙⟦ m ⟧ ⟧ = do
    rec ← handle-pattern A m m' B
    return $ quote _⇒ₜ_ ∙⟦ quote ⇒-double-negate-left ∙ ∣ rec ⟧
  -- A ᵀ [ ¬ₘ m ]⇒[ m' ] B
  ... | quote _ᵀ ∙⟦ A ⟧ | quote ¬ₘ_ ∙⟦ m ⟧ = do
    rec ← handle-pattern A m m' B
    return $ quote _⇒ₜ_ ∙⟦ quote ⇒-negate-transpose-left ∙ ∣ rec ⟧
  -- A ᵀ [ m ]⇒[ m' ] B
  ... | quote _ᵀ ∙⟦ A ⟧ | _ = do
    m'' ← reduce (quote ¬ₘ_ ∙⟦ m ⟧)
    rec ← handle-pattern A m'' m' B
    return $ quote _⇒ₜ_ ∙⟦ quote ⇒-transpose-left-negate-right ∙ ∣ rec ⟧
  -- A ⊗ C [ m ]⇒[ m' ] B
  ... | quote _⊗_ ∙⟦ A ∣ C ⟧ | _ = do
    rec-left ← handle-pattern A m m' B
    rec-right ← handle-pattern C m m' B
    return $ quote ⊗-merge ∙⟦ rec-left ∣ rec-right ⟧
  ... | _ | _
  ------------------------
  -- Inspecting the RHS --
  ------------------------
    with m' | B
  -- A [ m ]⇒[ m' ] B ᵀ ᵀ
  ... | _ | quote _ᵀ ∙⟦ quote _ᵀ ∙⟦ B ⟧ ⟧ = do
    rec ← handle-pattern A m m' B
    return $ quote _⇒ₜ_ ∙⟦ rec ∣ quote ⇒-double-transpose-right ∙ ⟧
  -- A [ m ]⇒[ ¬ₘ ¬ₘ m' ] B
  ... | quote ¬ₘ_ ∙⟦ quote ¬ₘ_ ∙⟦ m' ⟧ ⟧ | _ = do
    rec ← handle-pattern A m m' B
    return $ quote _⇒ₜ_ ∙⟦ rec ∣ quote ⇒-double-negate-right ∙ ⟧
  -- A [ m ]⇒[ ¬ₘ m' ] B ᵀ
  ... | quote ¬ₘ_ ∙⟦ m' ⟧ | quote _ᵀ ∙⟦ B ⟧ = do
    rec ← handle-pattern A m m' B
    return $ quote _⇒ₜ_ ∙⟦ rec ∣ quote ⇒-negate-transpose-right ∙ ⟧
  -- A [ m ]⇒[ m' ] B ᵀ
  ... | _ | quote _ᵀ ∙⟦ B ⟧ = do
    m'' ← reduce (quote ¬ₘ_ ∙⟦ m' ⟧)
    rec ← handle-pattern A m m'' B
    return $ quote _⇒ₜ_ ∙⟦ rec ∣ quote ⇒-negate-left-transpose-right ∙ ⟧
  -- A [ m ]⇒[ m' ] B ⊗ C
  ... | _ | quote _⊗_ ∙⟦ B ∣ C ⟧ = do
    catch
      (do
        res-left ← handle-pattern A m m' B
        catch
          (do
            handle-pattern A m m' C
            error1 "Unique solution required, multiple found.")
          (const $ return $ quote _⇒ₜ_ ∙⟦ res-left ∣ quote ⊗-right-intro ∙ ⟧))
      (const $ do
        res-right ← handle-pattern A m m' C
        return $ quote _⇒ₜ_ ∙⟦ res-right ∣ quote ⊗-left-intro ∙ ⟧)
  -- otherwise throw error
  ... | _ | _
    = error $  "No solution found, unable to match " ∷ᵈ A
            ∷ᵈ " with mode " ∷ᵈ m ∷ᵈ " on the right hand side" ∷ᵈ B ∷ᵈ " with mode " ∷ᵈ m' ∷ᵈ []

module _ ⦃ _ : TCOptions ⦄ where
  ⇒-solver-tactic = initTac ⇒-solver-tactic'
  macro
    ⇒-solver = ⇒-solver-tactic

instance
  defaultTCOptionsI = record
    { debug = record defaultDebugOptions
      { prefix = '┃'
      ; filter = Filter.⊤
      }
    ; fuel  = ("reduceDec/constrs" , 5) ∷ []
    }
