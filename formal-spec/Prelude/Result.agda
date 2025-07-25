{-# OPTIONS --safe #-}
module Prelude.Result where

open import Prelude.Init
--open import Prelude.Monad
open import Class.Decidable

private variable
  A B E E₁ : Type

data Result (E A : Type) : Type where
  Ok  : A → Result E A
  Err : E → Result E A

module Monad-Result where
  -- annoyingly, this currently cannot instantiate Class.Monad (https://github.com/agda/agda-stdlib-classes/issues/2)
  _>>=_ : Result E A → (A → Result E B) → Result E B
  _>>=_ (Ok  x) f = f x
  _>>=_ (Err e) _ = Err e

  return : A → Result E A
  return = Ok

IsOk : Result E A → Type
IsOk (Ok _)  = ⊤
IsOk (Err _) = ⊥

_catch_ : Result E A → (E → Result E₁ A) → Result E₁ A
Ok x  catch _ = Ok x
Err e catch h = h e

mapErr : (E → E₁) → Result E A → Result E₁ A
mapErr f (Ok x)  = Ok x
mapErr f (Err e) = Err (f e)

infixr 4 _`mapErr`_
_`mapErr`_ : Result E A → (E → E₁) → Result E₁ A
m `mapErr` h = mapErr h m

mapErr-IsOk : {r : Result E A} {f : E → E₁} → IsOk r → IsOk (mapErr f r)
mapErr-IsOk {r = Ok x} ok = _

DecResult : Type → Type
DecResult A = Result (¬ A) A

decResult : Dec A → DecResult A
decResult (yes p) = Ok p
decResult (no ¬p) = Err ¬p

¿_¿ᴿ : (A : Type) → ⦃ A ⁇ ⦄ → DecResult A
¿ A ¿ᴿ = decResult ¿ A ¿

infix 4 ¿_¿ᴿ:_
¿_¿ᴿ:_ : (A : Type) → ⦃ A ⁇ ⦄ → (¬ A → E) → Result E A
¿ A ¿ᴿ: h = mapErr h ¿ A ¿ᴿ

isJustᴿ : {A : Type} (m : Maybe A) → Result (m ≡ nothing) (∃[ x ] m ≡ just x)
isJustᴿ (just x) = Ok (x , refl)
isJustᴿ nothing  = Err refl
