{-# OPTIONS --safe #-}

module Leios.FFD where

open import Leios.Prelude

record FFDAbstract : Type₁ where
  field Header Body ID : Type
        ⦃ DecEq-Header ⦄ : DecEq Header
        ⦃ DecEq-Body ⦄ : DecEq Body
        match : Header → Body → Type
        msgID : Header → ID

  data Input : Type where
    Send  : Header → Maybe Body → Input
    Fetch : Input

  data Output : Type where
    SendRes  : Output
    FetchRes : List (Header ⊎ Body) → Output

  record Functionality : Type₁ where
    field State : Type
          initFFDState : State
          _-⟦_/_⟧⇀_ : State → Input → Output → State → Type
          Dec-_-⟦_/_⟧⇀_ : {s : State} → {i : Input} → {o : Output} → {s' : State} → (s -⟦ i / o ⟧⇀ s') ⁇
          FFD-Send-total : ∀ {ffds h b} → ∃[ ffds' ] ffds -⟦ Send h b / SendRes ⟧⇀ ffds'

    open Input public
    open Output public
