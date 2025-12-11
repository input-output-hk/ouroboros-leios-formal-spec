<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
module Leios.FFD where
```
<!--
```agda
open import Leios.Prelude
```
-->
```agda
record FFDAbstract : Type₁ where
  field Header Body ID : Type
        ⦃ DecEq-Header ⦄ : DecEq Header
        ⦃ DecEq-Body ⦄ : DecEq Body
        match : Header → Body → Type
        msgID : Header → ID
```
```agda
  data Input : Type where
    Send  : Header → Maybe Body → Input
    Fetch : Input
```
```agda
  data Output : Type where
    SendRes  : Output
    FetchRes : List (Header ⊎ Body) → Output
```
```agda
  record Functionality : Type₁ where
    field State : Type
          initFFDState : State
          _-⟦_/_⟧⇀_ : State → Input → Output → State → Type
```
```agda
    open Input public
    open Output public
```
