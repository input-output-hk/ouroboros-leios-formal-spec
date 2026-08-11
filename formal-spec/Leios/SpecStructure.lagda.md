## Leios.SpecStructure
<!--
```agda
{-# OPTIONS --safe #-}

open import Leios.Abstract
open import Leios.FFD
open import Leios.Prelude hiding (id)
open import Leios.VRF

import Leios.Base
import Leios.Blocks
import Leios.KeyRegistration
import Leios.Voting

open import Data.Fin
```
-->
```agda
module Leios.SpecStructure where
```
```agda
record SpecStructure : Type₂ where
```
```agda
  field a : LeiosAbstract

  open LeiosAbstract a public
  open Leios.Blocks a public
```
```agda
  field ⦃ IsBlock-Vote ⦄ : IsBlock (List Vote)
        ⦃ Hashable-PreEndorserBlock ⦄ : Hashable PreEndorserBlock Hash
        id : PoolID
        FFD' : FFDAbstract.Functionality ffdAbstract
        vrf' : LeiosVRF a

  open LeiosVRF vrf' public
```
```agda
  field sk-EB sk-VT : PrivKey
        pk-EB pk-VT : PubKey

  open Leios.Base a vrf' public
```
```agda
  field B' : BaseAbstract
        BM : BaseAbstract.BaseMachine B'

  open Leios.KeyRegistration a vrf' public
```
```agda
  field K' : KeyRegistrationAbstract
        KF : KeyRegistrationAbstract.Functionality K'

  module B   = BaseAbstract.BaseMachine BM
  module K   = KeyRegistrationAbstract.Functionality KF
  module FFD = FFDAbstract.Functionality FFD'

  open Leios.Voting public
```
```agda
  field va : VotingAbstract EndorserBlock
  open VotingAbstract va public
```
```agda
  field getEBCert         : ∀ {s eb} → isVoteCertified s eb → EBCert
        -- Whether validation of the given EB has completed by the given slot.
        -- Replaces the former `validityCheckTime : EndorserBlock → ℕ` oracle:
        -- validation latency is a property of the node and its environment,
        -- not of the EB alone, so the spec only assumes an observable
        -- completion predicate (monotone in the slot in intended
        -- instantiations). Eventually to be provided by an asynchronous
        -- validation functionality (Valid/Invalid/InProgress with bounded
        -- InProgress).
        isValidityChecked  : ℕ → EndorserBlock → Type
        isValidityChecked? : ∀ n eb → Dec (isValidityChecked n eb)
```
