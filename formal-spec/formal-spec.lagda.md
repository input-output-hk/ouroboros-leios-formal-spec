This module serves as the main entry point for the Leios formal specification.
It imports all the core modules that together define the complete Leios protocol.
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
module formal-spec where
```
The specification is organized into several key areas

### Prelude
TODO: move into iog-agda-prelude
```agda
open import Prelude.Result
open import Prelude.Errors

open import Class.Computational22
```
### Core Protocol Components
Abstract interface, specifing core types and functions
```agda
open import Leios.Abstract
```
Fundamental types and structures
```agda
open import Leios.Base
```
Block structure and validation
```agda
open import Leios.Blocks
```
Protocol parameters and configuration
```agda
open import Leios.Config
```
Freshest first delivery abstraction
```agda
open import Leios.FFD
```
Key registration abstraction
```agda
open import Leios.KeyRegistration
```
Project specific prelude
```agda
open import Leios.Prelude
```
Main protocol definition
```agda
open import Leios.Protocol
```
Abstractions bundled
```agda
open import Leios.SpecStructure
```
Voting mechanism specification
```agda
open import Leios.Voting
```
Verifiable Random Function implementation
```agda
open import Leios.VRF
```
Linear Leios specification
```agda
open import Leios.Linear
```
### Cryptographic Foundations
Category-theoretic approach to cryptography
```agda
open import CategoricalCrypto
```
### Network Layer
Basic broadcast networking primitives
```agda
open import Network.BasicBroadcast
```
### Verification and Testing
Trace verification for protocol properties
```agda
open import Leios.Linear.Trace.Verifier
open import Leios.Linear.Trace.Verifier.Test
open import Test.Defaults
```
