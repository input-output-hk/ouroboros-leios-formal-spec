{- | 
This module serves as the main entry point for the Leios formal specification.
It imports all the core modules that together define the complete Leios protocol.

The specification is organized into several key areas:

## Core Protocol Components
- `Leios.Protocol` - Main protocol definition
- `Leios.Base` - Fundamental types and structures
- `Leios.Blocks` - Block structure and validation
- `Leios.Voting` - Voting mechanism specification

## Cryptographic Foundations  
- `CategoricalCrypto` - Category-theoretic approach to cryptography
- `Leios.VRF` - Verifiable Random Function implementation

## Network Layer
- `Network.Leios` - Leios-specific networking protocols
- `Network.BasicBroadcast` - Basic broadcast networking primitives

## Simplified Models
- `Leios.Simplified` - Simplified protocol models for analysis
- `Leios.Short` - Short protocol variants

## Foreign Function Interface
- `Leios.Foreign.*` - Haskell interoperability types and utilities

## Verification and Testing
- `Leios.Short.Trace.Verifier` - Trace verification for protocol properties
- State machine abstractions for protocol verification
-}

module formal-spec where

-- open import CategoricalCrypto
open import Class.Computational22
open import Leios.Abstract
open import Leios.Base
open import Leios.Blocks
open import Leios.Config
open import Leios.Defaults
open import Leios.FFD
open import Leios.Foreign.BaseTypes
open import Leios.Foreign.HsTypes
open import Leios.Foreign.Types
open import Leios.Foreign.Util
open import Leios.KeyRegistration
open import Leios.Linear
open import Leios.Linear.Premises
open import Leios.Linear.Trace.Verifier
open import Leios.Linear.Trace.Verifier.Test
-- -- open import Leios.Network
-- open import Leios.Prelude
-- open import Leios.Protocol
-- open import Leios.Short
-- -- open import Leios.Short.Deterministic
-- open import Leios.Short.Trace.Verifier
-- -- open import Leios.Short.Trace.Verifier.Test
-- -- open import Leios.Simplified
-- -- open import Leios.Simplified.Deterministic
-- -- open import Leios.Simplified.Deterministic.Test
-- open import Leios.SpecStructure
-- open import Leios.Traces
-- open import Leios.Voting
-- open import Leios.VRF
-- open import StateMachine

-- -- Networking
-- open import Network.BasicBroadcast
-- -- open import Network.Leios

-- open import Prelude.Result
