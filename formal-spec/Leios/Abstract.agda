{-# OPTIONS --safe #-}

{- Module: Leios.Abstract
   
   This module defines the abstract interface for the Leios protocol,
   specifying the core types and operations required by the implementation.
   It provides type signatures for transactions, pool identifiers, and 
   cryptographic primitives such as hashes, signatures, and verification proofs.
-}

module Leios.Abstract where

open import Leios.Prelude

record LeiosAbstract : Type₁ where
  field Tx : Type
        ⦃ DecEq-Tx ⦄ : DecEq Tx
        PoolID : Type
        ⦃ DecEq-PoolID ⦄ : DecEq PoolID
        BodyHash VrfPf PrivKey Sig Hash EBCert : Type -- these could have been byte strings, but this is safer
        ⦃ DecEq-Hash ⦄ : DecEq Hash
        ⦃ DecEq-VrfPf ⦄ : DecEq VrfPf
        ⦃ DecEq-Sig ⦄ : DecEq Sig
        Vote : Type
        ⦃ DecEq-Vote ⦄ : DecEq Vote
        vote : PrivKey → Hash → Vote
        sign : PrivKey → Hash → Sig
        ⦃ Hashable-Txs ⦄ : Hashable (List Tx) Hash
        getEBHash : EBCert → Hash
