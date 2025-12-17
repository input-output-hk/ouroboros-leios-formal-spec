## Leios.Abstract

This module defines the abstract interface for the Leios protocol,
specifying the core types and operations required by the implementation.
It provides type signatures for transactions, pool identifiers, and
cryptographic primitives such as hashes, signatures, and verification proofs.
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
module Leios.Abstract where
```
<!--
```agda
open import Leios.Prelude
```
-->
```agda
record LeiosAbstract : Type₁ where
  field Tx       : Type
        PoolID   : Type
        BodyHash : Type
        VrfPf    : Type
        PrivKey  : Type
        Sig      : Type
        Hash     : Type
        EBCert   : Type
        Vote     : Type
```
```agda
        vote      : PrivKey → Hash → Vote
        sign      : PrivKey → Hash → Sig
        getEBHash : EBCert → Hash
```
```agda
        ⦃ DecEq-Tx ⦄     : DecEq Tx
        ⦃ DecEq-PoolID ⦄ : DecEq PoolID
        ⦃ DecEq-Hash ⦄   : DecEq Hash
        ⦃ DecEq-VrfPf ⦄  : DecEq VrfPf
        ⦃ DecEq-Sig ⦄    : DecEq Sig
        ⦃ DecEq-Vote ⦄   : DecEq Vote
        ⦃ Hashable-Txs ⦄ : Hashable (List Tx) Hash
```
