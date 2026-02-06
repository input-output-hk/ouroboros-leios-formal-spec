{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Constraints where

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import Leios.Prelude
open import Tactic.Defaults
open import Function.Bundles

record IsConstrained
  {A B             : Channel}
  -- The machine that needs to be constrained
  (m               : Machine A B)
  -- The type of possible queries
  {Query           : Type}
  -- The return type from a given query
  (QueryReturnType : Query → Type) : Type₁ where

  open Channel
  open Machine m renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)

  field
    -- Channels on which the queries are sent and received. This should
    -- correspond to "parts" of A and B regarding the tensor product and the
    -- transposition. The idea is to infer the propagation proof.
    {inChannel outChannel} : Channel
    -- Modes (In or Out) where the messages are sent and received
    {inMode outMode} : Mode
    -- Proofs that we can "wire" things properly. The rationale is that these
    -- proofs should be easily computed using the ⇒-solver tactics.
    @(tactic ⇒-solver-tactic) {inWire} : inChannel [ inMode ]⇒[ In ] machine-channel
    @(tactic ⇒-solver-tactic) {outWire} : outChannel [ outMode ]⇒[ Out ] machine-channel
    -- We can create an input message from a query
    queryI : Query → modeType inMode inChannel
    -- We can create an output message for all the possible types of the queries
    -- responses
    queryO : ∀ {query} → QueryReturnType query → modeType outMode outChannel
    -- Constrains the possible outcomes for a given query, initial state,
    -- response and resulting state. This relation forces to have a response
    -- (just XXX) but can easily be changed to force a nothing if need be
    queryResponse : ∀ query → State → QueryReturnType query → State → Type
    -- The initial relation restricted to the wired signals should be equivalent
    -- to queryResponse
    correctness :
      ∀ {query s response s'} →
        s -⟦ app inWire (queryI query) / just (app outWire (queryO response)) ⟧ᵐ⇀ s'
        ⇔ queryResponse query s response s'  

record IsPure
  {A B             : Channel}
  {m               : Machine A B}
  {Query           : Type}
  {QueryReturnType : Query → Type}
  (isConstrained   : IsConstrained m QueryReturnType) : Type₁ where

  open IsConstrained isConstrained

  field
    -- A proof that the state remains unchanged, and thus responding to the
    -- query did not cause any side effect
    isPure : ∀ {query s response s'} → queryResponse query s response s' → s ≡ s'

record IsDet
  {A B             : Channel}
  {m               : Machine A B}
  {Query           : Type}
  {QueryReturnType : Query → Type}
  (isConstrained   : IsConstrained m QueryReturnType) : Type₁ where
  
  open IsConstrained isConstrained
  open Machine m

  field
    -- A proof that there is a unique pair (response , state) related to a given
    -- pair (query , state), thus making this relation a deterministic function
    isDet :
      ∀ {query s}
      → ∃! {A = QueryReturnType query × State} _≡_ (uncurry (queryResponse query s))

  -- Views the deterministic relation as a function, and applies it on an input
  queryCompute : ∀ query s → (QueryReturnType query × State)
  queryCompute query s = proj₁ (isDet {query} {s})
