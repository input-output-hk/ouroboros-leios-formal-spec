{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Constraints where

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import Leios.Prelude
open import Tactic.Defaults

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
    -- We can create an input message from a query
    queryI : Query → machine-channel .inType
    
    -- We can create an output message for all the possible types of the queries
    -- responses
    queryO : ∀ {query} → QueryReturnType query → machine-channel .outType
    
    -- Correctness: For every received query of a given shape and wiring which
    -- gets a response, the response is also properly shaped and wired.
    correctness : ∀ {query s response' s'}
      → s -⟦ queryI query / response' ⟧ᵐ⇀ s'
      → ∃ λ response → response' ≡ just (queryO {query} response)
      
    -- Completeness: queries of the right shape and wiring always get a response
    completeness : ∀ {query s}
      → ∃ λ response'
      → ∃ λ s'
      → s -⟦ queryI query / just response' ⟧ᵐ⇀ s'

  -- Retrieves the response to a given query
  queryCompute : ∀ query (s : State) → (QueryReturnType query × State)
  queryCompute query s with completeness {query} {s}
  ... | response' , s' , p with correctness p
  ... | response , _ = response , s'

-- Ensures that a certain constrained machine does not change it inner state
-- when receiving a specific constrained query
IsPureOn :
  {A B             : Channel}
  {m               : Machine A B}
  {Query           : Type}
  {QueryReturnType : Query → Type}
  (isConstrained   : IsConstrained m QueryReturnType)
  (query           : Query)
  → Type
IsPureOn {m = m} isConstrained query =
  let open IsConstrained isConstrained
      open Machine m renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
   in ∀ {s s' response'}
     → s -⟦ queryI query / response' ⟧ᵐ⇀ s'
     → s ≡ s'

-- Ensures that a certain constrained machine does not change its inner state
-- when receiving any constrained query
IsPure : 
  {A B             : Channel}
  {m               : Machine A B}
  {Query           : Type}
  {QueryReturnType : Query → Type}
  (isConstrained   : IsConstrained m QueryReturnType)
  → Type
IsPure isConstrained = ∀ query → IsPureOn isConstrained query

-- Ensures that a certain constrained machine can only return a single response
-- when receiving a specific constrained query
IsDetOn :
  {A B             : Channel}
  {m               : Machine A B}
  {Query           : Type}
  {QueryReturnType : Query → Type}
  (isConstrained   : IsConstrained m QueryReturnType)
  (query           : Query)
  → Type
IsDetOn {m = m} isConstrained query =
  let open IsConstrained isConstrained
      open Machine m renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
   in ∀ {s}
     → ∃! _≡_ λ response'
     → ∃! _≡_ λ s'
     → s -⟦ queryI query / response' ⟧ᵐ⇀ s'

-- Ensures that a certain constrained machine can only return a single response
-- per constrained queries
IsDet : 
  {A B             : Channel}
  {m               : Machine A B}
  {Query           : Type}
  {QueryReturnType : Query → Type}
  (isConstrained   : IsConstrained m QueryReturnType)
  → Type
IsDet isConstrained = ∀ query → IsDetOn isConstrained query
