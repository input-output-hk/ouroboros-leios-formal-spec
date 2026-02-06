{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Constraints where

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import Leios.Prelude
open import Tactic.Defaults

module _ 
  {A B             : Channel}
  -- The machine that needs to be constrained
  (m               : Machine A B)
  -- The type of possible queries
  (Query           : Type)
  -- The return type from a given query
  (QueryReturnType : Query → Type)
  where

  record IsConstrained : Type₁ where

    open Channel
    open Machine m renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)

    field
      -- The channels on which the queries are sent and received. This
      -- should correspond to "parts" of A and B regarding the tensor product
      -- and the transposition. The idea is to infer the propagation proof.
      {inChannel outChannel} : Channel
      -- Similarly, these are the modes (In or Out) where the messages are
      -- send and received
      {inMode outMode} : Mode
      -- Then we have the proofs that we can "wire" things properly. The
      -- rationale is that these proofs should be easily computed using the
      -- ⇒-solver tactics.
      @(tactic ⇒-solver-tactic) {inWire} : inChannel [ inMode ]⇒[ In ] machine-channel
      @(tactic ⇒-solver-tactic) {outWire} : outChannel [ outMode ]⇒[ Out ] machine-channel
      -- We can create an input message from a query
      queryI : Query → modeType inMode inChannel
      -- We can create an output message for all the possible types
      -- of the queries responses
      queryO : ∀ {query} → QueryReturnType query → modeType outMode outChannel
      -- Constrains the possible outcomes for a given query, initial state,
      -- response and resulting state
      queryResponse : ∀ query → State → QueryReturnType query → State → Type
      -- A response has to be sent when induced by queryResponse
      correctnessNothing :
        ∀ {query s response s'}
        → s -⟦ app inWire (queryI query) / nothing ⟧ᵐ⇀ s'
        → queryResponse query s response s'
        → ⊥
      -- And it has to be the right response
      correctnessJust :
        ∀ {query s response s'}
        → s -⟦ app inWire (queryI query) / just (app outWire (queryO response)) ⟧ᵐ⇀ s'
        → queryResponse query s response s'
          
  record IsConstrainedPure : Type₂ where
    field
      isConstrained : IsConstrained

    open IsConstrained isConstrained

    field
      isPure :
        ∀ {query s response s'} → queryResponse query s response s' → s ≡ s'

  record IsConstrainedDet : Type₂ where
    field
      isConstrained : IsConstrained

    open IsConstrained isConstrained
    open Machine m

    field 
      isDet :
        ∀ {query s} → ∃ {A = QueryReturnType query × State}
          λ where
            (response , s') →
              (queryResponse query s response s' ×
              (∀ response' s''
               → queryResponse query s response' s''
               → response ≡ response' × s' ≡ s''))

    queryCompute : ∀ query s → (QueryReturnType query × State)
    queryCompute query s = proj₁ (isDet {query} {s})
