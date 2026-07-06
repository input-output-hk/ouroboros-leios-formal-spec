```agda
{-# OPTIONS --safe #-}

open import Leios.Prelude

module Leios.Voting where

record VotingAbstract (Vote Subject : Type) : Type₁ where
  field VotingState     : Type
        initVotingState : VotingState
        addVote         : VotingState → Vote → VotingState
        isVoteCertified : VotingState → Subject → Type

        ⦃ isVoteCertified⁇ ⦄ : ∀ {vs x} → isVoteCertified vs x ⁇

        -- A certificate can only exist if some honest voter validated the block
        Voter        : Type
        HonestVoter  : Voter → Type
        ValidatedBy  : Voter → Subject → Type
        cert-correct : ∀ {vs x} →
                       isVoteCertified vs x → ∃[ p ] (HonestVoter p × ValidatedBy p x)
```
