{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)
open import CategoricalCrypto hiding (id; _∘_)

-- The interface channel between a Leios node and the voting functionality:
-- a node casts votes and receives certificates for endorser blocks with a
-- vote quorum. The module is parameterized so that the node (via
-- `Leios.Protocol.Types`) and the voting functionality (`Leios.Voting.Certifier`)
-- refer to the same channel.
module Leios.Voting.Channel (Vote EBCert : Type) where

data VotingT : Mode → Type where
  CAST : Vote → VotingT Out
  CERT : EBCert → VotingT In

VotingC : Channel
VotingC = simpleChannel VotingT
