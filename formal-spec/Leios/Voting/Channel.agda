{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)
open import CategoricalCrypto hiding (id; _∘_)

-- The interface channel between a Leios node and the voting functionality:
-- a node casts votes, and — when producing a ranking block — queries the
-- functionality for a certificate for the endorser block it wants to endorse.
-- The functionality answers a query synchronously from its vote log:
-- `CERT (just c)` if the votes certify the block, `CERT nothing` otherwise.
-- The module is parameterized so that the node (via `Leios.Protocol.Types`)
-- and the voting functionalities (`Leios.Voting.Certifier`,
-- `Leios.Voting.Voter`) refer to the same channel.
module Leios.Voting.Channel (Vote EBRef EBCert : Type) where

data VotingT : Mode → Type where
  CAST  : Vote → VotingT Out
  QUERY : EBRef → VotingT Out
  CERT  : Maybe EBCert → VotingT In

VotingC : Channel
VotingC = simpleChannel VotingT
