{-# OPTIONS --safe #-}

open import Leios.Prelude
open import CategoricalCrypto

-- The interface between a Leios node and the voting functionality.  A node
-- casts votes and, when producing a ranking block, queries for a certificate
-- for the endorser block the chain tip announces.  A cast is not answered; a
-- query is answered synchronously from the vote log, with `CERT (just c)` if
-- the votes certify the block and `CERT nothing` otherwise.  The module is
-- parameterized so that the node (via `Leios.Protocol.Types`) and both voting
-- functionalities (`Leios.Voting.Certifier`, `Leios.Voting.Voter`) refer to
-- the same channel.
module Leios.Voting.Channel (Vote EBRef EBCert : Type) where

data VotingT : Mode → Type where
  CAST  : Vote → VotingT Out
  QUERY : EBRef → VotingT Out
  CERT  : Maybe EBCert → VotingT In

VotingC : Channel
VotingC = simpleChannel VotingT
