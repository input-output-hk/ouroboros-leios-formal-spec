{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Leios.Voting where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Class.Decidable.Core

-- Leios.Voting.VotingAbstract
d_VotingAbstract_6 a0 = ()
data T_VotingAbstract_6
  = C_VotingAbstract'46'constructor_155 AgdaAny
                                        (AgdaAny ->
                                         AgdaAny -> MAlonzo.Code.Class.Decidable.Core.T__'8263'_10)
-- Leios.Voting.VotingAbstract.VotingState
d_VotingState_22 :: T_VotingAbstract_6 -> ()
d_VotingState_22 = erased
-- Leios.Voting.VotingAbstract.initVotingState
d_initVotingState_24 :: T_VotingAbstract_6 -> AgdaAny
d_initVotingState_24 v0
  = case coe v0 of
      C_VotingAbstract'46'constructor_155 v2 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Voting.VotingAbstract.isVoteCertified
d_isVoteCertified_26 ::
  T_VotingAbstract_6 -> AgdaAny -> AgdaAny -> ()
d_isVoteCertified_26 = erased
-- Leios.Voting.VotingAbstract.isVoteCertified⁇
d_isVoteCertified'8263'_32 ::
  T_VotingAbstract_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Decidable.Core.T__'8263'_10
d_isVoteCertified'8263'_32 v0
  = case coe v0 of
      C_VotingAbstract'46'constructor_155 v2 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
