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

module MAlonzo.Code.Leios.Abstract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.Hashable
import qualified MAlonzo.Code.Data.Nat.Base

-- Leios.Abstract.LeiosAbstract
d_LeiosAbstract_4 = ()
data T_LeiosAbstract_4
  = C_LeiosAbstract'46'constructor_383 MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
                                       MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
                                       (AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny)
                                       MAlonzo.Code.Class.Hashable.T_Hashable_8 Integer
                                       MAlonzo.Code.Data.Nat.Base.T_NonZero_112
-- Leios.Abstract.LeiosAbstract.Tx
d_Tx_36 :: T_LeiosAbstract_4 -> ()
d_Tx_36 = erased
-- Leios.Abstract.LeiosAbstract.PoolID
d_PoolID_38 :: T_LeiosAbstract_4 -> ()
d_PoolID_38 = erased
-- Leios.Abstract.LeiosAbstract.DecEq-PoolID
d_DecEq'45'PoolID_40 ::
  T_LeiosAbstract_4 -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'PoolID_40 v0
  = case coe v0 of
      C_LeiosAbstract'46'constructor_383 v3 v9 v11 v12 v13 v14 v15
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Abstract.LeiosAbstract.BodyHash
d_BodyHash_42 :: T_LeiosAbstract_4 -> ()
d_BodyHash_42 = erased
-- Leios.Abstract.LeiosAbstract.VrfPf
d_VrfPf_44 :: T_LeiosAbstract_4 -> ()
d_VrfPf_44 = erased
-- Leios.Abstract.LeiosAbstract.PrivKey
d_PrivKey_46 :: T_LeiosAbstract_4 -> ()
d_PrivKey_46 = erased
-- Leios.Abstract.LeiosAbstract.Sig
d_Sig_48 :: T_LeiosAbstract_4 -> ()
d_Sig_48 = erased
-- Leios.Abstract.LeiosAbstract.Hash
d_Hash_50 :: T_LeiosAbstract_4 -> ()
d_Hash_50 = erased
-- Leios.Abstract.LeiosAbstract.DecEq-Hash
d_DecEq'45'Hash_52 ::
  T_LeiosAbstract_4 -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Hash_52 v0
  = case coe v0 of
      C_LeiosAbstract'46'constructor_383 v3 v9 v11 v12 v13 v14 v15
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Abstract.LeiosAbstract.Vote
d_Vote_54 :: T_LeiosAbstract_4 -> ()
d_Vote_54 = erased
-- Leios.Abstract.LeiosAbstract.vote
d_vote_56 :: T_LeiosAbstract_4 -> AgdaAny -> AgdaAny -> AgdaAny
d_vote_56 v0
  = case coe v0 of
      C_LeiosAbstract'46'constructor_383 v3 v9 v11 v12 v13 v14 v15
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Abstract.LeiosAbstract.sign
d_sign_58 :: T_LeiosAbstract_4 -> AgdaAny -> AgdaAny -> AgdaAny
d_sign_58 v0
  = case coe v0 of
      C_LeiosAbstract'46'constructor_383 v3 v9 v11 v12 v13 v14 v15
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Abstract.LeiosAbstract.Hashable-Txs
d_Hashable'45'Txs_60 ::
  T_LeiosAbstract_4 -> MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'Txs_60 v0
  = case coe v0 of
      C_LeiosAbstract'46'constructor_383 v3 v9 v11 v12 v13 v14 v15
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Abstract.LeiosAbstract.L
d_L_62 :: T_LeiosAbstract_4 -> Integer
d_L_62 v0
  = case coe v0 of
      C_LeiosAbstract'46'constructor_383 v3 v9 v11 v12 v13 v14 v15
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Abstract.LeiosAbstract.NonZero-L
d_NonZero'45'L_64 ::
  T_LeiosAbstract_4 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_NonZero'45'L_64 v0
  = case coe v0 of
      C_LeiosAbstract'46'constructor_383 v3 v9 v11 v12 v13 v14 v15
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
