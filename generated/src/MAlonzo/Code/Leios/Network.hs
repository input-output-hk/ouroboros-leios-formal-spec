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

module MAlonzo.Code.Leios.Network where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.CategoricalCrypto
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base

-- Leios.Network.Abstract
d_Abstract_4 = ()
newtype T_Abstract_4
  = C_Abstract'46'constructor_35 (AgdaAny -> AgdaAny)
-- Leios.Network.Abstract.Header
d_Header_16 :: T_Abstract_4 -> ()
d_Header_16 = erased
-- Leios.Network.Abstract.Body
d_Body_18 :: T_Abstract_4 -> ()
d_Body_18 = erased
-- Leios.Network.Abstract.ID
d_ID_20 :: T_Abstract_4 -> ()
d_ID_20 = erased
-- Leios.Network.Abstract.match
d_match_22 :: T_Abstract_4 -> AgdaAny -> AgdaAny -> ()
d_match_22 = erased
-- Leios.Network.Abstract.msgID
d_msgID_24 :: T_Abstract_4 -> AgdaAny -> AgdaAny
d_msgID_24 v0
  = case coe v0 of
      C_Abstract'46'constructor_35 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Network.Broadcast.C
d_C_32 :: () -> () -> MAlonzo.Code.CategoricalCrypto.T_Channel_2
d_C_32 = erased
-- Leios.Network.Broadcast.Functionality
d_Functionality_34
  = error
      "MAlonzo Runtime Error: postulate evaluated: Leios.Network.Broadcast.Functionality"
-- Leios.Network.Broadcast.Single
d_Single_36 ::
  () -> () -> MAlonzo.Code.CategoricalCrypto.T_Channel_2
d_Single_36 = erased
-- Leios.Network.Broadcast.SingleFunctionality
d_SingleFunctionality_38
  = error
      "MAlonzo Runtime Error: postulate evaluated: Leios.Network.Broadcast.SingleFunctionality"
-- Leios.Network.HeaderDiffusion._.Body
d_Body_50 :: T_Abstract_4 -> () -> AgdaAny -> ()
d_Body_50 = erased
-- Leios.Network.HeaderDiffusion._.Header
d_Header_52 :: T_Abstract_4 -> () -> AgdaAny -> ()
d_Header_52 = erased
-- Leios.Network.HeaderDiffusion._.ID
d_ID_54 :: T_Abstract_4 -> () -> AgdaAny -> ()
d_ID_54 = erased
-- Leios.Network.HeaderDiffusion._.match
d_match_56 ::
  T_Abstract_4 -> () -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d_match_56 = erased
-- Leios.Network.HeaderDiffusion._.msgID
d_msgID_58 :: T_Abstract_4 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_msgID_58 v0 ~v1 ~v2 = du_msgID_58 v0
du_msgID_58 :: T_Abstract_4 -> AgdaAny -> AgdaAny
du_msgID_58 v0 = coe d_msgID_24 (coe v0)
-- Leios.Network.HeaderDiffusion.B.C
d_C_62 ::
  T_Abstract_4 ->
  () -> AgdaAny -> MAlonzo.Code.CategoricalCrypto.T_Channel_2
d_C_62 = erased
-- Leios.Network.HeaderDiffusion.B.Functionality
d_Functionality_64 ::
  T_Abstract_4 ->
  () -> AgdaAny -> MAlonzo.Code.CategoricalCrypto.T_Machine_96
d_Functionality_64 = erased
-- Leios.Network.HeaderDiffusion.B.Single
d_Single_66 ::
  T_Abstract_4 ->
  () -> AgdaAny -> MAlonzo.Code.CategoricalCrypto.T_Channel_2
d_Single_66 = erased
-- Leios.Network.HeaderDiffusion.B.SingleFunctionality
d_SingleFunctionality_68 ::
  T_Abstract_4 ->
  () -> AgdaAny -> MAlonzo.Code.CategoricalCrypto.T_Machine_96
d_SingleFunctionality_68 = erased
-- Leios.Network.HeaderDiffusion.Port
d_Port_70 a0 a1 a2 = ()
data T_Port_70 = C_Send_72 | C_Forward_74
-- Leios.Network.HeaderDiffusion.C
d_C_76 ::
  T_Abstract_4 ->
  () -> AgdaAny -> MAlonzo.Code.CategoricalCrypto.T_Channel_2
d_C_76 = erased
-- Leios.Network.HeaderDiffusion.Input
d_Input_78 a0 a1 a2 = ()
data T_Input_78
  = C_S_80 AgdaAny | C_F_82 AgdaAny | C_R_84 AgdaAny AgdaAny
-- Leios.Network.HeaderDiffusion.Output
d_Output_86 a0 a1 a2 = ()
newtype T_Output_86 = C_Verify_88 AgdaAny
-- Leios.Network.HeaderDiffusion.Step
d_Step_94 a0 a1 a2 a3 a4 a5 = ()
data T_Step_94
  = C_Init_96 | C_Receive1_100 | C_Receive2_102 |
    C_Receive2''_104 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
-- Leios.Network.HeaderDiffusion.step
d_step_106 ::
  T_Abstract_4 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_106 ~v0 ~v1 ~v2 v3 = du_step_106 v3
du_step_106 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_106 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_Forward_74))
                           (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    seq (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Network.HeaderDiffusion.Functionality
d_Functionality_114 ::
  T_Abstract_4 ->
  () -> AgdaAny -> MAlonzo.Code.CategoricalCrypto.T_Machine_96
d_Functionality_114 = erased
