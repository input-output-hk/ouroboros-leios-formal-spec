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

module MAlonzo.Code.Leios.VRF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Class.Decidable.Core
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Leios.VRF.VRF
d_VRF_44 a0 a1 a2 a3 = ()
newtype T_VRF_44
  = C_VRF'46'constructor_163 (AgdaAny ->
                              AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Leios.VRF.VRF.isKeyPair
d_isKeyPair_58 :: T_VRF_44 -> AgdaAny -> AgdaAny -> ()
d_isKeyPair_58 = erased
-- Leios.VRF.VRF.eval
d_eval_60 ::
  T_VRF_44 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_60 v0
  = case coe v0 of
      C_VRF'46'constructor_163 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.VRF.VRF.verify
d_verify_62 ::
  T_VRF_44 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d_verify_62 = erased
-- Leios.VRF.LeiosVRF
d_LeiosVRF_64 a0 = ()
data T_LeiosVRF_64
  = C_LeiosVRF'46'constructor_489 T_VRF_44 (Integer -> Integer)
                                  (Integer -> Integer) (Integer -> Integer) (Integer -> Integer)
                                  (Integer -> Integer)
-- Leios.VRF._.eval
d_eval_72 ::
  T_VRF_44 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_72 v0 = coe d_eval_60 (coe v0)
-- Leios.VRF._.isKeyPair
d_isKeyPair_74 :: T_VRF_44 -> AgdaAny -> AgdaAny -> ()
d_isKeyPair_74 = erased
-- Leios.VRF._.verify
d_verify_76 ::
  T_VRF_44 -> AgdaAny -> Integer -> Integer -> AgdaAny -> ()
d_verify_76 = erased
-- Leios.VRF.LeiosVRF.PubKey
d_PubKey_88 :: T_LeiosVRF_64 -> ()
d_PubKey_88 = erased
-- Leios.VRF.LeiosVRF.vrf
d_vrf_90 :: T_LeiosVRF_64 -> T_VRF_44
d_vrf_90 v0
  = case coe v0 of
      C_LeiosVRF'46'constructor_489 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.VRF.LeiosVRF._.eval
d_eval_94 ::
  T_LeiosVRF_64 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_94 v0 = coe d_eval_60 (coe d_vrf_90 (coe v0))
-- Leios.VRF.LeiosVRF._.isKeyPair
d_isKeyPair_96 :: T_LeiosVRF_64 -> AgdaAny -> AgdaAny -> ()
d_isKeyPair_96 = erased
-- Leios.VRF.LeiosVRF._.verify
d_verify_98 ::
  T_LeiosVRF_64 -> AgdaAny -> Integer -> Integer -> AgdaAny -> ()
d_verify_98 = erased
-- Leios.VRF.LeiosVRF.genIBInput
d_genIBInput_100 :: T_LeiosVRF_64 -> Integer -> Integer
d_genIBInput_100 v0
  = case coe v0 of
      C_LeiosVRF'46'constructor_489 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.VRF.LeiosVRF.genEBInput
d_genEBInput_102 :: T_LeiosVRF_64 -> Integer -> Integer
d_genEBInput_102 v0
  = case coe v0 of
      C_LeiosVRF'46'constructor_489 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.VRF.LeiosVRF.genVInput
d_genVInput_104 :: T_LeiosVRF_64 -> Integer -> Integer
d_genVInput_104 v0
  = case coe v0 of
      C_LeiosVRF'46'constructor_489 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.VRF.LeiosVRF.genV1Input
d_genV1Input_106 :: T_LeiosVRF_64 -> Integer -> Integer
d_genV1Input_106 v0
  = case coe v0 of
      C_LeiosVRF'46'constructor_489 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.VRF.LeiosVRF.genV2Input
d_genV2Input_108 :: T_LeiosVRF_64 -> Integer -> Integer
d_genV2Input_108 v0
  = case coe v0 of
      C_LeiosVRF'46'constructor_489 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.VRF.LeiosVRF.canProduceIB
d_canProduceIB_110 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 -> Integer -> AgdaAny -> Integer -> AgdaAny -> ()
d_canProduceIB_110 = erased
-- Leios.VRF.LeiosVRF.Dec-canProduceIB
d_Dec'45'canProduceIB_134 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceIB_134 ~v0 v1 v2 v3 v4
  = du_Dec'45'canProduceIB_134 v1 v2 v3 v4
du_Dec'45'canProduceIB_134 ::
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_Dec'45'canProduceIB_134 v0 v1 v2 v3
  = let v4
          = coe
              d_eval_60 (d_vrf_90 (coe v0)) v2 (coe d_genIBInput_100 v0 v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Class.Decidable.Core.du_'191'_'191'_42
                        (coe
                           MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                              (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v3))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                     -> if coe v8
                          then case coe v9 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          else coe
                                 seq (coe v9) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Leios.VRF.LeiosVRF.canProduceIBPub
d_canProduceIBPub_168 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 ->
  Integer -> Integer -> AgdaAny -> AgdaAny -> Integer -> ()
d_canProduceIBPub_168 = erased
-- Leios.VRF.LeiosVRF.canProduceEB
d_canProduceEB_180 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 -> Integer -> AgdaAny -> Integer -> AgdaAny -> ()
d_canProduceEB_180 = erased
-- Leios.VRF.LeiosVRF.Dec-canProduceEB
d_Dec'45'canProduceEB_204 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceEB_204 ~v0 v1 v2 v3 v4
  = du_Dec'45'canProduceEB_204 v1 v2 v3 v4
du_Dec'45'canProduceEB_204 ::
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_Dec'45'canProduceEB_204 v0 v1 v2 v3
  = let v4
          = coe
              d_eval_60 (d_vrf_90 (coe v0)) v2 (coe d_genEBInput_102 v0 v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Class.Decidable.Core.du_'191'_'191'_42
                        (coe
                           MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                              (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v3))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                     -> if coe v8
                          then case coe v9 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          else coe
                                 seq (coe v9) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Leios.VRF.LeiosVRF.canProduceEBPub
d_canProduceEBPub_238 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 ->
  Integer -> Integer -> AgdaAny -> AgdaAny -> Integer -> ()
d_canProduceEBPub_238 = erased
-- Leios.VRF.LeiosVRF.canProduceV
d_canProduceV_250 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 -> Integer -> AgdaAny -> Integer -> ()
d_canProduceV_250 = erased
-- Leios.VRF.LeiosVRF.Dec-canProduceV
d_Dec'45'canProduceV_264 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV_264 ~v0 v1 v2 v3 v4
  = du_Dec'45'canProduceV_264 v1 v2 v3 v4
du_Dec'45'canProduceV_264 ::
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Dec'45'canProduceV_264 v0 v1 v2 v3
  = let v4
          = coe
              d_eval_60 (d_vrf_90 (coe v0)) v2 (coe d_genVInput_104 v0 v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe
                MAlonzo.Code.Class.Decidable.Core.du_'191'_'191'_42
                (coe
                   MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                      (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v3)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Leios.VRF.LeiosVRF.canProduceV1
d_canProduceV1_286 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 -> Integer -> AgdaAny -> Integer -> ()
d_canProduceV1_286 = erased
-- Leios.VRF.LeiosVRF.Dec-canProduceV1
d_Dec'45'canProduceV1_300 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV1_300 ~v0 v1 v2 v3 v4
  = du_Dec'45'canProduceV1_300 v1 v2 v3 v4
du_Dec'45'canProduceV1_300 ::
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Dec'45'canProduceV1_300 v0 v1 v2 v3
  = let v4
          = coe
              d_eval_60 (d_vrf_90 (coe v0)) v2 (coe d_genV1Input_106 v0 v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe
                MAlonzo.Code.Class.Decidable.Core.du_'191'_'191'_42
                (coe
                   MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                      (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v3)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Leios.VRF.LeiosVRF.canProduceV2
d_canProduceV2_322 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 -> Integer -> AgdaAny -> Integer -> ()
d_canProduceV2_322 = erased
-- Leios.VRF.LeiosVRF.Dec-canProduceV2
d_Dec'45'canProduceV2_336 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV2_336 ~v0 v1 v2 v3 v4
  = du_Dec'45'canProduceV2_336 v1 v2 v3 v4
du_Dec'45'canProduceV2_336 ::
  T_LeiosVRF_64 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Dec'45'canProduceV2_336 v0 v1 v2 v3
  = let v4
          = coe
              d_eval_60 (d_vrf_90 (coe v0)) v2 (coe d_genV2Input_108 v0 v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe
                MAlonzo.Code.Class.Decidable.Core.du_'191'_'191'_42
                (coe
                   MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                      (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v3)))
         _ -> MAlonzo.RTE.mazUnreachableError)
