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

module MAlonzo.Code.Leios.Blocks where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.Hashable
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Leios.FFD
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Leios.Blocks.IsBlock
d_IsBlock_40 a0 a1 = ()
data T_IsBlock_40
  = C_IsBlock'46'constructor_41 (AgdaAny -> Integer)
                                (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Leios.Blocks.IsBlock.slotNumber
d_slotNumber_50 :: T_IsBlock_40 -> AgdaAny -> Integer
d_slotNumber_50 v0
  = case coe v0 of
      C_IsBlock'46'constructor_41 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IsBlock.producerID
d_producerID_52 :: T_IsBlock_40 -> AgdaAny -> AgdaAny
d_producerID_52 v0
  = case coe v0 of
      C_IsBlock'46'constructor_41 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IsBlock.lotteryPf
d_lotteryPf_54 :: T_IsBlock_40 -> AgdaAny -> AgdaAny
d_lotteryPf_54 v0
  = case coe v0 of
      C_IsBlock'46'constructor_41 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IsBlock._∈ᴮ_
d__'8712''7470'__56 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  () -> T_IsBlock_40 -> AgdaAny -> [Integer] -> ()
d__'8712''7470'__56 = erased
-- Leios.Blocks._._∈ᴮ_
d__'8712''7470'__64 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  () -> T_IsBlock_40 -> AgdaAny -> [Integer] -> ()
d__'8712''7470'__64 = erased
-- Leios.Blocks._.lotteryPf
d_lotteryPf_66 :: T_IsBlock_40 -> AgdaAny -> AgdaAny
d_lotteryPf_66 v0 = coe d_lotteryPf_54 (coe v0)
-- Leios.Blocks._.producerID
d_producerID_68 :: T_IsBlock_40 -> AgdaAny -> AgdaAny
d_producerID_68 v0 = coe d_producerID_52 (coe v0)
-- Leios.Blocks._.slotNumber
d_slotNumber_70 :: T_IsBlock_40 -> AgdaAny -> Integer
d_slotNumber_70 v0 = coe d_slotNumber_50 (coe v0)
-- Leios.Blocks.OSig
d_OSig_72 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> Bool -> ()
d_OSig_72 = erased
-- Leios.Blocks.IBRef
d_IBRef_74 :: MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_IBRef_74 = erased
-- Leios.Blocks.EBRef
d_EBRef_76 :: MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_EBRef_76 = erased
-- Leios.Blocks.IBHeaderOSig
d_IBHeaderOSig_80 a0 a1 = ()
data T_IBHeaderOSig_80
  = C_IBHeaderOSig'46'constructor_591 Integer AgdaAny AgdaAny AgdaAny
                                      AgdaAny
-- Leios.Blocks.IBHeaderOSig.slotNumber
d_slotNumber_94 :: T_IBHeaderOSig_80 -> Integer
d_slotNumber_94 v0
  = case coe v0 of
      C_IBHeaderOSig'46'constructor_591 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IBHeaderOSig.producerID
d_producerID_96 :: T_IBHeaderOSig_80 -> AgdaAny
d_producerID_96 v0
  = case coe v0 of
      C_IBHeaderOSig'46'constructor_591 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IBHeaderOSig.lotteryPf
d_lotteryPf_98 :: T_IBHeaderOSig_80 -> AgdaAny
d_lotteryPf_98 v0
  = case coe v0 of
      C_IBHeaderOSig'46'constructor_591 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IBHeaderOSig.bodyHash
d_bodyHash_100 :: T_IBHeaderOSig_80 -> AgdaAny
d_bodyHash_100 v0
  = case coe v0 of
      C_IBHeaderOSig'46'constructor_591 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IBHeaderOSig.signature
d_signature_102 :: T_IBHeaderOSig_80 -> AgdaAny
d_signature_102 v0
  = case coe v0 of
      C_IBHeaderOSig'46'constructor_591 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.IBHeader
d_IBHeader_104 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_IBHeader_104 = erased
-- Leios.Blocks.PreIBHeader
d_PreIBHeader_106 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_PreIBHeader_106 = erased
-- Leios.Blocks.IBBody
d_IBBody_108 a0 = ()
newtype T_IBBody_108 = C_IBBody'46'constructor_795 [AgdaAny]
-- Leios.Blocks.IBBody.txs
d_txs_112 :: T_IBBody_108 -> [AgdaAny]
d_txs_112 v0
  = case coe v0 of
      C_IBBody'46'constructor_795 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.InputBlock
d_InputBlock_114 a0 = ()
data T_InputBlock_114
  = C_InputBlock'46'constructor_823 T_IBHeaderOSig_80 T_IBBody_108
-- Leios.Blocks.InputBlock.header
d_header_120 :: T_InputBlock_114 -> T_IBHeaderOSig_80
d_header_120 v0
  = case coe v0 of
      C_InputBlock'46'constructor_823 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.InputBlock.body
d_body_122 :: T_InputBlock_114 -> T_IBBody_108
d_body_122 v0
  = case coe v0 of
      C_InputBlock'46'constructor_823 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.InputBlock._.bodyHash
d_bodyHash_126 :: T_InputBlock_114 -> AgdaAny
d_bodyHash_126 v0 = coe d_bodyHash_100 (coe d_header_120 (coe v0))
-- Leios.Blocks.InputBlock._.lotteryPf
d_lotteryPf_128 :: T_InputBlock_114 -> AgdaAny
d_lotteryPf_128 v0 = coe d_lotteryPf_98 (coe d_header_120 (coe v0))
-- Leios.Blocks.InputBlock._.producerID
d_producerID_130 :: T_InputBlock_114 -> AgdaAny
d_producerID_130 v0
  = coe d_producerID_96 (coe d_header_120 (coe v0))
-- Leios.Blocks.InputBlock._.signature
d_signature_132 :: T_InputBlock_114 -> AgdaAny
d_signature_132 v0
  = coe d_signature_102 (coe d_header_120 (coe v0))
-- Leios.Blocks.InputBlock._.slotNumber
d_slotNumber_134 :: T_InputBlock_114 -> Integer
d_slotNumber_134 v0
  = coe d_slotNumber_94 (coe d_header_120 (coe v0))
-- Leios.Blocks.IsBlock-IBHeaderOSig
d_IsBlock'45'IBHeaderOSig_138 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  Bool -> T_IsBlock_40
d_IsBlock'45'IBHeaderOSig_138 ~v0 ~v1
  = du_IsBlock'45'IBHeaderOSig_138
du_IsBlock'45'IBHeaderOSig_138 :: T_IsBlock_40
du_IsBlock'45'IBHeaderOSig_138
  = coe
      C_IsBlock'46'constructor_41
      (coe (\ v0 -> d_slotNumber_94 (coe v0)))
      (coe (\ v0 -> d_producerID_96 (coe v0)))
      (coe (\ v0 -> d_lotteryPf_98 (coe v0)))
-- Leios.Blocks.Hashable-IBBody
d_Hashable'45'IBBody_140 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'IBBody_140 v0
  = coe
      MAlonzo.Code.Class.Hashable.C_Hashable'46'constructor_9
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Class.Hashable.d_hash_16
              (MAlonzo.Code.Leios.Abstract.d_Hashable'45'Txs_60 (coe v0))
              (d_txs_112 (coe v1))))
-- Leios.Blocks.IsBlock-InputBlock
d_IsBlock'45'InputBlock_144 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> T_IsBlock_40
d_IsBlock'45'InputBlock_144 ~v0 = du_IsBlock'45'InputBlock_144
du_IsBlock'45'InputBlock_144 :: T_IsBlock_40
du_IsBlock'45'InputBlock_144
  = coe
      C_IsBlock'46'constructor_41
      (coe (\ v0 -> d_slotNumber_94 (coe d_header_120 (coe v0))))
      (coe (\ v0 -> d_producerID_96 (coe d_header_120 (coe v0))))
      (coe (\ v0 -> d_lotteryPf_98 (coe d_header_120 (coe v0))))
-- Leios.Blocks.mkIBHeader
d_mkIBHeader_146 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> T_IBHeaderOSig_80
d_mkIBHeader_146 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_IBHeaderOSig'46'constructor_591 (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Class.Hashable.d_hash_16
         (MAlonzo.Code.Leios.Abstract.d_Hashable'45'Txs_60 (coe v0)) v6)
      (coe
         MAlonzo.Code.Leios.Abstract.d_sign_58 v0 v5
         (coe
            MAlonzo.Code.Class.Hashable.d_hash_16 v1
            (coe du_h_162 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6))))
-- Leios.Blocks._.h
d_h_162 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> T_IBHeaderOSig_80
d_h_162 v0 ~v1 v2 v3 v4 ~v5 v6 = du_h_162 v0 v2 v3 v4 v6
du_h_162 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  Integer -> AgdaAny -> AgdaAny -> [AgdaAny] -> T_IBHeaderOSig_80
du_h_162 v0 v1 v2 v3 v4
  = coe
      C_IBHeaderOSig'46'constructor_591 (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Class.Hashable.d_hash_16
         (MAlonzo.Code.Leios.Abstract.d_Hashable'45'Txs_60 (coe v0)) v4)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Leios.Blocks._._.bodyHash
d_bodyHash_168 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> AgdaAny
d_bodyHash_168 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_bodyHash_168 v0 v6
du_bodyHash_168 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  [AgdaAny] -> AgdaAny
du_bodyHash_168 v0 v1
  = coe
      MAlonzo.Code.Class.Hashable.d_hash_16
      (MAlonzo.Code.Leios.Abstract.d_Hashable'45'Txs_60 (coe v0)) v1
-- Leios.Blocks._._.lotteryPf
d_lotteryPf_170 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> AgdaAny
d_lotteryPf_170 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_lotteryPf_170 v4
du_lotteryPf_170 :: AgdaAny -> AgdaAny
du_lotteryPf_170 v0 = coe v0
-- Leios.Blocks._._.producerID
d_producerID_172 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> AgdaAny
d_producerID_172 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_producerID_172 v3
du_producerID_172 :: AgdaAny -> AgdaAny
du_producerID_172 v0 = coe v0
-- Leios.Blocks._._.signature
d_signature_174 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_signature_174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_signature_174
du_signature_174 :: MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_signature_174 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Leios.Blocks._._.slotNumber
d_slotNumber_176 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> Integer
d_slotNumber_176 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 = du_slotNumber_176 v2
du_slotNumber_176 :: Integer -> Integer
du_slotNumber_176 v0 = coe v0
-- Leios.Blocks.getIBRef
d_getIBRef_178 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  T_InputBlock_114 -> AgdaAny
d_getIBRef_178 ~v0 v1 v2 = du_getIBRef_178 v1 v2
du_getIBRef_178 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  T_InputBlock_114 -> AgdaAny
du_getIBRef_178 v0 v1
  = coe
      MAlonzo.Code.Class.Hashable.d_hash_16 v0 (d_header_120 (coe v1))
-- Leios.Blocks.ibHeaderValid
d_ibHeaderValid_182 a0 a1 = ()
data T_ibHeaderValid_182 = C_ibHeaderValid'46'constructor_2323
-- Leios.Blocks.ibBodyValid
d_ibBodyValid_188 a0 a1 = ()
data T_ibBodyValid_188 = C_ibBodyValid'46'constructor_2343
-- Leios.Blocks.ibHeaderValid?
d_ibHeaderValid'63'_194 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IBHeaderOSig_80 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibHeaderValid'63'_194 ~v0 ~v1 = du_ibHeaderValid'63'_194
du_ibHeaderValid'63'_194 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ibHeaderValid'63'_194
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Leios.Blocks.ibBodyValid?
d_ibBodyValid'63'_198 ::
  T_IBBody_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibBodyValid'63'_198 ~v0 = du_ibBodyValid'63'_198
du_ibBodyValid'63'_198 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ibBodyValid'63'_198
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Leios.Blocks.ibValid
d_ibValid_200 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_InputBlock_114 -> ()
d_ibValid_200 = erased
-- Leios.Blocks.ibValid?
d_ibValid'63'_208 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_InputBlock_114 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibValid'63'_208 ~v0 v1 = du_ibValid'63'_208 v1
du_ibValid'63'_208 ::
  T_InputBlock_114 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ibValid'63'_208 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
         (coe du_ibHeaderValid'63'_194)
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
            (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
            (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)))
-- Leios.Blocks.EndorserBlockOSig
d_EndorserBlockOSig_216 a0 a1 = ()
data T_EndorserBlockOSig_216
  = C_EndorserBlockOSig'46'constructor_3013 Integer AgdaAny AgdaAny
                                            [AgdaAny] [AgdaAny] AgdaAny
-- Leios.Blocks.EndorserBlockOSig.slotNumber
d_slotNumber_232 :: T_EndorserBlockOSig_216 -> Integer
d_slotNumber_232 v0
  = case coe v0 of
      C_EndorserBlockOSig'46'constructor_3013 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.EndorserBlockOSig.producerID
d_producerID_234 :: T_EndorserBlockOSig_216 -> AgdaAny
d_producerID_234 v0
  = case coe v0 of
      C_EndorserBlockOSig'46'constructor_3013 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.EndorserBlockOSig.lotteryPf
d_lotteryPf_236 :: T_EndorserBlockOSig_216 -> AgdaAny
d_lotteryPf_236 v0
  = case coe v0 of
      C_EndorserBlockOSig'46'constructor_3013 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.EndorserBlockOSig.ibRefs
d_ibRefs_238 :: T_EndorserBlockOSig_216 -> [AgdaAny]
d_ibRefs_238 v0
  = case coe v0 of
      C_EndorserBlockOSig'46'constructor_3013 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.EndorserBlockOSig.ebRefs
d_ebRefs_240 :: T_EndorserBlockOSig_216 -> [AgdaAny]
d_ebRefs_240 v0
  = case coe v0 of
      C_EndorserBlockOSig'46'constructor_3013 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.EndorserBlockOSig.signature
d_signature_242 :: T_EndorserBlockOSig_216 -> AgdaAny
d_signature_242 v0
  = case coe v0 of
      C_EndorserBlockOSig'46'constructor_3013 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.EndorserBlock
d_EndorserBlock_244 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_EndorserBlock_244 = erased
-- Leios.Blocks.PreEndorserBlock
d_PreEndorserBlock_246 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_PreEndorserBlock_246 = erased
-- Leios.Blocks.Hashable-EndorserBlock
d_Hashable'45'EndorserBlock_248 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'EndorserBlock_248 ~v0 v1
  = du_Hashable'45'EndorserBlock_248 v1
du_Hashable'45'EndorserBlock_248 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8
du_Hashable'45'EndorserBlock_248 v0
  = coe
      MAlonzo.Code.Class.Hashable.C_Hashable'46'constructor_9
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Class.Hashable.d_hash_16 v0
              (coe
                 C_EndorserBlockOSig'46'constructor_3013
                 (coe d_slotNumber_232 (coe v1)) (coe d_producerID_234 (coe v1))
                 (coe d_lotteryPf_236 (coe v1)) (coe d_ibRefs_238 (coe v1))
                 (coe d_ebRefs_240 (coe v1))
                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
-- Leios.Blocks._.ebRefs
d_ebRefs_256 :: T_EndorserBlockOSig_216 -> [AgdaAny]
d_ebRefs_256 v0 = coe d_ebRefs_240 (coe v0)
-- Leios.Blocks._.ibRefs
d_ibRefs_258 :: T_EndorserBlockOSig_216 -> [AgdaAny]
d_ibRefs_258 v0 = coe d_ibRefs_238 (coe v0)
-- Leios.Blocks._.lotteryPf
d_lotteryPf_260 :: T_EndorserBlockOSig_216 -> AgdaAny
d_lotteryPf_260 v0 = coe d_lotteryPf_236 (coe v0)
-- Leios.Blocks._.producerID
d_producerID_262 :: T_EndorserBlockOSig_216 -> AgdaAny
d_producerID_262 v0 = coe d_producerID_234 (coe v0)
-- Leios.Blocks._.slotNumber
d_slotNumber_264 :: T_EndorserBlockOSig_216 -> Integer
d_slotNumber_264 v0 = coe d_slotNumber_232 (coe v0)
-- Leios.Blocks.IsBlock-EndorserBlockOSig
d_IsBlock'45'EndorserBlockOSig_268 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  Bool -> T_IsBlock_40
d_IsBlock'45'EndorserBlockOSig_268 ~v0 ~v1
  = du_IsBlock'45'EndorserBlockOSig_268
du_IsBlock'45'EndorserBlockOSig_268 :: T_IsBlock_40
du_IsBlock'45'EndorserBlockOSig_268
  = coe
      C_IsBlock'46'constructor_41
      (coe (\ v0 -> d_slotNumber_232 (coe v0)))
      (coe (\ v0 -> d_producerID_234 (coe v0)))
      (coe (\ v0 -> d_lotteryPf_236 (coe v0)))
-- Leios.Blocks.mkEB
d_mkEB_272 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> [AgdaAny] -> [AgdaAny] -> T_EndorserBlockOSig_216
d_mkEB_272 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_EndorserBlockOSig'46'constructor_3013 (coe v2) (coe v3) (coe v4)
      (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Leios.Abstract.d_sign_58 v0 v5
         (coe
            MAlonzo.Code.Class.Hashable.d_hash_16 v1
            (coe du_b_290 (coe v2) (coe v3) (coe v4) (coe v6) (coe v7))))
-- Leios.Blocks._.b
d_b_290 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> [AgdaAny] -> [AgdaAny] -> T_EndorserBlockOSig_216
d_b_290 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 = du_b_290 v2 v3 v4 v6 v7
du_b_290 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> [AgdaAny] -> [AgdaAny] -> T_EndorserBlockOSig_216
du_b_290 v0 v1 v2 v3 v4
  = coe
      C_EndorserBlockOSig'46'constructor_3013 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Leios.Blocks._._.ebRefs
d_ebRefs_296 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_ebRefs_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_ebRefs_296 v7
du_ebRefs_296 :: [AgdaAny] -> [AgdaAny]
du_ebRefs_296 v0 = coe v0
-- Leios.Blocks._._.ibRefs
d_ibRefs_298 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_ibRefs_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 = du_ibRefs_298 v6
du_ibRefs_298 :: [AgdaAny] -> [AgdaAny]
du_ibRefs_298 v0 = coe v0
-- Leios.Blocks._._.lotteryPf
d_lotteryPf_300 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> [AgdaAny] -> AgdaAny
d_lotteryPf_300 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7
  = du_lotteryPf_300 v4
du_lotteryPf_300 :: AgdaAny -> AgdaAny
du_lotteryPf_300 v0 = coe v0
-- Leios.Blocks._._.producerID
d_producerID_302 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> [AgdaAny] -> AgdaAny
d_producerID_302 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_producerID_302 v3
du_producerID_302 :: AgdaAny -> AgdaAny
du_producerID_302 v0 = coe v0
-- Leios.Blocks._._.signature
d_signature_304 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_signature_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_signature_304
du_signature_304 :: MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_signature_304 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Leios.Blocks._._.slotNumber
d_slotNumber_306 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny -> AgdaAny -> AgdaAny -> [AgdaAny] -> [AgdaAny] -> Integer
d_slotNumber_306 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_slotNumber_306 v2
du_slotNumber_306 :: Integer -> Integer
du_slotNumber_306 v0 = coe v0
-- Leios.Blocks.getEBRef
d_getEBRef_308 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  T_EndorserBlockOSig_216 -> AgdaAny
d_getEBRef_308 ~v0 v1 v2 = du_getEBRef_308 v1 v2
du_getEBRef_308 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  T_EndorserBlockOSig_216 -> AgdaAny
du_getEBRef_308 v0 v1
  = coe
      MAlonzo.Code.Class.Hashable.d_hash_16 v0
      (coe
         C_EndorserBlockOSig'46'constructor_3013
         (coe d_slotNumber_232 (coe v1)) (coe d_producerID_234 (coe v1))
         (coe d_lotteryPf_236 (coe v1)) (coe d_ibRefs_238 (coe v1))
         (coe d_ebRefs_240 (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Leios.Blocks.ebValid
d_ebValid_312 a0 a1 = ()
data T_ebValid_312 = C_ebValid'46'constructor_4575
-- Leios.Blocks.ebValid?
d_ebValid'63'_318 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ebValid'63'_318 ~v0 ~v1 = du_ebValid'63'_318
du_ebValid'63'_318 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ebValid'63'_318
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Leios.Blocks.vsValid
d_vsValid_322 a0 a1 = ()
data T_vsValid_322 = C_vsValid'46'constructor_4673
-- Leios.Blocks.vsValid?
d_vsValid'63'_328 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_vsValid'63'_328 ~v0 ~v1 = du_vsValid'63'_328
du_vsValid'63'_328 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_vsValid'63'_328
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Leios.Blocks.GenFFD.Header
d_Header_334 a0 a1 = ()
data T_Header_334
  = C_ibHeader_336 T_IBHeaderOSig_80 |
    C_ebHeader_338 T_EndorserBlockOSig_216 | C_vHeader_340 [AgdaAny]
-- Leios.Blocks.GenFFD.Body
d_Body_342 a0 a1 = ()
newtype T_Body_342 = C_ibBody_344 T_IBBody_108
-- Leios.Blocks.GenFFD.ID
d_ID_346 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> T_IsBlock_40 -> ()
d_ID_346 = erased
-- Leios.Blocks.GenFFD.matchIB
d_matchIB_348 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> ()
d_matchIB_348 = erased
-- Leios.Blocks.GenFFD._._.bodyHash
d_bodyHash_360 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_bodyHash_360 ~v0 ~v1 v2 ~v3 = du_bodyHash_360 v2
du_bodyHash_360 :: T_IBHeaderOSig_80 -> AgdaAny
du_bodyHash_360 v0 = coe d_bodyHash_100 (coe v0)
-- Leios.Blocks.GenFFD._._.lotteryPf
d_lotteryPf_362 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_lotteryPf_362 ~v0 ~v1 v2 ~v3 = du_lotteryPf_362 v2
du_lotteryPf_362 :: T_IBHeaderOSig_80 -> AgdaAny
du_lotteryPf_362 v0 = coe d_lotteryPf_98 (coe v0)
-- Leios.Blocks.GenFFD._._.producerID
d_producerID_364 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_producerID_364 ~v0 ~v1 v2 ~v3 = du_producerID_364 v2
du_producerID_364 :: T_IBHeaderOSig_80 -> AgdaAny
du_producerID_364 v0 = coe d_producerID_96 (coe v0)
-- Leios.Blocks.GenFFD._._.signature
d_signature_366 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_signature_366 ~v0 ~v1 v2 ~v3 = du_signature_366 v2
du_signature_366 :: T_IBHeaderOSig_80 -> AgdaAny
du_signature_366 v0 = coe d_signature_102 (coe v0)
-- Leios.Blocks.GenFFD._._.slotNumber
d_slotNumber_368 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> Integer
d_slotNumber_368 ~v0 ~v1 v2 ~v3 = du_slotNumber_368 v2
du_slotNumber_368 :: T_IBHeaderOSig_80 -> Integer
du_slotNumber_368 v0 = coe d_slotNumber_94 (coe v0)
-- Leios.Blocks.GenFFD._._.txs
d_txs_372 :: T_IBBody_108 -> [AgdaAny]
d_txs_372 v0 = coe d_txs_112 (coe v0)
-- Leios.Blocks.GenFFD.matchIB?
d_matchIB'63'_378 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 ->
  T_IBHeaderOSig_80 ->
  T_IBBody_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_matchIB'63'_378 v0 ~v1 v2 v3 = du_matchIB'63'_378 v0 v2 v3
du_matchIB'63'_378 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IBHeaderOSig_80 ->
  T_IBBody_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_matchIB'63'_378 v0 v1 v2
  = coe
      MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
      (MAlonzo.Code.Leios.Abstract.d_DecEq'45'Hash_52 (coe v0))
      (d_bodyHash_100 (coe v1))
      (coe
         MAlonzo.Code.Class.Hashable.d_hash_16
         (MAlonzo.Code.Leios.Abstract.d_Hashable'45'Txs_60 (coe v0))
         (d_txs_112 (coe v2)))
-- Leios.Blocks.GenFFD._._.bodyHash
d_bodyHash_390 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_bodyHash_390 ~v0 ~v1 v2 ~v3 = du_bodyHash_390 v2
du_bodyHash_390 :: T_IBHeaderOSig_80 -> AgdaAny
du_bodyHash_390 v0 = coe d_bodyHash_100 (coe v0)
-- Leios.Blocks.GenFFD._._.lotteryPf
d_lotteryPf_392 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_lotteryPf_392 ~v0 ~v1 v2 ~v3 = du_lotteryPf_392 v2
du_lotteryPf_392 :: T_IBHeaderOSig_80 -> AgdaAny
du_lotteryPf_392 v0 = coe d_lotteryPf_98 (coe v0)
-- Leios.Blocks.GenFFD._._.producerID
d_producerID_394 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_producerID_394 ~v0 ~v1 v2 ~v3 = du_producerID_394 v2
du_producerID_394 :: T_IBHeaderOSig_80 -> AgdaAny
du_producerID_394 v0 = coe d_producerID_96 (coe v0)
-- Leios.Blocks.GenFFD._._.signature
d_signature_396 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> AgdaAny
d_signature_396 ~v0 ~v1 v2 ~v3 = du_signature_396 v2
du_signature_396 :: T_IBHeaderOSig_80 -> AgdaAny
du_signature_396 v0 = coe d_signature_102 (coe v0)
-- Leios.Blocks.GenFFD._._.slotNumber
d_slotNumber_398 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_IBHeaderOSig_80 -> T_IBBody_108 -> Integer
d_slotNumber_398 ~v0 ~v1 v2 ~v3 = du_slotNumber_398 v2
du_slotNumber_398 :: T_IBHeaderOSig_80 -> Integer
du_slotNumber_398 v0 = coe d_slotNumber_94 (coe v0)
-- Leios.Blocks.GenFFD._._.txs
d_txs_402 :: T_IBBody_108 -> [AgdaAny]
d_txs_402 v0 = coe d_txs_112 (coe v0)
-- Leios.Blocks.GenFFD.match
d_match_404 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_Header_334 -> T_Body_342 -> ()
d_match_404 = erased
-- Leios.Blocks.GenFFD.headerValid
d_headerValid_410 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_Header_334 -> ()
d_headerValid_410 = erased
-- Leios.Blocks.GenFFD.headerValid?
d_headerValid'63'_420 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 ->
  T_Header_334 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_headerValid'63'_420 ~v0 ~v1 v2 = du_headerValid'63'_420 v2
du_headerValid'63'_420 ::
  T_Header_334 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_headerValid'63'_420 v0
  = case coe v0 of
      C_ibHeader_336 v1 -> coe du_ibHeaderValid'63'_194
      C_ebHeader_338 v1 -> coe du_ebValid'63'_318
      C_vHeader_340 v1 -> coe du_vsValid'63'_328
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.GenFFD.bodyValid
d_bodyValid_428 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> T_Body_342 -> ()
d_bodyValid_428 = erased
-- Leios.Blocks.GenFFD.bodyValid?
d_bodyValid'63'_434 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 ->
  T_Body_342 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_bodyValid'63'_434 ~v0 ~v1 v2 = du_bodyValid'63'_434 v2
du_bodyValid'63'_434 ::
  T_Body_342 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_bodyValid'63'_434 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
-- Leios.Blocks.GenFFD.isValid
d_isValid_438 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_isValid_438 = erased
-- Leios.Blocks.GenFFD.isValid?
d_isValid'63'_446 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isValid'63'_446 ~v0 ~v1 v2 = du_isValid'63'_446 v2
du_isValid'63'_446 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isValid'63'_446 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe du_headerValid'63'_420 (coe v1)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe du_bodyValid'63'_434 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.GenFFD.msgID
d_msgID_452 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 ->
  T_Header_334 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_msgID_452 ~v0 v1 v2 = du_msgID_452 v1 v2
du_msgID_452 ::
  T_IsBlock_40 ->
  T_Header_334 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_msgID_452 v0 v1
  = case coe v1 of
      C_ibHeader_336 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_slotNumber_94 (coe v2)) (coe d_producerID_96 (coe v2))
      C_ebHeader_338 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_slotNumber_232 (coe v2)) (coe d_producerID_234 (coe v2))
      C_vHeader_340 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_slotNumber_50 v0 v2) (coe d_producerID_52 v0 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Blocks.ffdAbstract
d_ffdAbstract_462 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  T_IsBlock_40 -> MAlonzo.Code.Leios.FFD.T_FFDAbstract_4
d_ffdAbstract_462 ~v0 v1 = du_ffdAbstract_462 v1
du_ffdAbstract_462 ::
  T_IsBlock_40 -> MAlonzo.Code.Leios.FFD.T_FFDAbstract_4
du_ffdAbstract_462 v0
  = coe
      MAlonzo.Code.Leios.FFD.C_FFDAbstract'46'constructor_35
      (coe du_msgID_452 (coe v0))
