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

module MAlonzo.Code.Leios.SpecStructure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.Decidable.Core
import qualified MAlonzo.Code.Class.Hashable
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Leios.Base
import qualified MAlonzo.Code.Leios.Blocks
import qualified MAlonzo.Code.Leios.FFD
import qualified MAlonzo.Code.Leios.KeyRegistration
import qualified MAlonzo.Code.Leios.VRF
import qualified MAlonzo.Code.Leios.Voting
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Leios.SpecStructure.SpecStructure
d_SpecStructure_6 a0 = ()
data T_SpecStructure_6
  = C_SpecStructure'46'constructor_4605 MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4
                                        MAlonzo.Code.Leios.Blocks.T_IsBlock_40
                                        (Bool -> MAlonzo.Code.Class.Hashable.T_Hashable_8)
                                        MAlonzo.Code.Class.Hashable.T_Hashable_8 AgdaAny
                                        MAlonzo.Code.Leios.FFD.T_Functionality_38
                                        MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 AgdaAny AgdaAny AgdaAny
                                        AgdaAny AgdaAny AgdaAny
                                        MAlonzo.Code.Leios.Base.T_BaseAbstract_94
                                        MAlonzo.Code.Leios.Base.T_Functionality_128 AgdaAny
                                        MAlonzo.Code.Leios.Voting.T_VotingAbstract_6
-- Leios.SpecStructure._.EndorserBlock
d_EndorserBlock_50 ::
  Integer -> MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_EndorserBlock_50 = erased
-- Leios.SpecStructure._.IBHeaderOSig
d_IBHeaderOSig_62 a0 a1 a2 = ()
-- Leios.SpecStructure._.IsBlock
d_IsBlock_68 a0 a1 a2 = ()
-- Leios.SpecStructure._.PreEndorserBlock
d_PreEndorserBlock_78 ::
  Integer -> MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 -> ()
d_PreEndorserBlock_78 = erased
-- Leios.SpecStructure._.ffdAbstract
d_ffdAbstract_86 ::
  Integer ->
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.FFD.T_FFDAbstract_4
d_ffdAbstract_86 ~v0 ~v1 = du_ffdAbstract_86
du_ffdAbstract_86 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.FFD.T_FFDAbstract_4
du_ffdAbstract_86
  = coe MAlonzo.Code.Leios.Blocks.du_ffdAbstract_462
-- Leios.SpecStructure._.IBHeaderOSig.bodyHash
d_bodyHash_186 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_bodyHash_186 v0
  = coe MAlonzo.Code.Leios.Blocks.d_bodyHash_100 (coe v0)
-- Leios.SpecStructure._.IBHeaderOSig.lotteryPf
d_lotteryPf_188 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_lotteryPf_188 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_98 (coe v0)
-- Leios.SpecStructure._.IBHeaderOSig.producerID
d_producerID_190 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_producerID_190 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_96 (coe v0)
-- Leios.SpecStructure._.IBHeaderOSig.signature
d_signature_192 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_signature_192 v0
  = coe MAlonzo.Code.Leios.Blocks.d_signature_102 (coe v0)
-- Leios.SpecStructure._.IBHeaderOSig.slotNumber
d_slotNumber_194 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> Integer
d_slotNumber_194 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_94 (coe v0)
-- Leios.SpecStructure._.IsBlock.lotteryPf
d_lotteryPf_216 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> AgdaAny
d_lotteryPf_216 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_54 (coe v0)
-- Leios.SpecStructure._.IsBlock.producerID
d_producerID_218 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> AgdaAny
d_producerID_218 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_52 (coe v0)
-- Leios.SpecStructure._.IsBlock.slotNumber
d_slotNumber_220 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> Integer
d_slotNumber_220 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_50 (coe v0)
-- Leios.SpecStructure._.BaseAbstract
d_BaseAbstract_304 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  = ()
-- Leios.SpecStructure._.BaseAbstract.Cert
d_Cert_314 :: MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> ()
d_Cert_314 = erased
-- Leios.SpecStructure._.BaseAbstract.Functionality
d_Functionality_320 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Leios.SpecStructure._.BaseAbstract.V-chkCerts
d_V'45'chkCerts_332 ::
  MAlonzo.Code.Leios.Base.T_BaseAbstract_94 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_V'45'chkCerts_332 v0
  = coe MAlonzo.Code.Leios.Base.d_V'45'chkCerts_110 (coe v0)
-- Leios.SpecStructure._.BaseAbstract.VTy
d_VTy_334 :: MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> ()
d_VTy_334 = erased
-- Leios.SpecStructure._.BaseAbstract.initSlot
d_initSlot_336 ::
  MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> AgdaAny -> Integer
d_initSlot_336 v0
  = coe MAlonzo.Code.Leios.Base.d_initSlot_108 (coe v0)
-- Leios.SpecStructure._.BaseAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__340 ::
  MAlonzo.Code.Leios.Base.T_Functionality_128 ->
  AgdaAny ->
  MAlonzo.Code.Leios.Base.T_Input_112 ->
  MAlonzo.Code.Leios.Base.T_Output_120 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__340 = erased
-- Leios.SpecStructure._.BaseAbstract.Functionality.SUBMIT-total
d_SUBMIT'45'total_342 ::
  MAlonzo.Code.Leios.Base.T_Functionality_128 ->
  AgdaAny ->
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_SUBMIT'45'total_342 v0
  = coe MAlonzo.Code.Leios.Base.d_SUBMIT'45'total_152 (coe v0)
-- Leios.SpecStructure._.BaseAbstract.Functionality.State
d_State_344 :: MAlonzo.Code.Leios.Base.T_Functionality_128 -> ()
d_State_344 = erased
-- Leios.SpecStructure._.KeyRegistrationAbstract
d_KeyRegistrationAbstract_382 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
                              a12 a13 a14 a15 a16
  = ()
-- Leios.SpecStructure._.KeyRegistrationAbstract.Functionality
d_Functionality_386 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14 a15 a16 a17
  = ()
-- Leios.SpecStructure._.KeyRegistrationAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__398 ::
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96 ->
  AgdaAny ->
  MAlonzo.Code.Leios.KeyRegistration.T_Input_88 ->
  MAlonzo.Code.Leios.KeyRegistration.T_Output_92 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__398 = erased
-- Leios.SpecStructure._.KeyRegistrationAbstract.Functionality.State
d_State_400 ::
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96 -> ()
d_State_400 = erased
-- Leios.SpecStructure.SpecStructure.a
d_a_480 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4
d_a_480 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure._.BodyHash
d_BodyHash_484 :: T_SpecStructure_6 -> ()
d_BodyHash_484 = erased
-- Leios.SpecStructure.SpecStructure._.DecEq-Hash
d_DecEq'45'Hash_486 ::
  T_SpecStructure_6 -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Hash_486 v0
  = coe
      MAlonzo.Code.Leios.Abstract.d_DecEq'45'Hash_52
      (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.DecEq-PoolID
d_DecEq'45'PoolID_488 ::
  T_SpecStructure_6 -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'PoolID_488 v0
  = coe
      MAlonzo.Code.Leios.Abstract.d_DecEq'45'PoolID_40
      (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.Hash
d_Hash_490 :: T_SpecStructure_6 -> ()
d_Hash_490 = erased
-- Leios.SpecStructure.SpecStructure._.Hashable-Txs
d_Hashable'45'Txs_492 ::
  T_SpecStructure_6 -> MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'Txs_492 v0
  = coe
      MAlonzo.Code.Leios.Abstract.d_Hashable'45'Txs_60
      (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.L
d_L_494 :: T_SpecStructure_6 -> Integer
d_L_494 v0
  = coe MAlonzo.Code.Leios.Abstract.d_L_62 (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.NonZero-L
d_NonZero'45'L_496 ::
  T_SpecStructure_6 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_NonZero'45'L_496 v0
  = coe
      MAlonzo.Code.Leios.Abstract.d_NonZero'45'L_64
      (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.PoolID
d_PoolID_498 :: T_SpecStructure_6 -> ()
d_PoolID_498 = erased
-- Leios.SpecStructure.SpecStructure._.PrivKey
d_PrivKey_500 :: T_SpecStructure_6 -> ()
d_PrivKey_500 = erased
-- Leios.SpecStructure.SpecStructure._.Sig
d_Sig_502 :: T_SpecStructure_6 -> ()
d_Sig_502 = erased
-- Leios.SpecStructure.SpecStructure._.Tx
d_Tx_504 :: T_SpecStructure_6 -> ()
d_Tx_504 = erased
-- Leios.SpecStructure.SpecStructure._.Vote
d_Vote_506 :: T_SpecStructure_6 -> ()
d_Vote_506 = erased
-- Leios.SpecStructure.SpecStructure._.VrfPf
d_VrfPf_508 :: T_SpecStructure_6 -> ()
d_VrfPf_508 = erased
-- Leios.SpecStructure.SpecStructure._.sign
d_sign_510 :: T_SpecStructure_6 -> AgdaAny -> AgdaAny -> AgdaAny
d_sign_510 v0
  = coe MAlonzo.Code.Leios.Abstract.d_sign_58 (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.vote
d_vote_512 :: T_SpecStructure_6 -> AgdaAny -> AgdaAny -> AgdaAny
d_vote_512 v0
  = coe MAlonzo.Code.Leios.Abstract.d_vote_56 (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._._∈ᴮ_
d__'8712''7470'__516 ::
  T_SpecStructure_6 ->
  () ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> [Integer] -> ()
d__'8712''7470'__516 = erased
-- Leios.SpecStructure.SpecStructure._.EBRef
d_EBRef_518 :: T_SpecStructure_6 -> ()
d_EBRef_518 = erased
-- Leios.SpecStructure.SpecStructure._.EndorserBlock
d_EndorserBlock_520 :: T_SpecStructure_6 -> ()
d_EndorserBlock_520 = erased
-- Leios.SpecStructure.SpecStructure._.EndorserBlockOSig
d_EndorserBlockOSig_522 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.Hashable-EndorserBlock
d_Hashable'45'EndorserBlock_524 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'EndorserBlock_524 ~v0
  = du_Hashable'45'EndorserBlock_524
du_Hashable'45'EndorserBlock_524 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8
du_Hashable'45'EndorserBlock_524
  = coe MAlonzo.Code.Leios.Blocks.du_Hashable'45'EndorserBlock_248
-- Leios.SpecStructure.SpecStructure._.Hashable-IBBody
d_Hashable'45'IBBody_526 ::
  T_SpecStructure_6 -> MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'IBBody_526 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_Hashable'45'IBBody_140
      (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.IBBody
d_IBBody_528 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure._.IBHeader
d_IBHeader_530 :: T_SpecStructure_6 -> ()
d_IBHeader_530 = erased
-- Leios.SpecStructure.SpecStructure._.IBHeaderOSig
d_IBHeaderOSig_532 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.IBRef
d_IBRef_534 :: T_SpecStructure_6 -> ()
d_IBRef_534 = erased
-- Leios.SpecStructure.SpecStructure._.InputBlock
d_InputBlock_536 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure._.IsBlock
d_IsBlock_538 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.IsBlock-EndorserBlockOSig
d_IsBlock'45'EndorserBlockOSig_540 ::
  T_SpecStructure_6 -> Bool -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_IsBlock'45'EndorserBlockOSig_540 ~v0
  = du_IsBlock'45'EndorserBlockOSig_540
du_IsBlock'45'EndorserBlockOSig_540 ::
  Bool -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
du_IsBlock'45'EndorserBlockOSig_540 v0
  = coe MAlonzo.Code.Leios.Blocks.du_IsBlock'45'EndorserBlockOSig_268
-- Leios.SpecStructure.SpecStructure._.IsBlock-IBHeaderOSig
d_IsBlock'45'IBHeaderOSig_542 ::
  T_SpecStructure_6 -> Bool -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_IsBlock'45'IBHeaderOSig_542 ~v0 = du_IsBlock'45'IBHeaderOSig_542
du_IsBlock'45'IBHeaderOSig_542 ::
  Bool -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
du_IsBlock'45'IBHeaderOSig_542 v0
  = coe MAlonzo.Code.Leios.Blocks.du_IsBlock'45'IBHeaderOSig_138
-- Leios.SpecStructure.SpecStructure._.IsBlock-InputBlock
d_IsBlock'45'InputBlock_544 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_IsBlock'45'InputBlock_544 ~v0 = du_IsBlock'45'InputBlock_544
du_IsBlock'45'InputBlock_544 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40
du_IsBlock'45'InputBlock_544
  = coe MAlonzo.Code.Leios.Blocks.du_IsBlock'45'InputBlock_144
-- Leios.SpecStructure.SpecStructure._.OSig
d_OSig_546 :: T_SpecStructure_6 -> Bool -> ()
d_OSig_546 = erased
-- Leios.SpecStructure.SpecStructure._.PreEndorserBlock
d_PreEndorserBlock_548 :: T_SpecStructure_6 -> ()
d_PreEndorserBlock_548 = erased
-- Leios.SpecStructure.SpecStructure._.PreIBHeader
d_PreIBHeader_550 :: T_SpecStructure_6 -> ()
d_PreIBHeader_550 = erased
-- Leios.SpecStructure.SpecStructure._.ebValid
d_ebValid_552 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.ebValid?
d_ebValid'63'_554 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ebValid'63'_554 ~v0 = du_ebValid'63'_554
du_ebValid'63'_554 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ebValid'63'_554 v0
  = coe MAlonzo.Code.Leios.Blocks.du_ebValid'63'_318
-- Leios.SpecStructure.SpecStructure._.ffdAbstract
d_ffdAbstract_556 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.FFD.T_FFDAbstract_4
d_ffdAbstract_556 ~v0 = du_ffdAbstract_556
du_ffdAbstract_556 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.FFD.T_FFDAbstract_4
du_ffdAbstract_556
  = coe MAlonzo.Code.Leios.Blocks.du_ffdAbstract_462
-- Leios.SpecStructure.SpecStructure._.getEBRef
d_getEBRef_558 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_getEBRef_558 ~v0 = du_getEBRef_558
du_getEBRef_558 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
du_getEBRef_558 = coe MAlonzo.Code.Leios.Blocks.du_getEBRef_308
-- Leios.SpecStructure.SpecStructure._.getIBRef
d_getIBRef_560 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> AgdaAny
d_getIBRef_560 ~v0 = du_getIBRef_560
du_getIBRef_560 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> AgdaAny
du_getIBRef_560 = coe MAlonzo.Code.Leios.Blocks.du_getIBRef_178
-- Leios.SpecStructure.SpecStructure._.ibBodyValid
d_ibBodyValid_562 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.ibBodyValid?
d_ibBodyValid'63'_564 ::
  MAlonzo.Code.Leios.Blocks.T_IBBody_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibBodyValid'63'_564 ~v0 = du_ibBodyValid'63'_564
du_ibBodyValid'63'_564 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ibBodyValid'63'_564
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Leios.SpecStructure.SpecStructure._.ibHeaderValid
d_ibHeaderValid_566 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.ibHeaderValid?
d_ibHeaderValid'63'_568 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibHeaderValid'63'_568 ~v0 = du_ibHeaderValid'63'_568
du_ibHeaderValid'63'_568 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ibHeaderValid'63'_568 v0
  = coe MAlonzo.Code.Leios.Blocks.du_ibHeaderValid'63'_194
-- Leios.SpecStructure.SpecStructure._.ibValid
d_ibValid_570 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> ()
d_ibValid_570 = erased
-- Leios.SpecStructure.SpecStructure._.ibValid?
d_ibValid'63'_572 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibValid'63'_572 ~v0 = du_ibValid'63'_572
du_ibValid'63'_572 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ibValid'63'_572
  = coe MAlonzo.Code.Leios.Blocks.du_ibValid'63'_208
-- Leios.SpecStructure.SpecStructure._.lotteryPf
d_lotteryPf_574 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> AgdaAny
d_lotteryPf_574 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_54 (coe v0)
-- Leios.SpecStructure.SpecStructure._.mkEB
d_mkEB_576 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_mkEB_576 v0
  = coe MAlonzo.Code.Leios.Blocks.d_mkEB_272 (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.mkIBHeader
d_mkIBHeader_578 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80
d_mkIBHeader_578 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_mkIBHeader_146 (coe d_a_480 (coe v0))
-- Leios.SpecStructure.SpecStructure._.producerID
d_producerID_580 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> AgdaAny
d_producerID_580 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_52 (coe v0)
-- Leios.SpecStructure.SpecStructure._.slotNumber
d_slotNumber_582 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> Integer
d_slotNumber_582 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_50 (coe v0)
-- Leios.SpecStructure.SpecStructure._.vsValid
d_vsValid_584 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.vsValid?
d_vsValid'63'_586 ::
  T_SpecStructure_6 ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_vsValid'63'_586 ~v0 = du_vsValid'63'_586
du_vsValid'63'_586 ::
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_vsValid'63'_586 v0
  = coe MAlonzo.Code.Leios.Blocks.du_vsValid'63'_328
-- Leios.SpecStructure.SpecStructure._.EndorserBlockOSig.ebRefs
d_ebRefs_590 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_ebRefs_590 v0
  = coe MAlonzo.Code.Leios.Blocks.d_ebRefs_240 (coe v0)
-- Leios.SpecStructure.SpecStructure._.EndorserBlockOSig.ibRefs
d_ibRefs_592 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_ibRefs_592 v0
  = coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v0)
-- Leios.SpecStructure.SpecStructure._.EndorserBlockOSig.lotteryPf
d_lotteryPf_594 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_lotteryPf_594 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_236 (coe v0)
-- Leios.SpecStructure.SpecStructure._.EndorserBlockOSig.producerID
d_producerID_596 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_producerID_596 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v0)
-- Leios.SpecStructure.SpecStructure._.EndorserBlockOSig.signature
d_signature_598 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_signature_598 v0
  = coe MAlonzo.Code.Leios.Blocks.d_signature_242 (coe v0)
-- Leios.SpecStructure.SpecStructure._.EndorserBlockOSig.slotNumber
d_slotNumber_600 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> Integer
d_slotNumber_600 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v0)
-- Leios.SpecStructure.SpecStructure._.GenFFD.Body
d_Body_604 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.GenFFD.Header
d_Header_606 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.GenFFD.ID
d_ID_608 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> ()
d_ID_608 = erased
-- Leios.SpecStructure.SpecStructure._.GenFFD.bodyValid
d_bodyValid_610 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Body_342 -> ()
d_bodyValid_610 = erased
-- Leios.SpecStructure.SpecStructure._.GenFFD.bodyValid?
d_bodyValid'63'_612 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Body_342 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_bodyValid'63'_612 ~v0 = du_bodyValid'63'_612
du_bodyValid'63'_612 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Body_342 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_bodyValid'63'_612 v0 v1
  = coe MAlonzo.Code.Leios.Blocks.du_bodyValid'63'_434 v1
-- Leios.SpecStructure.SpecStructure._.GenFFD.headerValid
d_headerValid_616 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 -> ()
d_headerValid_616 = erased
-- Leios.SpecStructure.SpecStructure._.GenFFD.headerValid?
d_headerValid'63'_618 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_headerValid'63'_618 ~v0 = du_headerValid'63'_618
du_headerValid'63'_618 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_headerValid'63'_618 v0 v1
  = coe MAlonzo.Code.Leios.Blocks.du_headerValid'63'_420 v1
-- Leios.SpecStructure.SpecStructure._.GenFFD.isValid
d_isValid_624 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_isValid_624 = erased
-- Leios.SpecStructure.SpecStructure._.GenFFD.isValid?
d_isValid'63'_626 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isValid'63'_626 ~v0 = du_isValid'63'_626
du_isValid'63'_626 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isValid'63'_626 v0 v1
  = coe MAlonzo.Code.Leios.Blocks.du_isValid'63'_446 v1
-- Leios.SpecStructure.SpecStructure._.GenFFD.match
d_match_628 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Leios.Blocks.T_Body_342 -> ()
d_match_628 = erased
-- Leios.SpecStructure.SpecStructure._.GenFFD.matchIB
d_matchIB_630 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Leios.Blocks.T_IBBody_108 -> ()
d_matchIB_630 = erased
-- Leios.SpecStructure.SpecStructure._.GenFFD.matchIB?
d_matchIB'63'_632 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Leios.Blocks.T_IBBody_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_matchIB'63'_632 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Leios.Blocks.du_matchIB'63'_378 (coe d_a_480 (coe v0))
      v2 v3
-- Leios.SpecStructure.SpecStructure._.GenFFD.msgID
d_msgID_634 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_msgID_634 ~v0 = du_msgID_634
du_msgID_634 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_msgID_634 = coe MAlonzo.Code.Leios.Blocks.du_msgID_452
-- Leios.SpecStructure.SpecStructure._.IBBody.txs
d_txs_652 :: MAlonzo.Code.Leios.Blocks.T_IBBody_108 -> [AgdaAny]
d_txs_652 v0 = coe MAlonzo.Code.Leios.Blocks.d_txs_112 (coe v0)
-- Leios.SpecStructure.SpecStructure._.IBHeaderOSig.bodyHash
d_bodyHash_656 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_bodyHash_656 v0
  = coe MAlonzo.Code.Leios.Blocks.d_bodyHash_100 (coe v0)
-- Leios.SpecStructure.SpecStructure._.IBHeaderOSig.lotteryPf
d_lotteryPf_658 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_lotteryPf_658 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_98 (coe v0)
-- Leios.SpecStructure.SpecStructure._.IBHeaderOSig.producerID
d_producerID_660 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_producerID_660 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_96 (coe v0)
-- Leios.SpecStructure.SpecStructure._.IBHeaderOSig.signature
d_signature_662 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_signature_662 v0
  = coe MAlonzo.Code.Leios.Blocks.d_signature_102 (coe v0)
-- Leios.SpecStructure.SpecStructure._.IBHeaderOSig.slotNumber
d_slotNumber_664 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> Integer
d_slotNumber_664 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_94 (coe v0)
-- Leios.SpecStructure.SpecStructure._.InputBlock.body
d_body_668 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Leios.Blocks.T_IBBody_108
d_body_668 v0 = coe MAlonzo.Code.Leios.Blocks.d_body_122 (coe v0)
-- Leios.SpecStructure.SpecStructure._.InputBlock.bodyHash
d_bodyHash_670 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> AgdaAny
d_bodyHash_670 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_bodyHash_100
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.SpecStructure.SpecStructure._.InputBlock.header
d_header_672 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80
d_header_672 v0
  = coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0)
-- Leios.SpecStructure.SpecStructure._.InputBlock.lotteryPf
d_lotteryPf_674 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> AgdaAny
d_lotteryPf_674 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_lotteryPf_98
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.SpecStructure.SpecStructure._.InputBlock.producerID
d_producerID_676 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> AgdaAny
d_producerID_676 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_producerID_96
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.SpecStructure.SpecStructure._.InputBlock.signature
d_signature_678 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> AgdaAny
d_signature_678 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_signature_102
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.SpecStructure.SpecStructure._.InputBlock.slotNumber
d_slotNumber_680 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> Integer
d_slotNumber_680 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_slotNumber_94
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.SpecStructure.SpecStructure._.IsBlock._∈ᴮ_
d__'8712''7470'__684 ::
  T_SpecStructure_6 ->
  () ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> [Integer] -> ()
d__'8712''7470'__684 = erased
-- Leios.SpecStructure.SpecStructure._.IsBlock.lotteryPf
d_lotteryPf_686 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> AgdaAny
d_lotteryPf_686 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_54 (coe v0)
-- Leios.SpecStructure.SpecStructure._.IsBlock.producerID
d_producerID_688 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> AgdaAny
d_producerID_688 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_52 (coe v0)
-- Leios.SpecStructure.SpecStructure._.IsBlock.slotNumber
d_slotNumber_690 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> Integer
d_slotNumber_690 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_50 (coe v0)
-- Leios.SpecStructure.SpecStructure.IsBlock-Vote
d_IsBlock'45'Vote_700 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_IsBlock'45'Vote_700 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.Hashable-IBHeaderOSig
d_Hashable'45'IBHeaderOSig_704 ::
  T_SpecStructure_6 ->
  Bool -> MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'IBHeaderOSig_704 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.Hashable-PreEndorserBlock
d_Hashable'45'PreEndorserBlock_706 ::
  T_SpecStructure_6 -> MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'PreEndorserBlock_706 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.id
d_id_708 :: T_SpecStructure_6 -> AgdaAny
d_id_708 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.FFD'
d_FFD''_710 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.FFD.T_Functionality_38
d_FFD''_710 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.vrf'
d_vrf''_712 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.VRF.T_LeiosVRF_64
d_vrf''_712 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure._.Dec-canProduceEB
d_Dec'45'canProduceEB_716 ::
  T_SpecStructure_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceEB_716 v0
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceEB_204
      (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.Dec-canProduceIB
d_Dec'45'canProduceIB_718 ::
  T_SpecStructure_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceIB_718 v0
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceIB_134
      (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.Dec-canProduceV
d_Dec'45'canProduceV_720 ::
  T_SpecStructure_6 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV_720 v0
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV_264
      (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.Dec-canProduceV1
d_Dec'45'canProduceV1_722 ::
  T_SpecStructure_6 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV1_722 v0
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV1_300
      (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.Dec-canProduceV2
d_Dec'45'canProduceV2_724 ::
  T_SpecStructure_6 ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV2_724 v0
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV2_336
      (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.PubKey
d_PubKey_726 :: T_SpecStructure_6 -> ()
d_PubKey_726 = erased
-- Leios.SpecStructure.SpecStructure._.canProduceEB
d_canProduceEB_728 ::
  T_SpecStructure_6 -> Integer -> AgdaAny -> Integer -> AgdaAny -> ()
d_canProduceEB_728 = erased
-- Leios.SpecStructure.SpecStructure._.canProduceEBPub
d_canProduceEBPub_730 ::
  T_SpecStructure_6 ->
  Integer -> Integer -> AgdaAny -> AgdaAny -> Integer -> ()
d_canProduceEBPub_730 = erased
-- Leios.SpecStructure.SpecStructure._.canProduceIB
d_canProduceIB_732 ::
  T_SpecStructure_6 -> Integer -> AgdaAny -> Integer -> AgdaAny -> ()
d_canProduceIB_732 = erased
-- Leios.SpecStructure.SpecStructure._.canProduceIBPub
d_canProduceIBPub_734 ::
  T_SpecStructure_6 ->
  Integer -> Integer -> AgdaAny -> AgdaAny -> Integer -> ()
d_canProduceIBPub_734 = erased
-- Leios.SpecStructure.SpecStructure._.canProduceV
d_canProduceV_736 ::
  T_SpecStructure_6 -> Integer -> AgdaAny -> Integer -> ()
d_canProduceV_736 = erased
-- Leios.SpecStructure.SpecStructure._.canProduceV1
d_canProduceV1_738 ::
  T_SpecStructure_6 -> Integer -> AgdaAny -> Integer -> ()
d_canProduceV1_738 = erased
-- Leios.SpecStructure.SpecStructure._.canProduceV2
d_canProduceV2_740 ::
  T_SpecStructure_6 -> Integer -> AgdaAny -> Integer -> ()
d_canProduceV2_740 = erased
-- Leios.SpecStructure.SpecStructure._.eval
d_eval_742 ::
  T_SpecStructure_6 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_742 v0
  = coe
      MAlonzo.Code.Leios.VRF.d_eval_60
      (coe MAlonzo.Code.Leios.VRF.d_vrf_90 (coe d_vrf''_712 (coe v0)))
-- Leios.SpecStructure.SpecStructure._.genEBInput
d_genEBInput_744 :: T_SpecStructure_6 -> Integer -> Integer
d_genEBInput_744 v0
  = coe
      MAlonzo.Code.Leios.VRF.d_genEBInput_102 (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.genIBInput
d_genIBInput_746 :: T_SpecStructure_6 -> Integer -> Integer
d_genIBInput_746 v0
  = coe
      MAlonzo.Code.Leios.VRF.d_genIBInput_100 (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.genV1Input
d_genV1Input_748 :: T_SpecStructure_6 -> Integer -> Integer
d_genV1Input_748 v0
  = coe
      MAlonzo.Code.Leios.VRF.d_genV1Input_106 (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.genV2Input
d_genV2Input_750 :: T_SpecStructure_6 -> Integer -> Integer
d_genV2Input_750 v0
  = coe
      MAlonzo.Code.Leios.VRF.d_genV2Input_108 (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.genVInput
d_genVInput_752 :: T_SpecStructure_6 -> Integer -> Integer
d_genVInput_752 v0
  = coe
      MAlonzo.Code.Leios.VRF.d_genVInput_104 (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure._.isKeyPair
d_isKeyPair_754 :: T_SpecStructure_6 -> AgdaAny -> AgdaAny -> ()
d_isKeyPair_754 = erased
-- Leios.SpecStructure.SpecStructure._.verify
d_verify_756 ::
  T_SpecStructure_6 -> AgdaAny -> Integer -> Integer -> AgdaAny -> ()
d_verify_756 = erased
-- Leios.SpecStructure.SpecStructure._.vrf
d_vrf_758 :: T_SpecStructure_6 -> MAlonzo.Code.Leios.VRF.T_VRF_44
d_vrf_758 v0
  = coe MAlonzo.Code.Leios.VRF.d_vrf_90 (coe d_vrf''_712 (coe v0))
-- Leios.SpecStructure.SpecStructure.sk-IB
d_sk'45'IB_760 :: T_SpecStructure_6 -> AgdaAny
d_sk'45'IB_760 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.sk-EB
d_sk'45'EB_762 :: T_SpecStructure_6 -> AgdaAny
d_sk'45'EB_762 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.sk-V
d_sk'45'V_764 :: T_SpecStructure_6 -> AgdaAny
d_sk'45'V_764 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.pk-IB
d_pk'45'IB_766 :: T_SpecStructure_6 -> AgdaAny
d_pk'45'IB_766 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.pk-EB
d_pk'45'EB_768 :: T_SpecStructure_6 -> AgdaAny
d_pk'45'EB_768 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.pk-V
d_pk'45'V_770 :: T_SpecStructure_6 -> AgdaAny
d_pk'45'V_770 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure._.BaseAbstract
d_BaseAbstract_774 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure._.RankingBlock
d_RankingBlock_776 :: T_SpecStructure_6 -> ()
d_RankingBlock_776 = erased
-- Leios.SpecStructure.SpecStructure._.StakeDistr
d_StakeDistr_778 :: T_SpecStructure_6 -> ()
d_StakeDistr_778 = erased
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.Cert
d_Cert_784 :: MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> ()
d_Cert_784 = erased
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.Functionality
d_Functionality_790 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.Input
d_Input_794 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.Output
d_Output_796 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.V-chkCerts
d_V'45'chkCerts_802 ::
  MAlonzo.Code.Leios.Base.T_BaseAbstract_94 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_V'45'chkCerts_802 v0
  = coe MAlonzo.Code.Leios.Base.d_V'45'chkCerts_110 (coe v0)
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.VTy
d_VTy_804 :: MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> ()
d_VTy_804 = erased
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.initSlot
d_initSlot_806 ::
  MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> AgdaAny -> Integer
d_initSlot_806 v0
  = coe MAlonzo.Code.Leios.Base.d_initSlot_108 (coe v0)
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__810 ::
  MAlonzo.Code.Leios.Base.T_Functionality_128 ->
  AgdaAny ->
  MAlonzo.Code.Leios.Base.T_Input_112 ->
  MAlonzo.Code.Leios.Base.T_Output_120 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__810 = erased
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.Functionality.SUBMIT-total
d_SUBMIT'45'total_812 ::
  MAlonzo.Code.Leios.Base.T_Functionality_128 ->
  AgdaAny ->
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_SUBMIT'45'total_812 v0
  = coe MAlonzo.Code.Leios.Base.d_SUBMIT'45'total_152 (coe v0)
-- Leios.SpecStructure.SpecStructure._.BaseAbstract.Functionality.State
d_State_814 :: MAlonzo.Code.Leios.Base.T_Functionality_128 -> ()
d_State_814 = erased
-- Leios.SpecStructure.SpecStructure.B'
d_B''_844 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.Base.T_BaseAbstract_94
d_B''_844 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.BF
d_BF_846 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.Base.T_Functionality_128
d_BF_846 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure.initBaseState
d_initBaseState_848 :: T_SpecStructure_6 -> AgdaAny
d_initBaseState_848 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure._.KeyRegistrationAbstract
d_KeyRegistrationAbstract_852 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure._.KeyRegistrationAbstract.Functionality
d_Functionality_856 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.KeyRegistrationAbstract.Input
d_Input_860 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.KeyRegistrationAbstract.Output
d_Output_862 a0 a1 a2 = ()
-- Leios.SpecStructure.SpecStructure._.KeyRegistrationAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__868 ::
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96 ->
  AgdaAny ->
  MAlonzo.Code.Leios.KeyRegistration.T_Input_88 ->
  MAlonzo.Code.Leios.KeyRegistration.T_Output_92 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__868 = erased
-- Leios.SpecStructure.SpecStructure._.KeyRegistrationAbstract.Functionality.State
d_State_870 ::
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96 -> ()
d_State_870 = erased
-- Leios.SpecStructure.SpecStructure.K'
d_K''_884 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.KeyRegistration.T_KeyRegistrationAbstract_86
d_K''_884 = erased
-- Leios.SpecStructure.SpecStructure.KF
d_KF_886 ::
  T_SpecStructure_6 ->
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96
d_KF_886 = erased
-- Leios.SpecStructure.SpecStructure.B._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__890 ::
  T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Leios.Base.T_Input_112 ->
  MAlonzo.Code.Leios.Base.T_Output_120 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__890 = erased
-- Leios.SpecStructure.SpecStructure.B.SUBMIT-total
d_SUBMIT'45'total_892 ::
  T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_SUBMIT'45'total_892 v0
  = coe
      MAlonzo.Code.Leios.Base.d_SUBMIT'45'total_152
      (coe d_BF_846 (coe v0))
-- Leios.SpecStructure.SpecStructure.B.State
d_State_894 :: T_SpecStructure_6 -> ()
d_State_894 = erased
-- Leios.SpecStructure.SpecStructure.K._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__914 ::
  T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Leios.KeyRegistration.T_Input_88 ->
  MAlonzo.Code.Leios.KeyRegistration.T_Output_92 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__914 = erased
-- Leios.SpecStructure.SpecStructure.K.State
d_State_916 :: T_SpecStructure_6 -> ()
d_State_916 = erased
-- Leios.SpecStructure.SpecStructure.FFD._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__928 ::
  T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Leios.FFD.T_Input_26 ->
  MAlonzo.Code.Leios.FFD.T_Output_32 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__928 = erased
-- Leios.SpecStructure.SpecStructure.FFD.FFD-Send-total
d_FFD'45'Send'45'total_930 ::
  T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  Maybe MAlonzo.Code.Leios.Blocks.T_Body_342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_FFD'45'Send'45'total_930 v0
  = coe
      MAlonzo.Code.Leios.FFD.d_FFD'45'Send'45'total_70
      (coe d_FFD''_710 (coe v0))
-- Leios.SpecStructure.SpecStructure.FFD.State
d_State_932 :: T_SpecStructure_6 -> ()
d_State_932 = erased
-- Leios.SpecStructure.SpecStructure.FFD.initFFDState
d_initFFDState_934 :: T_SpecStructure_6 -> AgdaAny
d_initFFDState_934 v0
  = coe
      MAlonzo.Code.Leios.FFD.d_initFFDState_58 (coe d_FFD''_710 (coe v0))
-- Leios.SpecStructure.SpecStructure.va
d_va_948 ::
  T_SpecStructure_6 -> MAlonzo.Code.Leios.Voting.T_VotingAbstract_6
d_va_948 v0
  = case coe v0 of
      C_SpecStructure'46'constructor_4605 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v19
        -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.SpecStructure.SpecStructure._.VotingState
d_VotingState_952 :: T_SpecStructure_6 -> ()
d_VotingState_952 = erased
-- Leios.SpecStructure.SpecStructure._.initVotingState
d_initVotingState_954 :: T_SpecStructure_6 -> AgdaAny
d_initVotingState_954 v0
  = coe
      MAlonzo.Code.Leios.Voting.d_initVotingState_24
      (coe d_va_948 (coe v0))
-- Leios.SpecStructure.SpecStructure._.isVoteCertified
d_isVoteCertified_956 ::
  T_SpecStructure_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_isVoteCertified_956 = erased
-- Leios.SpecStructure.SpecStructure._.isVoteCertified⁇
d_isVoteCertified'8263'_958 ::
  T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Class.Decidable.Core.T__'8263'_10
d_isVoteCertified'8263'_958 v0
  = coe
      MAlonzo.Code.Leios.Voting.d_isVoteCertified'8263'_32
      (coe d_va_948 (coe v0))
-- Leios.SpecStructure.SpecStructure.B.Output.Output
d_Output_6577 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure.B.Input.Input
d_Input_6579 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure.K.Input.Input
d_Input_6661 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure.K.Output.Output
d_Output_6663 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure.FFD.Input.Input
d_Input_6715 a0 a1 = ()
-- Leios.SpecStructure.SpecStructure.FFD.Output.Output
d_Output_6717 a0 a1 = ()
