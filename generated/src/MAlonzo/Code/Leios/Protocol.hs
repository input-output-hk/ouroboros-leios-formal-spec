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

module MAlonzo.Code.Leios.Protocol where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Axiom.Set
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.Monad.Instances
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Leios.Base
import qualified MAlonzo.Code.Leios.Blocks
import qualified MAlonzo.Code.Leios.FFD
import qualified MAlonzo.Code.Leios.SpecStructure
import qualified MAlonzo.Code.Leios.Voting
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory

-- _.IBBody
d_IBBody_54 a0 a1 = ()
-- _.InputBlock
d_InputBlock_62 a0 a1 = ()
-- _.GenFFD.Body
d_Body_328 a0 a1 a2 = ()
-- _.GenFFD.Header
d_Header_330 a0 a1 a2 = ()
-- _.IBBody.txs
d_txs_376 :: MAlonzo.Code.Leios.Blocks.T_IBBody_108 -> [AgdaAny]
d_txs_376 v0 = coe MAlonzo.Code.Leios.Blocks.d_txs_112 (coe v0)
-- _.InputBlock.body
d_body_392 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Leios.Blocks.T_IBBody_108
d_body_392 v0 = coe MAlonzo.Code.Leios.Blocks.d_body_122 (coe v0)
-- _.InputBlock.header
d_header_396 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80
d_header_396 v0
  = coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0)
-- Leios.Protocol._.VTy
d_VTy_486 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 -> () -> ()
d_VTy_486 = erased
-- Leios.Protocol.LeiosInput
d_LeiosInput_490 a0 a1 a2 = ()
data T_LeiosInput_490
  = C_INIT_492 AgdaAny |
    C_SUBMIT_494 MAlonzo.Code.Data.Sum.Base.T__'8846'__30 |
    C_SLOT_496 | C_FTCH'45'LDG_498
-- Leios.Protocol.LeiosOutput
d_LeiosOutput_500 a0 a1 a2 = ()
data T_LeiosOutput_500 = C_FTCH'45'LDG_502 [AgdaAny] | C_EMPTY_504
-- Leios.Protocol.LeiosState
d_LeiosState_506 a0 a1 a2 = ()
data T_LeiosState_506
  = C_LeiosState'46'constructor_2273 AgdaAny
                                     MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 AgdaAny
                                     [AgdaAny] [AgdaAny]
                                     [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
                                     [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216] [[AgdaAny]]
                                     Integer [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
                                     [MAlonzo.Code.Leios.Blocks.T_IBBody_108] [AgdaAny] AgdaAny
                                     AgdaAny
-- Leios.Protocol.LeiosState.V
d_V_536 :: T_LeiosState_506 -> AgdaAny
d_V_536 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.SD
d_SD_538 ::
  T_LeiosState_506 -> MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_538 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.FFDState
d_FFDState_540 :: T_LeiosState_506 -> AgdaAny
d_FFDState_540 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.Ledger
d_Ledger_542 :: T_LeiosState_506 -> [AgdaAny]
d_Ledger_542 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.ToPropose
d_ToPropose_544 :: T_LeiosState_506 -> [AgdaAny]
d_ToPropose_544 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.IBs
d_IBs_546 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_546 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.EBs
d_EBs_548 ::
  T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_548 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.Vs
d_Vs_550 :: T_LeiosState_506 -> [[AgdaAny]]
d_Vs_550 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.slot
d_slot_552 :: T_LeiosState_506 -> Integer
d_slot_552 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.IBHeaders
d_IBHeaders_554 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_554 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.IBBodies
d_IBBodies_556 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_556 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.Upkeep
d_Upkeep_558 :: T_LeiosState_506 -> [AgdaAny]
d_Upkeep_558 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.BaseState
d_BaseState_560 :: T_LeiosState_506 -> AgdaAny
d_BaseState_560 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.votingState
d_votingState_562 :: T_LeiosState_506 -> AgdaAny
d_votingState_562 v0
  = case coe v0 of
      C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol.LeiosState.lookupEB
d_lookupEB_564 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_564 ~v0 v1 ~v2 v3 v4 = du_lookupEB_564 v1 v3 v4
du_lookupEB_564 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_564 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_find_914
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
              (MAlonzo.Code.Leios.Abstract.d_DecEq'45'Hash_52
                 (coe MAlonzo.Code.Leios.SpecStructure.d_a_480 (coe v0)))
              (coe
                 MAlonzo.Code.Leios.Blocks.du_getEBRef_308
                 (coe
                    MAlonzo.Code.Leios.SpecStructure.d_Hashable'45'PreEndorserBlock_706
                    (coe v0))
                 (coe v3))
              v2))
      (coe d_EBs_548 (coe v1))
-- Leios.Protocol.LeiosState.lookupIB
d_lookupIB_570 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_570 ~v0 v1 ~v2 v3 v4 = du_lookupIB_570 v1 v3 v4
du_lookupIB_570 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_570 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_find_914
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
              (MAlonzo.Code.Leios.Abstract.d_DecEq'45'Hash_52
                 (coe MAlonzo.Code.Leios.SpecStructure.d_a_480 (coe v0)))
              (coe
                 MAlonzo.Code.Leios.Blocks.du_getIBRef_178
                 (coe
                    MAlonzo.Code.Leios.SpecStructure.d_Hashable'45'IBHeaderOSig_704 v0
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                 (coe v3))
              v2))
      (coe d_IBs_546 (coe v1))
-- Leios.Protocol.LeiosState.lookupTxs
d_lookupTxs_576 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_576 ~v0 v1 ~v2 v3 v4 = du_lookupTxs_576 v1 v3 v4
du_lookupTxs_576 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_576 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_concatMap_246
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__18
              MAlonzo.Code.Class.Monad.Instances.d_Monad'45'List_12 () erased ()
              erased
              (coe
                 MAlonzo.Code.Data.List.Base.du_mapMaybe_258
                 (coe du_lookupIB_570 (coe v0) (coe v1))
                 (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v3)))
              (\ v4 ->
                 MAlonzo.Code.Leios.Blocks.d_txs_112
                   (coe MAlonzo.Code.Leios.Blocks.d_body_122 (coe v4)))))
      (coe
         MAlonzo.Code.Data.List.Base.du_mapMaybe_258
         (coe du_lookupEB_564 (coe v0) (coe v1))
         (coe MAlonzo.Code.Leios.Blocks.d_ebRefs_240 (coe v2)))
-- Leios.Protocol.LeiosState.constructLedger
d_constructLedger_588 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_588 ~v0 v1 ~v2 v3 v4
  = du_constructLedger_588 v1 v3 v4
du_constructLedger_588 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_588 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_concat_244
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.Data.These.du_mergeThese_20
                 (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
                 (coe
                    MAlonzo.Code.Data.These.Base.du_map'8321'_84
                    (coe du_lookupTxs_576 (coe v0) (coe v1)) v3)))
         (coe v2))
-- Leios.Protocol.LeiosState.needsUpkeep
d_needsUpkeep_590 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () -> T_LeiosState_506 -> AgdaAny -> ()
d_needsUpkeep_590 = erased
-- Leios.Protocol.addUpkeep
d_addUpkeep_594 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () -> T_LeiosState_506 -> AgdaAny -> T_LeiosState_506
d_addUpkeep_594 ~v0 ~v1 ~v2 v3 v4 = du_addUpkeep_594 v3 v4
du_addUpkeep_594 :: T_LeiosState_506 -> AgdaAny -> T_LeiosState_506
du_addUpkeep_594 v0 v1
  = coe
      C_LeiosState'46'constructor_2273 (coe d_V_536 (coe v0))
      (coe d_SD_538 (coe v0)) (coe d_FFDState_540 (coe v0))
      (coe d_Ledger_542 (coe v0)) (coe d_ToPropose_544 (coe v0))
      (coe d_IBs_546 (coe v0)) (coe d_EBs_548 (coe v0))
      (coe d_Vs_550 (coe v0)) (coe d_slot_552 (coe v0))
      (coe d_IBHeaders_554 (coe v0)) (coe d_IBBodies_556 (coe v0))
      (coe
         MAlonzo.Code.Axiom.Set.du__'8746'__680
         (coe
            MAlonzo.Code.Axiom.Set.d_th_1470
            (coe
               MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
         (coe d_Upkeep_558 (coe v0))
         (coe
            MAlonzo.Code.Axiom.Set.du_'10100'_'10101'_452
            (MAlonzo.Code.Axiom.Set.d_th_1470
               (coe
                  MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
            erased v1))
      (coe d_BaseState_560 (coe v0)) (coe d_votingState_562 (coe v0))
-- Leios.Protocol._.BaseState
d_BaseState_602 :: T_LeiosState_506 -> AgdaAny -> AgdaAny
d_BaseState_602 v0 ~v1 = du_BaseState_602 v0
du_BaseState_602 :: T_LeiosState_506 -> AgdaAny
du_BaseState_602 v0 = coe d_BaseState_560 (coe v0)
-- Leios.Protocol._.EBs
d_EBs_604 ::
  T_LeiosState_506 ->
  AgdaAny -> [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_604 v0 ~v1 = du_EBs_604 v0
du_EBs_604 ::
  T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_604 v0 = coe d_EBs_548 (coe v0)
-- Leios.Protocol._.FFDState
d_FFDState_606 :: T_LeiosState_506 -> AgdaAny -> AgdaAny
d_FFDState_606 v0 ~v1 = du_FFDState_606 v0
du_FFDState_606 :: T_LeiosState_506 -> AgdaAny
du_FFDState_606 v0 = coe d_FFDState_540 (coe v0)
-- Leios.Protocol._.IBBodies
d_IBBodies_608 ::
  T_LeiosState_506 ->
  AgdaAny -> [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_608 v0 ~v1 = du_IBBodies_608 v0
du_IBBodies_608 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
du_IBBodies_608 v0 = coe d_IBBodies_556 (coe v0)
-- Leios.Protocol._.IBHeaders
d_IBHeaders_610 ::
  T_LeiosState_506 ->
  AgdaAny -> [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_610 v0 ~v1 = du_IBHeaders_610 v0
du_IBHeaders_610 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
du_IBHeaders_610 v0 = coe d_IBHeaders_554 (coe v0)
-- Leios.Protocol._.IBs
d_IBs_612 ::
  T_LeiosState_506 ->
  AgdaAny -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_612 v0 ~v1 = du_IBs_612 v0
du_IBs_612 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
du_IBs_612 v0 = coe d_IBs_546 (coe v0)
-- Leios.Protocol._.Ledger
d_Ledger_614 :: T_LeiosState_506 -> AgdaAny -> [AgdaAny]
d_Ledger_614 v0 ~v1 = du_Ledger_614 v0
du_Ledger_614 :: T_LeiosState_506 -> [AgdaAny]
du_Ledger_614 v0 = coe d_Ledger_542 (coe v0)
-- Leios.Protocol._.SD
d_SD_616 ::
  T_LeiosState_506 ->
  AgdaAny -> MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_616 v0 ~v1 = du_SD_616 v0
du_SD_616 ::
  T_LeiosState_506 -> MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
du_SD_616 v0 = coe d_SD_538 (coe v0)
-- Leios.Protocol._.ToPropose
d_ToPropose_618 :: T_LeiosState_506 -> AgdaAny -> [AgdaAny]
d_ToPropose_618 v0 ~v1 = du_ToPropose_618 v0
du_ToPropose_618 :: T_LeiosState_506 -> [AgdaAny]
du_ToPropose_618 v0 = coe d_ToPropose_544 (coe v0)
-- Leios.Protocol._.Upkeep
d_Upkeep_620 :: T_LeiosState_506 -> AgdaAny -> [AgdaAny]
d_Upkeep_620 v0 ~v1 = du_Upkeep_620 v0
du_Upkeep_620 :: T_LeiosState_506 -> [AgdaAny]
du_Upkeep_620 v0 = coe d_Upkeep_558 (coe v0)
-- Leios.Protocol._.V
d_V_622 :: T_LeiosState_506 -> AgdaAny -> AgdaAny
d_V_622 v0 ~v1 = du_V_622 v0
du_V_622 :: T_LeiosState_506 -> AgdaAny
du_V_622 v0 = coe d_V_536 (coe v0)
-- Leios.Protocol._.Vs
d_Vs_624 :: T_LeiosState_506 -> AgdaAny -> [[AgdaAny]]
d_Vs_624 v0 ~v1 = du_Vs_624 v0
du_Vs_624 :: T_LeiosState_506 -> [[AgdaAny]]
du_Vs_624 v0 = coe d_Vs_550 (coe v0)
-- Leios.Protocol._.constructLedger
d_constructLedger_626 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny -> [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_626 ~v0 v1 ~v2 v3 ~v4
  = du_constructLedger_626 v1 v3
du_constructLedger_626 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_626 v0 v1
  = coe du_constructLedger_588 (coe v0) (coe v1)
-- Leios.Protocol._.lookupEB
d_lookupEB_628 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_628 ~v0 v1 ~v2 v3 ~v4 = du_lookupEB_628 v1 v3
du_lookupEB_628 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_628 v0 v1 = coe du_lookupEB_564 (coe v0) (coe v1)
-- Leios.Protocol._.lookupIB
d_lookupIB_630 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_630 ~v0 v1 ~v2 v3 ~v4 = du_lookupIB_630 v1 v3
du_lookupIB_630 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_630 v0 v1 = coe du_lookupIB_570 (coe v0) (coe v1)
-- Leios.Protocol._.lookupTxs
d_lookupTxs_632 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_632 ~v0 v1 ~v2 v3 ~v4 = du_lookupTxs_632 v1 v3
du_lookupTxs_632 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_632 v0 v1 = coe du_lookupTxs_576 (coe v0) (coe v1)
-- Leios.Protocol._.needsUpkeep
d_needsUpkeep_634 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () -> T_LeiosState_506 -> AgdaAny -> AgdaAny -> ()
d_needsUpkeep_634 = erased
-- Leios.Protocol._.slot
d_slot_636 :: T_LeiosState_506 -> AgdaAny -> Integer
d_slot_636 v0 ~v1 = du_slot_636 v0
du_slot_636 :: T_LeiosState_506 -> Integer
du_slot_636 v0 = coe d_slot_552 (coe v0)
-- Leios.Protocol._.votingState
d_votingState_638 :: T_LeiosState_506 -> AgdaAny -> AgdaAny
d_votingState_638 v0 ~v1 = du_votingState_638 v0
du_votingState_638 :: T_LeiosState_506 -> AgdaAny
du_votingState_638 v0 = coe d_votingState_562 (coe v0)
-- Leios.Protocol.initLeiosState
d_initLeiosState_640 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 ->
  AgdaAny -> T_LeiosState_506
d_initLeiosState_640 ~v0 v1 ~v2 v3 v4 v5
  = du_initLeiosState_640 v1 v3 v4 v5
du_initLeiosState_640 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 ->
  AgdaAny -> T_LeiosState_506
du_initLeiosState_640 v0 v1 v2 v3
  = coe
      C_LeiosState'46'constructor_2273 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Leios.FFD.d_initFFDState_58
         (coe MAlonzo.Code.Leios.SpecStructure.d_FFD''_710 (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Leios.Base.d_initSlot_108
         (MAlonzo.Code.Leios.SpecStructure.d_B''_844 (coe v0)) v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Axiom.Set.du_'8709'_442
         (coe
            MAlonzo.Code.Axiom.Set.d_th_1470
            (coe
               MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8)))
      (coe v3)
      (coe
         MAlonzo.Code.Leios.Voting.d_initVotingState_24
         (coe MAlonzo.Code.Leios.SpecStructure.d_va_948 (coe v0)))
-- Leios.Protocol._._.BaseState
d_BaseState_672 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_BaseState_672 v0 ~v1 = du_BaseState_672 v0
du_BaseState_672 :: T_LeiosState_506 -> AgdaAny
du_BaseState_672 v0 = coe d_BaseState_560 (coe v0)
-- Leios.Protocol._._.EBs
d_EBs_674 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_674 v0 ~v1 = du_EBs_674 v0
du_EBs_674 ::
  T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_674 v0 = coe d_EBs_548 (coe v0)
-- Leios.Protocol._._.FFDState
d_FFDState_676 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_FFDState_676 v0 ~v1 = du_FFDState_676 v0
du_FFDState_676 :: T_LeiosState_506 -> AgdaAny
du_FFDState_676 v0 = coe d_FFDState_540 (coe v0)
-- Leios.Protocol._._.IBBodies
d_IBBodies_678 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_678 v0 ~v1 = du_IBBodies_678 v0
du_IBBodies_678 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
du_IBBodies_678 v0 = coe d_IBBodies_556 (coe v0)
-- Leios.Protocol._._.IBHeaders
d_IBHeaders_680 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_680 v0 ~v1 = du_IBHeaders_680 v0
du_IBHeaders_680 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
du_IBHeaders_680 v0 = coe d_IBHeaders_554 (coe v0)
-- Leios.Protocol._._.IBs
d_IBs_682 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_682 v0 ~v1 = du_IBs_682 v0
du_IBs_682 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
du_IBs_682 v0 = coe d_IBs_546 (coe v0)
-- Leios.Protocol._._.Ledger
d_Ledger_684 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_Ledger_684 v0 ~v1 = du_Ledger_684 v0
du_Ledger_684 :: T_LeiosState_506 -> [AgdaAny]
du_Ledger_684 v0 = coe d_Ledger_542 (coe v0)
-- Leios.Protocol._._.SD
d_SD_686 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_686 v0 ~v1 = du_SD_686 v0
du_SD_686 ::
  T_LeiosState_506 -> MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
du_SD_686 v0 = coe d_SD_538 (coe v0)
-- Leios.Protocol._._.ToPropose
d_ToPropose_688 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_ToPropose_688 v0 ~v1 = du_ToPropose_688 v0
du_ToPropose_688 :: T_LeiosState_506 -> [AgdaAny]
du_ToPropose_688 v0 = coe d_ToPropose_544 (coe v0)
-- Leios.Protocol._._.Upkeep
d_Upkeep_690 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_Upkeep_690 v0 ~v1 = du_Upkeep_690 v0
du_Upkeep_690 :: T_LeiosState_506 -> [AgdaAny]
du_Upkeep_690 v0 = coe d_Upkeep_558 (coe v0)
-- Leios.Protocol._._.V
d_V_692 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_V_692 v0 ~v1 = du_V_692 v0
du_V_692 :: T_LeiosState_506 -> AgdaAny
du_V_692 v0 = coe d_V_536 (coe v0)
-- Leios.Protocol._._.Vs
d_Vs_694 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [[AgdaAny]]
d_Vs_694 v0 ~v1 = du_Vs_694 v0
du_Vs_694 :: T_LeiosState_506 -> [[AgdaAny]]
du_Vs_694 v0 = coe d_Vs_550 (coe v0)
-- Leios.Protocol._._.constructLedger
d_constructLedger_696 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_696 ~v0 v1 ~v2 v3 ~v4
  = du_constructLedger_696 v1 v3
du_constructLedger_696 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_696 v0 v1
  = coe du_constructLedger_588 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupEB
d_lookupEB_698 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_698 ~v0 v1 ~v2 v3 ~v4 = du_lookupEB_698 v1 v3
du_lookupEB_698 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_698 v0 v1 = coe du_lookupEB_564 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupIB
d_lookupIB_700 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_700 ~v0 v1 ~v2 v3 ~v4 = du_lookupIB_700 v1 v3
du_lookupIB_700 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_700 v0 v1 = coe du_lookupIB_570 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupTxs
d_lookupTxs_702 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_702 ~v0 v1 ~v2 v3 ~v4 = du_lookupTxs_702 v1 v3
du_lookupTxs_702 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_702 v0 v1 = coe du_lookupTxs_576 (coe v0) (coe v1)
-- Leios.Protocol._._.needsUpkeep
d_needsUpkeep_704 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny -> ()
d_needsUpkeep_704 = erased
-- Leios.Protocol._._.slot
d_slot_706 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> Integer
d_slot_706 v0 ~v1 = du_slot_706 v0
du_slot_706 :: T_LeiosState_506 -> Integer
du_slot_706 v0 = coe d_slot_552 (coe v0)
-- Leios.Protocol._._.votingState
d_votingState_708 ::
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_votingState_708 v0 ~v1 = du_votingState_708 v0
du_votingState_708 :: T_LeiosState_506 -> AgdaAny
du_votingState_708 v0 = coe d_votingState_562 (coe v0)
-- Leios.Protocol._.allIBRefsKnown
d_allIBRefsKnown_710 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_allIBRefsKnown_710 = erased
-- Leios.Protocol.stake
d_stake_714 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () -> T_LeiosState_506 -> Integer
d_stake_714 ~v0 v1 ~v2 v3 = du_stake_714 v1 v3
du_stake_714 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 -> Integer
du_stake_714 v0 v1
  = case coe v1 of
      C_LeiosState'46'constructor_2273 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe
             MAlonzo.Code.Axiom.Set.TotalMap.du_lookup_188
             (coe
                MAlonzo.Code.Axiom.Set.d_th_1470
                (coe
                   MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
             (coe v3) (coe MAlonzo.Code.Leios.SpecStructure.d_id_708 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol._._.BaseState
d_BaseState_726 :: T_LeiosState_506 -> AgdaAny
d_BaseState_726 v0 = coe d_BaseState_560 (coe v0)
-- Leios.Protocol._._.EBs
d_EBs_728 ::
  T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_728 v0 = coe d_EBs_548 (coe v0)
-- Leios.Protocol._._.FFDState
d_FFDState_730 :: T_LeiosState_506 -> AgdaAny
d_FFDState_730 v0 = coe d_FFDState_540 (coe v0)
-- Leios.Protocol._._.IBBodies
d_IBBodies_732 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_732 v0 = coe d_IBBodies_556 (coe v0)
-- Leios.Protocol._._.IBHeaders
d_IBHeaders_734 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_734 v0 = coe d_IBHeaders_554 (coe v0)
-- Leios.Protocol._._.IBs
d_IBs_736 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_736 v0 = coe d_IBs_546 (coe v0)
-- Leios.Protocol._._.Ledger
d_Ledger_738 :: T_LeiosState_506 -> [AgdaAny]
d_Ledger_738 v0 = coe d_Ledger_542 (coe v0)
-- Leios.Protocol._._.SD
d_SD_740 ::
  T_LeiosState_506 -> MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_740 v0 = coe d_SD_538 (coe v0)
-- Leios.Protocol._._.ToPropose
d_ToPropose_742 :: T_LeiosState_506 -> [AgdaAny]
d_ToPropose_742 v0 = coe d_ToPropose_544 (coe v0)
-- Leios.Protocol._._.Upkeep
d_Upkeep_744 :: T_LeiosState_506 -> [AgdaAny]
d_Upkeep_744 v0 = coe d_Upkeep_558 (coe v0)
-- Leios.Protocol._._.V
d_V_746 :: T_LeiosState_506 -> AgdaAny
d_V_746 v0 = coe d_V_536 (coe v0)
-- Leios.Protocol._._.Vs
d_Vs_748 :: T_LeiosState_506 -> [[AgdaAny]]
d_Vs_748 v0 = coe d_Vs_550 (coe v0)
-- Leios.Protocol._._.constructLedger
d_constructLedger_750 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_750 ~v0 v1 ~v2 v3 = du_constructLedger_750 v1 v3
du_constructLedger_750 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_750 v0 v1
  = coe du_constructLedger_588 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupEB
d_lookupEB_752 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_752 ~v0 v1 ~v2 v3 = du_lookupEB_752 v1 v3
du_lookupEB_752 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_752 v0 v1 = coe du_lookupEB_564 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupIB
d_lookupIB_754 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_754 ~v0 v1 ~v2 v3 = du_lookupIB_754 v1 v3
du_lookupIB_754 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_754 v0 v1 = coe du_lookupIB_570 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupTxs
d_lookupTxs_756 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_756 ~v0 v1 ~v2 v3 = du_lookupTxs_756 v1 v3
du_lookupTxs_756 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_756 v0 v1 = coe du_lookupTxs_576 (coe v0) (coe v1)
-- Leios.Protocol._._.needsUpkeep
d_needsUpkeep_758 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () -> T_LeiosState_506 -> AgdaAny -> ()
d_needsUpkeep_758 = erased
-- Leios.Protocol._._.slot
d_slot_760 :: T_LeiosState_506 -> Integer
d_slot_760 v0 = coe d_slot_552 (coe v0)
-- Leios.Protocol._._.votingState
d_votingState_762 :: T_LeiosState_506 -> AgdaAny
d_votingState_762 v0 = coe d_votingState_562 (coe v0)
-- Leios.Protocol._.upd
d_upd_764 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_LeiosState_506
d_upd_764 ~v0 v1 ~v2 v3 v4 = du_upd_764 v1 v3 v4
du_upd_764 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_LeiosState_506
du_upd_764 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> case coe v3 of
             MAlonzo.Code.Leios.Blocks.C_ibHeader_336 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                            (coe
                               MAlonzo.Code.Leios.Blocks.du_matchIB'63'_378
                               (coe MAlonzo.Code.Leios.SpecStructure.d_a_480 (coe v0)) (coe v4))
                            (coe d_IBBodies_556 (coe v1)) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                       -> coe
                                            C_LeiosState'46'constructor_2273 (coe d_V_536 (coe v1))
                                            (coe d_SD_538 (coe v1)) (coe d_FFDState_540 (coe v1))
                                            (coe d_Ledger_542 (coe v1))
                                            (coe d_ToPropose_544 (coe v1))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Leios.Blocks.C_InputBlock'46'constructor_823
                                                  (coe v4)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.Any.du_lookup_94
                                                     (coe d_IBBodies_556 (coe v1)) (coe v8)))
                                               (coe d_IBs_546 (coe v1)))
                                            (coe d_EBs_548 (coe v1)) (coe d_Vs_550 (coe v1))
                                            (coe d_slot_552 (coe v1)) (coe d_IBHeaders_554 (coe v1))
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                               (coe d_IBBodies_556 (coe v1)) (coe v8))
                                            (coe d_Upkeep_558 (coe v1))
                                            (coe d_BaseState_560 (coe v1))
                                            (coe d_votingState_562 (coe v1))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v7)
                                     (coe
                                        C_LeiosState'46'constructor_2273 (coe d_V_536 (coe v1))
                                        (coe d_SD_538 (coe v1)) (coe d_FFDState_540 (coe v1))
                                        (coe d_Ledger_542 (coe v1)) (coe d_ToPropose_544 (coe v1))
                                        (coe d_IBs_546 (coe v1)) (coe d_EBs_548 (coe v1))
                                        (coe d_Vs_550 (coe v1)) (coe d_slot_552 (coe v1))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                           (coe d_IBHeaders_554 (coe v1)))
                                        (coe d_IBBodies_556 (coe v1)) (coe d_Upkeep_558 (coe v1))
                                        (coe d_BaseState_560 (coe v1))
                                        (coe d_votingState_562 (coe v1)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Leios.Blocks.C_ebHeader_338 v4
               -> coe
                    C_LeiosState'46'constructor_2273 (coe d_V_536 (coe v1))
                    (coe d_SD_538 (coe v1)) (coe d_FFDState_540 (coe v1))
                    (coe d_Ledger_542 (coe v1)) (coe d_ToPropose_544 (coe v1))
                    (coe d_IBs_546 (coe v1))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                       (coe d_EBs_548 (coe v1)))
                    (coe d_Vs_550 (coe v1)) (coe d_slot_552 (coe v1))
                    (coe d_IBHeaders_554 (coe v1)) (coe d_IBBodies_556 (coe v1))
                    (coe d_Upkeep_558 (coe v1)) (coe d_BaseState_560 (coe v1))
                    (coe d_votingState_562 (coe v1))
             MAlonzo.Code.Leios.Blocks.C_vHeader_340 v4
               -> coe
                    C_LeiosState'46'constructor_2273 (coe d_V_536 (coe v1))
                    (coe d_SD_538 (coe v1)) (coe d_FFDState_540 (coe v1))
                    (coe d_Ledger_542 (coe v1)) (coe d_ToPropose_544 (coe v1))
                    (coe d_IBs_546 (coe v1)) (coe d_EBs_548 (coe v1))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                       (coe d_Vs_550 (coe v1)))
                    (coe d_slot_552 (coe v1)) (coe d_IBHeaders_554 (coe v1))
                    (coe d_IBBodies_556 (coe v1)) (coe d_Upkeep_558 (coe v1))
                    (coe d_BaseState_560 (coe v1)) (coe d_votingState_562 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v3 of
             MAlonzo.Code.Leios.Blocks.C_ibBody_344 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                            (coe
                               (\ v5 ->
                                  coe
                                    MAlonzo.Code.Leios.Blocks.du_matchIB'63'_378
                                    (coe MAlonzo.Code.Leios.SpecStructure.d_a_480 (coe v0)) (coe v5)
                                    (coe v4)))
                            (coe d_IBHeaders_554 (coe v1)) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                       -> coe
                                            C_LeiosState'46'constructor_2273 (coe d_V_536 (coe v1))
                                            (coe d_SD_538 (coe v1)) (coe d_FFDState_540 (coe v1))
                                            (coe d_Ledger_542 (coe v1))
                                            (coe d_ToPropose_544 (coe v1))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Leios.Blocks.C_InputBlock'46'constructor_823
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.Any.du_lookup_94
                                                     (coe d_IBHeaders_554 (coe v1)) (coe v8))
                                                  (coe v4))
                                               (coe d_IBs_546 (coe v1)))
                                            (coe d_EBs_548 (coe v1)) (coe d_Vs_550 (coe v1))
                                            (coe d_slot_552 (coe v1))
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                               (coe d_IBHeaders_554 (coe v1)) (coe v8))
                                            (coe d_IBBodies_556 (coe v1))
                                            (coe d_Upkeep_558 (coe v1))
                                            (coe d_BaseState_560 (coe v1))
                                            (coe d_votingState_562 (coe v1))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v7)
                                     (coe
                                        C_LeiosState'46'constructor_2273 (coe d_V_536 (coe v1))
                                        (coe d_SD_538 (coe v1)) (coe d_FFDState_540 (coe v1))
                                        (coe d_Ledger_542 (coe v1)) (coe d_ToPropose_544 (coe v1))
                                        (coe d_IBs_546 (coe v1)) (coe d_EBs_548 (coe v1))
                                        (coe d_Vs_550 (coe v1)) (coe d_slot_552 (coe v1))
                                        (coe d_IBHeaders_554 (coe v1))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                           (coe d_IBBodies_556 (coe v1)))
                                        (coe d_Upkeep_558 (coe v1)) (coe d_BaseState_560 (coe v1))
                                        (coe d_votingState_562 (coe v1)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Protocol._._.BaseState
d_BaseState_804 :: T_LeiosState_506 -> AgdaAny
d_BaseState_804 v0 = coe d_BaseState_560 (coe v0)
-- Leios.Protocol._._.EBs
d_EBs_806 ::
  T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_806 v0 = coe d_EBs_548 (coe v0)
-- Leios.Protocol._._.FFDState
d_FFDState_808 :: T_LeiosState_506 -> AgdaAny
d_FFDState_808 v0 = coe d_FFDState_540 (coe v0)
-- Leios.Protocol._._.IBBodies
d_IBBodies_810 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_810 v0 = coe d_IBBodies_556 (coe v0)
-- Leios.Protocol._._.IBHeaders
d_IBHeaders_812 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_812 v0 = coe d_IBHeaders_554 (coe v0)
-- Leios.Protocol._._.IBs
d_IBs_814 ::
  T_LeiosState_506 -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_814 v0 = coe d_IBs_546 (coe v0)
-- Leios.Protocol._._.Ledger
d_Ledger_816 :: T_LeiosState_506 -> [AgdaAny]
d_Ledger_816 v0 = coe d_Ledger_542 (coe v0)
-- Leios.Protocol._._.SD
d_SD_818 ::
  T_LeiosState_506 -> MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_818 v0 = coe d_SD_538 (coe v0)
-- Leios.Protocol._._.ToPropose
d_ToPropose_820 :: T_LeiosState_506 -> [AgdaAny]
d_ToPropose_820 v0 = coe d_ToPropose_544 (coe v0)
-- Leios.Protocol._._.Upkeep
d_Upkeep_822 :: T_LeiosState_506 -> [AgdaAny]
d_Upkeep_822 v0 = coe d_Upkeep_558 (coe v0)
-- Leios.Protocol._._.V
d_V_824 :: T_LeiosState_506 -> AgdaAny
d_V_824 v0 = coe d_V_536 (coe v0)
-- Leios.Protocol._._.Vs
d_Vs_826 :: T_LeiosState_506 -> [[AgdaAny]]
d_Vs_826 v0 = coe d_Vs_550 (coe v0)
-- Leios.Protocol._._.constructLedger
d_constructLedger_828 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_828 ~v0 v1 ~v2 ~v3 v4
  = du_constructLedger_828 v1 v4
du_constructLedger_828 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_828 v0 v1
  = coe du_constructLedger_588 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupEB
d_lookupEB_830 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_830 ~v0 v1 ~v2 ~v3 v4 = du_lookupEB_830 v1 v4
du_lookupEB_830 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_830 v0 v1 = coe du_lookupEB_564 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupIB
d_lookupIB_832 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_832 ~v0 v1 ~v2 ~v3 v4 = du_lookupIB_832 v1 v4
du_lookupIB_832 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_832 v0 v1 = coe du_lookupIB_570 (coe v0) (coe v1)
-- Leios.Protocol._._.lookupTxs
d_lookupTxs_834 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_834 ~v0 v1 ~v2 ~v3 v4 = du_lookupTxs_834 v1 v4
du_lookupTxs_834 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_834 v0 v1 = coe du_lookupTxs_576 (coe v0) (coe v1)
-- Leios.Protocol._._.needsUpkeep
d_needsUpkeep_836 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () -> T_LeiosState_506 -> T_LeiosState_506 -> AgdaAny -> ()
d_needsUpkeep_836 = erased
-- Leios.Protocol._._.slot
d_slot_838 :: T_LeiosState_506 -> Integer
d_slot_838 v0 = coe d_slot_552 (coe v0)
-- Leios.Protocol._._.votingState
d_votingState_840 :: T_LeiosState_506 -> AgdaAny
d_votingState_840 v0 = coe d_votingState_562 (coe v0)
-- Leios.Protocol._.upd-preserves-Upkeep
d_upd'45'preserves'45'Upkeep_844 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_upd'45'preserves'45'Upkeep_844 = erased
-- Leios.Protocol._↑_
d__'8593'__878 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] -> T_LeiosState_506
d__'8593'__878 ~v0 v1 ~v2 = du__'8593'__878 v1
du__'8593'__878 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] -> T_LeiosState_506
du__'8593'__878 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe (\ v1 v2 -> coe du_upd_764 (coe v0) (coe v2) (coe v1)))
-- Leios.Protocol.↑-preserves-Upkeep
d_'8593''45'preserves'45'Upkeep_884 ::
  Integer ->
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  () ->
  T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''45'preserves'45'Upkeep_884 = erased
