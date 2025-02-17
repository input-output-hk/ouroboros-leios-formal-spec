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

module MAlonzo.Code.Leios.Short where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Axiom.Set
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Leios.Base
import qualified MAlonzo.Code.Leios.Blocks
import qualified MAlonzo.Code.Leios.FFD
import qualified MAlonzo.Code.Leios.KeyRegistration
import qualified MAlonzo.Code.Leios.Protocol
import qualified MAlonzo.Code.Leios.SpecStructure
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Tactic.Derive.DecEq
import qualified MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory

-- _.B.Output
d_Output_9 a0 = ()
-- _.B.Input
d_Input_11 a0 = ()
-- _.K.Input
d_Input_13 a0 = ()
-- _.K.Output
d_Output_15 a0 = ()
-- _.FFD.Input
d_Input_17 a0 = ()
-- _.FFD.Output
d_Output_19 a0 = ()
-- _.BaseAbstract.Input
d_Input_242 a0 a1 = ()
-- _.BaseAbstract.Output
d_Output_244 a0 a1 = ()
-- _.GenFFD.Body
d_Body_326 a0 a1 = ()
-- _.GenFFD.Header
d_Header_328 a0 a1 = ()
-- _.KeyRegistrationAbstract.Input
d_Input_430 a0 a1 = ()
-- _.KeyRegistrationAbstract.Output
d_Output_432 a0 a1 = ()
-- Leios.Short.SlotUpkeep
d_SlotUpkeep_476 a0 = ()
data T_SlotUpkeep_476
  = C_Base_478 | C_IB'45'Role_480 | C_EB'45'Role_482 |
    C_V'45'Role_484
-- Leios.Short.DecEq-SlotUpkeep
d_DecEq'45'SlotUpkeep_486 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'SlotUpkeep_486 ~v0 = du_DecEq'45'SlotUpkeep_486
du_DecEq'45'SlotUpkeep_486 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'SlotUpkeep_486
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         (\ v0 ->
            case coe v0 of
              C_Base_478
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_478
                            -> coe
                                 MAlonzo.Code.Tactic.Derive.DecEq.du_map''_38
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                 (coe
                                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
                                    (coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                          C_IB'45'Role_480
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_EB'45'Role_482
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V'45'Role_484
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              C_IB'45'Role_480
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_478
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_IB'45'Role_480
                            -> coe
                                 MAlonzo.Code.Tactic.Derive.DecEq.du_map''_38
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                 (coe
                                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
                                    (coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                          C_EB'45'Role_482
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V'45'Role_484
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              C_EB'45'Role_482
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_478
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_IB'45'Role_480
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_EB'45'Role_482
                            -> coe
                                 MAlonzo.Code.Tactic.Derive.DecEq.du_map''_38
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                 (coe
                                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
                                    (coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                          C_V'45'Role_484
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              C_V'45'Role_484
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_478
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_IB'45'Role_480
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_EB'45'Role_482
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V'45'Role_484
                            -> coe
                                 MAlonzo.Code.Tactic.Derive.DecEq.du_map''_38
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                 (coe
                                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
                                    (coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                          _ -> MAlonzo.RTE.mazUnreachableError)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Short.allUpkeep
d_allUpkeep_488 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  [T_SlotUpkeep_476]
d_allUpkeep_488 ~v0 = du_allUpkeep_488
du_allUpkeep_488 :: [T_SlotUpkeep_476]
du_allUpkeep_488
  = coe
      MAlonzo.Code.Axiom.Set.du__'8746'__680
      (coe
         MAlonzo.Code.Axiom.Set.d_th_1470
         (coe
            MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
      (coe
         MAlonzo.Code.Axiom.Set.du__'8746'__680
         (coe
            MAlonzo.Code.Axiom.Set.d_th_1470
            (coe
               MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
         (coe
            MAlonzo.Code.Axiom.Set.du__'8746'__680
            (coe
               MAlonzo.Code.Axiom.Set.d_th_1470
               (coe
                  MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
            (coe
               MAlonzo.Code.Axiom.Set.du__'8746'__680
               (coe
                  MAlonzo.Code.Axiom.Set.d_th_1470
                  (coe
                     MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
               (coe
                  MAlonzo.Code.Axiom.Set.du_'8709'_442
                  (coe
                     MAlonzo.Code.Axiom.Set.d_th_1470
                     (coe
                        MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8)))
               (coe
                  MAlonzo.Code.Axiom.Set.du_'10100'_'10101'_452
                  (MAlonzo.Code.Axiom.Set.d_th_1470
                     (coe
                        MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
                  erased (coe C_IB'45'Role_480)))
            (coe
               MAlonzo.Code.Axiom.Set.du_'10100'_'10101'_452
               (MAlonzo.Code.Axiom.Set.d_th_1470
                  (coe
                     MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
               erased (coe C_EB'45'Role_482)))
         (coe
            MAlonzo.Code.Axiom.Set.du_'10100'_'10101'_452
            (MAlonzo.Code.Axiom.Set.d_th_1470
               (coe
                  MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
            erased (coe C_V'45'Role_484)))
      (coe
         MAlonzo.Code.Axiom.Set.du_'10100'_'10101'_452
         (MAlonzo.Code.Axiom.Set.d_th_1470
            (coe
               MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
         erased (coe C_Base_478))
-- Leios.Short._._↑_
d__'8593'__492 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d__'8593'__492 v0
  = coe MAlonzo.Code.Leios.Protocol.du__'8593'__878 (coe v0)
-- Leios.Short._.LeiosInput
d_LeiosInput_502 a0 = ()
-- Leios.Short._.LeiosOutput
d_LeiosOutput_504 a0 = ()
-- Leios.Short._.LeiosState
d_LeiosState_506 a0 = ()
-- Leios.Short._.addUpkeep
d_addUpkeep_512 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  T_SlotUpkeep_476 -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_addUpkeep_512 ~v0 = du_addUpkeep_512
du_addUpkeep_512 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  T_SlotUpkeep_476 -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506
du_addUpkeep_512 = coe MAlonzo.Code.Leios.Protocol.du_addUpkeep_594
-- Leios.Short._.allIBRefsKnown
d_allIBRefsKnown_514 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_allIBRefsKnown_514 = erased
-- Leios.Short._.initLeiosState
d_initLeiosState_516 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 ->
  AgdaAny -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_initLeiosState_516 v0
  = coe MAlonzo.Code.Leios.Protocol.du_initLeiosState_640 (coe v0)
-- Leios.Short._.stake
d_stake_518 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_stake_518 v0
  = coe MAlonzo.Code.Leios.Protocol.du_stake_714 (coe v0)
-- Leios.Short._.upd
d_upd_520 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_upd_520 v0 = coe MAlonzo.Code.Leios.Protocol.du_upd_764 (coe v0)
-- Leios.Short._.upd-preserves-Upkeep
d_upd'45'preserves'45'Upkeep_522 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_upd'45'preserves'45'Upkeep_522 = erased
-- Leios.Short._.↑-preserves-Upkeep
d_'8593''45'preserves'45'Upkeep_524 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''45'preserves'45'Upkeep_524 = erased
-- Leios.Short._.LeiosState.BaseState
d_BaseState_544 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_BaseState_544 v0
  = coe MAlonzo.Code.Leios.Protocol.d_BaseState_560 (coe v0)
-- Leios.Short._.LeiosState.EBs
d_EBs_546 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_546 v0 = coe MAlonzo.Code.Leios.Protocol.d_EBs_548 (coe v0)
-- Leios.Short._.LeiosState.FFDState
d_FFDState_548 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_FFDState_548 v0
  = coe MAlonzo.Code.Leios.Protocol.d_FFDState_540 (coe v0)
-- Leios.Short._.LeiosState.IBBodies
d_IBBodies_550 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_550 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBBodies_556 (coe v0)
-- Leios.Short._.LeiosState.IBHeaders
d_IBHeaders_552 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_552 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBHeaders_554 (coe v0)
-- Leios.Short._.LeiosState.IBs
d_IBs_554 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_554 v0 = coe MAlonzo.Code.Leios.Protocol.d_IBs_546 (coe v0)
-- Leios.Short._.LeiosState.Ledger
d_Ledger_556 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [AgdaAny]
d_Ledger_556 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Ledger_542 (coe v0)
-- Leios.Short._.LeiosState.SD
d_SD_558 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_558 v0 = coe MAlonzo.Code.Leios.Protocol.d_SD_538 (coe v0)
-- Leios.Short._.LeiosState.ToPropose
d_ToPropose_560 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [AgdaAny]
d_ToPropose_560 v0
  = coe MAlonzo.Code.Leios.Protocol.d_ToPropose_544 (coe v0)
-- Leios.Short._.LeiosState.Upkeep
d_Upkeep_562 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [T_SlotUpkeep_476]
d_Upkeep_562 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Upkeep_558 (coe v0)
-- Leios.Short._.LeiosState.V
d_V_564 :: MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_V_564 v0 = coe MAlonzo.Code.Leios.Protocol.d_V_536 (coe v0)
-- Leios.Short._.LeiosState.Vs
d_Vs_566 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [[AgdaAny]]
d_Vs_566 v0 = coe MAlonzo.Code.Leios.Protocol.d_Vs_550 (coe v0)
-- Leios.Short._.LeiosState.constructLedger
d_constructLedger_568 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_568 v0
  = coe MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
-- Leios.Short._.LeiosState.lookupEB
d_lookupEB_570 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_570 v0
  = coe MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
-- Leios.Short._.LeiosState.lookupIB
d_lookupIB_572 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_572 v0
  = coe MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
-- Leios.Short._.LeiosState.lookupTxs
d_lookupTxs_574 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_574 v0
  = coe MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
-- Leios.Short._.LeiosState.needsUpkeep
d_needsUpkeep_576 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  T_SlotUpkeep_476 -> ()
d_needsUpkeep_576 = erased
-- Leios.Short._.LeiosState.slot
d_slot_578 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_slot_578 v0 = coe MAlonzo.Code.Leios.Protocol.d_slot_552 (coe v0)
-- Leios.Short._.LeiosState.votingState
d_votingState_580 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_votingState_580 v0
  = coe MAlonzo.Code.Leios.Protocol.d_votingState_562 (coe v0)
-- Leios.Short._.V-chkCerts
d_V'45'chkCerts_586 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_V'45'chkCerts_586 v0
  = coe
      MAlonzo.Code.Leios.Base.d_V'45'chkCerts_110
      (coe MAlonzo.Code.Leios.SpecStructure.d_B''_844 (coe v0))
-- Leios.Short._.VTy
d_VTy_588 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 -> ()
d_VTy_588 = erased
-- Leios.Short.isVoteCertified
d_isVoteCertified_592 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_isVoteCertified_592 = erased
-- Leios.Short._↝_
d__'8605'__626 a0 a1 a2 = ()
data T__'8605'__626
  = C_IB'45'Role_672 AgdaAny AgdaAny
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 AgdaAny |
    C_EB'45'Role_720 AgdaAny AgdaAny
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 AgdaAny |
    C_V'45'Role_768 AgdaAny MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                    AgdaAny |
    C_No'45'IB'45'Role_812 | C_No'45'EB'45'Role_856 |
    C_No'45'V'45'Role_898
-- Leios.Short._.ToPropose
d_ToPropose_644 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 -> [AgdaAny]
d_ToPropose_644 ~v0 v1 = du_ToPropose_644 v1
du_ToPropose_644 :: T_GeneralizeTel_9513 -> [AgdaAny]
du_ToPropose_644 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_ToPropose_544
      (coe d_'46'generalizedField'45's_9507 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_652 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_652 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_9507 (coe v1))
-- Leios.Short._.FFDState
d_FFDState_654 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 -> AgdaAny
d_FFDState_654 ~v0 v1 = du_FFDState_654 v1
du_FFDState_654 :: T_GeneralizeTel_9513 -> AgdaAny
du_FFDState_654 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_9507 (coe v0))
-- Leios.Short._.lookupEB
d_lookupEB_656 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_656 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_9507 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_658 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_658 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_9507 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_660 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_660 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_9507 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_662 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_662 = erased
-- Leios.Short._.slot
d_slot_664 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_9513 -> Integer
d_slot_664 ~v0 v1 = du_slot_664 v1
du_slot_664 :: T_GeneralizeTel_9513 -> Integer
du_slot_664 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_9507 (coe v0))
-- Leios.Short._.IBs
d_IBs_684 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_684 ~v0 v1 = du_IBs_684 v1
du_IBs_684 ::
  T_GeneralizeTel_14419 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
du_IBs_684 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_IBs_546
      (coe d_'46'generalizedField'45's_14413 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_698 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_698 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_14413 (coe v1))
-- Leios.Short._.FFDState
d_FFDState_700 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 -> AgdaAny
d_FFDState_700 ~v0 v1 = du_FFDState_700 v1
du_FFDState_700 :: T_GeneralizeTel_14419 -> AgdaAny
du_FFDState_700 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_14413 (coe v0))
-- Leios.Short._.lookupEB
d_lookupEB_702 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_702 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_14413 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_704 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_704 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_14413 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_706 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_706 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_14413 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_708 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_708 = erased
-- Leios.Short._.slot
d_slot_710 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_14419 -> Integer
d_slot_710 ~v0 v1 = du_slot_710 v1
du_slot_710 :: T_GeneralizeTel_14419 -> Integer
du_slot_710 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_14413 (coe v0))
-- Leios.Short._.EBs
d_EBs_726 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_726 ~v0 v1 = du_EBs_726 v1
du_EBs_726 ::
  T_GeneralizeTel_19977 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_726 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_19973 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_746 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_746 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_19973 (coe v1))
-- Leios.Short._.FFDState
d_FFDState_748 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 -> AgdaAny
d_FFDState_748 ~v0 v1 = du_FFDState_748 v1
du_FFDState_748 :: T_GeneralizeTel_19977 -> AgdaAny
du_FFDState_748 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_19973 (coe v0))
-- Leios.Short._.lookupEB
d_lookupEB_750 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_750 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_19973 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_752 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_752 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_19973 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_754 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_754 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_19973 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_756 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_756 = erased
-- Leios.Short._.slot
d_slot_758 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_19977 -> Integer
d_slot_758 ~v0 v1 = du_slot_758 v1
du_slot_758 :: T_GeneralizeTel_19977 -> Integer
du_slot_758 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_19973 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_796 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21299 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_796 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_21297 (coe v1))
-- Leios.Short._.lookupEB
d_lookupEB_798 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21299 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_798 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_21297 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_800 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21299 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_800 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_21297 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_802 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21299 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_802 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_21297 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_804 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21299 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_804 = erased
-- Leios.Short._.slot
d_slot_806 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21299 -> Integer
d_slot_806 ~v0 v1 = du_slot_806 v1
du_slot_806 :: T_GeneralizeTel_21299 -> Integer
du_slot_806 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_21297 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_840 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21497 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_840 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_21495 (coe v1))
-- Leios.Short._.lookupEB
d_lookupEB_842 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21497 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_842 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_21495 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_844 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21497 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_844 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_21495 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_846 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21497 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_846 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_21495 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_848 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21497 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_848 = erased
-- Leios.Short._.slot
d_slot_850 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21497 -> Integer
d_slot_850 ~v0 v1 = du_slot_850 v1
du_slot_850 :: T_GeneralizeTel_21497 -> Integer
du_slot_850 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_21495 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_884 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21663 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_884 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_21661 (coe v1))
-- Leios.Short._.lookupEB
d_lookupEB_886 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21663 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_886 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_21661 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_888 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21663 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_888 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_21661 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_890 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21663 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_890 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_21661 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_892 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21663 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_892 = erased
-- Leios.Short._.slot
d_slot_894 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_21663 -> Integer
d_slot_894 ~v0 v1 = du_slot_894 v1
du_slot_894 :: T_GeneralizeTel_21663 -> Integer
du_slot_894 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_21661 (coe v0))
-- Leios.Short._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__900 a0 a1 a2 a3 a4 = ()
data T__'45''10214'_'47'_'10215''8640'__900
  = C_Init_902 AgdaAny [AgdaAny] AgdaAny
               MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 AgdaAny AgdaAny
               AgdaAny |
    C_Slot_944 [MAlonzo.Code.Data.These.Base.T_These_38] AgdaAny
               [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] AgdaAny
               MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 AgdaAny AgdaAny |
    C_Ftch_946 | C_Base'8321'_948 |
    C_Base'8322'a_992 MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
                      AgdaAny MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
                      AgdaAny |
    C_Base'8322'b_1036 AgdaAny AgdaAny | C_Roles_1038 T__'8605'__626
-- Leios.Short._.Upkeep
d_Upkeep_920 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 -> [T_SlotUpkeep_476]
d_Upkeep_920 ~v0 v1 = du_Upkeep_920 v1
du_Upkeep_920 :: T_GeneralizeTel_26555 -> [T_SlotUpkeep_476]
du_Upkeep_920 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_Upkeep_558
      (coe d_'46'generalizedField'45's_26545 (coe v0))
-- Leios.Short._.BaseState
d_BaseState_926 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 -> AgdaAny
d_BaseState_926 ~v0 v1 = du_BaseState_926 v1
du_BaseState_926 :: T_GeneralizeTel_26555 -> AgdaAny
du_BaseState_926 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_BaseState_560
      (coe d_'46'generalizedField'45's_26545 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_928 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_928 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_26545 (coe v1))
-- Leios.Short._.FFDState
d_FFDState_930 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 -> AgdaAny
d_FFDState_930 ~v0 v1 = du_FFDState_930 v1
du_FFDState_930 :: T_GeneralizeTel_26555 -> AgdaAny
du_FFDState_930 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_26545 (coe v0))
-- Leios.Short._.lookupEB
d_lookupEB_932 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_932 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_26545 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_934 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_934 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_26545 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_936 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_936 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_26545 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_938 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_938 = erased
-- Leios.Short._.slot
d_slot_940 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_26555 -> Integer
d_slot_940 ~v0 v1 = du_slot_940 v1
du_slot_940 :: T_GeneralizeTel_26555 -> Integer
du_slot_940 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_26545 (coe v0))
-- Leios.Short._.EBs
d_EBs_952 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_952 ~v0 v1 = du_EBs_952 v1
du_EBs_952 ::
  T_GeneralizeTel_34181 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_952 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_34175 (coe v0))
-- Leios.Short._.BaseState
d_BaseState_974 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 -> AgdaAny
d_BaseState_974 ~v0 v1 = du_BaseState_974 v1
du_BaseState_974 :: T_GeneralizeTel_34181 -> AgdaAny
du_BaseState_974 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_BaseState_560
      (coe d_'46'generalizedField'45's_34175 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_976 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_976 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_34175 (coe v1))
-- Leios.Short._.lookupEB
d_lookupEB_978 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_978 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_34175 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_980 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_980 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_34175 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_982 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_982 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_34175 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_984 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_984 = erased
-- Leios.Short._.slot
d_slot_986 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34181 -> Integer
d_slot_986 ~v0 v1 = du_slot_986 v1
du_slot_986 :: T_GeneralizeTel_34181 -> Integer
du_slot_986 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_34175 (coe v0))
-- Leios.Short._.EBs
d_EBs_996 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_996 ~v0 v1 = du_EBs_996 v1
du_EBs_996 ::
  T_GeneralizeTel_38965 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_996 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_38961 (coe v0))
-- Leios.Short._.ToPropose
d_ToPropose_1010 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 -> [AgdaAny]
d_ToPropose_1010 ~v0 v1 = du_ToPropose_1010 v1
du_ToPropose_1010 :: T_GeneralizeTel_38965 -> [AgdaAny]
du_ToPropose_1010 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_ToPropose_544
      (coe d_'46'generalizedField'45's_38961 (coe v0))
-- Leios.Short._.BaseState
d_BaseState_1018 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 -> AgdaAny
d_BaseState_1018 ~v0 v1 = du_BaseState_1018 v1
du_BaseState_1018 :: T_GeneralizeTel_38965 -> AgdaAny
du_BaseState_1018 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_BaseState_560
      (coe d_'46'generalizedField'45's_38961 (coe v0))
-- Leios.Short._.constructLedger
d_constructLedger_1020 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_1020 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_38961 (coe v1))
-- Leios.Short._.lookupEB
d_lookupEB_1022 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_1022 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_38961 (coe v1))
-- Leios.Short._.lookupIB
d_lookupIB_1024 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_1024 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_38961 (coe v1))
-- Leios.Short._.lookupTxs
d_lookupTxs_1026 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_1026 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_38961 (coe v1))
-- Leios.Short._.needsUpkeep
d_needsUpkeep_1028 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 -> T_SlotUpkeep_476 -> ()
d_needsUpkeep_1028 = erased
-- Leios.Short._.slot
d_slot_1030 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_38965 -> Integer
d_slot_1030 ~v0 v1 = du_slot_1030 v1
du_slot_1030 :: T_GeneralizeTel_38965 -> Integer
du_slot_1030 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_38961 (coe v0))
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_9507 ::
  T_GeneralizeTel_9513 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_9507 v0
  = case coe v0 of
      C_mkGeneralizeTel_9515 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-π
d_'46'generalizedField'45'π_9509 :: T_GeneralizeTel_9513 -> AgdaAny
d_'46'generalizedField'45'π_9509 v0
  = case coe v0 of
      C_mkGeneralizeTel_9515 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_9511 ::
  T_GeneralizeTel_9513 -> AgdaAny
d_'46'generalizedField'45'ffds''_9511 v0
  = case coe v0 of
      C_mkGeneralizeTel_9515 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_9513 a0 = ()
data T_GeneralizeTel_9513
  = C_mkGeneralizeTel_9515 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                           AgdaAny AgdaAny
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_14413 ::
  T_GeneralizeTel_14419 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_14413 v0
  = case coe v0 of
      C_mkGeneralizeTel_14421 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-π
d_'46'generalizedField'45'π_14415 ::
  T_GeneralizeTel_14419 -> AgdaAny
d_'46'generalizedField'45'π_14415 v0
  = case coe v0 of
      C_mkGeneralizeTel_14421 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_14417 ::
  T_GeneralizeTel_14419 -> AgdaAny
d_'46'generalizedField'45'ffds''_14417 v0
  = case coe v0 of
      C_mkGeneralizeTel_14421 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_14419 a0 = ()
data T_GeneralizeTel_14419
  = C_mkGeneralizeTel_14421 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny AgdaAny
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_19973 ::
  T_GeneralizeTel_19977 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_19973 v0
  = case coe v0 of
      C_mkGeneralizeTel_19979 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_19975 ::
  T_GeneralizeTel_19977 -> AgdaAny
d_'46'generalizedField'45'ffds''_19975 v0
  = case coe v0 of
      C_mkGeneralizeTel_19979 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_19977 a0 = ()
data T_GeneralizeTel_19977
  = C_mkGeneralizeTel_19979 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_21297 ::
  T_GeneralizeTel_21299 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_21297 v0
  = case coe v0 of
      C_mkGeneralizeTel_21301 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_21299 a0 = ()
newtype T_GeneralizeTel_21299
  = C_mkGeneralizeTel_21301 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_21495 ::
  T_GeneralizeTel_21497 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_21495 v0
  = case coe v0 of
      C_mkGeneralizeTel_21499 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_21497 a0 = ()
newtype T_GeneralizeTel_21497
  = C_mkGeneralizeTel_21499 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_21661 ::
  T_GeneralizeTel_21663 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_21661 v0
  = case coe v0 of
      C_mkGeneralizeTel_21665 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_21663 a0 = ()
newtype T_GeneralizeTel_21663
  = C_mkGeneralizeTel_21665 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_26545 ::
  T_GeneralizeTel_26555 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_26545 v0
  = case coe v0 of
      C_mkGeneralizeTel_26557 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-rbs
d_'46'generalizedField'45'rbs_26547 ::
  T_GeneralizeTel_26555 -> [MAlonzo.Code.Data.These.Base.T_These_38]
d_'46'generalizedField'45'rbs_26547 v0
  = case coe v0 of
      C_mkGeneralizeTel_26557 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-bs'
d_'46'generalizedField'45'bs''_26549 ::
  T_GeneralizeTel_26555 -> AgdaAny
d_'46'generalizedField'45'bs''_26549 v0
  = case coe v0 of
      C_mkGeneralizeTel_26557 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-msgs
d_'46'generalizedField'45'msgs_26551 ::
  T_GeneralizeTel_26555 -> [MAlonzo.Code.Data.Sum.Base.T__'8846'__30]
d_'46'generalizedField'45'msgs_26551 v0
  = case coe v0 of
      C_mkGeneralizeTel_26557 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_26553 ::
  T_GeneralizeTel_26555 -> AgdaAny
d_'46'generalizedField'45'ffds''_26553 v0
  = case coe v0 of
      C_mkGeneralizeTel_26557 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_26555 a0 = ()
data T_GeneralizeTel_26555
  = C_mkGeneralizeTel_26557 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            [MAlonzo.Code.Data.These.Base.T_These_38] AgdaAny
                            [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] AgdaAny
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_34175 ::
  T_GeneralizeTel_34181 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_34175 v0
  = case coe v0 of
      C_mkGeneralizeTel_34183 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-eb
d_'46'generalizedField'45'eb_34177 ::
  T_GeneralizeTel_34181 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_'46'generalizedField'45'eb_34177 v0
  = case coe v0 of
      C_mkGeneralizeTel_34183 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-bs'
d_'46'generalizedField'45'bs''_34179 ::
  T_GeneralizeTel_34181 -> AgdaAny
d_'46'generalizedField'45'bs''_34179 v0
  = case coe v0 of
      C_mkGeneralizeTel_34183 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_34181 a0 = ()
data T_GeneralizeTel_34181
  = C_mkGeneralizeTel_34183 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 AgdaAny
-- Leios.Short..generalizedField-s
d_'46'generalizedField'45's_38961 ::
  T_GeneralizeTel_38965 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_38961 v0
  = case coe v0 of
      C_mkGeneralizeTel_38967 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short..generalizedField-bs'
d_'46'generalizedField'45'bs''_38963 ::
  T_GeneralizeTel_38965 -> AgdaAny
d_'46'generalizedField'45'bs''_38963 v0
  = case coe v0 of
      C_mkGeneralizeTel_38967 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Short.GeneralizeTel
d_GeneralizeTel_38965 a0 = ()
data T_GeneralizeTel_38965
  = C_mkGeneralizeTel_38967 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny
