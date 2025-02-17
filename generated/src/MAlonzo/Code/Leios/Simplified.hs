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

module MAlonzo.Code.Leios.Simplified where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Axiom.Set
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.DecEq.Instances
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Leios.Base
import qualified MAlonzo.Code.Leios.Blocks
import qualified MAlonzo.Code.Leios.FFD
import qualified MAlonzo.Code.Leios.KeyRegistration
import qualified MAlonzo.Code.Leios.Prelude
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
-- Leios.Simplified.SlotUpkeep
d_SlotUpkeep_480 a0 a1 a2 = ()
data T_SlotUpkeep_480
  = C_Base_482 | C_IB'45'Role_484 | C_EB'45'Role_486 |
    C_V1'45'Role_488 | C_V2'45'Role_490
-- Leios.Simplified.DecEq-SlotUpkeep
d_DecEq'45'SlotUpkeep_492 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'SlotUpkeep_492 ~v0 ~v1 ~v2 = du_DecEq'45'SlotUpkeep_492
du_DecEq'45'SlotUpkeep_492 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'SlotUpkeep_492
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         (\ v0 ->
            case coe v0 of
              C_Base_482
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_482
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
                          C_IB'45'Role_484
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_EB'45'Role_486
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V1'45'Role_488
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V2'45'Role_490
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              C_IB'45'Role_484
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_482
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_IB'45'Role_484
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
                          C_EB'45'Role_486
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V1'45'Role_488
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V2'45'Role_490
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              C_EB'45'Role_486
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_482
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_IB'45'Role_484
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_EB'45'Role_486
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
                          C_V1'45'Role_488
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V2'45'Role_490
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              C_V1'45'Role_488
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_482
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_IB'45'Role_484
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_EB'45'Role_486
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V1'45'Role_488
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
                          C_V2'45'Role_490
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              C_V2'45'Role_490
                -> coe
                     (\ v1 ->
                        case coe v1 of
                          C_Base_482
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_IB'45'Role_484
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_EB'45'Role_486
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V1'45'Role_488
                            -> coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                          C_V2'45'Role_490
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
-- Leios.Simplified.allUpkeep
d_allUpkeep_494 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> [T_SlotUpkeep_480]
d_allUpkeep_494 ~v0 ~v1 ~v2 = du_allUpkeep_494
du_allUpkeep_494 :: [T_SlotUpkeep_480]
du_allUpkeep_494
  = coe
      MAlonzo.Code.Axiom.Set.du_fromList_428
      (coe
         MAlonzo.Code.Axiom.Set.d_th_1470
         (coe
            MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_Base_482)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_IB'45'Role_484)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_EB'45'Role_486)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_V1'45'Role_488)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_V2'45'Role_490)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Leios.Simplified._._↑_
d__'8593'__498 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d__'8593'__498 v0 ~v1 ~v2 = du__'8593'__498 v0
du__'8593'__498 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
du__'8593'__498 v0
  = coe MAlonzo.Code.Leios.Protocol.du__'8593'__878 (coe v0)
-- Leios.Simplified._.LeiosInput
d_LeiosInput_508 a0 a1 a2 = ()
-- Leios.Simplified._.LeiosOutput
d_LeiosOutput_510 a0 a1 a2 = ()
-- Leios.Simplified._.LeiosState
d_LeiosState_512 a0 a1 a2 = ()
-- Leios.Simplified._.addUpkeep
d_addUpkeep_518 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  T_SlotUpkeep_480 -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_addUpkeep_518 ~v0 ~v1 ~v2 = du_addUpkeep_518
du_addUpkeep_518 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  T_SlotUpkeep_480 -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506
du_addUpkeep_518 = coe MAlonzo.Code.Leios.Protocol.du_addUpkeep_594
-- Leios.Simplified._.allIBRefsKnown
d_allIBRefsKnown_520 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_allIBRefsKnown_520 = erased
-- Leios.Simplified._.initLeiosState
d_initLeiosState_522 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 ->
  AgdaAny -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_initLeiosState_522 v0 ~v1 ~v2 = du_initLeiosState_522 v0
du_initLeiosState_522 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  AgdaAny ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 ->
  AgdaAny -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506
du_initLeiosState_522 v0
  = coe MAlonzo.Code.Leios.Protocol.du_initLeiosState_640 (coe v0)
-- Leios.Simplified._.stake
d_stake_524 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_stake_524 v0 ~v1 ~v2 = du_stake_524 v0
du_stake_524 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
du_stake_524 v0
  = coe MAlonzo.Code.Leios.Protocol.du_stake_714 (coe v0)
-- Leios.Simplified._.upd
d_upd_526 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_upd_526 v0 ~v1 ~v2 = du_upd_526 v0
du_upd_526 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
du_upd_526 v0 = coe MAlonzo.Code.Leios.Protocol.du_upd_764 (coe v0)
-- Leios.Simplified._.upd-preserves-Upkeep
d_upd'45'preserves'45'Upkeep_528 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_upd'45'preserves'45'Upkeep_528 = erased
-- Leios.Simplified._.↑-preserves-Upkeep
d_'8593''45'preserves'45'Upkeep_530 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''45'preserves'45'Upkeep_530 = erased
-- Leios.Simplified._.LeiosState.BaseState
d_BaseState_550 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_BaseState_550 v0
  = coe MAlonzo.Code.Leios.Protocol.d_BaseState_560 (coe v0)
-- Leios.Simplified._.LeiosState.EBs
d_EBs_552 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_552 v0 = coe MAlonzo.Code.Leios.Protocol.d_EBs_548 (coe v0)
-- Leios.Simplified._.LeiosState.FFDState
d_FFDState_554 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_FFDState_554 v0
  = coe MAlonzo.Code.Leios.Protocol.d_FFDState_540 (coe v0)
-- Leios.Simplified._.LeiosState.IBBodies
d_IBBodies_556 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_556 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBBodies_556 (coe v0)
-- Leios.Simplified._.LeiosState.IBHeaders
d_IBHeaders_558 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_558 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBHeaders_554 (coe v0)
-- Leios.Simplified._.LeiosState.IBs
d_IBs_560 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_560 v0 = coe MAlonzo.Code.Leios.Protocol.d_IBs_546 (coe v0)
-- Leios.Simplified._.LeiosState.Ledger
d_Ledger_562 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [AgdaAny]
d_Ledger_562 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Ledger_542 (coe v0)
-- Leios.Simplified._.LeiosState.SD
d_SD_564 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_564 v0 = coe MAlonzo.Code.Leios.Protocol.d_SD_538 (coe v0)
-- Leios.Simplified._.LeiosState.ToPropose
d_ToPropose_566 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [AgdaAny]
d_ToPropose_566 v0
  = coe MAlonzo.Code.Leios.Protocol.d_ToPropose_544 (coe v0)
-- Leios.Simplified._.LeiosState.Upkeep
d_Upkeep_568 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [T_SlotUpkeep_480]
d_Upkeep_568 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Upkeep_558 (coe v0)
-- Leios.Simplified._.LeiosState.V
d_V_570 :: MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_V_570 v0 = coe MAlonzo.Code.Leios.Protocol.d_V_536 (coe v0)
-- Leios.Simplified._.LeiosState.Vs
d_Vs_572 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [[AgdaAny]]
d_Vs_572 v0 = coe MAlonzo.Code.Leios.Protocol.d_Vs_550 (coe v0)
-- Leios.Simplified._.LeiosState.constructLedger
d_constructLedger_574 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_574 v0 ~v1 ~v2 = du_constructLedger_574 v0
du_constructLedger_574 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_574 v0
  = coe MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
-- Leios.Simplified._.LeiosState.lookupEB
d_lookupEB_576 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_576 v0 ~v1 ~v2 = du_lookupEB_576 v0
du_lookupEB_576 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_576 v0
  = coe MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
-- Leios.Simplified._.LeiosState.lookupIB
d_lookupIB_578 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_578 v0 ~v1 ~v2 = du_lookupIB_578 v0
du_lookupIB_578 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_578 v0
  = coe MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
-- Leios.Simplified._.LeiosState.lookupTxs
d_lookupTxs_580 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_580 v0 ~v1 ~v2 = du_lookupTxs_580 v0
du_lookupTxs_580 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_580 v0
  = coe MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
-- Leios.Simplified._.LeiosState.needsUpkeep
d_needsUpkeep_582 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  T_SlotUpkeep_480 -> ()
d_needsUpkeep_582 = erased
-- Leios.Simplified._.LeiosState.slot
d_slot_584 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_slot_584 v0 = coe MAlonzo.Code.Leios.Protocol.d_slot_552 (coe v0)
-- Leios.Simplified._.LeiosState.votingState
d_votingState_586 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> AgdaAny
d_votingState_586 v0
  = coe MAlonzo.Code.Leios.Protocol.d_votingState_562 (coe v0)
-- Leios.Simplified._.V-chkCerts
d_V'45'chkCerts_592 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_V'45'chkCerts_592 v0 ~v1 ~v2 = du_V'45'chkCerts_592 v0
du_V'45'chkCerts_592 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
du_V'45'chkCerts_592 v0
  = coe
      MAlonzo.Code.Leios.Base.d_V'45'chkCerts_110
      (coe MAlonzo.Code.Leios.SpecStructure.d_B''_844 (coe v0))
-- Leios.Simplified._.VTy
d_VTy_594 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> ()
d_VTy_594 = erased
-- Leios.Simplified.isVote1Certified
d_isVote1Certified_598 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_isVote1Certified_598 = erased
-- Leios.Simplified.isVote2Certified
d_isVote2Certified_604 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_isVote2Certified_604 = erased
-- Leios.Simplified._._.constructLedger
d_constructLedger_658 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_658 v0 ~v1 ~v2 v3 ~v4
  = du_constructLedger_658 v0 v3
du_constructLedger_658 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_658 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe v1)
-- Leios.Simplified._._.lookupEB
d_lookupEB_660 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_660 v0 ~v1 ~v2 v3 ~v4 = du_lookupEB_660 v0 v3
du_lookupEB_660 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_660 v0 v1
  = coe MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0) (coe v1)
-- Leios.Simplified._._.lookupIB
d_lookupIB_662 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_662 v0 ~v1 ~v2 v3 ~v4 = du_lookupIB_662 v0 v3
du_lookupIB_662 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_662 v0 v1
  = coe MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0) (coe v1)
-- Leios.Simplified._._.lookupTxs
d_lookupTxs_664 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_664 v0 ~v1 ~v2 v3 ~v4 = du_lookupTxs_664 v0 v3
du_lookupTxs_664 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_664 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0) (coe v1)
-- Leios.Simplified._._.needsUpkeep
d_needsUpkeep_666 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  T_SlotUpkeep_480 -> ()
d_needsUpkeep_666 = erased
-- Leios.Simplified._.vote2Eligible
d_vote2Eligible_672 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_vote2Eligible_672 = erased
-- Leios.Simplified._._.candidateEBs
d_candidateEBs_678 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_candidateEBs_678 v0 ~v1 v2 v3 ~v4 = du_candidateEBs_678 v0 v2 v3
du_candidateEBs_678 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [AgdaAny]
du_candidateEBs_678 v0 v1 v2
  = coe
      MAlonzo.Code.Axiom.Set.du_map_398
      (MAlonzo.Code.Axiom.Set.d_th_1470
         (coe
            MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
      (coe
         MAlonzo.Code.Leios.Blocks.du_getEBRef_308
         (coe
            MAlonzo.Code.Leios.SpecStructure.d_Hashable'45'PreEndorserBlock_706
            (coe v0)))
      (coe
         MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.du_filter'738'_1160
         (\ v3 ->
            coe
              MAlonzo.Code.Axiom.Set.du_Dec'45''8712'_1672
              (coe
                 MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8)
              (coe MAlonzo.Code.Class.DecEq.Instances.d_DecEq'45'ℕ_22)
              (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v3))
              (coe
                 MAlonzo.Code.Leios.Prelude.du_slice_20
                 (coe
                    MAlonzo.Code.Leios.Abstract.d_L_62
                    (coe MAlonzo.Code.Leios.SpecStructure.d_a_480 (coe v0)))
                 (coe MAlonzo.Code.Leios.Protocol.d_slot_552 (coe v2))
                 (coe addInt (coe (3 :: Integer)) (coe v1))))
         (coe
            MAlonzo.Code.Axiom.Set.du_fromList_428
            (coe
               MAlonzo.Code.Axiom.Set.d_th_1470
               (coe
                  MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
            (coe MAlonzo.Code.Leios.Protocol.d_EBs_548 (coe v2))))
-- Leios.Simplified._↝_
d__'8605'__710 a0 a1 a2 a3 a4 = ()
data T__'8605'__710
  = C_IB'45'Role_756 AgdaAny AgdaAny
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 AgdaAny |
    C_EB'45'Role_808 AgdaAny AgdaAny
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 AgdaAny |
    C_V1'45'Role_856 AgdaAny MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                     AgdaAny |
    C_V2'45'Role_904 AgdaAny MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                     AgdaAny |
    C_No'45'IB'45'Role_948 | C_No'45'EB'45'Role_992 |
    C_No'45'V1'45'Role_1034 | C_No'45'V2'45'Role_1076
-- Leios.Simplified._.ToPropose
d_ToPropose_728 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_24713 -> [AgdaAny]
d_ToPropose_728 ~v0 ~v1 ~v2 v3 = du_ToPropose_728 v3
du_ToPropose_728 :: T_GeneralizeTel_24713 -> [AgdaAny]
du_ToPropose_728 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_ToPropose_544
      (coe d_'46'generalizedField'45's_24707 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_736 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_24713 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_736 v0 ~v1 ~v2 v3 = du_constructLedger_736 v0 v3
du_constructLedger_736 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_24713 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_736 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_24707 (coe v1))
-- Leios.Simplified._.FFDState
d_FFDState_738 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_24713 -> AgdaAny
d_FFDState_738 ~v0 ~v1 ~v2 v3 = du_FFDState_738 v3
du_FFDState_738 :: T_GeneralizeTel_24713 -> AgdaAny
du_FFDState_738 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_24707 (coe v0))
-- Leios.Simplified._.lookupEB
d_lookupEB_740 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_24713 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_740 v0 ~v1 ~v2 v3 = du_lookupEB_740 v0 v3
du_lookupEB_740 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_24713 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_740 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_24707 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_742 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_24713 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_742 v0 ~v1 ~v2 v3 = du_lookupIB_742 v0 v3
du_lookupIB_742 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_24713 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_742 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_24707 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_744 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_24713 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_744 v0 ~v1 ~v2 v3 = du_lookupTxs_744 v0 v3
du_lookupTxs_744 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_24713 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_744 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_24707 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_746 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_24713 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_746 = erased
-- Leios.Simplified._.slot
d_slot_748 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_24713 -> Integer
d_slot_748 ~v0 ~v1 ~v2 v3 = du_slot_748 v3
du_slot_748 :: T_GeneralizeTel_24713 -> Integer
du_slot_748 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_24707 (coe v0))
-- Leios.Simplified._.EBs
d_EBs_762 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_34887 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_762 ~v0 ~v1 ~v2 v3 = du_EBs_762 v3
du_EBs_762 ::
  T_GeneralizeTel_34887 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_762 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_34881 (coe v0))
-- Leios.Simplified._.IBs
d_IBs_768 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_34887 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_768 ~v0 ~v1 ~v2 v3 = du_IBs_768 v3
du_IBs_768 ::
  T_GeneralizeTel_34887 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
du_IBs_768 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_IBs_546
      (coe d_'46'generalizedField'45's_34881 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_782 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_34887 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_782 v0 ~v1 ~v2 v3 = du_constructLedger_782 v0 v3
du_constructLedger_782 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34887 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_782 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_34881 (coe v1))
-- Leios.Simplified._.FFDState
d_FFDState_784 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_34887 -> AgdaAny
d_FFDState_784 ~v0 ~v1 ~v2 v3 = du_FFDState_784 v3
du_FFDState_784 :: T_GeneralizeTel_34887 -> AgdaAny
du_FFDState_784 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_34881 (coe v0))
-- Leios.Simplified._.lookupEB
d_lookupEB_786 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_34887 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_786 v0 ~v1 ~v2 v3 = du_lookupEB_786 v0 v3
du_lookupEB_786 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34887 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_786 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_34881 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_788 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_34887 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_788 v0 ~v1 ~v2 v3 = du_lookupIB_788 v0 v3
du_lookupIB_788 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34887 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_788 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_34881 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_790 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_34887 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_790 v0 ~v1 ~v2 v3 = du_lookupTxs_790 v0 v3
du_lookupTxs_790 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_34887 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_790 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_34881 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_792 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_34887 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_792 = erased
-- Leios.Simplified._.slot
d_slot_794 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_34887 -> Integer
d_slot_794 ~v0 ~v1 ~v2 v3 = du_slot_794 v3
du_slot_794 :: T_GeneralizeTel_34887 -> Integer
du_slot_794 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_34881 (coe v0))
-- Leios.Simplified._.EBs
d_EBs_814 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_45873 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_814 ~v0 ~v1 ~v2 v3 = du_EBs_814 v3
du_EBs_814 ::
  T_GeneralizeTel_45873 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_814 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_45869 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_834 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_45873 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_834 v0 ~v1 ~v2 v3 = du_constructLedger_834 v0 v3
du_constructLedger_834 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_45873 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_834 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_45869 (coe v1))
-- Leios.Simplified._.FFDState
d_FFDState_836 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_45873 -> AgdaAny
d_FFDState_836 ~v0 ~v1 ~v2 v3 = du_FFDState_836 v3
du_FFDState_836 :: T_GeneralizeTel_45873 -> AgdaAny
du_FFDState_836 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_45869 (coe v0))
-- Leios.Simplified._.lookupEB
d_lookupEB_838 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_45873 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_838 v0 ~v1 ~v2 v3 = du_lookupEB_838 v0 v3
du_lookupEB_838 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_45873 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_838 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_45869 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_840 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_45873 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_840 v0 ~v1 ~v2 v3 = du_lookupIB_840 v0 v3
du_lookupIB_840 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_45873 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_840 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_45869 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_842 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_45873 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_842 v0 ~v1 ~v2 v3 = du_lookupTxs_842 v0 v3
du_lookupTxs_842 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_45873 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_842 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_45869 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_844 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_45873 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_844 = erased
-- Leios.Simplified._.slot
d_slot_846 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_45873 -> Integer
d_slot_846 ~v0 ~v1 ~v2 v3 = du_slot_846 v3
du_slot_846 :: T_GeneralizeTel_45873 -> Integer
du_slot_846 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_45869 (coe v0))
-- Leios.Simplified._.EBs
d_EBs_862 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_56461 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_862 ~v0 ~v1 ~v2 v3 = du_EBs_862 v3
du_EBs_862 ::
  T_GeneralizeTel_56461 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_862 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_56457 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_882 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_56461 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_882 v0 ~v1 ~v2 v3 = du_constructLedger_882 v0 v3
du_constructLedger_882 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_56461 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_882 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_56457 (coe v1))
-- Leios.Simplified._.FFDState
d_FFDState_884 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_56461 -> AgdaAny
d_FFDState_884 ~v0 ~v1 ~v2 v3 = du_FFDState_884 v3
du_FFDState_884 :: T_GeneralizeTel_56461 -> AgdaAny
du_FFDState_884 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_56457 (coe v0))
-- Leios.Simplified._.lookupEB
d_lookupEB_886 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_56461 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_886 v0 ~v1 ~v2 v3 = du_lookupEB_886 v0 v3
du_lookupEB_886 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_56461 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_886 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_56457 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_888 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_56461 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_888 v0 ~v1 ~v2 v3 = du_lookupIB_888 v0 v3
du_lookupIB_888 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_56461 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_888 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_56457 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_890 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_56461 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_890 v0 ~v1 ~v2 v3 = du_lookupTxs_890 v0 v3
du_lookupTxs_890 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_56461 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_890 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_56457 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_892 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_56461 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_892 = erased
-- Leios.Simplified._.slot
d_slot_894 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_56461 -> Integer
d_slot_894 ~v0 ~v1 ~v2 v3 = du_slot_894 v3
du_slot_894 :: T_GeneralizeTel_56461 -> Integer
du_slot_894 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_56457 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_932 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58349 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_932 v0 ~v1 ~v2 v3 = du_constructLedger_932 v0 v3
du_constructLedger_932 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58349 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_932 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_58347 (coe v1))
-- Leios.Simplified._.lookupEB
d_lookupEB_934 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58349 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_934 v0 ~v1 ~v2 v3 = du_lookupEB_934 v0 v3
du_lookupEB_934 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58349 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_934 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_58347 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_936 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58349 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_936 v0 ~v1 ~v2 v3 = du_lookupIB_936 v0 v3
du_lookupIB_936 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58349 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_936 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_58347 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_938 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58349 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_938 v0 ~v1 ~v2 v3 = du_lookupTxs_938 v0 v3
du_lookupTxs_938 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58349 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_938 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_58347 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_940 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_58349 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_940 = erased
-- Leios.Simplified._.slot
d_slot_942 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_58349 -> Integer
d_slot_942 ~v0 ~v1 ~v2 v3 = du_slot_942 v3
du_slot_942 :: T_GeneralizeTel_58349 -> Integer
du_slot_942 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_58347 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_976 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58683 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_976 v0 ~v1 ~v2 v3 = du_constructLedger_976 v0 v3
du_constructLedger_976 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58683 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_976 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_58681 (coe v1))
-- Leios.Simplified._.lookupEB
d_lookupEB_978 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58683 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_978 v0 ~v1 ~v2 v3 = du_lookupEB_978 v0 v3
du_lookupEB_978 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58683 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_978 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_58681 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_980 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58683 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_980 v0 ~v1 ~v2 v3 = du_lookupIB_980 v0 v3
du_lookupIB_980 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58683 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_980 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_58681 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_982 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58683 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_982 v0 ~v1 ~v2 v3 = du_lookupTxs_982 v0 v3
du_lookupTxs_982 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58683 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_982 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_58681 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_984 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_58683 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_984 = erased
-- Leios.Simplified._.slot
d_slot_986 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_58683 -> Integer
d_slot_986 ~v0 ~v1 ~v2 v3 = du_slot_986 v3
du_slot_986 :: T_GeneralizeTel_58683 -> Integer
du_slot_986 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_58681 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_1020 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58965 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_1020 v0 ~v1 ~v2 v3
  = du_constructLedger_1020 v0 v3
du_constructLedger_1020 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58965 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_1020 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_58963 (coe v1))
-- Leios.Simplified._.lookupEB
d_lookupEB_1022 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58965 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_1022 v0 ~v1 ~v2 v3 = du_lookupEB_1022 v0 v3
du_lookupEB_1022 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58965 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_1022 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_58963 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_1024 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58965 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_1024 v0 ~v1 ~v2 v3 = du_lookupIB_1024 v0 v3
du_lookupIB_1024 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58965 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_1024 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_58963 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_1026 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_58965 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_1026 v0 ~v1 ~v2 v3 = du_lookupTxs_1026 v0 v3
du_lookupTxs_1026 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_58965 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_1026 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_58963 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_1028 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_58965 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_1028 = erased
-- Leios.Simplified._.slot
d_slot_1030 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_58965 -> Integer
d_slot_1030 ~v0 ~v1 ~v2 v3 = du_slot_1030 v3
du_slot_1030 :: T_GeneralizeTel_58965 -> Integer
du_slot_1030 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_58963 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_1062 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_59247 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_1062 v0 ~v1 ~v2 v3
  = du_constructLedger_1062 v0 v3
du_constructLedger_1062 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_59247 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_1062 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_59245 (coe v1))
-- Leios.Simplified._.lookupEB
d_lookupEB_1064 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_59247 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_1064 v0 ~v1 ~v2 v3 = du_lookupEB_1064 v0 v3
du_lookupEB_1064 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_59247 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_1064 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_59245 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_1066 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_59247 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_1066 v0 ~v1 ~v2 v3 = du_lookupIB_1066 v0 v3
du_lookupIB_1066 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_59247 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_1066 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_59245 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_1068 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_59247 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_1068 v0 ~v1 ~v2 v3 = du_lookupTxs_1068 v0 v3
du_lookupTxs_1068 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_59247 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_1068 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_59245 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_1070 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_59247 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_1070 = erased
-- Leios.Simplified._.slot
d_slot_1072 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_59247 -> Integer
d_slot_1072 ~v0 ~v1 ~v2 v3 = du_slot_1072 v3
du_slot_1072 :: T_GeneralizeTel_59247 -> Integer
du_slot_1072 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_59245 (coe v0))
-- Leios.Simplified._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__1078 a0 a1 a2 a3 a4 a5 a6 = ()
data T__'45''10214'_'47'_'10215''8640'__1078
  = C_Init_1080 AgdaAny [AgdaAny] AgdaAny
                MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 AgdaAny AgdaAny
                AgdaAny |
    C_Slot_1122 [MAlonzo.Code.Data.These.Base.T_These_38] AgdaAny
                [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] AgdaAny
                MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 AgdaAny AgdaAny |
    C_Ftch_1124 | C_Base'8321'_1126 |
    C_Base'8322'a_1170 MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
                       AgdaAny MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
                       AgdaAny |
    C_Base'8322'b_1214 AgdaAny AgdaAny | C_Roles_1216 T__'8605'__710
-- Leios.Simplified._.Upkeep
d_Upkeep_1098 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_69185 -> [T_SlotUpkeep_480]
d_Upkeep_1098 ~v0 ~v1 ~v2 v3 = du_Upkeep_1098 v3
du_Upkeep_1098 :: T_GeneralizeTel_69185 -> [T_SlotUpkeep_480]
du_Upkeep_1098 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_Upkeep_558
      (coe d_'46'generalizedField'45's_69175 (coe v0))
-- Leios.Simplified._.BaseState
d_BaseState_1104 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_69185 -> AgdaAny
d_BaseState_1104 ~v0 ~v1 ~v2 v3 = du_BaseState_1104 v3
du_BaseState_1104 :: T_GeneralizeTel_69185 -> AgdaAny
du_BaseState_1104 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_BaseState_560
      (coe d_'46'generalizedField'45's_69175 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_1106 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_69185 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_1106 v0 ~v1 ~v2 v3
  = du_constructLedger_1106 v0 v3
du_constructLedger_1106 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_69185 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_1106 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_69175 (coe v1))
-- Leios.Simplified._.FFDState
d_FFDState_1108 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_69185 -> AgdaAny
d_FFDState_1108 ~v0 ~v1 ~v2 v3 = du_FFDState_1108 v3
du_FFDState_1108 :: T_GeneralizeTel_69185 -> AgdaAny
du_FFDState_1108 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_FFDState_540
      (coe d_'46'generalizedField'45's_69175 (coe v0))
-- Leios.Simplified._.lookupEB
d_lookupEB_1110 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_69185 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_1110 v0 ~v1 ~v2 v3 = du_lookupEB_1110 v0 v3
du_lookupEB_1110 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_69185 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_1110 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_69175 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_1112 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_69185 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_1112 v0 ~v1 ~v2 v3 = du_lookupIB_1112 v0 v3
du_lookupIB_1112 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_69185 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_1112 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_69175 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_1114 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_69185 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_1114 v0 ~v1 ~v2 v3 = du_lookupTxs_1114 v0 v3
du_lookupTxs_1114 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_69185 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_1114 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_69175 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_1116 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_69185 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_1116 = erased
-- Leios.Simplified._.slot
d_slot_1118 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_69185 -> Integer
d_slot_1118 ~v0 ~v1 ~v2 v3 = du_slot_1118 v3
du_slot_1118 :: T_GeneralizeTel_69185 -> Integer
du_slot_1118 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_69175 (coe v0))
-- Leios.Simplified._.EBs
d_EBs_1130 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_83471 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_1130 ~v0 ~v1 ~v2 v3 = du_EBs_1130 v3
du_EBs_1130 ::
  T_GeneralizeTel_83471 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_1130 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_83465 (coe v0))
-- Leios.Simplified._.BaseState
d_BaseState_1152 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_83471 -> AgdaAny
d_BaseState_1152 ~v0 ~v1 ~v2 v3 = du_BaseState_1152 v3
du_BaseState_1152 :: T_GeneralizeTel_83471 -> AgdaAny
du_BaseState_1152 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_BaseState_560
      (coe d_'46'generalizedField'45's_83465 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_1154 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_83471 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_1154 v0 ~v1 ~v2 v3
  = du_constructLedger_1154 v0 v3
du_constructLedger_1154 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_83471 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_1154 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_83465 (coe v1))
-- Leios.Simplified._.lookupEB
d_lookupEB_1156 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_83471 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_1156 v0 ~v1 ~v2 v3 = du_lookupEB_1156 v0 v3
du_lookupEB_1156 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_83471 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_1156 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_83465 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_1158 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_83471 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_1158 v0 ~v1 ~v2 v3 = du_lookupIB_1158 v0 v3
du_lookupIB_1158 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_83471 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_1158 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_83465 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_1160 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_83471 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_1160 v0 ~v1 ~v2 v3 = du_lookupTxs_1160 v0 v3
du_lookupTxs_1160 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_83471 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_1160 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_83465 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_1162 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_83471 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_1162 = erased
-- Leios.Simplified._.slot
d_slot_1164 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_83471 -> Integer
d_slot_1164 ~v0 ~v1 ~v2 v3 = du_slot_1164 v3
du_slot_1164 :: T_GeneralizeTel_83471 -> Integer
du_slot_1164 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_83465 (coe v0))
-- Leios.Simplified._.EBs
d_EBs_1174 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_92227 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_1174 ~v0 ~v1 ~v2 v3 = du_EBs_1174 v3
du_EBs_1174 ::
  T_GeneralizeTel_92227 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
du_EBs_1174 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_EBs_548
      (coe d_'46'generalizedField'45's_92223 (coe v0))
-- Leios.Simplified._.ToPropose
d_ToPropose_1188 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_92227 -> [AgdaAny]
d_ToPropose_1188 ~v0 ~v1 ~v2 v3 = du_ToPropose_1188 v3
du_ToPropose_1188 :: T_GeneralizeTel_92227 -> [AgdaAny]
du_ToPropose_1188 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_ToPropose_544
      (coe d_'46'generalizedField'45's_92223 (coe v0))
-- Leios.Simplified._.BaseState
d_BaseState_1196 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_92227 -> AgdaAny
d_BaseState_1196 ~v0 ~v1 ~v2 v3 = du_BaseState_1196 v3
du_BaseState_1196 :: T_GeneralizeTel_92227 -> AgdaAny
du_BaseState_1196 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_BaseState_560
      (coe d_'46'generalizedField'45's_92223 (coe v0))
-- Leios.Simplified._.constructLedger
d_constructLedger_1198 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_92227 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
d_constructLedger_1198 v0 ~v1 ~v2 v3
  = du_constructLedger_1198 v0 v3
du_constructLedger_1198 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_92227 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [AgdaAny]
du_constructLedger_1198 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0)
      (coe d_'46'generalizedField'45's_92223 (coe v1))
-- Leios.Simplified._.lookupEB
d_lookupEB_1200 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_92227 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_1200 v0 ~v1 ~v2 v3 = du_lookupEB_1200 v0 v3
du_lookupEB_1200 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_92227 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
du_lookupEB_1200 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0)
      (coe d_'46'generalizedField'45's_92223 (coe v1))
-- Leios.Simplified._.lookupIB
d_lookupIB_1202 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_92227 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_1202 v0 ~v1 ~v2 v3 = du_lookupIB_1202 v0 v3
du_lookupIB_1202 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_92227 ->
  AgdaAny -> Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
du_lookupIB_1202 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0)
      (coe d_'46'generalizedField'45's_92223 (coe v1))
-- Leios.Simplified._.lookupTxs
d_lookupTxs_1204 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer ->
  T_GeneralizeTel_92227 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
d_lookupTxs_1204 v0 ~v1 ~v2 v3 = du_lookupTxs_1204 v0 v3
du_lookupTxs_1204 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  T_GeneralizeTel_92227 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [AgdaAny]
du_lookupTxs_1204 v0 v1
  = coe
      MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0)
      (coe d_'46'generalizedField'45's_92223 (coe v1))
-- Leios.Simplified._.needsUpkeep
d_needsUpkeep_1206 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer ->
  Integer -> T_GeneralizeTel_92227 -> T_SlotUpkeep_480 -> ()
d_needsUpkeep_1206 = erased
-- Leios.Simplified._.slot
d_slot_1208 ::
  MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6 ->
  Integer -> Integer -> T_GeneralizeTel_92227 -> Integer
d_slot_1208 ~v0 ~v1 ~v2 v3 = du_slot_1208 v3
du_slot_1208 :: T_GeneralizeTel_92227 -> Integer
du_slot_1208 v0
  = coe
      MAlonzo.Code.Leios.Protocol.d_slot_552
      (coe d_'46'generalizedField'45's_92223 (coe v0))
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_24707 ::
  T_GeneralizeTel_24713 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_24707 v0
  = case coe v0 of
      C_mkGeneralizeTel_24715 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-π
d_'46'generalizedField'45'π_24709 ::
  T_GeneralizeTel_24713 -> AgdaAny
d_'46'generalizedField'45'π_24709 v0
  = case coe v0 of
      C_mkGeneralizeTel_24715 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_24711 ::
  T_GeneralizeTel_24713 -> AgdaAny
d_'46'generalizedField'45'ffds''_24711 v0
  = case coe v0 of
      C_mkGeneralizeTel_24715 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_24713 a0 a1 a2 = ()
data T_GeneralizeTel_24713
  = C_mkGeneralizeTel_24715 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny AgdaAny
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_34881 ::
  T_GeneralizeTel_34887 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_34881 v0
  = case coe v0 of
      C_mkGeneralizeTel_34889 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-π
d_'46'generalizedField'45'π_34883 ::
  T_GeneralizeTel_34887 -> AgdaAny
d_'46'generalizedField'45'π_34883 v0
  = case coe v0 of
      C_mkGeneralizeTel_34889 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_34885 ::
  T_GeneralizeTel_34887 -> AgdaAny
d_'46'generalizedField'45'ffds''_34885 v0
  = case coe v0 of
      C_mkGeneralizeTel_34889 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_34887 a0 a1 a2 = ()
data T_GeneralizeTel_34887
  = C_mkGeneralizeTel_34889 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny AgdaAny
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_45869 ::
  T_GeneralizeTel_45873 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_45869 v0
  = case coe v0 of
      C_mkGeneralizeTel_45875 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_45871 ::
  T_GeneralizeTel_45873 -> AgdaAny
d_'46'generalizedField'45'ffds''_45871 v0
  = case coe v0 of
      C_mkGeneralizeTel_45875 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_45873 a0 a1 a2 = ()
data T_GeneralizeTel_45873
  = C_mkGeneralizeTel_45875 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_56457 ::
  T_GeneralizeTel_56461 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_56457 v0
  = case coe v0 of
      C_mkGeneralizeTel_56463 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_56459 ::
  T_GeneralizeTel_56461 -> AgdaAny
d_'46'generalizedField'45'ffds''_56459 v0
  = case coe v0 of
      C_mkGeneralizeTel_56463 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_56461 a0 a1 a2 = ()
data T_GeneralizeTel_56461
  = C_mkGeneralizeTel_56463 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_58347 ::
  T_GeneralizeTel_58349 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_58347 v0
  = case coe v0 of
      C_mkGeneralizeTel_58351 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_58349 a0 a1 a2 = ()
newtype T_GeneralizeTel_58349
  = C_mkGeneralizeTel_58351 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_58681 ::
  T_GeneralizeTel_58683 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_58681 v0
  = case coe v0 of
      C_mkGeneralizeTel_58685 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_58683 a0 a1 a2 = ()
newtype T_GeneralizeTel_58683
  = C_mkGeneralizeTel_58685 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_58963 ::
  T_GeneralizeTel_58965 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_58963 v0
  = case coe v0 of
      C_mkGeneralizeTel_58967 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_58965 a0 a1 a2 = ()
newtype T_GeneralizeTel_58965
  = C_mkGeneralizeTel_58967 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_59245 ::
  T_GeneralizeTel_59247 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_59245 v0
  = case coe v0 of
      C_mkGeneralizeTel_59249 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_59247 a0 a1 a2 = ()
newtype T_GeneralizeTel_59247
  = C_mkGeneralizeTel_59249 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_69175 ::
  T_GeneralizeTel_69185 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_69175 v0
  = case coe v0 of
      C_mkGeneralizeTel_69187 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-rbs
d_'46'generalizedField'45'rbs_69177 ::
  T_GeneralizeTel_69185 -> [MAlonzo.Code.Data.These.Base.T_These_38]
d_'46'generalizedField'45'rbs_69177 v0
  = case coe v0 of
      C_mkGeneralizeTel_69187 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-bs'
d_'46'generalizedField'45'bs''_69179 ::
  T_GeneralizeTel_69185 -> AgdaAny
d_'46'generalizedField'45'bs''_69179 v0
  = case coe v0 of
      C_mkGeneralizeTel_69187 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-msgs
d_'46'generalizedField'45'msgs_69181 ::
  T_GeneralizeTel_69185 -> [MAlonzo.Code.Data.Sum.Base.T__'8846'__30]
d_'46'generalizedField'45'msgs_69181 v0
  = case coe v0 of
      C_mkGeneralizeTel_69187 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-ffds'
d_'46'generalizedField'45'ffds''_69183 ::
  T_GeneralizeTel_69185 -> AgdaAny
d_'46'generalizedField'45'ffds''_69183 v0
  = case coe v0 of
      C_mkGeneralizeTel_69187 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_69185 a0 a1 a2 = ()
data T_GeneralizeTel_69185
  = C_mkGeneralizeTel_69187 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            [MAlonzo.Code.Data.These.Base.T_These_38] AgdaAny
                            [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] AgdaAny
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_83465 ::
  T_GeneralizeTel_83471 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_83465 v0
  = case coe v0 of
      C_mkGeneralizeTel_83473 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-eb
d_'46'generalizedField'45'eb_83467 ::
  T_GeneralizeTel_83471 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_'46'generalizedField'45'eb_83467 v0
  = case coe v0 of
      C_mkGeneralizeTel_83473 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-bs'
d_'46'generalizedField'45'bs''_83469 ::
  T_GeneralizeTel_83471 -> AgdaAny
d_'46'generalizedField'45'bs''_83469 v0
  = case coe v0 of
      C_mkGeneralizeTel_83473 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_83471 a0 a1 a2 = ()
data T_GeneralizeTel_83471
  = C_mkGeneralizeTel_83473 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 AgdaAny
-- Leios.Simplified..generalizedField-s
d_'46'generalizedField'45's_92223 ::
  T_GeneralizeTel_92227 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_'46'generalizedField'45's_92223 v0
  = case coe v0 of
      C_mkGeneralizeTel_92229 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified..generalizedField-bs'
d_'46'generalizedField'45'bs''_92225 ::
  T_GeneralizeTel_92227 -> AgdaAny
d_'46'generalizedField'45'bs''_92225 v0
  = case coe v0 of
      C_mkGeneralizeTel_92229 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Simplified.GeneralizeTel
d_GeneralizeTel_92227 a0 a1 a2 = ()
data T_GeneralizeTel_92227
  = C_mkGeneralizeTel_92229 MAlonzo.Code.Leios.Protocol.T_LeiosState_506
                            AgdaAny
