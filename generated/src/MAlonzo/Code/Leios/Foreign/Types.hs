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
{-# LANGUAGE DuplicateRecordFields #-}

module MAlonzo.Code.Leios.Foreign.Types where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Axiom.Set
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Class.Computational
import qualified MAlonzo.Code.Class.Computational22
import qualified MAlonzo.Code.Class.Convertible
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.DecEq.Instances
import qualified MAlonzo.Code.Class.Decidable.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.HasHsType
import qualified MAlonzo.Code.Class.HasOrder.Core
import qualified MAlonzo.Code.Data.Char.Base
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Foreign.Haskell.Coerce
import qualified MAlonzo.Code.Foreign.Haskell.Either
import qualified MAlonzo.Code.Foreign.Haskell.Pair
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Leios.Base
import qualified MAlonzo.Code.Leios.Blocks
import qualified MAlonzo.Code.Leios.FFD
import qualified MAlonzo.Code.Leios.Foreign.BaseTypes
import qualified MAlonzo.Code.Leios.Foreign.Defaults
import qualified MAlonzo.Code.Leios.Foreign.HsTypes
import qualified MAlonzo.Code.Leios.Foreign.Util
import qualified MAlonzo.Code.Leios.Protocol
import qualified MAlonzo.Code.Leios.Short
import qualified MAlonzo.Code.Leios.Short.Deterministic
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory

import GHC.Generics (Generic)
data IBHeader = IBHeader {slotNumber :: Integer, producerID :: Integer, bodyHash :: Data.Text.Text }
  deriving (Show, Eq, Generic)
data EndorserBlock = EndorserBlock { slotNumber :: Integer, producerID :: Integer, ibRefs :: [Data.Text.Text] }
  deriving (Show, Eq, Generic)
data SlotUpkeep = Base  | IBRole  | EBRole  | VRole 
  deriving (Show, Eq, Generic)
data IBBody = IBBody {txs :: [Integer]}
  deriving (Show, Eq, Generic)
data InputBlock = InputBlock {header :: MAlonzo.Code.Leios.Foreign.Types.IBHeader, body :: MAlonzo.Code.Leios.Foreign.Types.IBBody}
  deriving (Show, Eq, Generic)
data FFDState = FFDState {inIBs :: [MAlonzo.Code.Leios.Foreign.Types.InputBlock], inEBs :: [MAlonzo.Code.Leios.Foreign.Types.EndorserBlock], inVTs :: [[()]], outIBs :: [MAlonzo.Code.Leios.Foreign.Types.InputBlock], outEBs :: [MAlonzo.Code.Leios.Foreign.Types.EndorserBlock], outVTs :: [[()]]}
  deriving (Show, Eq, Generic)
data LeiosState = LeiosState {v :: (), sD :: (MAlonzo.Code.Leios.Foreign.HsTypes.HSMap Integer Integer), fFDState :: MAlonzo.Code.Leios.Foreign.Types.FFDState, ledger :: [Integer], toPropose :: [Integer], iBs :: [MAlonzo.Code.Leios.Foreign.Types.InputBlock], eBs :: [MAlonzo.Code.Leios.Foreign.Types.EndorserBlock], vs :: [[()]], slot :: Integer, iBHeaders :: [MAlonzo.Code.Leios.Foreign.Types.IBHeader], iBBodies :: [MAlonzo.Code.Leios.Foreign.Types.IBBody], upkeep :: (MAlonzo.Code.Leios.Foreign.HsTypes.HSSet MAlonzo.Code.Leios.Foreign.Types.SlotUpkeep), baseState :: (), votingState :: ()}
  deriving (Show, Eq, Generic)
data LeiosInput = I_INIT () | I_SUBMIT (Either MAlonzo.Code.Leios.Foreign.Types.EndorserBlock [Integer]) | I_SLOT  | I_FTCHLDG 
  deriving (Show, Eq, Generic)
data LeiosOutput = O_FTCHLDG [Integer] | O_EMPTY 
  deriving (Show, Eq, Generic)
-- Leios.Foreign.Types.dropDash
d_dropDash_6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_dropDash_6 v0
  = coe
      MAlonzo.Code.Data.String.Base.d_concat_28
      (coe
         MAlonzo.Code.Data.String.Base.d_wordsBy'7495'_110
         (MAlonzo.Code.Data.Char.Base.d__'8776''7495'__14 (coe '-')) v0)
-- Leios.Foreign.Types.prefix
d_prefix_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_prefix_10 v0
  = coe MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
-- Leios.Foreign.Types.HsTy-SlotUpkeep
d_HsTy'45'SlotUpkeep_16 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'SlotUpkeep_16 = erased
-- Leios.Foreign.Types.Conv-SlotUpkeep
d_Conv'45'SlotUpkeep_18 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'SlotUpkeep_18
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Short.C_Base_478 -> coe C_Base_103
              MAlonzo.Code.Leios.Short.C_IB'45'Role_480 -> coe C_IBRole_105
              MAlonzo.Code.Leios.Short.C_EB'45'Role_482 -> coe C_EBRole_107
              MAlonzo.Code.Leios.Short.C_V'45'Role_484 -> coe C_VRole_109
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              C_Base_103 -> coe MAlonzo.Code.Leios.Short.C_Base_478
              C_IBRole_105 -> coe MAlonzo.Code.Leios.Short.C_IB'45'Role_480
              C_EBRole_107 -> coe MAlonzo.Code.Leios.Short.C_EB'45'Role_482
              C_VRole_109 -> coe MAlonzo.Code.Leios.Short.C_V'45'Role_484
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.IBHeader
d_IBHeader_20 = ()
type T_IBHeader_20 = IBHeader
pattern C_IBHeader'46'constructor_243 a0 a1 a2 = IBHeader a0 a1 a2
check_IBHeader'46'constructor_243 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_IBHeader_20
check_IBHeader'46'constructor_243 = IBHeader
cover_IBHeader_20 :: IBHeader -> ()
cover_IBHeader_20 x
  = case x of
      IBHeader _ _ _ -> ()
-- Leios.Foreign.Types.IBHeader.slotNumber
d_slotNumber_28 :: T_IBHeader_20 -> Integer
d_slotNumber_28 v0
  = case coe v0 of
      C_IBHeader'46'constructor_243 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Types.IBHeader.producerID
d_producerID_30 :: T_IBHeader_20 -> Integer
d_producerID_30 v0
  = case coe v0 of
      C_IBHeader'46'constructor_243 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Types.IBHeader.bodyHash
d_bodyHash_32 ::
  T_IBHeader_20 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_bodyHash_32 v0
  = case coe v0 of
      C_IBHeader'46'constructor_243 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Types.HsTy-IBHeader
d_HsTy'45'IBHeader_34 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'IBHeader_34 = erased
-- Leios.Foreign.Types.Conv-IBHeader
d_Conv'45'IBHeader_36 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'IBHeader_36
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            coe
              C_IBHeader'46'constructor_243
              (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_94 (coe v0))
              (coe
                 MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                 (coe MAlonzo.Code.Leios.Blocks.d_producerID_96 (coe v0)))
              (coe MAlonzo.Code.Leios.Blocks.d_bodyHash_100 (coe v0))))
      (coe
         (\ v0 ->
            let v1
                  = coe
                      MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                      (\ v1 v2 ->
                         coe
                           MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                              (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2)))
                      (d_producerID_30 (coe v0))
                      MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
            coe
              (case coe v1 of
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
                   -> if coe v2
                        then coe
                               seq (coe v3)
                               (coe
                                  MAlonzo.Code.Leios.Blocks.C_IBHeaderOSig'46'constructor_591
                                  (coe d_slotNumber_28 (coe v0))
                                  (coe
                                     MAlonzo.Code.Data.Fin.du_'35'__10
                                     (coe d_producerID_30 (coe v0)))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe d_bodyHash_32 (coe v0))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                        else coe
                               seq (coe v3)
                               (coe
                                  MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                  ("Conversion to Fin not possible!" :: Data.Text.Text))
                 _ -> MAlonzo.RTE.mazUnreachableError)))
-- Leios.Foreign.Types.HsTy-IBBody
d_HsTy'45'IBBody_58 :: MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'IBBody_58 = erased
-- Leios.Foreign.Types.Conv-IBBody
d_Conv'45'IBBody_60 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'IBBody_60
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Blocks.C_IBBody'46'constructor_795 v1
                -> coe
                     C_IBBody_1511
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v1)
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              C_IBBody_1511 v1
                -> coe
                     MAlonzo.Code.Leios.Blocks.C_IBBody'46'constructor_795
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v1)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.HsTy-InputBlock
d_HsTy'45'InputBlock_62 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'InputBlock_62 = erased
-- Leios.Foreign.Types.Conv-InputBlock
d_Conv'45'InputBlock_64 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'InputBlock_64
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Blocks.C_InputBlock'46'constructor_823 v1 v2
                -> coe
                     C_InputBlock_1835
                     (coe
                        C_IBHeader'46'constructor_243
                        (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_94 (coe v1))
                        (coe
                           MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                           (coe MAlonzo.Code.Leios.Blocks.d_producerID_96 (coe v1)))
                        (coe MAlonzo.Code.Leios.Blocks.d_bodyHash_100 (coe v1)))
                     (coe
                        C_IBBody_1511
                        (coe
                           MAlonzo.Code.Class.Functor.Core.du_fmap_22
                           MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                           () erased
                           (MAlonzo.Code.Class.Convertible.d_to_18
                              (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                           (MAlonzo.Code.Leios.Blocks.d_txs_112 (coe v2))))
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              C_InputBlock_1835 v1 v2
                -> coe
                     MAlonzo.Code.Leios.Blocks.C_InputBlock'46'constructor_823
                     (let v3
                            = coe
                                MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                (\ v3 v4 ->
                                   coe
                                     MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                        (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))
                                (d_producerID_30 (coe v1))
                                MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                      coe
                        (case coe v3 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                             -> if coe v4
                                  then coe
                                         seq (coe v5)
                                         (coe
                                            MAlonzo.Code.Leios.Blocks.C_IBHeaderOSig'46'constructor_591
                                            (coe d_slotNumber_28 (coe v1))
                                            (coe
                                               MAlonzo.Code.Data.Fin.du_'35'__10
                                               (coe d_producerID_30 (coe v1)))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe d_bodyHash_32 (coe v1))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                  else coe
                                         seq (coe v5)
                                         (coe
                                            MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                            ("Conversion to Fin not possible!" :: Data.Text.Text))
                           _ -> MAlonzo.RTE.mazUnreachableError))
                     (coe
                        MAlonzo.Code.Class.Convertible.d_from_20
                        (coe
                           MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                           (coe
                              (\ v3 ->
                                 case coe v3 of
                                   MAlonzo.Code.Leios.Blocks.C_IBBody'46'constructor_795 v4
                                     -> coe
                                          C_IBBody_1511
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_to_18
                                                (coe
                                                   MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                                             v4)
                                   _ -> MAlonzo.RTE.mazUnreachableError))
                           (coe
                              (\ v3 ->
                                 case coe v3 of
                                   C_IBBody_1511 v4
                                     -> coe
                                          MAlonzo.Code.Leios.Blocks.C_IBBody'46'constructor_795
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_from_20
                                                (coe
                                                   MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                                             v4)
                                   _ -> MAlonzo.RTE.mazUnreachableError)))
                        v2)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.Conv-ℕ
d_Conv'45'ℕ_66 :: MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'ℕ_66
  = coe MAlonzo.Code.Class.Convertible.du_Convertible'45'Refl_36
-- Leios.Foreign.Types.EndorserBlock
d_EndorserBlock_68 = ()
type T_EndorserBlock_68 = EndorserBlock
pattern C_EndorserBlock'46'constructor_2385 a0 a1 a2 = EndorserBlock a0 a1 a2
check_EndorserBlock'46'constructor_2385 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    () MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_EndorserBlock_68
check_EndorserBlock'46'constructor_2385 = EndorserBlock
cover_EndorserBlock_68 :: EndorserBlock -> ()
cover_EndorserBlock_68 x
  = case x of
      EndorserBlock _ _ _ -> ()
-- Leios.Foreign.Types.EndorserBlock.slotNumber
d_slotNumber_76 :: T_EndorserBlock_68 -> Integer
d_slotNumber_76 v0
  = case coe v0 of
      C_EndorserBlock'46'constructor_2385 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Types.EndorserBlock.producerID
d_producerID_78 :: T_EndorserBlock_68 -> Integer
d_producerID_78 v0
  = case coe v0 of
      C_EndorserBlock'46'constructor_2385 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Types.EndorserBlock.ibRefs
d_ibRefs_80 ::
  T_EndorserBlock_68 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ibRefs_80 v0
  = case coe v0 of
      C_EndorserBlock'46'constructor_2385 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Types.HsTy-EndorserBlock
d_HsTy'45'EndorserBlock_82 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'EndorserBlock_82 = erased
-- Leios.Foreign.Types.Conv-EndorserBlock
d_Conv'45'EndorserBlock_84 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'EndorserBlock_84
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            coe
              C_EndorserBlock'46'constructor_2385
              (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v0))
              (coe
                 MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                 (coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v0)))
              (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v0))))
      (coe
         (\ v0 ->
            let v1
                  = coe
                      MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                      (\ v1 v2 ->
                         coe
                           MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                              (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2)))
                      (d_producerID_78 (coe v0))
                      MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
            coe
              (case coe v1 of
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
                   -> if coe v2
                        then coe
                               seq (coe v3)
                               (coe
                                  MAlonzo.Code.Leios.Blocks.C_EndorserBlockOSig'46'constructor_3013
                                  (coe d_slotNumber_76 (coe v0))
                                  (coe
                                     MAlonzo.Code.Data.Fin.du_'35'__10
                                     (coe d_producerID_78 (coe v0)))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe d_ibRefs_80 (coe v0))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                        else coe
                               seq (coe v3)
                               (coe
                                  MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                  ("Conversion to Fin not possible!" :: Data.Text.Text))
                 _ -> MAlonzo.RTE.mazUnreachableError)))
-- Leios.Foreign.Types.SlotUpkeep
d_SlotUpkeep_101 = ()
type T_SlotUpkeep_101 = SlotUpkeep
pattern C_Base_103 = Base
pattern C_IBRole_105 = IBRole
pattern C_EBRole_107 = EBRole
pattern C_VRole_109 = VRole
check_Base_103 :: T_SlotUpkeep_101
check_Base_103 = Base
check_IBRole_105 :: T_SlotUpkeep_101
check_IBRole_105 = IBRole
check_EBRole_107 :: T_SlotUpkeep_101
check_EBRole_107 = EBRole
check_VRole_109 :: T_SlotUpkeep_101
check_VRole_109 = VRole
cover_SlotUpkeep_101 :: SlotUpkeep -> ()
cover_SlotUpkeep_101 x
  = case x of
      Base -> ()
      IBRole -> ()
      EBRole -> ()
      VRole -> ()
-- Leios.Foreign.Types.Listable-Fin
d_Listable'45'Fin_106 ::
  MAlonzo.Code.Leios.Foreign.BaseTypes.T_Listable_90
d_Listable'45'Fin_106
  = coe
      MAlonzo.Code.Leios.Foreign.BaseTypes.C_Listable'46'constructor_10891
      (coe
         MAlonzo.Code.Axiom.Set.du_singleton_448
         (coe
            MAlonzo.Code.Axiom.Set.d_th_1470
            (coe
               MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1724
              (coe
                 MAlonzo.Code.Axiom.Set.du_'8712''45'singleton_458
                 (coe
                    MAlonzo.Code.Axiom.Set.d_th_1470
                    (coe
                       MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
                 (coe v0) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
              erased))
-- Leios.Foreign.Types._.a≡zero
d_a'8801'zero_114 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'8801'zero_114 = erased
-- Leios.Foreign.Types.HsTy-FFDState
d_HsTy'45'FFDState_118 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'FFDState_118 = erased
-- Leios.Foreign.Types.Conv-FFDState
d_Conv'45'FFDState_120 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'FFDState_120
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6
                -> coe
                     C_FFDState_4023
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe d_Conv'45'InputBlock_64))
                        v1)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v7 ->
                           coe
                             C_EndorserBlock'46'constructor_2385
                             (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v7))
                             (coe
                                MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                (coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v7)))
                             (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v7)))
                        v2)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe
                                 MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                        v3)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe d_Conv'45'InputBlock_64))
                        v4)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v7 ->
                           coe
                             C_EndorserBlock'46'constructor_2385
                             (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v7))
                             (coe
                                MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                (coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v7)))
                             (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v7)))
                        v5)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe
                                 MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                        v6)
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              C_FFDState_4023 v1 v2 v3 v4 v5 v6
                -> coe
                     MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe d_Conv'45'InputBlock_64))
                        v1)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v7 ->
                           let v8
                                 = coe
                                     MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                     (\ v8 v9 ->
                                        coe
                                          MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                             (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9)))
                                     (d_producerID_78 (coe v7))
                                     MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                           coe
                             (case coe v8 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                  -> if coe v9
                                       then coe
                                              seq (coe v10)
                                              (coe
                                                 MAlonzo.Code.Leios.Blocks.C_EndorserBlockOSig'46'constructor_3013
                                                 (coe d_slotNumber_76 (coe v7))
                                                 (coe
                                                    MAlonzo.Code.Data.Fin.du_'35'__10
                                                    (coe d_producerID_78 (coe v7)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe d_ibRefs_80 (coe v7))
                                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       else coe
                                              seq (coe v10)
                                              (coe
                                                 MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                                 ("Conversion to Fin not possible!"
                                                  ::
                                                  Data.Text.Text))
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        v2)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe
                                 MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                        v3)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe d_Conv'45'InputBlock_64))
                        v4)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v7 ->
                           let v8
                                 = coe
                                     MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                     (\ v8 v9 ->
                                        coe
                                          MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                             (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9)))
                                     (d_producerID_78 (coe v7))
                                     MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                           coe
                             (case coe v8 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                  -> if coe v9
                                       then coe
                                              seq (coe v10)
                                              (coe
                                                 MAlonzo.Code.Leios.Blocks.C_EndorserBlockOSig'46'constructor_3013
                                                 (coe d_slotNumber_76 (coe v7))
                                                 (coe
                                                    MAlonzo.Code.Data.Fin.du_'35'__10
                                                    (coe d_producerID_78 (coe v7)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe d_ibRefs_80 (coe v7))
                                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       else coe
                                              seq (coe v10)
                                              (coe
                                                 MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                                 ("Conversion to Fin not possible!"
                                                  ::
                                                  Data.Text.Text))
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        v5)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe
                                 MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                 (coe (\ v7 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                        v6)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.HsTy-Fin
d_HsTy'45'Fin_122 :: MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'Fin_122 = erased
-- Leios.Foreign.Types.Conv-Fin
d_Conv'45'Fin_124 :: MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'Fin_124
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18)
      (coe
         (\ v0 ->
            let v1
                  = coe
                      MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                      (\ v1 v2 ->
                         coe
                           MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                              (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2)))
                      v0 MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
            coe
              (case coe v1 of
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
                   -> if coe v2
                        then coe
                               seq (coe v3) (coe MAlonzo.Code.Data.Fin.du_'35'__10 (coe v0))
                        else coe
                               seq (coe v3)
                               (coe
                                  MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                  ("Conversion to Fin not possible!" :: Data.Text.Text))
                 _ -> MAlonzo.RTE.mazUnreachableError)))
-- Leios.Foreign.Types.HsTy-LeiosState
d_HsTy'45'LeiosState_132 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'LeiosState_132 = erased
-- Leios.Foreign.Types.Conv-LeiosState
d_Conv'45'LeiosState_134 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'LeiosState_134
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Protocol.C_LeiosState'46'constructor_2273 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                -> coe
                     C_LeiosState_10685 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Leios.Foreign.HsTypes.C_MkHSMap_26
                        (coe
                           MAlonzo.Code.Class.Convertible.d_to_18
                           (coe
                              MAlonzo.Code.Leios.Foreign.BaseTypes.du_Convertible'45'FinSet_50
                              (coe
                                 MAlonzo.Code.Class.Convertible.du_Convertible'45'Pair_96
                                 (coe d_Conv'45'Fin_124)
                                 (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8)))
                           (MAlonzo.Code.Axiom.Set.TotalMap.d_rel_180 (coe v2))))
                     (coe
                        C_FFDState_4023
                        (coe
                           MAlonzo.Code.Class.Functor.Core.du_fmap_22
                           MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                           () erased
                           (MAlonzo.Code.Class.Convertible.d_to_18
                              (coe d_Conv'45'InputBlock_64))
                           (MAlonzo.Code.Leios.Foreign.Defaults.d_inIBs_704 (coe v3)))
                        (coe
                           MAlonzo.Code.Class.Functor.Core.du_fmap_22
                           MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                           () erased
                           (\ v15 ->
                              coe
                                C_EndorserBlock'46'constructor_2385
                                (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v15))
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                   (coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v15)))
                                (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v15)))
                           (MAlonzo.Code.Leios.Foreign.Defaults.d_inEBs_706 (coe v3)))
                        (coe
                           MAlonzo.Code.Class.Functor.Core.du_fmap_22
                           MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                           () erased
                           (MAlonzo.Code.Class.Convertible.d_to_18
                              (coe
                                 MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                                 (coe
                                    MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                    (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                    (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                           (MAlonzo.Code.Leios.Foreign.Defaults.d_inVTs_708 (coe v3)))
                        (coe
                           MAlonzo.Code.Class.Functor.Core.du_fmap_22
                           MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                           () erased
                           (MAlonzo.Code.Class.Convertible.d_to_18
                              (coe d_Conv'45'InputBlock_64))
                           (MAlonzo.Code.Leios.Foreign.Defaults.d_outIBs_710 (coe v3)))
                        (coe
                           MAlonzo.Code.Class.Functor.Core.du_fmap_22
                           MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                           () erased
                           (\ v15 ->
                              coe
                                C_EndorserBlock'46'constructor_2385
                                (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v15))
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                   (coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v15)))
                                (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v15)))
                           (MAlonzo.Code.Leios.Foreign.Defaults.d_outEBs_712 (coe v3)))
                        (coe
                           MAlonzo.Code.Class.Functor.Core.du_fmap_22
                           MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                           () erased
                           (MAlonzo.Code.Class.Convertible.d_to_18
                              (coe
                                 MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                                 (coe
                                    MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                    (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                    (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                           (MAlonzo.Code.Leios.Foreign.Defaults.d_outVTs_714 (coe v3))))
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v4)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v5)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe d_Conv'45'InputBlock_64))
                        v6)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v15 ->
                           coe
                             C_EndorserBlock'46'constructor_2385
                             (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v15))
                             (coe
                                MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                (coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v15)))
                             (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v15)))
                        v7)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe
                                 MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                 (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                 (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                        v8)
                     (coe v9)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v15 ->
                           coe
                             C_IBHeader'46'constructor_243
                             (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_94 (coe v15))
                             (coe
                                MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                (coe MAlonzo.Code.Leios.Blocks.d_producerID_96 (coe v15)))
                             (coe MAlonzo.Code.Leios.Blocks.d_bodyHash_100 (coe v15)))
                        v10)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18 (coe d_Conv'45'IBBody_60))
                        v11)
                     (coe
                        MAlonzo.Code.Leios.Foreign.HsTypes.C_MkHSSet_38
                        (coe
                           MAlonzo.Code.Class.Convertible.d_to_18
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe d_Conv'45'SlotUpkeep_18))
                           v12))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              C_LeiosState_10685 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                -> coe
                     MAlonzo.Code.Leios.Protocol.C_LeiosState'46'constructor_2273
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Class.Convertible.d_from_20
                        (coe
                           MAlonzo.Code.Leios.Foreign.BaseTypes.du_Convertible'45'TotalMap_168
                           (coe MAlonzo.Code.Class.DecEq.Instances.du_DecEq'45'Fin_52)
                           (coe d_Listable'45'Fin_106) (coe d_Conv'45'Fin_124)
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        (MAlonzo.Code.Leios.Foreign.HsTypes.d_assocList_24 (coe v2)))
                     (coe
                        MAlonzo.Code.Class.Convertible.d_from_20
                        (coe
                           MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                           (coe
                              (\ v15 ->
                                 case coe v15 of
                                   MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539 v16 v17 v18 v19 v20 v21
                                     -> coe
                                          C_FFDState_4023
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_to_18
                                                (coe d_Conv'45'InputBlock_64))
                                             v16)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (\ v22 ->
                                                coe
                                                  C_EndorserBlock'46'constructor_2385
                                                  (coe
                                                     MAlonzo.Code.Leios.Blocks.d_slotNumber_232
                                                     (coe v22))
                                                  (coe
                                                     MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                                     (coe
                                                        MAlonzo.Code.Leios.Blocks.d_producerID_234
                                                        (coe v22)))
                                                  (coe
                                                     MAlonzo.Code.Leios.Blocks.d_ibRefs_238
                                                     (coe v22)))
                                             v17)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_to_18
                                                (coe
                                                   MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                                                   (coe
                                                      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                                             v18)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_to_18
                                                (coe d_Conv'45'InputBlock_64))
                                             v19)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (\ v22 ->
                                                coe
                                                  C_EndorserBlock'46'constructor_2385
                                                  (coe
                                                     MAlonzo.Code.Leios.Blocks.d_slotNumber_232
                                                     (coe v22))
                                                  (coe
                                                     MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                                     (coe
                                                        MAlonzo.Code.Leios.Blocks.d_producerID_234
                                                        (coe v22)))
                                                  (coe
                                                     MAlonzo.Code.Leios.Blocks.d_ibRefs_238
                                                     (coe v22)))
                                             v20)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_to_18
                                                (coe
                                                   MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                                                   (coe
                                                      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                                             v21)
                                   _ -> MAlonzo.RTE.mazUnreachableError))
                           (coe
                              (\ v15 ->
                                 case coe v15 of
                                   C_FFDState_4023 v16 v17 v18 v19 v20 v21
                                     -> coe
                                          MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_from_20
                                                (coe d_Conv'45'InputBlock_64))
                                             v16)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (\ v22 ->
                                                let v23
                                                      = coe
                                                          MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                                          (\ v23 v24 ->
                                                             coe
                                                               MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v23))
                                                                  (coe v24)))
                                                          (d_producerID_78 (coe v22))
                                                          MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                                                coe
                                                  (case coe v23 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                       -> if coe v24
                                                            then coe
                                                                   seq (coe v25)
                                                                   (coe
                                                                      MAlonzo.Code.Leios.Blocks.C_EndorserBlockOSig'46'constructor_3013
                                                                      (coe
                                                                         d_slotNumber_76 (coe v22))
                                                                      (coe
                                                                         MAlonzo.Code.Data.Fin.du_'35'__10
                                                                         (coe
                                                                            d_producerID_78
                                                                            (coe v22)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                      (coe d_ibRefs_80 (coe v22))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                            else coe
                                                                   seq (coe v25)
                                                                   (coe
                                                                      MAlonzo.Code.Leios.Foreign.Util.d_error_8
                                                                      erased
                                                                      ("Conversion to Fin not possible!"
                                                                       ::
                                                                       Data.Text.Text))
                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                             v17)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_from_20
                                                (coe
                                                   MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                                                   (coe
                                                      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                                             v18)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_from_20
                                                (coe d_Conv'45'InputBlock_64))
                                             v19)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (\ v22 ->
                                                let v23
                                                      = coe
                                                          MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                                          (\ v23 v24 ->
                                                             coe
                                                               MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v23))
                                                                  (coe v24)))
                                                          (d_producerID_78 (coe v22))
                                                          MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                                                coe
                                                  (case coe v23 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                       -> if coe v24
                                                            then coe
                                                                   seq (coe v25)
                                                                   (coe
                                                                      MAlonzo.Code.Leios.Blocks.C_EndorserBlockOSig'46'constructor_3013
                                                                      (coe
                                                                         d_slotNumber_76 (coe v22))
                                                                      (coe
                                                                         MAlonzo.Code.Data.Fin.du_'35'__10
                                                                         (coe
                                                                            d_producerID_78
                                                                            (coe v22)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                      (coe d_ibRefs_80 (coe v22))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                            else coe
                                                                   seq (coe v25)
                                                                   (coe
                                                                      MAlonzo.Code.Leios.Foreign.Util.d_error_8
                                                                      erased
                                                                      ("Conversion to Fin not possible!"
                                                                       ::
                                                                       Data.Text.Text))
                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                             v20)
                                          (coe
                                             MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                             MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                             () erased () erased
                                             (MAlonzo.Code.Class.Convertible.d_from_20
                                                (coe
                                                   MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                                                   (coe
                                                      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe
                                                         (\ v22 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                                             v21)
                                   _ -> MAlonzo.RTE.mazUnreachableError)))
                        v3)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v4)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v5)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe d_Conv'45'InputBlock_64))
                        v6)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v15 ->
                           let v16
                                 = coe
                                     MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                     (\ v16 v17 ->
                                        coe
                                          MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                             (coe addInt (coe (1 :: Integer)) (coe v16)) (coe v17)))
                                     (d_producerID_78 (coe v15))
                                     MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                           coe
                             (case coe v16 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                  -> if coe v17
                                       then coe
                                              seq (coe v18)
                                              (coe
                                                 MAlonzo.Code.Leios.Blocks.C_EndorserBlockOSig'46'constructor_3013
                                                 (coe d_slotNumber_76 (coe v15))
                                                 (coe
                                                    MAlonzo.Code.Data.Fin.du_'35'__10
                                                    (coe d_producerID_78 (coe v15)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe d_ibRefs_80 (coe v15))
                                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       else coe
                                              seq (coe v18)
                                              (coe
                                                 MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                                 ("Conversion to Fin not possible!"
                                                  ::
                                                  Data.Text.Text))
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        v7)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe
                                 MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
                                 (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                 (coe (\ v15 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                        v8)
                     (coe v9)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (\ v15 ->
                           let v16
                                 = coe
                                     MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                     (\ v16 v17 ->
                                        coe
                                          MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                             (coe addInt (coe (1 :: Integer)) (coe v16)) (coe v17)))
                                     (d_producerID_30 (coe v15))
                                     MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                           coe
                             (case coe v16 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                  -> if coe v17
                                       then coe
                                              seq (coe v18)
                                              (coe
                                                 MAlonzo.Code.Leios.Blocks.C_IBHeaderOSig'46'constructor_591
                                                 (coe d_slotNumber_28 (coe v15))
                                                 (coe
                                                    MAlonzo.Code.Data.Fin.du_'35'__10
                                                    (coe d_producerID_30 (coe v15)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe d_bodyHash_32 (coe v15))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       else coe
                                              seq (coe v18)
                                              (coe
                                                 MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                                 ("Conversion to Fin not possible!"
                                                  ::
                                                  Data.Text.Text))
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        v10)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe d_Conv'45'IBBody_60))
                        v11)
                     (coe
                        MAlonzo.Code.Axiom.Set.du_fromList_428
                        (coe
                           MAlonzo.Code.Axiom.Set.d_th_1470
                           (coe
                              MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
                        (coe
                           MAlonzo.Code.Class.Convertible.d_from_20
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe d_Conv'45'SlotUpkeep_18))
                           (MAlonzo.Code.Leios.Foreign.HsTypes.d_elems_36 (coe v12))))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.HsTy-LeiosInput
d_HsTy'45'LeiosInput_136 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'LeiosInput_136 = erased
-- Leios.Foreign.Types.Conv-LeiosInput
d_Conv'45'LeiosInput_138 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'LeiosInput_138
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Protocol.C_INIT_492 v1
                -> coe C_I_INIT_36785 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
              MAlonzo.Code.Leios.Protocol.C_SUBMIT_494 v1
                -> coe
                     C_I_SUBMIT_36811
                     (coe
                        MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 () erased () erased
                        (coe MAlonzo.Code.Foreign.Haskell.Coerce.du_either'45'toFFI_96)
                        (coe
                           MAlonzo.Code.Data.Sum.Base.du_map_84
                           (\ v2 ->
                              coe
                                C_EndorserBlock'46'constructor_2385
                                (coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v2))
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                   (coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v2)))
                                (coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v2)))
                           (MAlonzo.Code.Class.Convertible.d_to_18
                              (coe
                                 MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                                 (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8)))
                           v1))
              MAlonzo.Code.Leios.Protocol.C_SLOT_496 -> coe C_I_SLOT_36855
              MAlonzo.Code.Leios.Protocol.C_FTCH'45'LDG_498
                -> coe C_I_FTCHLDG_36857
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              C_I_INIT_36785 v1
                -> coe
                     MAlonzo.Code.Leios.Protocol.C_INIT_492
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
              C_I_SUBMIT_36811 v1
                -> coe
                     MAlonzo.Code.Leios.Protocol.C_SUBMIT_494
                     (coe
                        MAlonzo.Code.Data.Sum.Base.du_map_84
                        (\ v2 ->
                           let v3
                                 = coe
                                     MAlonzo.Code.Class.HasOrder.Core.du__'60''63'__64
                                     (\ v3 v4 ->
                                        coe
                                          MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
                                             (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))
                                     (d_producerID_78 (coe v2))
                                     MAlonzo.Code.Leios.Foreign.Defaults.d_numberOfParties_182 in
                           coe
                             (case coe v3 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                                  -> if coe v4
                                       then coe
                                              seq (coe v5)
                                              (coe
                                                 MAlonzo.Code.Leios.Blocks.C_EndorserBlockOSig'46'constructor_3013
                                                 (coe d_slotNumber_76 (coe v2))
                                                 (coe
                                                    MAlonzo.Code.Data.Fin.du_'35'__10
                                                    (coe d_producerID_78 (coe v2)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe d_ibRefs_80 (coe v2))
                                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       else coe
                                              seq (coe v5)
                                              (coe
                                                 MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                                 ("Conversion to Fin not possible!"
                                                  ::
                                                  Data.Text.Text))
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe
                              MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106
                              (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8)))
                        (coe
                           MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 () erased () erased
                           (coe MAlonzo.Code.Foreign.Haskell.Coerce.C_TrustMe_40) v1))
              C_I_SLOT_36855 -> coe MAlonzo.Code.Leios.Protocol.C_SLOT_496
              C_I_FTCHLDG_36857
                -> coe MAlonzo.Code.Leios.Protocol.C_FTCH'45'LDG_498
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.HsTy-LeiosOutput
d_HsTy'45'LeiosOutput_140 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'LeiosOutput_140 = erased
-- Leios.Foreign.Types.Conv-LeiosOutput
d_Conv'45'LeiosOutput_142 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'LeiosOutput_142
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Protocol.C_FTCH'45'LDG_502 v1
                -> coe
                     C_O_FTCHLDG_37799
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_to_18
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v1)
              MAlonzo.Code.Leios.Protocol.C_EMPTY_504 -> coe C_O_EMPTY_37819
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              C_O_FTCHLDG_37799 v1
                -> coe
                     MAlonzo.Code.Leios.Protocol.C_FTCH'45'LDG_502
                     (coe
                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                        () erased
                        (MAlonzo.Code.Class.Convertible.d_from_20
                           (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvNat_8))
                        v1)
              C_O_EMPTY_37819 -> coe MAlonzo.Code.Leios.Protocol.C_EMPTY_504
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.Computational-B
d_Computational'45'B_144 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26
d_Computational'45'B_144
  = coe
      MAlonzo.Code.Class.Computational22.C_MkComputational_86
      (\ v0 v1 ->
         case coe v1 of
           MAlonzo.Code.Leios.Base.C_INIT_114 v2
             -> coe
                  MAlonzo.Code.Class.Computational.C_success_36
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Leios.Base.C_STAKE_122
                           (coe MAlonzo.Code.Leios.Foreign.Defaults.d_sd_1016))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
           MAlonzo.Code.Leios.Base.C_SUBMIT_116 v2
             -> coe
                  MAlonzo.Code.Class.Computational.C_success_36
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Leios.Base.C_EMPTY_124)
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
           MAlonzo.Code.Leios.Base.C_FTCH'45'LDG_118
             -> coe
                  MAlonzo.Code.Class.Computational.C_success_36
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Leios.Base.C_BASE'45'LDG_126
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Leios.Foreign.Types.Computational-FFD
d_Computational'45'FFD_156 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26
d_Computational'45'FFD_156
  = coe
      MAlonzo.Code.Class.Computational22.C_MkComputational_86
      (\ v0 v1 ->
         let v2
               = coe
                   MAlonzo.Code.Class.Computational.C_failure_38
                   (coe ("FFD error" :: Data.Text.Text)) in
         coe
           (case coe v1 of
              MAlonzo.Code.Leios.FFD.C_Send_28 v3 v4
                -> case coe v3 of
                     MAlonzo.Code.Leios.Blocks.C_ibHeader_336 v5
                       -> case coe v4 of
                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                              -> case coe v6 of
                                   MAlonzo.Code.Leios.Blocks.C_ibBody_344 v7
                                     -> coe
                                          MAlonzo.Code.Class.Computational.C_success_36
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe MAlonzo.Code.Leios.FFD.C_SendRes_34)
                                                (coe
                                                   MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539
                                                   (coe
                                                      MAlonzo.Code.Leios.Foreign.Defaults.d_inIBs_704
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Leios.Foreign.Defaults.d_inEBs_706
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Leios.Foreign.Defaults.d_inVTs_708
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Leios.Blocks.C_InputBlock'46'constructor_823
                                                         (coe v5) (coe v7))
                                                      (coe
                                                         MAlonzo.Code.Leios.Foreign.Defaults.d_outIBs_710
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Leios.Foreign.Defaults.d_outEBs_712
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Leios.Foreign.Defaults.d_outVTs_714
                                                      (coe v0))))
                                             (coe MAlonzo.Code.Leios.Foreign.Defaults.C_SendIB_744))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> coe v2
                     MAlonzo.Code.Leios.Blocks.C_ebHeader_338 v5
                       -> case coe v4 of
                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              -> coe
                                   MAlonzo.Code.Class.Computational.C_success_36
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe MAlonzo.Code.Leios.FFD.C_SendRes_34)
                                         (coe
                                            MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_inIBs_704
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_inEBs_706
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_inVTs_708
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_outIBs_710
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                               (coe
                                                  MAlonzo.Code.Leios.Foreign.Defaults.d_outEBs_712
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_outVTs_714
                                               (coe v0))))
                                      (coe MAlonzo.Code.Leios.Foreign.Defaults.C_SendEB_750))
                            _ -> coe v2
                     MAlonzo.Code.Leios.Blocks.C_vHeader_340 v5
                       -> case coe v4 of
                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              -> coe
                                   MAlonzo.Code.Class.Computational.C_success_36
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe MAlonzo.Code.Leios.FFD.C_SendRes_34)
                                         (coe
                                            MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_inIBs_704
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_inEBs_706
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_inVTs_708
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_outIBs_710
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Leios.Foreign.Defaults.d_outEBs_712
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                               (coe
                                                  MAlonzo.Code.Leios.Foreign.Defaults.d_outVTs_714
                                                  (coe v0)))))
                                      (coe MAlonzo.Code.Leios.Foreign.Defaults.C_SendVS_756))
                            _ -> coe v2
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Leios.FFD.C_Fetch_30
                -> coe
                     MAlonzo.Code.Class.Computational.C_success_36
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Leios.FFD.C_FetchRes_36
                              (coe MAlonzo.Code.Leios.Foreign.Defaults.d_flushIns_716 (coe v0)))
                           (coe
                              MAlonzo.Code.Leios.Foreign.Defaults.C_FFDState'46'constructor_1539
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              (coe MAlonzo.Code.Leios.Foreign.Defaults.d_outIBs_710 (coe v0))
                              (coe MAlonzo.Code.Leios.Foreign.Defaults.d_outEBs_712 (coe v0))
                              (coe MAlonzo.Code.Leios.Foreign.Defaults.d_outVTs_714 (coe v0))))
                        (coe MAlonzo.Code.Leios.Foreign.Defaults.C_Fetch_782))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.Types.D._-⟦_/_⟧ⁿᵈ*⇀_
d__'45''10214'_'47'_'10215''8319''7496''42''8640'__176 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Protocol.T_LeiosInput_490] ->
  [MAlonzo.Code.Leios.Protocol.T_LeiosOutput_500] ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> ()
d__'45''10214'_'47'_'10215''8319''7496''42''8640'__176 = erased
-- Leios.Foreign.Types.D._-⟦_/_⟧ⁿᵈ⇀_
d__'45''10214'_'47'_'10215''8319''7496''8640'__178 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosInput_490 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosOutput_500 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> ()
d__'45''10214'_'47'_'10215''8319''7496''8640'__178 = erased
-- Leios.Foreign.Types.D._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__180 a0 a1 a2 a3 = ()
-- Leios.Foreign.Types.D._-⟦Base⟧⇀_
d__'45''10214'Base'10215''8640'__182 a0 a1 = ()
-- Leios.Foreign.Types.D._-⟦EB-Role⟧⇀_
d__'45''10214'EB'45'Role'10215''8640'__184 a0 a1 = ()
-- Leios.Foreign.Types.D._-⟦IB-Role⟧⇀_
d__'45''10214'IB'45'Role'10215''8640'__186 a0 a1 = ()
-- Leios.Foreign.Types.D._-⟦V-Role⟧⇀_
d__'45''10214'V'45'Role'10215''8640'__188 a0 a1 = ()
-- Leios.Foreign.Types.D._⊢_
d__'8866'__190 a0 a1 = ()
-- Leios.Foreign.Types.D.Base-Upkeep
d_Base'45'Upkeep_192 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'Base'10215''8640'__888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Base'45'Upkeep_192 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_Base'45'Upkeep_1064 v2
-- Leios.Foreign.Types.D.Base-total
d_Base'45'total_194 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Base'45'total_194 v0 v1
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_Base'45'total_998
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834) v0
-- Leios.Foreign.Types.D.Base⇒ND
d_Base'8658'ND_202 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'Base'10215''8640'__888 ->
  MAlonzo.Code.Leios.Short.T__'45''10214'_'47'_'10215''8640'__900
d_Base'8658'ND_202 v0 v1 v2
  = coe MAlonzo.Code.Leios.Short.Deterministic.du_Base'8658'ND_980 v2
-- Leios.Foreign.Types.D.Computational--⟦/⟧⇀
d_Computational'45''45''10214''47''10215''8640'_204 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26
d_Computational'45''45''10214''47''10215''8640'_204
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.d_Computational'45''45''10214''47''10215''8640'_1756
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
-- Leios.Foreign.Types.D.EB-Role-Upkeep
d_EB'45'Role'45'Upkeep_208 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'EB'45'Role'10215''8640'__1258 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_EB'45'Role'45'Upkeep_208 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_EB'45'Role'45'Upkeep_1420
      v2
-- Leios.Foreign.Types.D.EB-Role-total
d_EB'45'Role'45'total_210 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_EB'45'Role'45'total_210 v0 v1
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_EB'45'Role'45'total_1366
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834) v0
-- Leios.Foreign.Types.D.EB-Role⇒ND
d_EB'45'Role'8658'ND_212 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'EB'45'Role'10215''8640'__1258 ->
  MAlonzo.Code.Leios.Short.T__'45''10214'_'47'_'10215''8640'__900
d_EB'45'Role'8658'ND_212 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_EB'45'Role'8658'ND_1352
      v2
-- Leios.Foreign.Types.D.IB-Role-Upkeep
d_IB'45'Role'45'Upkeep_218 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'IB'45'Role'10215''8640'__1082 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_IB'45'Role'45'Upkeep_218 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_IB'45'Role'45'Upkeep_1242
      v2
-- Leios.Foreign.Types.D.IB-Role-total
d_IB'45'Role'45'total_220 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_IB'45'Role'45'total_220 v0 v1
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_IB'45'Role'45'total_1188
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834) v0
-- Leios.Foreign.Types.D.IB-Role⇒ND
d_IB'45'Role'8658'ND_222 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'IB'45'Role'10215''8640'__1082 ->
  MAlonzo.Code.Leios.Short.T__'45''10214'_'47'_'10215''8640'__900
d_IB'45'Role'8658'ND_222 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_IB'45'Role'8658'ND_1174
      v2
-- Leios.Foreign.Types.D.V-Role-Upkeep
d_V'45'Role'45'Upkeep_236 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'V'45'Role'10215''8640'__1436 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_V'45'Role'45'Upkeep_236 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_V'45'Role'45'Upkeep_1594
      v2
-- Leios.Foreign.Types.D.V-Role-total
d_V'45'Role'45'total_238 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_V'45'Role'45'total_238 v0 v1
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_V'45'Role'45'total_1542
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834) v0
-- Leios.Foreign.Types.D.V-Role⇒ND
d_V'45'Role'8658'ND_240 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.Deterministic.T__'45''10214'V'45'Role'10215''8640'__1436 ->
  MAlonzo.Code.Leios.Short.T__'45''10214'_'47'_'10215''8640'__900
d_V'45'Role'8658'ND_240 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.du_V'45'Role'8658'ND_1528 v2
-- Leios.Foreign.Types.D.addUpkeep⇒¬needsUpkeep
d_addUpkeep'8658''172'needsUpkeep_242 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.T_SlotUpkeep_476 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_addUpkeep'8658''172'needsUpkeep_242 = erased
-- Leios.Foreign.Types.D.a≢b→a∉b
d_a'8802'b'8594'a'8713'b_244 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_a'8802'b'8594'a'8713'b_244 = erased
-- Leios.Foreign.Types.D.bs
d_bs_246 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_bs_246
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.d_bs_1860
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
-- Leios.Foreign.Types.D.lemma
d_lemma_248 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.T_SlotUpkeep_476 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lemma_248
  = coe MAlonzo.Code.Leios.Short.Deterministic.du_lemma_870
-- Leios.Foreign.Types.D.sd
d_sd_250 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_sd_250
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.d_sd_1858
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
-- Leios.Foreign.Types.D.test₁
d_test'8321'_252 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_test'8321'_252
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.d_test'8321'_1866
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
-- Leios.Foreign.Types.D.test₂
d_test'8322'_254 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_test'8322'_254
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.d_test'8322'_1872
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
-- Leios.Foreign.Types.D.trace
d_trace_256 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_trace_256
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.d_trace_1874
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
-- Leios.Foreign.Types.D.upd-Upkeep
d_upd'45'Upkeep_258 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_upd'45'Upkeep_258 = erased
-- Leios.Foreign.Types.D.v
d_v_260 ::
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Class.Computational22.T_Computational22_26 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_v_260
  = coe
      MAlonzo.Code.Leios.Short.Deterministic.d_v_1856
      (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
-- Leios.Foreign.Types.D.↑-Upkeep
d_'8593''45'Upkeep_262 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''45'Upkeep_262 = erased
-- Leios.Foreign.Types.D.ND._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__302 a0 a1 a2 a3 = ()
-- Leios.Foreign.Types.D.ND._↑_
d__'8593'__304 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d__'8593'__304
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du__'8593'__878 (coe v0))
-- Leios.Foreign.Types.D.ND._↝_
d__'8605'__306 a0 a1 = ()
-- Leios.Foreign.Types.D.ND.DecEq-SlotUpkeep
d_DecEq'45'SlotUpkeep_316 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'SlotUpkeep_316
  = coe MAlonzo.Code.Leios.Short.du_DecEq'45'SlotUpkeep_486
-- Leios.Foreign.Types.D.ND.LeiosInput
d_LeiosInput_338 = ()
-- Leios.Foreign.Types.D.ND.LeiosOutput
d_LeiosOutput_340 = ()
-- Leios.Foreign.Types.D.ND.LeiosState
d_LeiosState_342 = ()
-- Leios.Foreign.Types.D.ND.SlotUpkeep
d_SlotUpkeep_358 = ()
-- Leios.Foreign.Types.D.ND.addUpkeep
d_addUpkeep_364 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.T_SlotUpkeep_476 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_addUpkeep_364 = coe MAlonzo.Code.Leios.Protocol.du_addUpkeep_594
-- Leios.Foreign.Types.D.ND.allIBRefsKnown
d_allIBRefsKnown_366 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_allIBRefsKnown_366 = erased
-- Leios.Foreign.Types.D.ND.allUpkeep
d_allUpkeep_368 :: [MAlonzo.Code.Leios.Short.T_SlotUpkeep_476]
d_allUpkeep_368 = coe MAlonzo.Code.Leios.Short.du_allUpkeep_488
-- Leios.Foreign.Types.D.ND.initLeiosState
d_initLeiosState_370 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_initLeiosState_370
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe
      (coe MAlonzo.Code.Leios.Protocol.du_initLeiosState_640 (coe v0))
-- Leios.Foreign.Types.D.ND.isVoteCertified
d_isVoteCertified_372 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_isVoteCertified_372 = erased
-- Leios.Foreign.Types.D.ND.stake
d_stake_374 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_stake_374
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_stake_714 (coe v0))
-- Leios.Foreign.Types.D.ND.upd
d_upd_376 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_upd_376
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_upd_764 (coe v0))
-- Leios.Foreign.Types.D.ND.upd-preserves-Upkeep
d_upd'45'preserves'45'Upkeep_378 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_upd'45'preserves'45'Upkeep_378 = erased
-- Leios.Foreign.Types.D.ND.↑-preserves-Upkeep
d_'8593''45'preserves'45'Upkeep_380 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''45'preserves'45'Upkeep_380 = erased
-- Leios.Foreign.Types.D.ND.LeiosState.BaseState
d_BaseState_430 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_BaseState_430 v0
  = coe MAlonzo.Code.Leios.Protocol.d_BaseState_560 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.EBs
d_EBs_432 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_432 v0 = coe MAlonzo.Code.Leios.Protocol.d_EBs_548 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.FFDState
d_FFDState_434 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Foreign.Defaults.T_FFDState_690
d_FFDState_434 v0
  = coe MAlonzo.Code.Leios.Protocol.d_FFDState_540 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.IBBodies
d_IBBodies_436 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_436 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBBodies_556 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.IBHeaders
d_IBHeaders_438 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_438 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBHeaders_554 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.IBs
d_IBs_440 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_440 v0 = coe MAlonzo.Code.Leios.Protocol.d_IBs_546 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.Ledger
d_Ledger_442 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [Integer]
d_Ledger_442 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Ledger_542 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.SD
d_SD_444 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_444 v0 = coe MAlonzo.Code.Leios.Protocol.d_SD_538 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.ToPropose
d_ToPropose_446 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [Integer]
d_ToPropose_446 v0
  = coe MAlonzo.Code.Leios.Protocol.d_ToPropose_544 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.Upkeep
d_Upkeep_448 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Short.T_SlotUpkeep_476]
d_Upkeep_448 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Upkeep_558 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.V
d_V_450 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_V_450 v0 = coe MAlonzo.Code.Leios.Protocol.d_V_536 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.Vs
d_Vs_452 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]]
d_Vs_452 v0 = coe MAlonzo.Code.Leios.Protocol.d_Vs_550 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.constructLedger
d_constructLedger_454 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [Integer]
d_constructLedger_454
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe
      (coe MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0))
-- Leios.Foreign.Types.D.ND.LeiosState.lookupEB
d_lookupEB_456 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_456
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0))
-- Leios.Foreign.Types.D.ND.LeiosState.lookupIB
d_lookupIB_458 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_458
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0))
-- Leios.Foreign.Types.D.ND.LeiosState.lookupTxs
d_lookupTxs_460 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [Integer]
d_lookupTxs_460
  = let v0 = MAlonzo.Code.Leios.Foreign.Defaults.d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0))
-- Leios.Foreign.Types.D.ND.LeiosState.needsUpkeep
d_needsUpkeep_462 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.T_SlotUpkeep_476 -> ()
d_needsUpkeep_462 = erased
-- Leios.Foreign.Types.D.ND.LeiosState.slot
d_slot_464 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_slot_464 v0 = coe MAlonzo.Code.Leios.Protocol.d_slot_552 (coe v0)
-- Leios.Foreign.Types.D.ND.LeiosState.votingState
d_votingState_466 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_votingState_466 v0
  = coe MAlonzo.Code.Leios.Protocol.d_votingState_562 (coe v0)
-- Leios.Foreign.Types.stepHs
step ::
  T_LeiosState_10683 ->
  T_LeiosInput_36783 ->
  MAlonzo.Code.Leios.Foreign.HsTypes.T_ComputationResult_44
    MAlonzo.Code.Agda.Builtin.String.T_String_6
    (MAlonzo.Code.Foreign.Haskell.Pair.T_Pair_22
       () () T_LeiosOutput_37797 T_LeiosState_10683)
step = coe d_stepHs_478
d_stepHs_478 ::
  T_LeiosState_10683 ->
  T_LeiosInput_36783 ->
  MAlonzo.Code.Leios.Foreign.HsTypes.T_ComputationResult_44
    MAlonzo.Code.Agda.Builtin.String.T_String_6
    (MAlonzo.Code.Foreign.Haskell.Pair.T_Pair_22
       AgdaAny AgdaAny T_LeiosOutput_37797 T_LeiosState_10683)
d_stepHs_478 v0
  = coe
      MAlonzo.Code.Class.Convertible.d_to_18
      (coe
         MAlonzo.Code.Class.Convertible.du_Convertible'45'Fun_118
         (coe d_Conv'45'LeiosInput_138)
         (coe
            MAlonzo.Code.Leios.Foreign.BaseTypes.du_Conv'45'ComputationResult_220
            (coe MAlonzo.Code.Leios.Foreign.BaseTypes.d_iConvString_10)
            (coe
               MAlonzo.Code.Class.Convertible.du_Convertible'45'Pair_96
               (coe d_Conv'45'LeiosOutput_142) (coe d_Conv'45'LeiosState_134))))
      (coe
         MAlonzo.Code.Class.Computational22.du_compute_70
         (coe
            MAlonzo.Code.Leios.Short.Deterministic.d_Computational'45''45''10214''47''10215''8640'_1756
            (coe MAlonzo.Code.Leios.Foreign.Defaults.d_st_834)
            (coe d_Computational'45'B_144) (coe d_Computational'45'FFD_156))
         (coe
            MAlonzo.Code.Class.Convertible.d_from_20 d_Conv'45'LeiosState_134
            v0))
-- Leios.Foreign.Types.IBBody
d_IBBody_1509 = ()
type T_IBBody_1509 = IBBody
pattern C_IBBody_1511 a0 = IBBody a0
check_IBBody_1511 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () Integer ->
  T_IBBody_1509
check_IBBody_1511 = IBBody
cover_IBBody_1509 :: IBBody -> ()
cover_IBBody_1509 x
  = case x of
      IBBody _ -> ()
-- Leios.Foreign.Types.InputBlock
d_InputBlock_1833 = ()
type T_InputBlock_1833 = InputBlock
pattern C_InputBlock_1835 a0 a1 = InputBlock a0 a1
check_InputBlock_1835 ::
  T_IBHeader_20 -> T_IBBody_1509 -> T_InputBlock_1833
check_InputBlock_1835 = InputBlock
cover_InputBlock_1833 :: InputBlock -> ()
cover_InputBlock_1833 x
  = case x of
      InputBlock _ _ -> ()
-- Leios.Foreign.Types.FFDState
d_FFDState_4021 = ()
type T_FFDState_4021 = FFDState
pattern C_FFDState_4023 a0 a1 a2 a3 a4 a5 = FFDState a0 a1 a2 a3 a4 a5
check_FFDState_4023 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InputBlock_1833 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_EndorserBlock_68 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    (MAlonzo.Code.Agda.Builtin.List.T_List_10
       () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6) ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InputBlock_1833 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_EndorserBlock_68 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    (MAlonzo.Code.Agda.Builtin.List.T_List_10
       () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6) ->
  T_FFDState_4021
check_FFDState_4023 = FFDState
cover_FFDState_4021 :: FFDState -> ()
cover_FFDState_4021 x
  = case x of
      FFDState _ _ _ _ _ _ -> ()
-- Leios.Foreign.Types.LeiosState
d_LeiosState_10683 = ()
type T_LeiosState_10683 = LeiosState
pattern C_LeiosState_10685 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = LeiosState a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
check_LeiosState_10685 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Leios.Foreign.HsTypes.T_HSMap_16 Integer Integer ->
  T_FFDState_4021 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () Integer ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () Integer ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InputBlock_1833 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_EndorserBlock_68 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    (MAlonzo.Code.Agda.Builtin.List.T_List_10
       () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_IBHeader_20 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_IBBody_1509 ->
  MAlonzo.Code.Leios.Foreign.HsTypes.T_HSSet_30 T_SlotUpkeep_101 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> T_LeiosState_10683
check_LeiosState_10685 = LeiosState
cover_LeiosState_10683 :: LeiosState -> ()
cover_LeiosState_10683 x
  = case x of
      LeiosState _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> ()
-- Leios.Foreign.Types.LeiosInput
d_LeiosInput_36783 = ()
type T_LeiosInput_36783 = LeiosInput
pattern C_I_INIT_36785 a0 = I_INIT a0
pattern C_I_SUBMIT_36811 a0 = I_SUBMIT a0
pattern C_I_SLOT_36855 = I_SLOT
pattern C_I_FTCHLDG_36857 = I_FTCHLDG
check_I_INIT_36785 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> T_LeiosInput_36783
check_I_INIT_36785 = I_INIT
check_I_SUBMIT_36811 ::
  MAlonzo.Code.Foreign.Haskell.Either.T_Either_22
    () () T_EndorserBlock_68
    (MAlonzo.Code.Agda.Builtin.List.T_List_10 () Integer) ->
  T_LeiosInput_36783
check_I_SUBMIT_36811 = I_SUBMIT
check_I_SLOT_36855 :: T_LeiosInput_36783
check_I_SLOT_36855 = I_SLOT
check_I_FTCHLDG_36857 :: T_LeiosInput_36783
check_I_FTCHLDG_36857 = I_FTCHLDG
cover_LeiosInput_36783 :: LeiosInput -> ()
cover_LeiosInput_36783 x
  = case x of
      I_INIT _ -> ()
      I_SUBMIT _ -> ()
      I_SLOT -> ()
      I_FTCHLDG -> ()
-- Leios.Foreign.Types.LeiosOutput
d_LeiosOutput_37797 = ()
type T_LeiosOutput_37797 = LeiosOutput
pattern C_O_FTCHLDG_37799 a0 = O_FTCHLDG a0
pattern C_O_EMPTY_37819 = O_EMPTY
check_O_FTCHLDG_37799 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () Integer ->
  T_LeiosOutput_37797
check_O_FTCHLDG_37799 = O_FTCHLDG
check_O_EMPTY_37819 :: T_LeiosOutput_37797
check_O_EMPTY_37819 = O_EMPTY
cover_LeiosOutput_37797 :: LeiosOutput -> ()
cover_LeiosOutput_37797 x
  = case x of
      O_FTCHLDG _ -> ()
      O_EMPTY -> ()
