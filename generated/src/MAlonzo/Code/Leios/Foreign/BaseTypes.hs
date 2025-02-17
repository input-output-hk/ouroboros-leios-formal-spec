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

module MAlonzo.Code.Leios.Foreign.BaseTypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Axiom.Set
import qualified MAlonzo.Code.Axiom.Set.Map
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Class.Computational
import qualified MAlonzo.Code.Class.Convertible
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.Decidable.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.HasHsType
import qualified MAlonzo.Code.Class.IsSet
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Foreign.Haskell.Coerce
import qualified MAlonzo.Code.Leios.Foreign.HsTypes
import qualified MAlonzo.Code.Leios.Foreign.Util
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory

-- Leios.Foreign.BaseTypes.iConvTop
d_iConvTop_6 :: MAlonzo.Code.Class.Convertible.T_Convertible_8
d_iConvTop_6
  = coe MAlonzo.Code.Class.Convertible.du_Convertible'45'Refl_36
-- Leios.Foreign.BaseTypes.iConvNat
d_iConvNat_8 :: MAlonzo.Code.Class.Convertible.T_Convertible_8
d_iConvNat_8
  = coe MAlonzo.Code.Class.Convertible.du_Convertible'45'Refl_36
-- Leios.Foreign.BaseTypes.iConvString
d_iConvString_10 :: MAlonzo.Code.Class.Convertible.T_Convertible_8
d_iConvString_10
  = coe MAlonzo.Code.Class.Convertible.du_Convertible'45'Refl_36
-- Leios.Foreign.BaseTypes.iConvBool
d_iConvBool_12 :: MAlonzo.Code.Class.Convertible.T_Convertible_8
d_iConvBool_12
  = coe MAlonzo.Code.Class.Convertible.du_Convertible'45'Refl_36
-- Leios.Foreign.BaseTypes.HsTy-⊥
d_HsTy'45''8869'_14 :: MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45''8869'_14 = erased
-- Leios.Foreign.BaseTypes.Conv-⊥
d_Conv'45''8869'_16 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45''8869'_16
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe (\ v0 -> MAlonzo.RTE.mazUnreachableError))
      (coe (\ v0 -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.BaseTypes.HsTy-⊤
d_HsTy'45''8868'_18 :: MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45''8868'_18 = erased
-- Leios.Foreign.BaseTypes.HsTy-Rational
d_HsTy'45'Rational_20 ::
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'Rational_20 = erased
-- Leios.Foreign.BaseTypes.Conv-Rational
d_Conv'45'Rational_22 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'Rational_22
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
                -> coe
                     MAlonzo.Code.Leios.Foreign.HsTypes.C__'44'__10 (coe v1)
                     (coe addInt (coe (1 :: Integer)) (coe v2))
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Leios.Foreign.HsTypes.C__'44'__10 v1 v2
                -> case coe v2 of
                     0 -> coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                     _ -> coe
                            MAlonzo.Code.Data.Rational.Base.du__'47'__156 (coe v1) (coe v2)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Leios.Foreign.BaseTypes.HsTy-HSSet
d_HsTy'45'HSSet_38 ::
  () ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'HSSet_38 = erased
-- Leios.Foreign.BaseTypes.Conv-HSSet
d_Conv'45'HSSet_46 ::
  () ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'HSSet_46 ~v0 ~v1 v2 = du_Conv'45'HSSet_46 v2
du_Conv'45'HSSet_46 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
du_Conv'45'HSSet_46 v0
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Leios.Foreign.HsTypes.C_MkHSSet_38
              (coe
                 MAlonzo.Code.Class.Convertible.d_to_18
                 (coe
                    MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106 (coe v0))
                 v1)))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Axiom.Set.du_fromList_428
              (coe
                 MAlonzo.Code.Axiom.Set.d_th_1470
                 (coe
                    MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
              (coe
                 MAlonzo.Code.Class.Convertible.d_from_20
                 (coe
                    MAlonzo.Code.Class.Convertible.du_Convertible'45'List_106 (coe v0))
                 (MAlonzo.Code.Leios.Foreign.HsTypes.d_elems_36 (coe v1)))))
-- Leios.Foreign.BaseTypes.Convertible-FinSet
d_Convertible'45'FinSet_50 ::
  () ->
  () ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Convertible'45'FinSet_50 ~v0 ~v1 v2
  = du_Convertible'45'FinSet_50 v2
du_Convertible'45'FinSet_50 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
du_Convertible'45'FinSet_50 v0
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Class.Functor.Core.du_fmap_22
              MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
              () erased (MAlonzo.Code.Class.Convertible.d_to_18 (coe v0)) v1))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Axiom.Set.du_fromList_428
              (coe
                 MAlonzo.Code.Axiom.Set.d_th_1470
                 (coe
                    MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
              (coe
                 MAlonzo.Code.Class.Functor.Core.du_fmap_22
                 MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                 () erased (MAlonzo.Code.Class.Convertible.d_from_20 (coe v0)) v1)))
-- Leios.Foreign.BaseTypes.Convertible-Map
d_Convertible'45'Map_62 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Convertible'45'Map_62 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_Convertible'45'Map_62 v4 v5 v6
du_Convertible'45'Map_62 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
du_Convertible'45'Map_62 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Class.Convertible.d_to_18
              (coe
                 du_Convertible'45'FinSet_50
                 (coe
                    MAlonzo.Code.Class.Convertible.du_Convertible'45'Pair_96 (coe v1)
                    (coe v2)))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Axiom.Set.Map.du_fromList'7504'_582
              (coe
                 MAlonzo.Code.Axiom.Set.d_th_1470
                 (coe
                    MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
              (coe v0)
              (coe
                 MAlonzo.Code.Class.Functor.Core.du_fmap_22
                 MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
                 () erased
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Data.Product.Base.du_map_128
                      (coe MAlonzo.Code.Class.Convertible.d_from_20 (coe v1))
                      (coe (\ v5 -> MAlonzo.Code.Class.Convertible.d_from_20 (coe v2)))
                      (coe
                         MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 () erased () erased
                         (coe MAlonzo.Code.Foreign.Haskell.Coerce.C_TrustMe_40) v4))
                 v3)))
-- Leios.Foreign.BaseTypes.HsTy-Map
d_HsTy'45'Map_70 ::
  () ->
  () ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'Map_70 = erased
-- Leios.Foreign.BaseTypes.Conv-HSMap
d_Conv'45'HSMap_84 ::
  () ->
  () ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'HSMap_84 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_Conv'45'HSMap_84 v4 v5 v6
du_Conv'45'HSMap_84 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
du_Conv'45'HSMap_84 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Leios.Foreign.HsTypes.C_MkHSMap_26
              (coe
                 MAlonzo.Code.Class.Convertible.d_to_18
                 (coe
                    du_Convertible'45'FinSet_50
                    (coe
                       MAlonzo.Code.Class.Convertible.du_Convertible'45'Pair_96 (coe v1)
                       (coe v2)))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Class.Convertible.d_from_20
              (coe du_Convertible'45'Map_62 (coe v0) (coe v1) (coe v2))
              (MAlonzo.Code.Leios.Foreign.HsTypes.d_assocList_24 (coe v3))))
-- Leios.Foreign.BaseTypes.Listable
d_Listable_90 a0 = ()
data T_Listable_90
  = C_Listable'46'constructor_10891 [AgdaAny]
                                    (AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
-- Leios.Foreign.BaseTypes.Listable.listing
d_listing_100 :: T_Listable_90 -> [AgdaAny]
d_listing_100 v0
  = case coe v0 of
      C_Listable'46'constructor_10891 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.BaseTypes.Listable.complete
d_complete_104 ::
  T_Listable_90 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_complete_104 v0
  = case coe v0 of
      C_Listable'46'constructor_10891 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.BaseTypes.totalDec
d_totalDec_112 ::
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_totalDec_112 ~v0 ~v1 v2 v3 v4 = du_totalDec_112 v2 v3 v4
du_totalDec_112 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_totalDec_112 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Axiom.Set.d_all'63'_1610
              MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8
              erased erased
              (\ v3 ->
                 coe
                   MAlonzo.Code.Axiom.Set.d__'8712''63'__1602
                   MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8
                   erased v0 v3
                   (coe
                      MAlonzo.Code.Class.IsSet.du_dom_548
                      (coe
                         MAlonzo.Code.Axiom.Set.d_th_1470
                         (coe
                            MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
                      (coe MAlonzo.Code.Class.IsSet.du_IsSet'45'Set_552) (coe v2)))
              (d_listing_100 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe (\ v7 -> coe v6 v7 (coe d_complete_104 v1 v7))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v4)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Leios.Foreign.BaseTypes.total?
d_total'63'_158 ::
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Class.Decidable.Core.T__'8263'_10
d_total'63'_158 ~v0 ~v1 v2 v3 v4 = du_total'63'_158 v2 v3 v4
du_total'63'_158 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Class.Decidable.Core.T__'8263'_10
du_total'63'_158 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
      (coe du_totalDec_112 (coe v0) (coe v1) (coe v2))
-- Leios.Foreign.BaseTypes.Convertible-TotalMap
d_Convertible'45'TotalMap_168 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Convertible'45'TotalMap_168 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_Convertible'45'TotalMap_168 v4 v5 v6 v7
du_Convertible'45'TotalMap_168 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
du_Convertible'45'TotalMap_168 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Class.Convertible.d_to_18
              (coe
                 du_Convertible'45'FinSet_50
                 (coe
                    MAlonzo.Code.Class.Convertible.du_Convertible'45'Pair_96 (coe v2)
                    (coe v3)))
              (MAlonzo.Code.Axiom.Set.TotalMap.d_rel_180 (coe v4))))
      (coe
         (\ v4 ->
            let v5
                  = coe
                      MAlonzo.Code.Class.Decidable.Core.du_'191'_'191'_42
                      (coe
                         MAlonzo.Code.Class.Decidable.Core.C_'8263'__30
                         (coe
                            du_totalDec_112 (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Axiom.Set.d_listing_216
                                  (MAlonzo.Code.Axiom.Set.d_th_1470
                                     (coe
                                        MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
                                  erased
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du_deduplicate_898
                                     (coe
                                        (\ v5 v6 ->
                                           coe
                                             MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 v0
                                             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                                             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6))))
                                     (coe
                                        MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                        MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 ()
                                        erased () erased
                                        (\ v5 ->
                                           coe
                                             MAlonzo.Code.Data.Product.Base.du_map_128
                                             (coe MAlonzo.Code.Class.Convertible.d_from_20 (coe v2))
                                             (coe
                                                (\ v6 ->
                                                   MAlonzo.Code.Class.Convertible.d_from_20
                                                     (coe v3)))
                                             (coe
                                                MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 ()
                                                erased () erased
                                                (coe
                                                   MAlonzo.Code.Foreign.Haskell.Coerce.C_TrustMe_40)
                                                v5))
                                        v4)))))) in
            coe
              (case coe v5 of
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                   -> if coe v6
                        then case coe v7 of
                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                 -> coe
                                      MAlonzo.Code.Axiom.Set.TotalMap.C_TotalMap'46'constructor_937
                                      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Axiom.Set.Map.du_fromList'7504'_582
                                            (coe
                                               MAlonzo.Code.Axiom.Set.d_th_1470
                                               (coe
                                                  MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
                                            (coe v0)
                                            (coe
                                               MAlonzo.Code.Class.Functor.Core.du_fmap_22
                                               MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20
                                               () erased () erased
                                               (\ v9 ->
                                                  coe
                                                    MAlonzo.Code.Data.Product.Base.du_map_128
                                                    (coe
                                                       MAlonzo.Code.Class.Convertible.d_from_20
                                                       (coe v2))
                                                    (coe
                                                       (\ v10 ->
                                                          MAlonzo.Code.Class.Convertible.d_from_20
                                                            (coe v3)))
                                                    (coe
                                                       MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44
                                                       () erased () erased
                                                       (coe
                                                          MAlonzo.Code.Foreign.Haskell.Coerce.C_TrustMe_40)
                                                       v9))
                                               v4)))
                                      v8
                               _ -> MAlonzo.RTE.mazUnreachableError
                        else coe
                               seq (coe v7)
                               (coe
                                  MAlonzo.Code.Leios.Foreign.Util.d_error_8 erased
                                  ("Expected total map" :: Data.Text.Text))
                 _ -> MAlonzo.RTE.mazUnreachableError)))
-- Leios.Foreign.BaseTypes.HsTy-TotalMap
d_HsTy'45'TotalMap_190 ::
  () ->
  () ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'TotalMap_190 = erased
-- Leios.Foreign.BaseTypes.Conv-HSTotalMap
d_Conv'45'HSTotalMap_204 ::
  () ->
  () ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'HSTotalMap_204 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_Conv'45'HSTotalMap_204 v4 v5 v6 v7
du_Conv'45'HSTotalMap_204 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  T_Listable_90 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
du_Conv'45'HSTotalMap_204 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Leios.Foreign.HsTypes.C_MkHSMap_26
              (coe
                 MAlonzo.Code.Class.Convertible.d_to_18
                 (coe
                    du_Convertible'45'FinSet_50
                    (coe
                       MAlonzo.Code.Class.Convertible.du_Convertible'45'Pair_96 (coe v2)
                       (coe v3)))
                 (MAlonzo.Code.Axiom.Set.TotalMap.d_rel_180 (coe v4)))))
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Class.Convertible.d_from_20
              (coe
                 du_Convertible'45'TotalMap_168 (coe v0) (coe v1) (coe v2) (coe v3))
              (MAlonzo.Code.Leios.Foreign.HsTypes.d_assocList_24 (coe v4))))
-- Leios.Foreign.BaseTypes.HsTy-ComputationResult
d_HsTy'45'ComputationResult_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14 ->
  MAlonzo.Code.Class.HasHsType.T_HasHsType_14
d_HsTy'45'ComputationResult_214 = erased
-- Leios.Foreign.BaseTypes.Conv-ComputationResult
d_Conv'45'ComputationResult_220 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
d_Conv'45'ComputationResult_220 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_Conv'45'ComputationResult_220 v4 v5
du_Conv'45'ComputationResult_220 ::
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8 ->
  MAlonzo.Code.Class.Convertible.T_Convertible_8
du_Conv'45'ComputationResult_220 v0 v1
  = coe
      MAlonzo.Code.Class.Convertible.C_Convertible'46'constructor_21
      (coe
         (\ v2 ->
            case coe v2 of
              MAlonzo.Code.Class.Computational.C_success_36 v3
                -> coe
                     MAlonzo.Code.Leios.Foreign.HsTypes.C_Success_50
                     (coe MAlonzo.Code.Class.Convertible.d_to_18 v1 v3)
              MAlonzo.Code.Class.Computational.C_failure_38 v3
                -> coe
                     MAlonzo.Code.Leios.Foreign.HsTypes.C_Failure_52
                     (coe MAlonzo.Code.Class.Convertible.d_to_18 v0 v3)
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v2 ->
            case coe v2 of
              MAlonzo.Code.Leios.Foreign.HsTypes.C_Success_50 v3
                -> coe
                     MAlonzo.Code.Class.Computational.C_success_36
                     (coe MAlonzo.Code.Class.Convertible.d_from_20 v1 v3)
              MAlonzo.Code.Leios.Foreign.HsTypes.C_Failure_52 v3
                -> coe
                     MAlonzo.Code.Class.Computational.C_failure_38
                     (coe MAlonzo.Code.Class.Convertible.d_from_20 v0 v3)
              _ -> MAlonzo.RTE.mazUnreachableError))
