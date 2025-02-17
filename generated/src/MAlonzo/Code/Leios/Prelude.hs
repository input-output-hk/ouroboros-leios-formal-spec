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

module MAlonzo.Code.Leios.Prelude where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Axiom.Set
import qualified MAlonzo.Code.Axiom.Set.Properties
import qualified MAlonzo.Code.Class.Decidable.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.IsSet
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory

-- Leios.Prelude.fromTo
d_fromTo_10 :: Integer -> Integer -> [Integer]
d_fromTo_10 v0 v1
  = coe
      MAlonzo.Code.Class.Functor.Core.du_fmap_22
      MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
      () erased (\ v2 -> addInt (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Base.d_upTo_418
         (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0))
-- Leios.Prelude.slice
d_slice_20 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer -> Integer -> [Integer]
d_slice_20 v0 ~v1 v2 v3 = du_slice_20 v0 v2 v3
du_slice_20 :: Integer -> Integer -> Integer -> [Integer]
du_slice_20 v0 v1 v2
  = coe
      MAlonzo.Code.Axiom.Set.du_fromList_428
      (coe
         MAlonzo.Code.Axiom.Set.d_th_1470
         (coe
            MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
      (coe
         d_fromTo_10 (coe du_s''_32 (coe v0) (coe v1) (coe v2))
         (coe
            addInt (coe du_s''_32 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer))))
-- Leios.Prelude._.s'
d_s''_32 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer -> Integer -> Integer
d_s''_32 v0 ~v1 v2 v3 = du_s''_32 v0 v2 v3
du_s''_32 :: Integer -> Integer -> Integer -> Integer
du_s''_32 v0 v1 v2
  = coe
      mulInt
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe MAlonzo.Code.Data.Nat.Base.du__'47'__314 (coe v1) (coe v0))
         v2)
      (coe v0)
-- Leios.Prelude.filter
d_filter_40 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Class.Decidable.Core.T__'8263'_10) ->
  [AgdaAny] -> [AgdaAny]
d_filter_40 ~v0 ~v1 v2 = du_filter_40 v2
du_filter_40 ::
  (AgdaAny -> MAlonzo.Code.Class.Decidable.Core.T__'8263'_10) ->
  [AgdaAny] -> [AgdaAny]
du_filter_40 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_filter_664
      (coe
         MAlonzo.Code.Class.Decidable.Core.du_'191'_'191''185'_116 (coe v0))
-- Leios.Prelude.IsSet-List
d_IsSet'45'List_46 :: () -> MAlonzo.Code.Class.IsSet.T_IsSet_482
d_IsSet'45'List_46 ~v0 = du_IsSet'45'List_46
du_IsSet'45'List_46 :: MAlonzo.Code.Class.IsSet.T_IsSet_482
du_IsSet'45'List_46
  = coe
      MAlonzo.Code.Class.IsSet.C_IsSet'46'constructor_2063
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Axiom.Set.du_fromList_428
              (coe
                 MAlonzo.Code.Axiom.Set.d_th_1470
                 (coe
                    MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
              (coe v0)))
-- Leios.Prelude.finite⇒A≡∅⊎∃a∈A
d_finite'8658'A'8801''8709''8846''8707'a'8712'A_56 ::
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_finite'8658'A'8801''8709''8846''8707'a'8712'A_56 ~v0 ~v1 v2
  = du_finite'8658'A'8801''8709''8846''8707'a'8712'A_56 v2
du_finite'8658'A'8801''8709''8846''8707'a'8712'A_56 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_finite'8658'A'8801''8709''8846''8707'a'8712'A_56 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Axiom.Set.Properties.du_'8709''45'least_432
                       (coe
                          (\ v3 v4 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)))
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Function.Bundles.d_from_1726 (coe v2 v3)
                          (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
