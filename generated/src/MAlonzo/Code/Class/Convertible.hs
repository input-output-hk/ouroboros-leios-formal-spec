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

module MAlonzo.Code.Class.Convertible where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Bifunctor
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.HasHsType
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Foreign.Haskell.Coerce

-- Class.Convertible.Convertible
d_Convertible_8 a0 a1 = ()
data T_Convertible_8
  = C_Convertible'46'constructor_21 (AgdaAny -> AgdaAny)
                                    (AgdaAny -> AgdaAny)
-- Class.Convertible.Convertible.to
d_to_18 :: T_Convertible_8 -> AgdaAny -> AgdaAny
d_to_18 v0
  = case coe v0 of
      C_Convertible'46'constructor_21 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Convertible.Convertible.from
d_from_20 :: T_Convertible_8 -> AgdaAny -> AgdaAny
d_from_20 v0
  = case coe v0 of
      C_Convertible'46'constructor_21 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Convertible._.from
d_from_24 :: T_Convertible_8 -> AgdaAny -> AgdaAny
d_from_24 v0 = coe d_from_20 (coe v0)
-- Class.Convertible._.to
d_to_26 :: T_Convertible_8 -> AgdaAny -> AgdaAny
d_to_26 v0 = coe d_to_18 (coe v0)
-- Class.Convertible.HsConvertible
d_HsConvertible_30 ::
  () -> MAlonzo.Code.Class.HasHsType.T_HasHsType_14 -> ()
d_HsConvertible_30 = erased
-- Class.Convertible.Convertible-Refl
d_Convertible'45'Refl_36 :: () -> T_Convertible_8
d_Convertible'45'Refl_36 ~v0 = du_Convertible'45'Refl_36
du_Convertible'45'Refl_36 :: T_Convertible_8
du_Convertible'45'Refl_36
  = coe
      C_Convertible'46'constructor_21 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0))
-- Class.Convertible.Convertible₁
d_Convertible'8321'_40 :: (() -> ()) -> (() -> ()) -> ()
d_Convertible'8321'_40 = erased
-- Class.Convertible.Convertible₂
d_Convertible'8322'_50 ::
  (() -> () -> ()) -> (() -> () -> ()) -> ()
d_Convertible'8322'_50 = erased
-- Class.Convertible.Functor⇒Convertible
d_Functor'8658'Convertible_62 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  () -> () -> T_Convertible_8 -> T_Convertible_8
d_Functor'8658'Convertible_62 ~v0 v1 ~v2 ~v3 v4
  = du_Functor'8658'Convertible_62 v1 v4
du_Functor'8658'Convertible_62 ::
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  T_Convertible_8 -> T_Convertible_8
du_Functor'8658'Convertible_62 v0 v1
  = coe
      C_Convertible'46'constructor_21
      (coe
         MAlonzo.Code.Class.Functor.Core.du_fmap_22 v0 () erased () erased
         (d_to_18 (coe v1)))
      (coe
         MAlonzo.Code.Class.Functor.Core.du_fmap_22 v0 () erased () erased
         (d_from_20 (coe v1)))
-- Class.Convertible.Bifunctor⇒Convertible
d_Bifunctor'8658'Convertible_68 ::
  (() -> () -> ()) ->
  MAlonzo.Code.Class.Bifunctor.T_Bifunctor_80 ->
  () ->
  () ->
  T_Convertible_8 -> () -> () -> T_Convertible_8 -> T_Convertible_8
d_Bifunctor'8658'Convertible_68 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_Bifunctor'8658'Convertible_68 v1 v4 v7
du_Bifunctor'8658'Convertible_68 ::
  MAlonzo.Code.Class.Bifunctor.T_Bifunctor_80 ->
  T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
du_Bifunctor'8658'Convertible_68 v0 v1 v2
  = coe
      C_Convertible'46'constructor_21
      (coe
         MAlonzo.Code.Class.Bifunctor.d_bimap_102 v0 erased erased erased
         erased (d_to_18 (coe v1)) (d_to_18 (coe v2)))
      (coe
         MAlonzo.Code.Class.Bifunctor.d_bimap_102 v0 erased erased erased
         erased (d_from_20 (coe v1)) (d_from_20 (coe v2)))
-- Class.Convertible._⨾_
d__'10814'__78 ::
  () ->
  () -> () -> T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
d__'10814'__78 ~v0 ~v1 ~v2 v3 v4 = du__'10814'__78 v3 v4
du__'10814'__78 ::
  T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
du__'10814'__78 v0 v1
  = coe
      C_Convertible'46'constructor_21
      (coe (\ v2 -> coe d_to_18 v1 (coe d_to_18 v0 v2)))
      (coe (\ v2 -> coe d_from_20 v0 (coe d_from_20 v1 v2)))
-- Class.Convertible.Convertible-ℕ
d_Convertible'45'ℕ_88 :: T_Convertible_8
d_Convertible'45'ℕ_88
  = coe
      C_Convertible'46'constructor_21 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0))
-- Class.Convertible.Convertible-Maybe
d_Convertible'45'Maybe_92 ::
  () -> () -> T_Convertible_8 -> T_Convertible_8
d_Convertible'45'Maybe_92 ~v0 ~v1 v2
  = du_Convertible'45'Maybe_92 v2
du_Convertible'45'Maybe_92 :: T_Convertible_8 -> T_Convertible_8
du_Convertible'45'Maybe_92 v0
  = coe
      du_Functor'8658'Convertible_62
      (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'Maybe_6)
      (coe v0)
-- Class.Convertible.Convertible-×
d_Convertible'45''215'_94 ::
  () ->
  () ->
  T_Convertible_8 -> () -> () -> T_Convertible_8 -> T_Convertible_8
d_Convertible'45''215'_94 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_Convertible'45''215'_94 v2 v5
du_Convertible'45''215'_94 ::
  T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
du_Convertible'45''215'_94 v0 v1
  = coe
      du_Bifunctor'8658'Convertible_68
      (coe MAlonzo.Code.Class.Bifunctor.du_Bifunctor'45''215'_152)
      (coe v0) (coe v1)
-- Class.Convertible.Convertible-Pair
d_Convertible'45'Pair_96 ::
  () ->
  () ->
  T_Convertible_8 -> () -> () -> T_Convertible_8 -> T_Convertible_8
d_Convertible'45'Pair_96 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_Convertible'45'Pair_96 v2 v5
du_Convertible'45'Pair_96 ::
  T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
du_Convertible'45'Pair_96 v0 v1
  = coe
      C_Convertible'46'constructor_21
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 () erased () erased
              (coe MAlonzo.Code.Foreign.Haskell.Coerce.du_pair'45'toFFI_92)
              (coe
                 MAlonzo.Code.Data.Product.Base.du_map_128 (coe d_to_18 (coe v0))
                 (coe (\ v3 -> d_to_18 (coe v1))) (coe v2))))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128 (coe d_from_20 (coe v0))
              (coe (\ v3 -> d_from_20 (coe v1)))
              (coe
                 MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 () erased () erased
                 (coe MAlonzo.Code.Foreign.Haskell.Coerce.C_TrustMe_40) v2)))
-- Class.Convertible.Convertible-⊎
d_Convertible'45''8846'_100 ::
  () ->
  () ->
  T_Convertible_8 -> () -> () -> T_Convertible_8 -> T_Convertible_8
d_Convertible'45''8846'_100 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_Convertible'45''8846'_100 v2 v5
du_Convertible'45''8846'_100 ::
  T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
du_Convertible'45''8846'_100 v0 v1
  = coe
      du_Bifunctor'8658'Convertible_68
      (coe MAlonzo.Code.Class.Bifunctor.du_Bifunctor'45''8846'_158)
      (coe v0) (coe v1)
-- Class.Convertible.Convertible-Either
d_Convertible'45'Either_102 ::
  () ->
  () ->
  T_Convertible_8 -> () -> () -> T_Convertible_8 -> T_Convertible_8
d_Convertible'45'Either_102 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_Convertible'45'Either_102 v2 v5
du_Convertible'45'Either_102 ::
  T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
du_Convertible'45'Either_102 v0 v1
  = coe
      C_Convertible'46'constructor_21
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 () erased () erased
              (coe MAlonzo.Code.Foreign.Haskell.Coerce.du_either'45'toFFI_96)
              (coe
                 MAlonzo.Code.Data.Sum.Base.du_map_84 (d_to_18 (coe v0))
                 (d_to_18 (coe v1)) v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Sum.Base.du_map_84 (d_from_20 (coe v0))
              (d_from_20 (coe v1))
              (coe
                 MAlonzo.Code.Foreign.Haskell.Coerce.d_coerce_44 () erased () erased
                 (coe MAlonzo.Code.Foreign.Haskell.Coerce.C_TrustMe_40) v2)))
-- Class.Convertible.Convertible-List
d_Convertible'45'List_106 ::
  () -> () -> T_Convertible_8 -> T_Convertible_8
d_Convertible'45'List_106 ~v0 ~v1 v2
  = du_Convertible'45'List_106 v2
du_Convertible'45'List_106 :: T_Convertible_8 -> T_Convertible_8
du_Convertible'45'List_106 v0
  = coe
      C_Convertible'46'constructor_21
      (coe
         MAlonzo.Code.Class.Functor.Core.du_fmap_22
         MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
         () erased (d_to_18 (coe v0)))
      (coe
         MAlonzo.Code.Class.Functor.Core.du_fmap_22
         MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_20 () erased
         () erased (d_from_20 (coe v0)))
-- Class.Convertible.Convertible-Fun
d_Convertible'45'Fun_118 ::
  () ->
  () ->
  () -> () -> T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
d_Convertible'45'Fun_118 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_Convertible'45'Fun_118 v4 v5
du_Convertible'45'Fun_118 ::
  T_Convertible_8 -> T_Convertible_8 -> T_Convertible_8
du_Convertible'45'Fun_118 v0 v1
  = coe
      C_Convertible'46'constructor_21
      (coe (\ v2 v3 -> coe d_to_18 v1 (coe v2 (coe d_from_20 v0 v3))))
      (coe (\ v2 v3 -> coe d_from_20 v1 (coe v2 (coe d_to_18 v0 v3))))
