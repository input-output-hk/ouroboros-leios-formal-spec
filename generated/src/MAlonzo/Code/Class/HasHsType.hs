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

module MAlonzo.Code.Class.HasHsType where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Class.HasHsType.HasHsType
d_HasHsType_14 a0 a1 = ()
data T_HasHsType_14 = C_HasHsType'46'constructor_45
-- Class.HasHsType.HasHsType.HsType
d_HsType_20 :: T_HasHsType_14 -> ()
d_HsType_20 = erased
-- Class.HasHsType.HsType
d_HsType_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_HasHsType_14 -> ()
d_HsType_24 = erased
-- Class.HasHsType.MkHsType
d_MkHsType_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> T_HasHsType_14
d_MkHsType_32 = erased
-- Class.HasHsType.iHsTy-ℕ
d_iHsTy'45'ℕ_38 :: T_HasHsType_14
d_iHsTy'45'ℕ_38 = erased
-- Class.HasHsType.iHsTy-Bool
d_iHsTy'45'Bool_40 :: T_HasHsType_14
d_iHsTy'45'Bool_40 = erased
-- Class.HasHsType.iHsTy-⊤
d_iHsTy'45''8868'_42 :: T_HasHsType_14
d_iHsTy'45''8868'_42 = erased
-- Class.HasHsType.iHsTy-String
d_iHsTy'45'String_44 :: T_HasHsType_14
d_iHsTy'45'String_44 = erased
-- Class.HasHsType.iHsTy-List
d_iHsTy'45'List_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_HasHsType_14 -> T_HasHsType_14
d_iHsTy'45'List_46 = erased
-- Class.HasHsType.iHsTy-Maybe
d_iHsTy'45'Maybe_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_HasHsType_14 -> T_HasHsType_14
d_iHsTy'45'Maybe_50 = erased
-- Class.HasHsType.iHsTy-Fun
d_iHsTy'45'Fun_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_HasHsType_14 -> T_HasHsType_14 -> T_HasHsType_14
d_iHsTy'45'Fun_54 = erased
-- Class.HasHsType.iHsTy-Sum
d_iHsTy'45'Sum_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_HasHsType_14 -> T_HasHsType_14 -> T_HasHsType_14
d_iHsTy'45'Sum_60 = erased
-- Class.HasHsType.iHsTy-Pair
d_iHsTy'45'Pair_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_HasHsType_14 -> T_HasHsType_14 -> T_HasHsType_14
d_iHsTy'45'Pair_66 = erased
