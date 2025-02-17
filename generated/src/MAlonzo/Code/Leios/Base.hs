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

module MAlonzo.Code.Leios.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Leios.VRF

-- Leios.Base._.EndorserBlock
d_EndorserBlock_88 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> ()
d_EndorserBlock_88 = erased
-- Leios.Base.StakeDistr
d_StakeDistr_90 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> ()
d_StakeDistr_90 = erased
-- Leios.Base.RankingBlock
d_RankingBlock_92 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4 ->
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> ()
d_RankingBlock_92 = erased
-- Leios.Base.BaseAbstract
d_BaseAbstract_94 a0 a1 = ()
data T_BaseAbstract_94
  = C_BaseAbstract'46'constructor_529 (AgdaAny -> Integer)
                                      ([AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool)
-- Leios.Base.BaseAbstract.Cert
d_Cert_104 :: T_BaseAbstract_94 -> ()
d_Cert_104 = erased
-- Leios.Base.BaseAbstract.VTy
d_VTy_106 :: T_BaseAbstract_94 -> ()
d_VTy_106 = erased
-- Leios.Base.BaseAbstract.initSlot
d_initSlot_108 :: T_BaseAbstract_94 -> AgdaAny -> Integer
d_initSlot_108 v0
  = case coe v0 of
      C_BaseAbstract'46'constructor_529 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Base.BaseAbstract.V-chkCerts
d_V'45'chkCerts_110 ::
  T_BaseAbstract_94 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_V'45'chkCerts_110 v0
  = case coe v0 of
      C_BaseAbstract'46'constructor_529 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Base.BaseAbstract.Input
d_Input_112 a0 a1 a2 = ()
data T_Input_112
  = C_INIT_114 (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool) |
    C_SUBMIT_116 MAlonzo.Code.Data.These.Base.T_These_38 |
    C_FTCH'45'LDG_118
-- Leios.Base.BaseAbstract.Output
d_Output_120 a0 a1 a2 = ()
data T_Output_120
  = C_STAKE_122 MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 |
    C_EMPTY_124 |
    C_BASE'45'LDG_126 [MAlonzo.Code.Data.These.Base.T_These_38]
-- Leios.Base.BaseAbstract.Functionality
d_Functionality_128 a0 a1 a2 = ()
newtype T_Functionality_128
  = C_Functionality'46'constructor_1019 (AgdaAny ->
                                         MAlonzo.Code.Data.These.Base.T_These_38 ->
                                         MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Leios.Base.BaseAbstract.Functionality.State
d_State_142 :: T_Functionality_128 -> ()
d_State_142 = erased
-- Leios.Base.BaseAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__144 ::
  T_Functionality_128 ->
  AgdaAny -> T_Input_112 -> T_Output_120 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__144 = erased
-- Leios.Base.BaseAbstract.Functionality.SUBMIT-total
d_SUBMIT'45'total_152 ::
  T_Functionality_128 ->
  AgdaAny ->
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_SUBMIT'45'total_152 v0
  = case coe v0 of
      C_Functionality'46'constructor_1019 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
