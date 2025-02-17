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

module MAlonzo.Code.Leios.FFD where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base

-- Leios.FFD.FFDAbstract
d_FFDAbstract_4 = ()
newtype T_FFDAbstract_4
  = C_FFDAbstract'46'constructor_35 (AgdaAny -> AgdaAny)
-- Leios.FFD.FFDAbstract.Header
d_Header_16 :: T_FFDAbstract_4 -> ()
d_Header_16 = erased
-- Leios.FFD.FFDAbstract.Body
d_Body_18 :: T_FFDAbstract_4 -> ()
d_Body_18 = erased
-- Leios.FFD.FFDAbstract.ID
d_ID_20 :: T_FFDAbstract_4 -> ()
d_ID_20 = erased
-- Leios.FFD.FFDAbstract.match
d_match_22 :: T_FFDAbstract_4 -> AgdaAny -> AgdaAny -> ()
d_match_22 = erased
-- Leios.FFD.FFDAbstract.msgID
d_msgID_24 :: T_FFDAbstract_4 -> AgdaAny -> AgdaAny
d_msgID_24 v0
  = case coe v0 of
      C_FFDAbstract'46'constructor_35 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.FFD.FFDAbstract.Input
d_Input_26 a0 = ()
data T_Input_26 = C_Send_28 AgdaAny (Maybe AgdaAny) | C_Fetch_30
-- Leios.FFD.FFDAbstract.Output
d_Output_32 a0 = ()
data T_Output_32
  = C_SendRes_34 |
    C_FetchRes_36 [MAlonzo.Code.Data.Sum.Base.T__'8846'__30]
-- Leios.FFD.FFDAbstract.Functionality
d_Functionality_38 a0 = ()
data T_Functionality_38
  = C_Functionality'46'constructor_457 AgdaAny
                                       (AgdaAny ->
                                        AgdaAny ->
                                        Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Leios.FFD.FFDAbstract.Functionality.State
d_State_56 :: T_Functionality_38 -> ()
d_State_56 = erased
-- Leios.FFD.FFDAbstract.Functionality.initFFDState
d_initFFDState_58 :: T_Functionality_38 -> AgdaAny
d_initFFDState_58 v0
  = case coe v0 of
      C_Functionality'46'constructor_457 v2 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.FFD.FFDAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__60 ::
  T_Functionality_38 ->
  AgdaAny -> T_Input_26 -> T_Output_32 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__60 = erased
-- Leios.FFD.FFDAbstract.Functionality.FFD-Send-total
d_FFD'45'Send'45'total_70 ::
  T_Functionality_38 ->
  AgdaAny ->
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_FFD'45'Send'45'total_70 v0
  = case coe v0 of
      C_Functionality'46'constructor_457 v2 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
