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

module MAlonzo.Code.StateMachine where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma

-- StateMachine._._-⟦_/_⟧*⇀_
d__'45''10214'_'47'_'10215''42''8640'__36 a0 a1 a2 a3 a4 a5 a6 a7
  = ()
data T__'45''10214'_'47'_'10215''42''8640'__36
  = C_BS'45'base_38 |
    C_BS'45'ind_40 AgdaAny AgdaAny
                   T__'45''10214'_'47'_'10215''42''8640'__36
-- StateMachine.ReflexiveTransitiveClosure
d_ReflexiveTransitiveClosure_42 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny] -> AgdaAny -> ()
d_ReflexiveTransitiveClosure_42 = erased
-- StateMachine.IdSTS
d_IdSTS_46 a0 a1 a2 a3 a4 = ()
data T_IdSTS_46 = C_Id'45'nop_50
-- StateMachine.Invariant
d_Invariant_52 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> ()
d_Invariant_52 = erased
-- StateMachine.Total
d_Total_66 ::
  () ->
  () -> () -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) -> ()
d_Total_66 = erased
-- StateMachine.STS⇒RTC
d_STS'8658'RTC_78 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__'45''10214'_'47'_'10215''42''8640'__36
d_STS'8658'RTC_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_STS'8658'RTC_78 v7 v8
du_STS'8658'RTC_78 ::
  AgdaAny -> AgdaAny -> T__'45''10214'_'47'_'10215''42''8640'__36
du_STS'8658'RTC_78 v0 v1
  = coe C_BS'45'ind_40 v0 v1 (coe C_BS'45'base_38)
-- StateMachine.RTC-preserves-inv
d_RTC'45'preserves'45'inv_84 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  T__'45''10214'_'47'_'10215''42''8640'__36 -> AgdaAny -> AgdaAny
d_RTC'45'preserves'45'inv_84 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9
                             v10
  = du_RTC'45'preserves'45'inv_84 v5 v6 v7 v8 v10
du_RTC'45'preserves'45'inv_84 ::
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  T__'45''10214'_'47'_'10215''42''8640'__36 -> AgdaAny -> AgdaAny
du_RTC'45'preserves'45'inv_84 v0 v1 v2 v3 v4
  = case coe v4 of
      C_BS'45'base_38 -> coe (\ v6 -> v6)
      C_BS'45'ind_40 v8 v12 v13
        -> case coe v2 of
             (:) v14 v15
               -> case coe v3 of
                    (:) v16 v17
                      -> coe
                           (\ v18 ->
                              coe
                                du_RTC'45'preserves'45'inv_84 v0 v8 v15 v17 v13
                                (coe v0 v1 v14 v16 v8 v12 v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- StateMachine.RTC-total
d_RTC'45'total_94 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_RTC'45'total_94 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_RTC'45'total_94 v4 v5 v6
du_RTC'45'total_94 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_RTC'45'total_94 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe C_BS'45'base_38))
      (:) v3 v4
        -> coe du_'46'extendedlambda0_108 (coe v0) (coe v4) (coe v0 v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- StateMachine..extendedlambda0
d_'46'extendedlambda0_108 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda0_108 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_'46'extendedlambda0_108 v4 v7 v8
du_'46'extendedlambda0_108 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda0_108 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> let v7
                        = coe
                            du_RTC'45'total_94 (coe (\ v7 v8 -> coe v0 v7 v8)) (coe v5)
                            (coe v1) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                        (coe v8))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                        (coe C_BS'45'ind_40 v5 v6 v11))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
