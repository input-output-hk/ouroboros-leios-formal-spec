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

module MAlonzo.Code.Class.Computational22 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Class.Computational
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Monad.Core

-- Class.Computational22._.Computational22
d_Computational22_26 a0 a1 a2 a3 a4 = ()
newtype T_Computational22_26
  = C_MkComputational_86 (AgdaAny ->
                          AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28)
-- Class.Computational22._.Computational22.computeProof
d_computeProof_68 ::
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_computeProof_68 v0
  = case coe v0 of
      C_MkComputational_86 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Computational22._.Computational22.compute
d_compute_70 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_compute_70 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 = du_compute_70 v5 v6 v7
du_compute_70 ::
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
du_compute_70 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Functor.Core.du_fmap_22
      (coe
         MAlonzo.Code.Class.Computational.du_Functor'45'ComputationResult_132)
      () erased () erased
      (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
      (coe d_computeProof_68 v0 v1 v2)
-- Class.Computational22._.Computational22.completeness
d_completeness_84 ::
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_completeness_84 = erased
-- Class.Computational22._.STS'
d_STS''_88 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_STS''_88 = erased
-- Class.Computational22._._._.completeness
d_completeness_108 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_completeness_108 = erased
-- Class.Computational22._._._.compute
d_compute_110 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_compute_110 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_compute_110 v5
du_compute_110 ::
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
du_compute_110 v0 = coe du_compute_70 (coe v0)
-- Class.Computational22._._._.computeProof
d_computeProof_112 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_computeProof_112 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_computeProof_112 v5
du_computeProof_112 ::
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
du_computeProof_112 v0 = coe d_computeProof_68 (coe v0)
-- Class.Computational22._._.comp22⇒comp
d_comp22'8658'comp_114 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational22_26 ->
  MAlonzo.Code.Class.Computational.T_Computational_216
d_comp22'8658'comp_114 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_comp22'8658'comp_114 v5
du_comp22'8658'comp_114 ::
  T_Computational22_26 ->
  MAlonzo.Code.Class.Computational.T_Computational_216
du_comp22'8658'comp_114 v0
  = coe
      MAlonzo.Code.Class.Computational.C_MkComputational_336
      (\ v1 ->
         case coe v1 of
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
             -> coe d_computeProof_68 v0 v2 v3
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.Computational22._._.completeness
d_completeness_146 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_completeness_146 = erased
-- Class.Computational22._._.compute
d_compute_148 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_compute_148 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_compute_148 v5
du_compute_148 ::
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
du_compute_148 v0 = coe du_compute_70 (coe v0)
-- Class.Computational22._._.computeProof
d_computeProof_150 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_computeProof_150 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_computeProof_150 v5
du_computeProof_150 ::
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Class.Computational.T_ComputationResult_28
du_computeProof_150 v0 = coe d_computeProof_68 (coe v0)
-- Class.Computational22._.computeTrace
d_computeTrace_152 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_Computational22_26 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_computeTrace_152 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_computeTrace_152 v5 v6 v7
du_computeTrace_152 ::
  T_Computational22_26 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Class.Computational.T_ComputationResult_28
du_computeTrace_152 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Class.Computational.C_success_36
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v1))
      (:) v3 v4
        -> coe
             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__18
             (coe
                MAlonzo.Code.Class.Computational.du_Monad'45'ComputationResult_152)
             () erased () erased (coe du_compute_70 (coe v0) (coe v1) (coe v3))
             (coe du_'46'extendedlambda0_162 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Computational22._..extendedlambda0
d_'46'extendedlambda0_162 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_Computational22_26 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Class.Computational.T_ComputationResult_28
d_'46'extendedlambda0_162 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9
  = du_'46'extendedlambda0_162 v5 v8 v9
du_'46'extendedlambda0_162 ::
  T_Computational22_26 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Class.Computational.T_ComputationResult_28
du_'46'extendedlambda0_162 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__18
             (coe
                MAlonzo.Code.Class.Computational.du_Monad'45'ComputationResult_152)
             () erased () erased
             (coe du_computeTrace_152 (coe v0) (coe v4) (coe v1))
             (\ v5 ->
                case coe v5 of
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                    -> coe
                         MAlonzo.Code.Class.Computational.C_success_36
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v6))
                            (coe v7))
                  _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
