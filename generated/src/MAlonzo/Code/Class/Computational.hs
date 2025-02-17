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

module MAlonzo.Code.Class.Computational where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.Bifunctor
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Class.Computational.ComputationResult
d_ComputationResult_28 a0 a1 a2 = ()
data T_ComputationResult_28
  = C_success_36 AgdaAny | C_failure_38 AgdaAny
-- Class.Computational.isFailure
d_isFailure_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> T_ComputationResult_28 -> ()
d_isFailure_42 = erased
-- Class.Computational._.caseCR_∣_∣_
d_caseCR_'8739'_'8739'__66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  T_ComputationResult_28 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) -> AgdaAny
d_caseCR_'8739'_'8739'__66 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_caseCR_'8739'_'8739'__66 v5 v6 v7
du_caseCR_'8739'_'8739'__66 ::
  T_ComputationResult_28 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) -> AgdaAny
du_caseCR_'8739'_'8739'__66 v0 v1 v2
  = case coe v0 of
      C_success_36 v3 -> coe v1 v3 erased
      C_failure_38 v3
        -> coe
             v2
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Computational._.caseCR-success
d_caseCR'45'success_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  T_ComputationResult_28 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_caseCR'45'success_104 = erased
-- Class.Computational._.caseCR-failure
d_caseCR'45'failure_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  T_ComputationResult_28 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_caseCR'45'failure_116 = erased
-- Class.Computational.Bifunctor-ComputationResult
d_Bifunctor'45'ComputationResult_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Class.Bifunctor.T_Bifunctor_80
d_Bifunctor'45'ComputationResult_120 ~v0
  = du_Bifunctor'45'ComputationResult_120
du_Bifunctor'45'ComputationResult_120 ::
  MAlonzo.Code.Class.Bifunctor.T_Bifunctor_80
du_Bifunctor'45'ComputationResult_120
  = coe
      MAlonzo.Code.Class.Bifunctor.C_Bifunctor'46'constructor_3915
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            case coe v6 of
              C_success_36 v7 -> coe C_success_36 (coe v5 v7)
              C_failure_38 v7 -> coe C_failure_38 (coe v4 v7)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Computational.Functor-ComputationResult
d_Functor'45'ComputationResult_132 ::
  () -> MAlonzo.Code.Class.Functor.Core.T_Functor_14
d_Functor'45'ComputationResult_132 ~v0
  = du_Functor'45'ComputationResult_132
du_Functor'45'ComputationResult_132 ::
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
du_Functor'45'ComputationResult_132
  = coe
      MAlonzo.Code.Class.Functor.Core.C_Functor'46'constructor_121
      (coe
         (\ v0 v1 v2 v3 v4 v5 ->
            case coe v5 of
              C_success_36 v6 -> coe C_success_36 (coe v4 v6)
              C_failure_38 v6 -> coe v5
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Computational.Applicative-ComputationResult
d_Applicative'45'ComputationResult_142 ::
  () -> MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'ComputationResult_142 ~v0
  = du_Applicative'45'ComputationResult_142
du_Applicative'45'ComputationResult_142 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
du_Applicative'45'ComputationResult_142
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe du_Functor'45'ComputationResult_132)
      (coe (\ v0 v1 -> coe C_success_36))
      (coe
         (\ v0 v1 v2 v3 v4 ->
            case coe v4 of
              C_success_36 v5
                -> coe
                     (\ v6 ->
                        coe
                          MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                          (coe du_Functor'45'ComputationResult_132) v0 erased v2 erased v5
                          v6)
              C_failure_38 v5 -> coe (\ v6 -> v4)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Computational.Monad-ComputationResult
d_Monad'45'ComputationResult_152 ::
  () -> MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_Monad'45'ComputationResult_152 ~v0
  = du_Monad'45'ComputationResult_152
du_Monad'45'ComputationResult_152 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8
du_Monad'45'ComputationResult_152
  = coe
      MAlonzo.Code.Class.Monad.Core.C_Monad'46'constructor_213
      (coe (\ v0 v1 -> coe C_success_36))
      (coe
         (\ v0 v1 v2 v3 v4 ->
            case coe v4 of
              C_success_36 v5 -> coe (\ v6 -> coe v6 v5)
              C_failure_38 v5 -> coe (\ v6 -> v4)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Computational.map-failure
d_map'45'failure_172 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_ComputationResult_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'failure_172 = erased
-- Class.Computational.success-maybe
d_success'45'maybe_176 ::
  () -> () -> T_ComputationResult_28 -> Maybe AgdaAny
d_success'45'maybe_176 ~v0 ~v1 v2 = du_success'45'maybe_176 v2
du_success'45'maybe_176 :: T_ComputationResult_28 -> Maybe AgdaAny
du_success'45'maybe_176 v0
  = case coe v0 of
      C_success_36 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_failure_38 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Computational.failure-maybe
d_failure'45'maybe_182 ::
  () -> () -> T_ComputationResult_28 -> Maybe AgdaAny
d_failure'45'maybe_182 ~v0 ~v1 v2 = du_failure'45'maybe_182 v2
du_failure'45'maybe_182 :: T_ComputationResult_28 -> Maybe AgdaAny
du_failure'45'maybe_182 v0
  = case coe v0 of
      C_success_36 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_failure_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Computational._≈ᶜʳ_
d__'8776''7580''691'__188 ::
  () -> () -> T_ComputationResult_28 -> T_ComputationResult_28 -> ()
d__'8776''7580''691'__188 = erased
-- Class.Computational._.ExtendedRel
d_ExtendedRel_204 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () -> AgdaAny -> T_ComputationResult_28 -> ()
d_ExtendedRel_204 = erased
-- Class.Computational._.Computational
d_Computational_216 a0 a1 a2 a3 = ()
newtype T_Computational_216
  = C_MkComputational_336 (AgdaAny -> T_ComputationResult_28)
-- Class.Computational._.Computational.computeProof
d_computeProof_240 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_computeProof_240 v0
  = case coe v0 of
      C_MkComputational_336 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Computational._.Computational.compute
d_compute_242 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () -> T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_compute_242 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_compute_242 v4 v5
du_compute_242 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
du_compute_242 v0 v1
  = coe
      MAlonzo.Code.Class.Functor.Core.du_fmap_22
      (coe du_Functor'45'ComputationResult_132) () erased () erased
      (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
      (coe d_computeProof_240 v0 v1)
-- Class.Computational._.Computational.completeness
d_completeness_250 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_completeness_250 = erased
-- Class.Computational._.Computational.computeFail
d_computeFail_252 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () -> T_Computational_216 -> AgdaAny -> ()
d_computeFail_252 = erased
-- Class.Computational._.Computational.≡-success⇔STS
d_'8801''45'success'8660'STS_256 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8801''45'success'8660'STS_256 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8801''45'success'8660'STS_256 v4 v5 v6
du_'8801''45'success'8660'STS_256 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8801''45'success'8660'STS_256 v0 v1 v2
  = let v3 = coe d_computeProof_240 v0 v1 in
    coe
      (case coe v3 of
         C_success_36 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 (coe (\ v7 -> v6))
                       (coe
                          (\ v7 ->
                             coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                               (\ v8 v9 v10 -> v10) (coe C_success_36 (coe v5))
                               (coe C_success_36 (coe v2))
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
                                  erased (coe C_success_36 (coe v5))
                                  (coe du_compute_242 (coe v0) (coe v1)) (coe C_success_36 (coe v2))
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                     erased (coe du_compute_242 (coe v0) (coe v1))
                                     (coe C_success_36 (coe v2)) (coe C_success_36 (coe v2))
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                        erased (coe C_success_36 (coe v2)))
                                     erased)
                                  erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         C_failure_38 v4
           -> coe
                MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
                (coe
                   (\ v5 ->
                      coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                        (\ v6 v7 v8 -> v8) v3 (coe C_success_36 (coe v2))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
                           erased v3 (coe du_compute_242 (coe v0) (coe v1))
                           (coe C_success_36 (coe v2))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                              erased (coe du_compute_242 (coe v0) (coe v1))
                              (coe C_success_36 (coe v2)) (coe C_success_36 (coe v2))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492 erased
                                 (coe C_success_36 (coe v2)))
                              erased)
                           erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.Computational._.Computational.failure⇒∀¬STS
d_failure'8658''8704''172'STS_290 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational_216 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_failure'8658''8704''172'STS_290 = erased
-- Class.Computational._.Computational.∀¬STS⇒failure
d_'8704''172'STS'8658'failure_304 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational_216 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8704''172'STS'8658'failure_304 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
  = du_'8704''172'STS'8658'failure_304 v4 v5
du_'8704''172'STS'8658'failure_304 ::
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8704''172'STS'8658'failure_304 v0 v1
  = let v2 = coe d_computeProof_240 v0 v1 in
    coe
      (case coe v2 of
         C_success_36 v3
           -> coe
                seq (coe v3) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)
         C_failure_38 v3
           -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.Computational._.Computational.failure⇔∀¬STS
d_failure'8660''8704''172'STS_330 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_failure'8660''8704''172'STS_330 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_failure'8660''8704''172'STS_330 v4 v5
du_failure'8660''8704''172'STS_330 ::
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_failure'8660''8704''172'STS_330 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2298 erased
      (\ v2 -> coe du_'8704''172'STS'8658'failure_304 (coe v0) (coe v1))
-- Class.Computational._.Computational.recomputeProof
d_recomputeProof_334 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  T_Computational_216 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_ComputationResult_28
d_recomputeProof_334 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_recomputeProof_334 v4 v5
du_recomputeProof_334 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
du_recomputeProof_334 v0 v1 = coe d_computeProof_240 v0 v1
-- Class.Computational._._.completeness
d_completeness_354 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_completeness_354 = erased
-- Class.Computational._._.compute
d_compute_356 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_compute_356 ~v0 ~v1 ~v2 ~v3 v4 = du_compute_356 v4
du_compute_356 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
du_compute_356 v0 = coe du_compute_242 (coe v0)
-- Class.Computational._._.computeFail
d_computeFail_358 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> T_Computational_216 -> AgdaAny -> ()
d_computeFail_358 = erased
-- Class.Computational._._.computeProof
d_computeProof_360 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_computeProof_360 v0 = coe d_computeProof_240 (coe v0)
-- Class.Computational._._.failure⇒∀¬STS
d_failure'8658''8704''172'STS_362 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_failure'8658''8704''172'STS_362 = erased
-- Class.Computational._._.failure⇔∀¬STS
d_failure'8660''8704''172'STS_364 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_failure'8660''8704''172'STS_364 ~v0 ~v1 ~v2 ~v3 v4
  = du_failure'8660''8704''172'STS_364 v4
du_failure'8660''8704''172'STS_364 ::
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_failure'8660''8704''172'STS_364 v0
  = coe du_failure'8660''8704''172'STS_330 (coe v0)
-- Class.Computational._._.recomputeProof
d_recomputeProof_366 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_ComputationResult_28
d_recomputeProof_366 ~v0 ~v1 ~v2 ~v3 v4 = du_recomputeProof_366 v4
du_recomputeProof_366 ::
  T_Computational_216 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_ComputationResult_28
du_recomputeProof_366 v0 v1 v2 v3
  = coe du_recomputeProof_334 (coe v0) v1
-- Class.Computational._._.∀¬STS⇒failure
d_'8704''172'STS'8658'failure_368 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8704''172'STS'8658'failure_368 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8704''172'STS'8658'failure_368 v4
du_'8704''172'STS'8658'failure_368 ::
  T_Computational_216 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8704''172'STS'8658'failure_368 v0 v1 v2
  = coe du_'8704''172'STS'8658'failure_304 (coe v0) v1
-- Class.Computational._._.≡-success⇔STS
d_'8801''45'success'8660'STS_370 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8801''45'success'8660'STS_370 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8801''45'success'8660'STS_370 v4
du_'8801''45'success'8660'STS_370 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8801''45'success'8660'STS_370 v0
  = coe du_'8801''45'success'8660'STS_256 (coe v0)
-- Class.Computational._.ExtendedRelSTS
d_ExtendedRelSTS_372 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  () -> AgdaAny -> T_ComputationResult_28 -> ()
d_ExtendedRelSTS_372 = erased
-- Class.Computational._.ExtendedRel-compute
d_ExtendedRel'45'compute_374 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 -> AgdaAny -> AgdaAny
d_ExtendedRel'45'compute_374 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_ExtendedRel'45'compute_374 v4 v5
du_ExtendedRel'45'compute_374 ::
  T_Computational_216 -> AgdaAny -> AgdaAny
du_ExtendedRel'45'compute_374 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
              (coe du_Functor'45'ComputationResult_132) () erased () erased
              (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
              (coe d_computeProof_240 v0 v1) in
    coe
      (case coe v2 of
         C_success_36 v3
           -> coe
                MAlonzo.Code.Function.Bundles.d_to_1724
                (coe du_'8801''45'success'8660'STS_256 (coe v0) (coe v1) (coe v3))
                erased
         C_failure_38 v3 -> erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.Computational._.ExtendedRel-rightUnique
d_ExtendedRel'45'rightUnique_394 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny ->
  T_ComputationResult_28 ->
  T_ComputationResult_28 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ExtendedRel'45'rightUnique_394 = erased
-- Class.Computational._.computational⇒rightUnique
d_computational'8658'rightUnique_436 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_computational'8658'rightUnique_436 = erased
-- Class.Computational._.Computational⇒Dec
d_Computational'8658'Dec_452 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Computational'8658'Dec_452 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_Computational'8658'Dec_452 v4 v5 v6 v7
du_Computational'8658'Dec_452 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Computational'8658'Dec_452 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
              (coe du_Functor'45'ComputationResult_132) () erased () erased
              (\ v4 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
              (coe d_computeProof_240 v0 v1) in
    coe
      (let v5
             = let v5
                     = coe
                         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                         (coe du_Functor'45'ComputationResult_132) () erased () erased
                         (\ v5 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                         (coe d_computeProof_240 v0 v1) in
               coe
                 (case coe v5 of
                    C_success_36 v6
                      -> coe
                           MAlonzo.Code.Function.Bundles.d_to_1724
                           (coe du_'8801''45'success'8660'STS_256 (coe v0) (coe v1) (coe v6))
                           erased
                    C_failure_38 v6 -> erased
                    _ -> MAlonzo.RTE.mazUnreachableError) in
       coe
         (case coe v4 of
            C_success_36 v6
              -> let v7
                       = coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 v3 v6 v2 in
                 coe
                   (case coe v7 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                        -> if coe v8
                             then coe
                                    seq (coe v9)
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                       (coe v8)
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                          (coe v5)))
                             else coe
                                    seq (coe v9)
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                       (coe v8)
                                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            C_failure_38 v6
              -> coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Computational._._.completeness
d_completeness_518 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_completeness_518 = erased
-- Class.Computational._._.computeFail
d_computeFail_520 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 -> T_Computational_216 -> AgdaAny -> ()
d_computeFail_520 = erased
-- Class.Computational._._.computeProof
d_computeProof_522 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_computeProof_522 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_computeProof_522 v4
du_computeProof_522 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
du_computeProof_522 v0 = coe d_computeProof_240 (coe v0)
-- Class.Computational._._.compute
d_compute_524 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_compute_524 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_compute_524 v4
du_compute_524 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
du_compute_524 v0 = coe du_compute_242 (coe v0)
-- Class.Computational._._.failure⇒∀¬STS
d_failure'8658''8704''172'STS_526 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_failure'8658''8704''172'STS_526 = erased
-- Class.Computational._._.failure⇔∀¬STS
d_failure'8660''8704''172'STS_528 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_failure'8660''8704''172'STS_528 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_failure'8660''8704''172'STS_528 v4
du_failure'8660''8704''172'STS_528 ::
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_failure'8660''8704''172'STS_528 v0
  = coe du_failure'8660''8704''172'STS_330 (coe v0)
-- Class.Computational._._.recomputeProof
d_recomputeProof_530 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_ComputationResult_28
d_recomputeProof_530 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_recomputeProof_530 v4
du_recomputeProof_530 ::
  T_Computational_216 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_ComputationResult_28
du_recomputeProof_530 v0 v1 v2 v3
  = coe du_recomputeProof_334 (coe v0) v1
-- Class.Computational._._.∀¬STS⇒failure
d_'8704''172'STS'8658'failure_532 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8704''172'STS'8658'failure_532 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'8704''172'STS'8658'failure_532 v4
du_'8704''172'STS'8658'failure_532 ::
  T_Computational_216 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8704''172'STS'8658'failure_532 v0 v1 v2
  = coe du_'8704''172'STS'8658'failure_304 (coe v0) v1
-- Class.Computational._._.≡-success⇔STS
d_'8801''45'success'8660'STS_534 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8801''45'success'8660'STS_534 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'8801''45'success'8660'STS_534 v4
du_'8801''45'success'8660'STS_534 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8801''45'success'8660'STS_534 v0
  = coe du_'8801''45'success'8660'STS_256 (coe v0)
-- Class.Computational._._.completeness
d_completeness_538 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_completeness_538 = erased
-- Class.Computational._._.computeFail
d_computeFail_540 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 -> T_Computational_216 -> AgdaAny -> ()
d_computeFail_540 = erased
-- Class.Computational._._.computeProof
d_computeProof_542 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_computeProof_542 v0 = coe d_computeProof_240 (coe v0)
-- Class.Computational._._.compute
d_compute_544 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
d_compute_544 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_compute_544 v5
du_compute_544 ::
  T_Computational_216 -> AgdaAny -> T_ComputationResult_28
du_compute_544 v0 = coe du_compute_242 (coe v0)
-- Class.Computational._._.failure⇒∀¬STS
d_failure'8658''8704''172'STS_546 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_failure'8658''8704''172'STS_546 = erased
-- Class.Computational._._.failure⇔∀¬STS
d_failure'8660''8704''172'STS_548 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_failure'8660''8704''172'STS_548 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_failure'8660''8704''172'STS_548 v5
du_failure'8660''8704''172'STS_548 ::
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_failure'8660''8704''172'STS_548 v0
  = coe du_failure'8660''8704''172'STS_330 (coe v0)
-- Class.Computational._._.recomputeProof
d_recomputeProof_550 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_ComputationResult_28
d_recomputeProof_550 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_recomputeProof_550 v5
du_recomputeProof_550 ::
  T_Computational_216 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_ComputationResult_28
du_recomputeProof_550 v0 v1 v2 v3
  = coe du_recomputeProof_334 (coe v0) v1
-- Class.Computational._._.∀¬STS⇒failure
d_'8704''172'STS'8658'failure_552 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8704''172'STS'8658'failure_552 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8704''172'STS'8658'failure_552 v5
du_'8704''172'STS'8658'failure_552 ::
  T_Computational_216 ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8704''172'STS'8658'failure_552 v0 v1 v2
  = coe du_'8704''172'STS'8658'failure_304 (coe v0) v1
-- Class.Computational._._.≡-success⇔STS
d_'8801''45'success'8660'STS_554 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8801''45'success'8660'STS_554 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8801''45'success'8660'STS_554 v5
du_'8801''45'success'8660'STS_554 ::
  T_Computational_216 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8801''45'success'8660'STS_554 v0
  = coe du_'8801''45'success'8660'STS_256 (coe v0)
-- Class.Computational._.compute-ext≡
d_compute'45'ext'8801'_556 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  T_Computational_216 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compute'45'ext'8801'_556 = erased
-- Class.Computational.Computational⇒Dec'
d_Computational'8658'Dec''_584 ::
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Computational_216 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Computational'8658'Dec''_584 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_Computational'8658'Dec''_584 v3 v5
du_Computational'8658'Dec''_584 ::
  AgdaAny ->
  T_Computational_216 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_Computational'8658'Dec''_584 v0 v1
  = let v2 = coe d_computeProof_240 v1 v0 in
    coe
      (case coe v2 of
         C_success_36 v3
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v3))
         C_failure_38 v3
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.Computational.InjectError
d_InjectError_604 a0 a1 = ()
newtype T_InjectError_604
  = C_InjectError'46'constructor_59939 (AgdaAny -> AgdaAny)
-- Class.Computational.InjectError.injectError
d_injectError_612 :: T_InjectError_604 -> AgdaAny -> AgdaAny
d_injectError_612 v0
  = case coe v0 of
      C_InjectError'46'constructor_59939 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Computational.InjectError-⊥
d_InjectError'45''8869'_614 :: () -> T_InjectError_604
d_InjectError'45''8869'_614 ~v0 = du_InjectError'45''8869'_614
du_InjectError'45''8869'_614 :: T_InjectError_604
du_InjectError'45''8869'_614
  = coe
      C_InjectError'46'constructor_59939
      (coe (\ v0 -> MAlonzo.RTE.mazUnreachableError))
-- Class.Computational.InjectError-Id
d_InjectError'45'Id_618 :: () -> T_InjectError_604
d_InjectError'45'Id_618 ~v0 = du_InjectError'45'Id_618
du_InjectError'45'Id_618 :: T_InjectError_604
du_InjectError'45'Id_618
  = coe C_InjectError'46'constructor_59939 (coe (\ v0 -> v0))
