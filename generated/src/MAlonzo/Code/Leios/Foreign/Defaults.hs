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

module MAlonzo.Code.Leios.Foreign.Defaults where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Axiom.Set
import qualified MAlonzo.Code.Axiom.Set.Rel
import qualified MAlonzo.Code.Axiom.Set.TotalMap
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.DecEq.Instances
import qualified MAlonzo.Code.Class.Decidable.Instances
import qualified MAlonzo.Code.Class.Hashable
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Leios.Base
import qualified MAlonzo.Code.Leios.Blocks
import qualified MAlonzo.Code.Leios.FFD
import qualified MAlonzo.Code.Leios.KeyRegistration
import qualified MAlonzo.Code.Leios.Protocol
import qualified MAlonzo.Code.Leios.Short
import qualified MAlonzo.Code.Leios.SpecStructure
import qualified MAlonzo.Code.Leios.VRF
import qualified MAlonzo.Code.Leios.Voting
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory

-- Leios.Foreign.Defaults.numberOfParties
d_numberOfParties_182 :: Integer
d_numberOfParties_182 = coe (1 :: Integer)
-- Leios.Foreign.Defaults.SUT-id
d_SUT'45'id_184 :: MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_SUT'45'id_184 = coe MAlonzo.Code.Data.Fin.Base.C_zero_12
-- Leios.Foreign.Defaults.htx
d_htx_186 :: MAlonzo.Code.Class.Hashable.T_Hashable_8
d_htx_186
  = coe
      MAlonzo.Code.Class.Hashable.C_Hashable'46'constructor_9
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d_intersperse_30
              ("#" :: Data.Text.Text)
              (coe
                 MAlonzo.Code.Data.List.Base.du_map_22
                 (coe MAlonzo.Code.Data.Nat.Show.d_show_56) (coe v0))))
-- Leios.Foreign.Defaults.d-Abstract
d_d'45'Abstract_188 ::
  MAlonzo.Code.Leios.Abstract.T_LeiosAbstract_4
d_d'45'Abstract_188
  = coe
      MAlonzo.Code.Leios.Abstract.C_LeiosAbstract'46'constructor_383
      (coe MAlonzo.Code.Class.DecEq.Instances.du_DecEq'45'Fin_52)
      (coe
         MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
         (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) d_htx_186
      (5 :: Integer)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Leios.Foreign.Defaults._.BodyHash
d_BodyHash_200 :: ()
d_BodyHash_200 = erased
-- Leios.Foreign.Defaults._.DecEq-Hash
d_DecEq'45'Hash_202 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Hash_202
  = coe
      MAlonzo.Code.Leios.Abstract.d_DecEq'45'Hash_52
      (coe d_d'45'Abstract_188)
-- Leios.Foreign.Defaults._.DecEq-PoolID
d_DecEq'45'PoolID_204 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'PoolID_204
  = coe MAlonzo.Code.Class.DecEq.Instances.du_DecEq'45'Fin_52
-- Leios.Foreign.Defaults._.Hash
d_Hash_206 :: ()
d_Hash_206 = erased
-- Leios.Foreign.Defaults._.Hashable-Txs
d_Hashable'45'Txs_208 :: MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'Txs_208 = coe d_htx_186
-- Leios.Foreign.Defaults._.L
d_L_210 :: Integer
d_L_210 = coe (5 :: Integer)
-- Leios.Foreign.Defaults._.NonZero-L
d_NonZero'45'L_212 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_NonZero'45'L_212
  = coe
      MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Leios.Foreign.Defaults._.PoolID
d_PoolID_214 :: ()
d_PoolID_214 = erased
-- Leios.Foreign.Defaults._.PrivKey
d_PrivKey_216 :: ()
d_PrivKey_216 = erased
-- Leios.Foreign.Defaults._.Sig
d_Sig_218 :: ()
d_Sig_218 = erased
-- Leios.Foreign.Defaults._.Tx
d_Tx_220 :: ()
d_Tx_220 = erased
-- Leios.Foreign.Defaults._.Vote
d_Vote_222 :: ()
d_Vote_222 = erased
-- Leios.Foreign.Defaults._.VrfPf
d_VrfPf_224 :: ()
d_VrfPf_224 = erased
-- Leios.Foreign.Defaults._.sign
d_sign_226 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_sign_226 ~v0 ~v1 = du_sign_226
du_sign_226 :: MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_sign_226 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Leios.Foreign.Defaults._.vote
d_vote_228 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_vote_228 ~v0 ~v1 = du_vote_228
du_vote_228 :: MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_vote_228 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Leios.Foreign.Defaults._.LeiosVRF
d_LeiosVRF_232 = ()
-- Leios.Foreign.Defaults._.VRF
d_VRF_234 a0 a1 a2 = ()
-- Leios.Foreign.Defaults._.LeiosVRF.Dec-canProduceEB
d_Dec'45'canProduceEB_238 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceEB_238
  = coe MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceEB_204
-- Leios.Foreign.Defaults._.LeiosVRF.Dec-canProduceIB
d_Dec'45'canProduceIB_240 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceIB_240
  = coe MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceIB_134
-- Leios.Foreign.Defaults._.LeiosVRF.Dec-canProduceV
d_Dec'45'canProduceV_242 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV_242
  = coe MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV_264
-- Leios.Foreign.Defaults._.LeiosVRF.Dec-canProduceV1
d_Dec'45'canProduceV1_244 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV1_244
  = coe MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV1_300
-- Leios.Foreign.Defaults._.LeiosVRF.Dec-canProduceV2
d_Dec'45'canProduceV2_246 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV2_246
  = coe MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV2_336
-- Leios.Foreign.Defaults._.LeiosVRF.PubKey
d_PubKey_248 :: MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> ()
d_PubKey_248 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.canProduceEB
d_canProduceEB_250 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_canProduceEB_250 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.canProduceEBPub
d_canProduceEBPub_252 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceEBPub_252 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.canProduceIB
d_canProduceIB_254 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_canProduceIB_254 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.canProduceIBPub
d_canProduceIBPub_256 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceIBPub_256 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.canProduceV
d_canProduceV_258 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceV_258 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.canProduceV1
d_canProduceV1_260 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceV1_260 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.canProduceV2
d_canProduceV2_262 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceV2_262 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.eval
d_eval_264 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_264 v0
  = coe
      MAlonzo.Code.Leios.VRF.d_eval_60
      (coe MAlonzo.Code.Leios.VRF.d_vrf_90 (coe v0))
-- Leios.Foreign.Defaults._.LeiosVRF.genEBInput
d_genEBInput_266 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> Integer -> Integer
d_genEBInput_266 v0
  = coe MAlonzo.Code.Leios.VRF.d_genEBInput_102 (coe v0)
-- Leios.Foreign.Defaults._.LeiosVRF.genIBInput
d_genIBInput_268 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> Integer -> Integer
d_genIBInput_268 v0
  = coe MAlonzo.Code.Leios.VRF.d_genIBInput_100 (coe v0)
-- Leios.Foreign.Defaults._.LeiosVRF.genV1Input
d_genV1Input_270 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> Integer -> Integer
d_genV1Input_270 v0
  = coe MAlonzo.Code.Leios.VRF.d_genV1Input_106 (coe v0)
-- Leios.Foreign.Defaults._.LeiosVRF.genV2Input
d_genV2Input_272 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> Integer -> Integer
d_genV2Input_272 v0
  = coe MAlonzo.Code.Leios.VRF.d_genV2Input_108 (coe v0)
-- Leios.Foreign.Defaults._.LeiosVRF.genVInput
d_genVInput_274 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 -> Integer -> Integer
d_genVInput_274 v0
  = coe MAlonzo.Code.Leios.VRF.d_genVInput_104 (coe v0)
-- Leios.Foreign.Defaults._.LeiosVRF.isKeyPair
d_isKeyPair_276 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_isKeyPair_276 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.verify
d_verify_278 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  AgdaAny ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_verify_278 = erased
-- Leios.Foreign.Defaults._.LeiosVRF.vrf
d_vrf_280 ::
  MAlonzo.Code.Leios.VRF.T_LeiosVRF_64 ->
  MAlonzo.Code.Leios.VRF.T_VRF_44
d_vrf_280 v0 = coe MAlonzo.Code.Leios.VRF.d_vrf_90 (coe v0)
-- Leios.Foreign.Defaults._.VRF.eval
d_eval_284 ::
  MAlonzo.Code.Leios.VRF.T_VRF_44 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_284 v0 = coe MAlonzo.Code.Leios.VRF.d_eval_60 (coe v0)
-- Leios.Foreign.Defaults._.VRF.isKeyPair
d_isKeyPair_286 ::
  MAlonzo.Code.Leios.VRF.T_VRF_44 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_isKeyPair_286 = erased
-- Leios.Foreign.Defaults._.VRF.verify
d_verify_288 ::
  MAlonzo.Code.Leios.VRF.T_VRF_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_verify_288 = erased
-- Leios.Foreign.Defaults.d-VRF
d_d'45'VRF_290 :: MAlonzo.Code.Leios.VRF.T_LeiosVRF_64
d_d'45'VRF_290
  = coe
      MAlonzo.Code.Leios.VRF.C_LeiosVRF'46'constructor_489
      (coe
         MAlonzo.Code.Leios.VRF.C_VRF'46'constructor_163
         (\ v0 v1 ->
            coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v0)))
      (\ v0 -> v0) (\ v0 -> v0) (\ v0 -> v0) (\ v0 -> v0) (\ v0 -> v0)
-- Leios.Foreign.Defaults._.Dec-canProduceEB
d_Dec'45'canProduceEB_310 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceEB_310
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceEB_204
      (coe d_d'45'VRF_290)
-- Leios.Foreign.Defaults._.Dec-canProduceIB
d_Dec'45'canProduceIB_312 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_Dec'45'canProduceIB_312
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceIB_134
      (coe d_d'45'VRF_290)
-- Leios.Foreign.Defaults._.Dec-canProduceV
d_Dec'45'canProduceV_314 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV_314
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV_264
      (coe d_d'45'VRF_290)
-- Leios.Foreign.Defaults._.Dec-canProduceV1
d_Dec'45'canProduceV1_316 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV1_316
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV1_300
      (coe d_d'45'VRF_290)
-- Leios.Foreign.Defaults._.Dec-canProduceV2
d_Dec'45'canProduceV2_318 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_Dec'45'canProduceV2_318
  = coe
      MAlonzo.Code.Leios.VRF.du_Dec'45'canProduceV2_336
      (coe d_d'45'VRF_290)
-- Leios.Foreign.Defaults._.PubKey
d_PubKey_320 :: ()
d_PubKey_320 = erased
-- Leios.Foreign.Defaults._.canProduceEB
d_canProduceEB_322 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_canProduceEB_322 = erased
-- Leios.Foreign.Defaults._.canProduceEBPub
d_canProduceEBPub_324 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceEBPub_324 = erased
-- Leios.Foreign.Defaults._.canProduceIB
d_canProduceIB_326 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_canProduceIB_326 = erased
-- Leios.Foreign.Defaults._.canProduceIBPub
d_canProduceIBPub_328 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceIBPub_328 = erased
-- Leios.Foreign.Defaults._.canProduceV
d_canProduceV_330 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceV_330 = erased
-- Leios.Foreign.Defaults._.canProduceV1
d_canProduceV1_332 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceV1_332 = erased
-- Leios.Foreign.Defaults._.canProduceV2
d_canProduceV2_334 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer -> ()
d_canProduceV2_334 = erased
-- Leios.Foreign.Defaults._.eval
d_eval_336 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_336 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v0)
-- Leios.Foreign.Defaults._.genEBInput
d_genEBInput_338 :: Integer -> Integer
d_genEBInput_338 v0 = coe v0
-- Leios.Foreign.Defaults._.genIBInput
d_genIBInput_340 :: Integer -> Integer
d_genIBInput_340 v0 = coe v0
-- Leios.Foreign.Defaults._.genV1Input
d_genV1Input_342 :: Integer -> Integer
d_genV1Input_342 v0 = coe v0
-- Leios.Foreign.Defaults._.genV2Input
d_genV2Input_344 :: Integer -> Integer
d_genV2Input_344 v0 = coe v0
-- Leios.Foreign.Defaults._.genVInput
d_genVInput_346 :: Integer -> Integer
d_genVInput_346 v0 = coe v0
-- Leios.Foreign.Defaults._.isKeyPair
d_isKeyPair_348 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_isKeyPair_348 = erased
-- Leios.Foreign.Defaults._.verify
d_verify_350 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> ()
d_verify_350 = erased
-- Leios.Foreign.Defaults._.vrf
d_vrf_352 :: MAlonzo.Code.Leios.VRF.T_VRF_44
d_vrf_352
  = coe MAlonzo.Code.Leios.VRF.d_vrf_90 (coe d_d'45'VRF_290)
-- Leios.Foreign.Defaults._._∈ᴮ_
d__'8712''7470'__356 ::
  () ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> [Integer] -> ()
d__'8712''7470'__356 = erased
-- Leios.Foreign.Defaults._.EBRef
d_EBRef_358 :: ()
d_EBRef_358 = erased
-- Leios.Foreign.Defaults._.EndorserBlock
d_EndorserBlock_360 :: ()
d_EndorserBlock_360 = erased
-- Leios.Foreign.Defaults._.EndorserBlockOSig
d_EndorserBlockOSig_362 a0 = ()
-- Leios.Foreign.Defaults._.Hashable-EndorserBlock
d_Hashable'45'EndorserBlock_364 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'EndorserBlock_364
  = coe MAlonzo.Code.Leios.Blocks.du_Hashable'45'EndorserBlock_248
-- Leios.Foreign.Defaults._.Hashable-IBBody
d_Hashable'45'IBBody_366 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8
d_Hashable'45'IBBody_366
  = coe
      MAlonzo.Code.Leios.Blocks.d_Hashable'45'IBBody_140
      (coe d_d'45'Abstract_188)
-- Leios.Foreign.Defaults._.IBBody
d_IBBody_368 = ()
-- Leios.Foreign.Defaults._.IBHeader
d_IBHeader_370 :: ()
d_IBHeader_370 = erased
-- Leios.Foreign.Defaults._.IBHeaderOSig
d_IBHeaderOSig_372 a0 = ()
-- Leios.Foreign.Defaults._.IBRef
d_IBRef_374 :: ()
d_IBRef_374 = erased
-- Leios.Foreign.Defaults._.InputBlock
d_InputBlock_376 = ()
-- Leios.Foreign.Defaults._.IsBlock
d_IsBlock_378 a0 = ()
-- Leios.Foreign.Defaults._.IsBlock-EndorserBlockOSig
d_IsBlock'45'EndorserBlockOSig_380 ::
  Bool -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_IsBlock'45'EndorserBlockOSig_380 v0
  = coe MAlonzo.Code.Leios.Blocks.du_IsBlock'45'EndorserBlockOSig_268
-- Leios.Foreign.Defaults._.IsBlock-IBHeaderOSig
d_IsBlock'45'IBHeaderOSig_382 ::
  Bool -> MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_IsBlock'45'IBHeaderOSig_382 v0
  = coe MAlonzo.Code.Leios.Blocks.du_IsBlock'45'IBHeaderOSig_138
-- Leios.Foreign.Defaults._.IsBlock-InputBlock
d_IsBlock'45'InputBlock_384 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_IsBlock'45'InputBlock_384
  = coe MAlonzo.Code.Leios.Blocks.du_IsBlock'45'InputBlock_144
-- Leios.Foreign.Defaults._.OSig
d_OSig_386 :: Bool -> ()
d_OSig_386 = erased
-- Leios.Foreign.Defaults._.PreEndorserBlock
d_PreEndorserBlock_388 :: ()
d_PreEndorserBlock_388 = erased
-- Leios.Foreign.Defaults._.PreIBHeader
d_PreIBHeader_390 :: ()
d_PreIBHeader_390 = erased
-- Leios.Foreign.Defaults._.ebValid
d_ebValid_392 a0 = ()
-- Leios.Foreign.Defaults._.ebValid?
d_ebValid'63'_394 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ebValid'63'_394 v0
  = coe MAlonzo.Code.Leios.Blocks.du_ebValid'63'_318
-- Leios.Foreign.Defaults._.ffdAbstract
d_ffdAbstract_396 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.FFD.T_FFDAbstract_4
d_ffdAbstract_396
  = coe MAlonzo.Code.Leios.Blocks.du_ffdAbstract_462
-- Leios.Foreign.Defaults._.getEBRef
d_getEBRef_398 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_getEBRef_398 = coe MAlonzo.Code.Leios.Blocks.du_getEBRef_308
-- Leios.Foreign.Defaults._.getIBRef
d_getIBRef_400 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_getIBRef_400 = coe MAlonzo.Code.Leios.Blocks.du_getIBRef_178
-- Leios.Foreign.Defaults._.ibBodyValid
d_ibBodyValid_402 a0 = ()
-- Leios.Foreign.Defaults._.ibBodyValid?
d_ibBodyValid'63'_404 ::
  MAlonzo.Code.Leios.Blocks.T_IBBody_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibBodyValid'63'_404 ~v0 = du_ibBodyValid'63'_404
du_ibBodyValid'63'_404 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_ibBodyValid'63'_404
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Leios.Foreign.Defaults._.ibHeaderValid
d_ibHeaderValid_406 a0 = ()
-- Leios.Foreign.Defaults._.ibHeaderValid?
d_ibHeaderValid'63'_408 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibHeaderValid'63'_408 v0
  = coe MAlonzo.Code.Leios.Blocks.du_ibHeaderValid'63'_194
-- Leios.Foreign.Defaults._.ibValid
d_ibValid_410 :: MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> ()
d_ibValid_410 = erased
-- Leios.Foreign.Defaults._.ibValid?
d_ibValid'63'_412 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_ibValid'63'_412
  = coe MAlonzo.Code.Leios.Blocks.du_ibValid'63'_208
-- Leios.Foreign.Defaults._.lotteryPf
d_lotteryPf_414 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_lotteryPf_414 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_54 (coe v0)
-- Leios.Foreign.Defaults._.mkEB
d_mkEB_416 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_mkEB_416
  = coe
      MAlonzo.Code.Leios.Blocks.d_mkEB_272 (coe d_d'45'Abstract_188)
-- Leios.Foreign.Defaults._.mkIBHeader
d_mkIBHeader_418 ::
  MAlonzo.Code.Class.Hashable.T_Hashable_8 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [Integer] -> MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80
d_mkIBHeader_418
  = coe
      MAlonzo.Code.Leios.Blocks.d_mkIBHeader_146
      (coe d_d'45'Abstract_188)
-- Leios.Foreign.Defaults._.producerID
d_producerID_420 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_producerID_420 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_52 (coe v0)
-- Leios.Foreign.Defaults._.slotNumber
d_slotNumber_422 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> Integer
d_slotNumber_422 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_50 (coe v0)
-- Leios.Foreign.Defaults._.vsValid
d_vsValid_424 a0 = ()
-- Leios.Foreign.Defaults._.vsValid?
d_vsValid'63'_426 ::
  [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_vsValid'63'_426 v0
  = coe MAlonzo.Code.Leios.Blocks.du_vsValid'63'_328
-- Leios.Foreign.Defaults._.EndorserBlockOSig.ebRefs
d_ebRefs_430 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ebRefs_430 v0
  = coe MAlonzo.Code.Leios.Blocks.d_ebRefs_240 (coe v0)
-- Leios.Foreign.Defaults._.EndorserBlockOSig.ibRefs
d_ibRefs_432 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ibRefs_432 v0
  = coe MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v0)
-- Leios.Foreign.Defaults._.EndorserBlockOSig.lotteryPf
d_lotteryPf_434 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_lotteryPf_434 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_236 (coe v0)
-- Leios.Foreign.Defaults._.EndorserBlockOSig.producerID
d_producerID_436 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_producerID_436 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_234 (coe v0)
-- Leios.Foreign.Defaults._.EndorserBlockOSig.signature
d_signature_438 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> AgdaAny
d_signature_438 v0
  = coe MAlonzo.Code.Leios.Blocks.d_signature_242 (coe v0)
-- Leios.Foreign.Defaults._.EndorserBlockOSig.slotNumber
d_slotNumber_440 ::
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> Integer
d_slotNumber_440 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_232 (coe v0)
-- Leios.Foreign.Defaults._.GenFFD.Body
d_Body_444 a0 = ()
-- Leios.Foreign.Defaults._.GenFFD.Header
d_Header_446 a0 = ()
-- Leios.Foreign.Defaults._.GenFFD.ID
d_ID_448 :: MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> ()
d_ID_448 = erased
-- Leios.Foreign.Defaults._.GenFFD.bodyValid
d_bodyValid_450 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Body_342 -> ()
d_bodyValid_450 = erased
-- Leios.Foreign.Defaults._.GenFFD.bodyValid?
d_bodyValid'63'_452 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Body_342 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_bodyValid'63'_452 v0 v1
  = coe MAlonzo.Code.Leios.Blocks.du_bodyValid'63'_434 v1
-- Leios.Foreign.Defaults._.GenFFD.headerValid
d_headerValid_456 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 -> ()
d_headerValid_456 = erased
-- Leios.Foreign.Defaults._.GenFFD.headerValid?
d_headerValid'63'_458 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_headerValid'63'_458 v0 v1
  = coe MAlonzo.Code.Leios.Blocks.du_headerValid'63'_420 v1
-- Leios.Foreign.Defaults._.GenFFD.isValid
d_isValid_464 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_isValid_464 = erased
-- Leios.Foreign.Defaults._.GenFFD.isValid?
d_isValid'63'_466 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isValid'63'_466 v0 v1
  = coe MAlonzo.Code.Leios.Blocks.du_isValid'63'_446 v1
-- Leios.Foreign.Defaults._.GenFFD.match
d_match_468 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Leios.Blocks.T_Body_342 -> ()
d_match_468 = erased
-- Leios.Foreign.Defaults._.GenFFD.matchIB
d_matchIB_470 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Leios.Blocks.T_IBBody_108 -> ()
d_matchIB_470 = erased
-- Leios.Foreign.Defaults._.GenFFD.matchIB?
d_matchIB'63'_472 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Leios.Blocks.T_IBBody_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_matchIB'63'_472 v0 v1 v2
  = coe
      MAlonzo.Code.Leios.Blocks.du_matchIB'63'_378
      (coe d_d'45'Abstract_188) v1 v2
-- Leios.Foreign.Defaults._.GenFFD.msgID
d_msgID_474 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_msgID_474 = coe MAlonzo.Code.Leios.Blocks.du_msgID_452
-- Leios.Foreign.Defaults._.IBBody.txs
d_txs_492 :: MAlonzo.Code.Leios.Blocks.T_IBBody_108 -> [Integer]
d_txs_492 v0 = coe MAlonzo.Code.Leios.Blocks.d_txs_112 (coe v0)
-- Leios.Foreign.Defaults._.IBHeaderOSig.bodyHash
d_bodyHash_496 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_bodyHash_496 v0
  = coe MAlonzo.Code.Leios.Blocks.d_bodyHash_100 (coe v0)
-- Leios.Foreign.Defaults._.IBHeaderOSig.lotteryPf
d_lotteryPf_498 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_lotteryPf_498 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_98 (coe v0)
-- Leios.Foreign.Defaults._.IBHeaderOSig.producerID
d_producerID_500 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_producerID_500 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_96 (coe v0)
-- Leios.Foreign.Defaults._.IBHeaderOSig.signature
d_signature_502 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> AgdaAny
d_signature_502 v0
  = coe MAlonzo.Code.Leios.Blocks.d_signature_102 (coe v0)
-- Leios.Foreign.Defaults._.IBHeaderOSig.slotNumber
d_slotNumber_504 ::
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80 -> Integer
d_slotNumber_504 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_94 (coe v0)
-- Leios.Foreign.Defaults._.InputBlock.body
d_body_508 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Leios.Blocks.T_IBBody_108
d_body_508 v0 = coe MAlonzo.Code.Leios.Blocks.d_body_122 (coe v0)
-- Leios.Foreign.Defaults._.InputBlock.bodyHash
d_bodyHash_510 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_bodyHash_510 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_bodyHash_100
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.Foreign.Defaults._.InputBlock.header
d_header_512 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80
d_header_512 v0
  = coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0)
-- Leios.Foreign.Defaults._.InputBlock.lotteryPf
d_lotteryPf_514 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_lotteryPf_514 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_lotteryPf_98
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.Foreign.Defaults._.InputBlock.producerID
d_producerID_516 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_producerID_516 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_producerID_96
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.Foreign.Defaults._.InputBlock.signature
d_signature_518 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_signature_518 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_signature_102
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.Foreign.Defaults._.InputBlock.slotNumber
d_slotNumber_520 ::
  MAlonzo.Code.Leios.Blocks.T_InputBlock_114 -> Integer
d_slotNumber_520 v0
  = coe
      MAlonzo.Code.Leios.Blocks.d_slotNumber_94
      (coe MAlonzo.Code.Leios.Blocks.d_header_120 (coe v0))
-- Leios.Foreign.Defaults._.IsBlock._∈ᴮ_
d__'8712''7470'__524 ::
  () ->
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> [Integer] -> ()
d__'8712''7470'__524 = erased
-- Leios.Foreign.Defaults._.IsBlock.lotteryPf
d_lotteryPf_526 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_lotteryPf_526 v0
  = coe MAlonzo.Code.Leios.Blocks.d_lotteryPf_54 (coe v0)
-- Leios.Foreign.Defaults._.IsBlock.producerID
d_producerID_528 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_producerID_528 v0
  = coe MAlonzo.Code.Leios.Blocks.d_producerID_52 (coe v0)
-- Leios.Foreign.Defaults._.IsBlock.slotNumber
d_slotNumber_530 ::
  MAlonzo.Code.Leios.Blocks.T_IsBlock_40 -> AgdaAny -> Integer
d_slotNumber_530 v0
  = coe MAlonzo.Code.Leios.Blocks.d_slotNumber_50 (coe v0)
-- Leios.Foreign.Defaults._.KeyRegistrationAbstract
d_KeyRegistrationAbstract_542 = ()
-- Leios.Foreign.Defaults._.KeyRegistrationAbstract.Functionality
d_Functionality_546 a0 = ()
-- Leios.Foreign.Defaults._.KeyRegistrationAbstract.Input
d_Input_550 a0 = ()
-- Leios.Foreign.Defaults._.KeyRegistrationAbstract.Output
d_Output_552 a0 = ()
-- Leios.Foreign.Defaults._.KeyRegistrationAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__558 ::
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96 ->
  AgdaAny ->
  MAlonzo.Code.Leios.KeyRegistration.T_Input_88 ->
  MAlonzo.Code.Leios.KeyRegistration.T_Output_92 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__558 = erased
-- Leios.Foreign.Defaults._.KeyRegistrationAbstract.Functionality.State
d_State_560 ::
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96 -> ()
d_State_560 = erased
-- Leios.Foreign.Defaults.d-KeyRegistration
d_d'45'KeyRegistration_574 ::
  MAlonzo.Code.Leios.KeyRegistration.T_KeyRegistrationAbstract_86
d_d'45'KeyRegistration_574 = erased
-- Leios.Foreign.Defaults.d-KeyRegistrationFunctionality
d_d'45'KeyRegistrationFunctionality_576 ::
  MAlonzo.Code.Leios.KeyRegistration.T_Functionality_96
d_d'45'KeyRegistrationFunctionality_576 = erased
-- Leios.Foreign.Defaults._.BaseAbstract
d_BaseAbstract_588 = ()
-- Leios.Foreign.Defaults._.RankingBlock
d_RankingBlock_590 :: ()
d_RankingBlock_590 = erased
-- Leios.Foreign.Defaults._.StakeDistr
d_StakeDistr_592 :: ()
d_StakeDistr_592 = erased
-- Leios.Foreign.Defaults._.BaseAbstract.Cert
d_Cert_598 :: MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> ()
d_Cert_598 = erased
-- Leios.Foreign.Defaults._.BaseAbstract.Functionality
d_Functionality_604 a0 = ()
-- Leios.Foreign.Defaults._.BaseAbstract.Input
d_Input_608 a0 = ()
-- Leios.Foreign.Defaults._.BaseAbstract.Output
d_Output_610 a0 = ()
-- Leios.Foreign.Defaults._.BaseAbstract.V-chkCerts
d_V'45'chkCerts_616 ::
  MAlonzo.Code.Leios.Base.T_BaseAbstract_94 ->
  [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_V'45'chkCerts_616 v0
  = coe MAlonzo.Code.Leios.Base.d_V'45'chkCerts_110 (coe v0)
-- Leios.Foreign.Defaults._.BaseAbstract.VTy
d_VTy_618 :: MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> ()
d_VTy_618 = erased
-- Leios.Foreign.Defaults._.BaseAbstract.initSlot
d_initSlot_620 ::
  MAlonzo.Code.Leios.Base.T_BaseAbstract_94 -> AgdaAny -> Integer
d_initSlot_620 v0
  = coe MAlonzo.Code.Leios.Base.d_initSlot_108 (coe v0)
-- Leios.Foreign.Defaults._.BaseAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__624 ::
  MAlonzo.Code.Leios.Base.T_Functionality_128 ->
  AgdaAny ->
  MAlonzo.Code.Leios.Base.T_Input_112 ->
  MAlonzo.Code.Leios.Base.T_Output_120 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__624 = erased
-- Leios.Foreign.Defaults._.BaseAbstract.Functionality.SUBMIT-total
d_SUBMIT'45'total_626 ::
  MAlonzo.Code.Leios.Base.T_Functionality_128 ->
  AgdaAny ->
  MAlonzo.Code.Data.These.Base.T_These_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_SUBMIT'45'total_626 v0
  = coe MAlonzo.Code.Leios.Base.d_SUBMIT'45'total_152 (coe v0)
-- Leios.Foreign.Defaults._.BaseAbstract.Functionality.State
d_State_628 :: MAlonzo.Code.Leios.Base.T_Functionality_128 -> ()
d_State_628 = erased
-- Leios.Foreign.Defaults.d-Base
d_d'45'Base_658 :: MAlonzo.Code.Leios.Base.T_BaseAbstract_94
d_d'45'Base_658
  = coe
      MAlonzo.Code.Leios.Base.C_BaseAbstract'46'constructor_529
      (\ v0 -> 0 :: Integer)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Leios.Foreign.Defaults.d-BaseFunctionality
d_d'45'BaseFunctionality_666 ::
  MAlonzo.Code.Leios.Base.T_Functionality_128
d_d'45'BaseFunctionality_666
  = coe
      MAlonzo.Code.Leios.Base.C_Functionality'46'constructor_1019
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Leios.Foreign.Defaults.isb
d_isb_676 :: MAlonzo.Code.Leios.Blocks.T_IsBlock_40
d_isb_676
  = coe
      MAlonzo.Code.Leios.Blocks.C_IsBlock'46'constructor_41
      (coe (\ v0 -> 0 :: Integer))
      (coe (\ v0 -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Leios.Foreign.Defaults.hhs
d_hhs_686 :: Bool -> MAlonzo.Code.Class.Hashable.T_Hashable_8
d_hhs_686 ~v0 = du_hhs_686
du_hhs_686 :: MAlonzo.Code.Class.Hashable.T_Hashable_8
du_hhs_686
  = coe
      MAlonzo.Code.Class.Hashable.C_Hashable'46'constructor_9
      (coe (\ v0 -> MAlonzo.Code.Leios.Blocks.d_bodyHash_100 (coe v0)))
-- Leios.Foreign.Defaults.hpe
d_hpe_688 :: MAlonzo.Code.Class.Hashable.T_Hashable_8
d_hpe_688
  = coe
      MAlonzo.Code.Class.Hashable.C_Hashable'46'constructor_9
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d_intersperse_30
              ("#" :: Data.Text.Text)
              (MAlonzo.Code.Leios.Blocks.d_ibRefs_238 (coe v0))))
-- Leios.Foreign.Defaults.FFDState
d_FFDState_690 = ()
data T_FFDState_690
  = C_FFDState'46'constructor_1539 [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
                                   [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
                                   [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]]
                                   [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
                                   [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
                                   [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]]
-- Leios.Foreign.Defaults.FFDState.inIBs
d_inIBs_704 ::
  T_FFDState_690 -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_inIBs_704 v0
  = case coe v0 of
      C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.FFDState.inEBs
d_inEBs_706 ::
  T_FFDState_690 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_inEBs_706 v0
  = case coe v0 of
      C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.FFDState.inVTs
d_inVTs_708 ::
  T_FFDState_690 -> [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]]
d_inVTs_708 v0
  = case coe v0 of
      C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.FFDState.outIBs
d_outIBs_710 ::
  T_FFDState_690 -> [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_outIBs_710 v0
  = case coe v0 of
      C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.FFDState.outEBs
d_outEBs_712 ::
  T_FFDState_690 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_outEBs_712 v0
  = case coe v0 of
      C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.FFDState.outVTs
d_outVTs_714 ::
  T_FFDState_690 -> [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]]
d_outVTs_714 v0
  = case coe v0 of
      C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.flushIns
d_flushIns_716 ::
  T_FFDState_690 -> [MAlonzo.Code.Data.Sum.Base.T__'8846'__30]
d_flushIns_716 v0
  = case coe v0 of
      C_FFDState'46'constructor_1539 v1 v2 v3 v4 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_flushIBs_728 (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe
                      (\ v7 ->
                         coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe MAlonzo.Code.Leios.Blocks.C_ebHeader_338 (coe v7))))
                   (coe v2))
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe
                      (\ v7 ->
                         coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe MAlonzo.Code.Leios.Blocks.C_vHeader_340 (coe v7))))
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults._.flushIBs
d_flushIBs_728 ::
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114] ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216] ->
  [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]] ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114] ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216] ->
  [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]] ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114] ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30]
d_flushIBs_728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_flushIBs_728 v6
du_flushIBs_728 ::
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114] ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30]
du_flushIBs_728 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Leios.Blocks.C_InputBlock'46'constructor_823 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe MAlonzo.Code.Leios.Blocks.C_ibHeader_336 (coe v3)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe MAlonzo.Code.Leios.Blocks.C_ibBody_344 (coe v4)))
                       (coe du_flushIBs_728 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.SimpleFFD
d_SimpleFFD_736 a0 a1 a2 a3 = ()
data T_SimpleFFD_736
  = C_SendIB_744 | C_SendEB_750 | C_SendVS_756 | C_BadSendIB_762 |
    C_BadSendEB_770 | C_BadSendVS_778 | C_Fetch_782
-- Leios.Foreign.Defaults.simple-total
d_simple'45'total_792 ::
  T_FFDState_690 ->
  MAlonzo.Code.Leios.Blocks.T_Header_334 ->
  Maybe MAlonzo.Code.Leios.Blocks.T_Body_342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_simple'45'total_792 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Leios.Blocks.C_ibHeader_336 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> case coe v4 of
                    MAlonzo.Code.Leios.Blocks.C_ibBody_344 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_FFDState'46'constructor_1539 (coe d_inIBs_704 (coe v0))
                              (coe d_inEBs_706 (coe v0)) (coe d_inVTs_708 (coe v0))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Leios.Blocks.C_InputBlock'46'constructor_823
                                    (coe v3) (coe v5))
                                 (coe d_outIBs_710 (coe v0)))
                              (coe d_outEBs_712 (coe v0)) (coe d_outVTs_714 (coe v0)))
                           (coe C_SendIB_744)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                    (coe C_BadSendIB_762)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Leios.Blocks.C_ebHeader_338 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                    (coe C_BadSendEB_770)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_FFDState'46'constructor_1539 (coe d_inIBs_704 (coe v0))
                       (coe d_inEBs_706 (coe v0)) (coe d_inVTs_708 (coe v0))
                       (coe d_outIBs_710 (coe v0))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                          (coe d_outEBs_712 (coe v0)))
                       (coe d_outVTs_714 (coe v0)))
                    (coe C_SendEB_750)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Leios.Blocks.C_vHeader_340 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                    (coe C_BadSendVS_778)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_FFDState'46'constructor_1539 (coe d_inIBs_704 (coe v0))
                       (coe d_inEBs_706 (coe v0)) (coe d_inVTs_708 (coe v0))
                       (coe d_outIBs_710 (coe v0)) (coe d_outEBs_712 (coe v0))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                          (coe d_outVTs_714 (coe v0))))
                    (coe C_SendVS_756)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Leios.Foreign.Defaults.d-FFDFunctionality
d_d'45'FFDFunctionality_820 ::
  MAlonzo.Code.Leios.FFD.T_Functionality_38
d_d'45'FFDFunctionality_820
  = coe
      MAlonzo.Code.Leios.FFD.C_Functionality'46'constructor_457
      (coe
         C_FFDState'46'constructor_1539
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      d_simple'45'total_792
-- Leios.Foreign.Defaults.d-VotingAbstract
d_d'45'VotingAbstract_822 ::
  MAlonzo.Code.Leios.Voting.T_VotingAbstract_6
d_d'45'VotingAbstract_822
  = coe
      MAlonzo.Code.Leios.Voting.C_VotingAbstract'46'constructor_155
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 ->
         MAlonzo.Code.Class.Decidable.Instances.d_Dec'45''8868'_20)
-- Leios.Foreign.Defaults.d-VotingAbstract-2
d_d'45'VotingAbstract'45'2_828 ::
  MAlonzo.Code.Leios.Voting.T_VotingAbstract_6
d_d'45'VotingAbstract'45'2_828
  = coe
      MAlonzo.Code.Leios.Voting.C_VotingAbstract'46'constructor_155
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 ->
         MAlonzo.Code.Class.Decidable.Instances.d_Dec'45''8868'_20)
-- Leios.Foreign.Defaults.st
d_st_834 :: MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6
d_st_834
  = coe
      MAlonzo.Code.Leios.SpecStructure.C_SpecStructure'46'constructor_4605
      d_d'45'Abstract_188 d_isb_676 (\ v0 -> coe du_hhs_686) d_hpe_688
      d_SUT'45'id_184 d_d'45'FFDFunctionality_820 d_d'45'VRF_290
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) d_d'45'Base_658
      d_d'45'BaseFunctionality_666
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      d_d'45'VotingAbstract_822
-- Leios.Foreign.Defaults.st-2
d_st'45'2_836 :: MAlonzo.Code.Leios.SpecStructure.T_SpecStructure_6
d_st'45'2_836
  = coe
      MAlonzo.Code.Leios.SpecStructure.C_SpecStructure'46'constructor_4605
      d_d'45'Abstract_188 d_isb_676 (\ v0 -> coe du_hhs_686) d_hpe_688
      d_SUT'45'id_184 d_d'45'FFDFunctionality_820 d_d'45'VRF_290
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) d_d'45'Base_658
      d_d'45'BaseFunctionality_666
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      d_d'45'VotingAbstract'45'2_828
-- Leios.Foreign.Defaults._._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__840 a0 a1 a2 a3 = ()
-- Leios.Foreign.Defaults._._↑_
d__'8593'__842 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d__'8593'__842
  = let v0 = d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du__'8593'__878 (coe v0))
-- Leios.Foreign.Defaults._._↝_
d__'8605'__844 a0 a1 = ()
-- Leios.Foreign.Defaults._.DecEq-SlotUpkeep
d_DecEq'45'SlotUpkeep_854 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'SlotUpkeep_854
  = coe MAlonzo.Code.Leios.Short.du_DecEq'45'SlotUpkeep_486
-- Leios.Foreign.Defaults._.LeiosInput
d_LeiosInput_876 = ()
-- Leios.Foreign.Defaults._.LeiosOutput
d_LeiosOutput_878 = ()
-- Leios.Foreign.Defaults._.LeiosState
d_LeiosState_880 = ()
-- Leios.Foreign.Defaults._.SlotUpkeep
d_SlotUpkeep_896 = ()
-- Leios.Foreign.Defaults._.addUpkeep
d_addUpkeep_902 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.T_SlotUpkeep_476 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_addUpkeep_902 = coe MAlonzo.Code.Leios.Protocol.du_addUpkeep_594
-- Leios.Foreign.Defaults._.allIBRefsKnown
d_allIBRefsKnown_904 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_allIBRefsKnown_904 = erased
-- Leios.Foreign.Defaults._.allUpkeep
d_allUpkeep_906 :: [MAlonzo.Code.Leios.Short.T_SlotUpkeep_476]
d_allUpkeep_906 = coe MAlonzo.Code.Leios.Short.du_allUpkeep_488
-- Leios.Foreign.Defaults._.initLeiosState
d_initLeiosState_908 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_initLeiosState_908
  = let v0 = d_st_834 in
    coe
      (coe MAlonzo.Code.Leios.Protocol.du_initLeiosState_640 (coe v0))
-- Leios.Foreign.Defaults._.isVoteCertified
d_isVoteCertified_910 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> ()
d_isVoteCertified_910 = erased
-- Leios.Foreign.Defaults._.stake
d_stake_912 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_stake_912
  = let v0 = d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_stake_714 (coe v0))
-- Leios.Foreign.Defaults._.upd
d_upd_914 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_upd_914
  = let v0 = d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_upd_764 (coe v0))
-- Leios.Foreign.Defaults._.upd-preserves-Upkeep
d_upd'45'preserves'45'Upkeep_916 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_upd'45'preserves'45'Upkeep_916 = erased
-- Leios.Foreign.Defaults._.↑-preserves-Upkeep
d_'8593''45'preserves'45'Upkeep_918 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''45'preserves'45'Upkeep_918 = erased
-- Leios.Foreign.Defaults._.LeiosState.BaseState
d_BaseState_968 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_BaseState_968 v0
  = coe MAlonzo.Code.Leios.Protocol.d_BaseState_560 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.EBs
d_EBs_970 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216]
d_EBs_970 v0 = coe MAlonzo.Code.Leios.Protocol.d_EBs_548 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.FFDState
d_FFDState_972 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> T_FFDState_690
d_FFDState_972 v0
  = coe MAlonzo.Code.Leios.Protocol.d_FFDState_540 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.IBBodies
d_IBBodies_974 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBBody_108]
d_IBBodies_974 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBBodies_556 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.IBHeaders
d_IBHeaders_976 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_IBHeaderOSig_80]
d_IBHeaders_976 v0
  = coe MAlonzo.Code.Leios.Protocol.d_IBHeaders_554 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.IBs
d_IBs_978 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Blocks.T_InputBlock_114]
d_IBs_978 v0 = coe MAlonzo.Code.Leios.Protocol.d_IBs_546 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.Ledger
d_Ledger_980 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [Integer]
d_Ledger_980 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Ledger_542 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.SD
d_SD_982 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_SD_982 v0 = coe MAlonzo.Code.Leios.Protocol.d_SD_538 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.ToPropose
d_ToPropose_984 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> [Integer]
d_ToPropose_984 v0
  = coe MAlonzo.Code.Leios.Protocol.d_ToPropose_544 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.Upkeep
d_Upkeep_986 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Leios.Short.T_SlotUpkeep_476]
d_Upkeep_986 v0
  = coe MAlonzo.Code.Leios.Protocol.d_Upkeep_558 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.V
d_V_988 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_V_988 v0 = coe MAlonzo.Code.Leios.Protocol.d_V_536 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.Vs
d_Vs_990 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [[MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]]
d_Vs_990 v0 = coe MAlonzo.Code.Leios.Protocol.d_Vs_550 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.constructLedger
d_constructLedger_992 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  [MAlonzo.Code.Data.These.Base.T_These_38] -> [Integer]
d_constructLedger_992
  = let v0 = d_st_834 in
    coe
      (coe MAlonzo.Code.Leios.Protocol.du_constructLedger_588 (coe v0))
-- Leios.Foreign.Defaults._.LeiosState.lookupEB
d_lookupEB_994 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216
d_lookupEB_994
  = let v0 = d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_lookupEB_564 (coe v0))
-- Leios.Foreign.Defaults._.LeiosState.lookupIB
d_lookupIB_996 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Leios.Blocks.T_InputBlock_114
d_lookupIB_996
  = let v0 = d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_lookupIB_570 (coe v0))
-- Leios.Foreign.Defaults._.LeiosState.lookupTxs
d_lookupTxs_998 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Blocks.T_EndorserBlockOSig_216 -> [Integer]
d_lookupTxs_998
  = let v0 = d_st_834 in
    coe (coe MAlonzo.Code.Leios.Protocol.du_lookupTxs_576 (coe v0))
-- Leios.Foreign.Defaults._.LeiosState.needsUpkeep
d_needsUpkeep_1000 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Leios.Short.T_SlotUpkeep_476 -> ()
d_needsUpkeep_1000 = erased
-- Leios.Foreign.Defaults._.LeiosState.slot
d_slot_1002 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 -> Integer
d_slot_1002 v0
  = coe MAlonzo.Code.Leios.Protocol.d_slot_552 (coe v0)
-- Leios.Foreign.Defaults._.LeiosState.votingState
d_votingState_1004 ::
  MAlonzo.Code.Leios.Protocol.T_LeiosState_506 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_votingState_1004 v0
  = coe MAlonzo.Code.Leios.Protocol.d_votingState_562 (coe v0)
-- Leios.Foreign.Defaults.sd
d_sd_1016 :: MAlonzo.Code.Axiom.Set.TotalMap.T_TotalMap_168
d_sd_1016
  = coe
      MAlonzo.Code.Axiom.Set.TotalMap.C_TotalMap'46'constructor_937
      (coe
         MAlonzo.Code.Axiom.Set.du_singleton_448
         (coe
            MAlonzo.Code.Axiom.Set.d_th_1470
            (coe
               MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_SUT'45'id_184)
            (coe (1 :: Integer))))
      d_total'45'rel'45'helper_1024
-- Leios.Foreign.Defaults._.total-rel-helper
d_total'45'rel'45'helper_1024 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_total'45'rel'45'helper_1024 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Function.Bundles.d_to_1724
         (coe
            MAlonzo.Code.Axiom.Set.Rel.du_dom'8712'_428
            (coe
               MAlonzo.Code.Axiom.Set.d_th_1470
               (coe
                  MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
            (coe
               MAlonzo.Code.Axiom.Set.du_singleton_448
               (coe
                  MAlonzo.Code.Axiom.Set.d_th_1470
                  (coe
                     MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe (1 :: Integer))))
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Function.Bundles.d_to_1724
               (coe
                  MAlonzo.Code.Axiom.Set.du_'8712''45'singleton_458
                  (coe
                     MAlonzo.Code.Axiom.Set.d_th_1470
                     (coe
                        MAlonzo.Code.QabstractZ45ZsetZ45Ztheory.FiniteSetTheory.d_List'45'Model'7496'_8))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe (1 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe (1 :: Integer))))
               erased)))
-- Leios.Foreign.Defaults.s₀
d_s'8320'_1034 :: MAlonzo.Code.Leios.Protocol.T_LeiosState_506
d_s'8320'_1034
  = coe
      MAlonzo.Code.Leios.Protocol.du_initLeiosState_640 (coe d_st_834)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe d_sd_1016)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
