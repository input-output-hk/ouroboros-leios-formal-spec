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

module MAlonzo.Code.CategoricalCrypto where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.Decidable.Core
import qualified MAlonzo.Code.Class.Decidable.Instances
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Sum.Base

-- CategoricalCrypto.Channel
d_Channel_2 = ()
data T_Channel_2 = C_Channel'46'constructor_9
-- CategoricalCrypto.Channel.P
d_P_10 :: T_Channel_2 -> ()
d_P_10 = erased
-- CategoricalCrypto.Channel.rcvType
d_rcvType_12 :: T_Channel_2 -> AgdaAny -> ()
d_rcvType_12 = erased
-- CategoricalCrypto.Channel.sndType
d_sndType_14 :: T_Channel_2 -> AgdaAny -> ()
d_sndType_14 = erased
-- CategoricalCrypto.I
d_I_16 :: T_Channel_2
d_I_16 = erased
-- CategoricalCrypto._ᵀ
d__'7488'_18 :: T_Channel_2 -> T_Channel_2
d__'7488'_18 = erased
-- CategoricalCrypto._.P
d_P_24 :: T_Channel_2 -> ()
d_P_24 = erased
-- CategoricalCrypto._.rcvType
d_rcvType_26 :: T_Channel_2 -> AgdaAny -> ()
d_rcvType_26 = erased
-- CategoricalCrypto._.sndType
d_sndType_28 :: T_Channel_2 -> AgdaAny -> ()
d_sndType_28 = erased
-- CategoricalCrypto._⊗_
d__'8855'__32 :: T_Channel_2 -> T_Channel_2 -> T_Channel_2
d__'8855'__32 = erased
-- CategoricalCrypto._.P
d_P_40 :: T_Channel_2 -> T_Channel_2 -> ()
d_P_40 = erased
-- CategoricalCrypto._.rcvType
d_rcvType_42 :: T_Channel_2 -> T_Channel_2 -> AgdaAny -> ()
d_rcvType_42 = erased
-- CategoricalCrypto._.sndType
d_sndType_44 :: T_Channel_2 -> T_Channel_2 -> AgdaAny -> ()
d_sndType_44 = erased
-- CategoricalCrypto._.P
d_P_48 :: T_Channel_2 -> ()
d_P_48 = erased
-- CategoricalCrypto._.rcvType
d_rcvType_50 :: T_Channel_2 -> AgdaAny -> ()
d_rcvType_50 = erased
-- CategoricalCrypto._.sndType
d_sndType_52 :: T_Channel_2 -> AgdaAny -> ()
d_sndType_52 = erased
-- CategoricalCrypto.snd₁
d_snd'8321'_68 ::
  T_Channel_2 ->
  T_Channel_2 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_snd'8321'_68 ~v0 ~v1 v2 = du_snd'8321'_68 v2
du_snd'8321'_68 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_snd'8321'_68 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CategoricalCrypto.snd₂
d_snd'8322'_78 ::
  T_Channel_2 ->
  T_Channel_2 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_snd'8322'_78 ~v0 ~v1 v2 = du_snd'8322'_78 v2
du_snd'8322'_78 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_snd'8322'_78 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- CategoricalCrypto.⊗-assoc
d_'8855''45'assoc_90
  = error
      "MAlonzo Runtime Error: postulate evaluated: CategoricalCrypto.\8855-assoc"
-- CategoricalCrypto.Machine
d_Machine_96 a0 a1 = ()
data T_Machine_96 = C_MkMachine_126
-- CategoricalCrypto._.P
d_P_104 :: T_Channel_2 -> T_Channel_2 -> ()
d_P_104 = erased
-- CategoricalCrypto._.rcvType
d_rcvType_106 ::
  T_Channel_2 ->
  T_Channel_2 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_rcvType_106 = erased
-- CategoricalCrypto._.sndType
d_sndType_108 ::
  T_Channel_2 ->
  T_Channel_2 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_sndType_108 = erased
-- CategoricalCrypto.Machine._.P
d_P_116 :: T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> ()
d_P_116 = erased
-- CategoricalCrypto.Machine._.rcvType
d_rcvType_118 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_rcvType_118 = erased
-- CategoricalCrypto.Machine._.sndType
d_sndType_120 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_sndType_120 = erased
-- CategoricalCrypto.Machine.State
d_State_122 :: T_Machine_96 -> ()
d_State_122 = erased
-- CategoricalCrypto.Machine.stepRel
d_stepRel_124 ::
  T_Machine_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_stepRel_124 = erased
-- CategoricalCrypto._._.P
d_P_142 :: T_Channel_2 -> T_Channel_2 -> ()
d_P_142 = erased
-- CategoricalCrypto._._.rcvType
d_rcvType_144 ::
  T_Channel_2 ->
  T_Channel_2 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_rcvType_144 = erased
-- CategoricalCrypto._._.sndType
d_sndType_146 ::
  T_Channel_2 ->
  T_Channel_2 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_sndType_146 = erased
-- CategoricalCrypto._._.MkMachine'
d_MkMachine''_150 ::
  T_Channel_2 ->
  T_Channel_2 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  T_Machine_96
d_MkMachine''_150 = erased
-- CategoricalCrypto._._.StatelessMachine
d_StatelessMachine_152 ::
  T_Channel_2 ->
  T_Channel_2 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  T_Machine_96
d_StatelessMachine_152 = erased
-- CategoricalCrypto._._.FunctionMachine
d_FunctionMachine_164 ::
  T_Channel_2 ->
  T_Channel_2 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Machine_96
d_FunctionMachine_164 = erased
-- CategoricalCrypto.id
d_id_174 :: T_Channel_2 -> T_Machine_96
d_id_174 = erased
-- CategoricalCrypto.Tensor._.P
d_P_204 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_P_204 = erased
-- CategoricalCrypto.Tensor._.State
d_State_206 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_State_206 = erased
-- CategoricalCrypto.Tensor._.rcvType
d_rcvType_208 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_rcvType_208 = erased
-- CategoricalCrypto.Tensor._.sndType
d_sndType_210 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_sndType_210 = erased
-- CategoricalCrypto.Tensor._.stepRel
d_stepRel_212 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_stepRel_212 = erased
-- CategoricalCrypto.Tensor._.P
d_P_216 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_P_216 = erased
-- CategoricalCrypto.Tensor._.State
d_State_218 :: T_Machine_96 -> ()
d_State_218 = erased
-- CategoricalCrypto.Tensor._.rcvType
d_rcvType_220 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_rcvType_220 = erased
-- CategoricalCrypto.Tensor._.sndType
d_sndType_222 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_sndType_222 = erased
-- CategoricalCrypto.Tensor._.stepRel
d_stepRel_224 ::
  T_Machine_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_stepRel_224 = erased
-- CategoricalCrypto.Tensor.State
d_State_226 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_State_226 = erased
-- CategoricalCrypto.Tensor.AllCs
d_AllCs_228 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> T_Channel_2
d_AllCs_228 = erased
-- CategoricalCrypto.Tensor.CompRel
d_CompRel_230 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_CompRel_230
  = C_Step'8321'_244 (Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     AgdaAny |
    C_Step'8322'_258 (Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     AgdaAny
-- CategoricalCrypto.Tensor._⊗'_
d__'8855'''__260 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> T_Machine_96
d__'8855'''__260 = erased
-- CategoricalCrypto.Tensor..extendedlambda0
d_'46'extendedlambda0_262 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> T_Machine_96
d_'46'extendedlambda0_262 = erased
-- CategoricalCrypto._⊗ˡ_
d__'8855''737'__314 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96
d__'8855''737'__314 = erased
-- CategoricalCrypto._⊗ʳ_
d__'8855''691'__326 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Channel_2 -> T_Machine_96
d__'8855''691'__326 = erased
-- CategoricalCrypto.Comp._.P
d_P_346 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_P_346 = erased
-- CategoricalCrypto.Comp._.State
d_State_348 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_State_348 = erased
-- CategoricalCrypto.Comp._.rcvType
d_rcvType_350 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_rcvType_350 = erased
-- CategoricalCrypto.Comp._.sndType
d_sndType_352 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_sndType_352 = erased
-- CategoricalCrypto.Comp._.stepRel
d_stepRel_354 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_stepRel_354 = erased
-- CategoricalCrypto.Comp._.P
d_P_358 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_P_358 = erased
-- CategoricalCrypto.Comp._.State
d_State_360 :: T_Machine_96 -> ()
d_State_360 = erased
-- CategoricalCrypto.Comp._.rcvType
d_rcvType_362 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_rcvType_362 = erased
-- CategoricalCrypto.Comp._.sndType
d_sndType_364 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 ->
  T_Machine_96 ->
  T_Machine_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_sndType_364 = erased
-- CategoricalCrypto.Comp._.stepRel
d_stepRel_366 ::
  T_Machine_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_stepRel_366 = erased
-- CategoricalCrypto.Comp.State
d_State_368 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d_State_368 = erased
-- CategoricalCrypto.Comp.AllCs
d_AllCs_370 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> T_Channel_2
d_AllCs_370 = erased
-- CategoricalCrypto.Comp.CompRel
d_CompRel_372 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_CompRel_372
  = C_Step'8321'_386 (Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     AgdaAny |
    C_Step'8322'_400 (Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     AgdaAny |
    C_Multi'8321'_416 AgdaAny AgdaAny
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_CompRel_372
                      T_CompRel_372 |
    C_Multi'8322'_432 AgdaAny AgdaAny
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_CompRel_372 T_CompRel_372
-- CategoricalCrypto.Comp._∘_
d__'8728'__434 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> T_Machine_96
d__'8728'__434 = erased
-- CategoricalCrypto.Comp..extendedlambda0
d_'46'extendedlambda0_436 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> T_Machine_96
d_'46'extendedlambda0_436 = erased
-- CategoricalCrypto.ℰ-Out
d_ℰ'45'Out_466 :: T_Channel_2
d_ℰ'45'Out_466 = erased
-- CategoricalCrypto.ℰ
d_ℰ_468 :: T_Channel_2 -> ()
d_ℰ_468 = erased
-- CategoricalCrypto.map-ℰ
d_map'45'ℰ_476 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> T_Machine_96
d_map'45'ℰ_476 = erased
-- CategoricalCrypto._≈ℰ_
d__'8776'ℰ__486 ::
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d__'8776'ℰ__486 = erased
-- CategoricalCrypto._≤UC_
d__'8804'UC__504 ::
  T_Channel_2 ->
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d__'8804'UC__504 = erased
-- CategoricalCrypto._≤'UC_
d__'8804'''UC__526 ::
  T_Channel_2 ->
  T_Channel_2 -> T_Channel_2 -> T_Machine_96 -> T_Machine_96 -> ()
d__'8804'''UC__526 = erased
-- CategoricalCrypto.LeakyChannel.A
d_A_540 :: () -> T_Channel_2
d_A_540 = erased
-- CategoricalCrypto.LeakyChannel.B
d_B_542 :: () -> T_Channel_2
d_B_542 = erased
-- CategoricalCrypto.LeakyChannel.E
d_E_544 :: () -> T_Channel_2
d_E_544 = erased
-- CategoricalCrypto.LeakyChannel.R
d_R_546 a0 a1 a2 a3 = ()
data T_R_546 = C_Send_552 | C_Req_558
-- CategoricalCrypto.LeakyChannel.Functionality
d_Functionality_560 :: () -> T_Machine_96
d_Functionality_560 = erased
-- CategoricalCrypto.SecureChannel.A
d_A_566 :: () -> T_Channel_2
d_A_566 = erased
-- CategoricalCrypto.SecureChannel.B
d_B_568 :: () -> T_Channel_2
d_B_568 = erased
-- CategoricalCrypto.SecureChannel.E
d_E_570 :: () -> T_Channel_2
d_E_570 = erased
-- CategoricalCrypto.SecureChannel._.R
d_R_578 a0 a1 a2 a3 a4 = ()
data T_R_578 = C_Send_584 | C_Req_590
-- CategoricalCrypto.SecureChannel._.Functionality
d_Functionality_592 :: () -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_592 = erased
-- CategoricalCrypto.SecureChannel._.Functionality'
d_Functionality''_594 :: () -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality''_594 = erased
-- CategoricalCrypto.Encryption.C
d_C_614 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Channel_2
d_C_614 = erased
-- CategoricalCrypto.Encryption.S
d_S_616 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_S_616 = erased
-- CategoricalCrypto.Encryption.lookup
d_lookup_620 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  () -> [AgdaAny] -> (AgdaAny -> Bool) -> Maybe AgdaAny
d_lookup_620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_lookup_620 v9 v10
du_lookup_620 :: [AgdaAny] -> (AgdaAny -> Bool) -> Maybe AgdaAny
du_lookup_620 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> let v4 = coe v1 v2 in
           coe
             (if coe v4
                then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                else coe du_lookup_620 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CategoricalCrypto.Encryption.lookupPlainText
d_lookupPlainText_646 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
d_lookupPlainText_646 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8 v9
  = du_lookupPlainText_646 v4 v5 v8 v9
du_lookupPlainText_646 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
du_lookupPlainText_646 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du_map_64
             (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6))
             (coe
                MAlonzo.Code.Data.Maybe.Base.du_map_64
                (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6))
                (coe
                   du_lookup_620 (coe v2)
                   (coe
                      (\ v6 ->
                         case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         MAlonzo.Code.Class.Decidable.Core.du_'191'_'191''7495'_46
                                         (coe ())
                                         (coe
                                            MAlonzo.Code.Class.Decidable.Instances.du_Dec'45''215'_24
                                            (coe
                                               MAlonzo.Code.Class.Decidable.Instances.du_DecEq'8658'Dec_16
                                               (coe v1) (coe v5) (coe v7))
                                            (coe
                                               MAlonzo.Code.Class.Decidable.Instances.du_DecEq'8658'Dec_16
                                               (coe v0) (coe v4) (coe v10)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- CategoricalCrypto.Encryption.R
d_R_660 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_R_660 = C_Enc_670 | C_Dec_680
-- CategoricalCrypto.Encryption.Functionality
d_Functionality_682 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Machine_96
d_Functionality_682 = erased
-- CategoricalCrypto.EncryptionShim.L.A
d_A_708 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Channel_2
d_A_708 = erased
-- CategoricalCrypto.EncryptionShim.L.B
d_B_710 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Channel_2
d_B_710 = erased
-- CategoricalCrypto.EncryptionShim.L.E
d_E_712 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Channel_2
d_E_712 = erased
-- CategoricalCrypto.EncryptionShim.L.Functionality
d_Functionality_714 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Machine_96
d_Functionality_714 = erased
-- CategoricalCrypto.EncryptionShim.L.R
d_R_716 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- CategoricalCrypto.EncryptionShim.S.A
d_A_730 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Channel_2
d_A_730 = erased
-- CategoricalCrypto.EncryptionShim.S.B
d_B_732 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Channel_2
d_B_732 = erased
-- CategoricalCrypto.EncryptionShim.S.E
d_E_734 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Channel_2
d_E_734 = erased
-- CategoricalCrypto.EncryptionShim.S.Functionality
d_Functionality_736 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_736 = erased
-- CategoricalCrypto.EncryptionShim.S.Functionality'
d_Functionality''_738 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality''_738 = erased
-- CategoricalCrypto.EncryptionShim.S.R
d_R_740 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- CategoricalCrypto.EncryptionShim.E.C
d_C_754 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Channel_2
d_C_754 = erased
-- CategoricalCrypto.EncryptionShim.E.Functionality
d_Functionality_760 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Machine_96
d_Functionality_760 = erased
-- CategoricalCrypto.EncryptionShim.E.R
d_R_762 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- CategoricalCrypto.EncryptionShim.E.S
d_S_764 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_S_764 = erased
-- CategoricalCrypto.EncryptionShim.E.lookup
d_lookup_766 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> () -> [AgdaAny] -> (AgdaAny -> Bool) -> Maybe AgdaAny
d_lookup_766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_lookup_766
du_lookup_766 ::
  () -> [AgdaAny] -> (AgdaAny -> Bool) -> Maybe AgdaAny
du_lookup_766 v0 v1 v2 = coe du_lookup_620 v1 v2
-- CategoricalCrypto.EncryptionShim.E.lookupPlainText
d_lookupPlainText_768 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
d_lookupPlainText_768 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_lookupPlainText_768 v4 v5
du_lookupPlainText_768 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
du_lookupPlainText_768 v0 v1
  = coe du_lookupPlainText_646 (coe v0) (coe v1)
-- CategoricalCrypto.EncryptionShim.R
d_R_776 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_R_776 = C_EncSend_786 T_R_660 | C_DecRcv_796 T_R_660
-- CategoricalCrypto.EncryptionShim.Functionality
d_Functionality_798 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> T_Machine_96
d_Functionality_798 = erased
-- CategoricalCrypto.SecureFromAuthenticated.L.A
d_A_826 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_A_826 = erased
-- CategoricalCrypto.SecureFromAuthenticated.L.B
d_B_828 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_B_828 = erased
-- CategoricalCrypto.SecureFromAuthenticated.L.E
d_E_830 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_E_830 = erased
-- CategoricalCrypto.SecureFromAuthenticated.L.Functionality
d_Functionality_832 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_832 = erased
-- CategoricalCrypto.SecureFromAuthenticated.L.R
d_R_834 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- CategoricalCrypto.SecureFromAuthenticated.S.A
d_A_848 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_A_848 = erased
-- CategoricalCrypto.SecureFromAuthenticated.S.B
d_B_850 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_B_850 = erased
-- CategoricalCrypto.SecureFromAuthenticated.S.E
d_E_852 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_E_852 = erased
-- CategoricalCrypto.SecureFromAuthenticated.S.Functionality
d_Functionality_854 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> Integer) -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_854 = erased
-- CategoricalCrypto.SecureFromAuthenticated.S.Functionality'
d_Functionality''_856 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> Integer) -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality''_856 = erased
-- CategoricalCrypto.SecureFromAuthenticated.S.R
d_R_858 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = ()
-- CategoricalCrypto.SecureFromAuthenticated.SH.Functionality
d_Functionality_876 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_876 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.R
d_R_878 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- CategoricalCrypto.SecureFromAuthenticated.SH.E.C
d_C_882 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_C_882 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.E.Functionality
d_Functionality_888 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_888 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.E.R
d_R_890 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- CategoricalCrypto.SecureFromAuthenticated.SH.E.S
d_S_892 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> ()
d_S_892 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.E.lookup
d_lookup_894 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> Integer) ->
  () -> [AgdaAny] -> (AgdaAny -> Bool) -> Maybe AgdaAny
d_lookup_894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_lookup_894
du_lookup_894 ::
  () -> [AgdaAny] -> (AgdaAny -> Bool) -> Maybe AgdaAny
du_lookup_894 v0 v1 v2 = coe du_lookup_620 v1 v2
-- CategoricalCrypto.SecureFromAuthenticated.SH.E.lookupPlainText
d_lookupPlainText_896 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> Integer) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
d_lookupPlainText_896 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_lookupPlainText_896 v4 v5
du_lookupPlainText_896 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
du_lookupPlainText_896 v0 v1
  = coe du_lookupPlainText_646 (coe v0) (coe v1)
-- CategoricalCrypto.SecureFromAuthenticated.SH.L.A
d_A_906 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_A_906 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.L.B
d_B_908 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_B_908 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.L.E
d_E_910 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_E_910 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.L.Functionality
d_Functionality_912 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_912 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.L.R
d_R_914 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- CategoricalCrypto.SecureFromAuthenticated.SH.S.A
d_A_934 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_A_934 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.S.B
d_B_936 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_B_936 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.S.E
d_E_938 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Channel_2
d_E_938 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.S.Functionality
d_Functionality_940 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> Integer) -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_940 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.S.Functionality'
d_Functionality''_942 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> Integer) -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality''_942 = erased
-- CategoricalCrypto.SecureFromAuthenticated.SH.S.R
d_R_944 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = ()
-- CategoricalCrypto.SecureFromAuthenticated.Functionality
d_Functionality_956 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality_956 = erased
-- CategoricalCrypto.SecureFromAuthenticated.Functionality'
d_Functionality''_958 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> (AgdaAny -> Integer) -> T_Machine_96
d_Functionality''_958 = erased
