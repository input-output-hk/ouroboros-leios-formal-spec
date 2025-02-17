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

module MAlonzo.Code.Leios.KeyRegistration where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Leios.Abstract
import qualified MAlonzo.Code.Leios.VRF

-- Leios.KeyRegistration.KeyRegistrationAbstract
d_KeyRegistrationAbstract_86 a0 a1 = ()
data T_KeyRegistrationAbstract_86
  = C_KeyRegistrationAbstract'46'constructor_257
-- Leios.KeyRegistration.KeyRegistrationAbstract.Input
d_Input_88 a0 a1 a2 = ()
data T_Input_88 = C_INIT_90 AgdaAny AgdaAny AgdaAny
-- Leios.KeyRegistration.KeyRegistrationAbstract.Output
d_Output_92 a0 a1 a2 = ()
newtype T_Output_92 = C_PUBKEYS_94 [AgdaAny]
-- Leios.KeyRegistration.KeyRegistrationAbstract.Functionality
d_Functionality_96 a0 a1 a2 = ()
data T_Functionality_96 = C_Functionality'46'constructor_389
-- Leios.KeyRegistration.KeyRegistrationAbstract.Functionality.State
d_State_102 :: T_Functionality_96 -> ()
d_State_102 = erased
-- Leios.KeyRegistration.KeyRegistrationAbstract.Functionality._-⟦_/_⟧⇀_
d__'45''10214'_'47'_'10215''8640'__104 ::
  T_Functionality_96 ->
  AgdaAny -> T_Input_88 -> T_Output_92 -> AgdaAny -> ()
d__'45''10214'_'47'_'10215''8640'__104 = erased
