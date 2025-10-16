{-# OPTIONS --safe #-}
module CategoricalCrypto where

-- Open problems

-- We want to conveniently specify a machine that, on an input, sends
-- messages to other machines, waits for replies and then continues
-- execution.

-- Can we write constructors more monadically?

-- Improve syntax generally

open import CategoricalCrypto.Channel.Core public
open import CategoricalCrypto.Channel.Selection public
open import CategoricalCrypto.Channel.Category public
open import CategoricalCrypto.Machine.Core public
open import CategoricalCrypto.Machine.Category public
open import CategoricalCrypto.Examples
