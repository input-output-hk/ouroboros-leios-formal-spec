{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Examples where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)
import abstract-set-theory.Prelude as P

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import CategoricalCrypto.Machine
open import CategoricalCrypto.Channel

--------------------------------------------------------------------------------
-- Example functionalities

module TemplateChannel (M : Type) {M' : Type} (f : M → M') where

  open Channel

  A B E : Channel

  -- can receive messages from Alice
  A = ⊥ ⇿ M

  -- can send messages to Bob
  B = M ⇿ ⊥

  -- upon request, can send next message to Eve
  E = M' ⇿ ⊤

  open Machine

  data WithState_receive_return_newState_ : MachineType I ((A ⊗ B) ⊗ E) (List M) where

    Send : ∀ {m s} → WithState s
                     receive ⊗-left-intro {In} $ ⇒-transpose $ ⊗-right-intro $ ⊗-right-intro m
                     return just $ ⊗-left-intro {Out} $ ⇒-transpose $ ⊗-right-intro $ ⊗-left-intro m
                     newState (s ∷ʳ m)

    Req  : ∀ {m s} → WithState m ∷ s
                     receive ⊗-left-intro {In} $ ⇒-transpose $ ⊗-left-intro tt
                     return just $ ⊗-left-intro {Out} $ ⇒-transpose $ ⊗-left-intro $ f m
                     newState s

  Functionality : Machine I ((A ⊗ B) ⊗ E)
  Functionality .State = List M -- queue of messages
  Functionality .stepRel = WithState_receive_return_newState_
  
-- authenticated, non-lossy, leaks all messages
module LeakyChannel (M : Type) = TemplateChannel M P.id

-- authenticated, non-lossy, leaks only message length
module SecureChannel (M : Type) = TemplateChannel M {ℕ}

module Encryption (PlainText CipherText PubKey PrivKey : Type)
                  ⦃ _ : DecEq CipherText ⦄
                  ⦃ _ : DecEq PubKey ⦄
                  (genCT : ℕ → CipherText)
                  (getPubKey : PrivKey → PubKey) where

  open Channel
  open Machine

  C : Channel
  C = (CipherText ⊎ Maybe PlainText) ⇿ (PlainText × PubKey ⊎ CipherText × PrivKey)

  S : Type
  S = List (PubKey × PlainText × CipherText)

  lookupPlainText : S → CipherText × PubKey → Maybe PlainText
  lookupPlainText s (c , k) = proj₁ <$> (proj₂ <$> flip findᵇ s λ where (k' , _ , c') → ¿ k ≡ k' × c ≡ c' ¿ᵇ)

  data WithState_receive_return_newState_ : MachineType I C S where

    Enc : ∀ {p k s} → let c = genCT (length s) in WithState s
                                                  receive ⊗-left-intro {In} $ inj₁ (p , k)
                                                  return just $ ⊗-left-intro {Out} $ inj₁ c
                                                  newState ((k , p , c) ∷ s)

    Dec : ∀ {c k s} → let p = lookupPlainText s (c , getPubKey k) in WithState s
                                                                     receive ⊗-left-intro {In} $ inj₂ (c , k)
                                                                     return just $ ⊗-left-intro {Out} $ inj₁ c
                                                                     newState s

  Functionality : Machine I C
  Functionality .State   = S
  Functionality .stepRel = WithState_receive_return_newState_

-- Note: it's a bad idea to do this as a wrapper, just make a shim to
-- compose with Encryption & the channel instead
module EncryptionShim (PlainText CipherText PubKey PrivKey : Type)
                      ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                      (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                      (pubKey : PubKey) (privKey : PrivKey) (msgLength : PlainText → ℕ) where
  open Channel
  open Machine

  module L = LeakyChannel CipherText
  module S = SecureChannel PlainText msgLength
  module E = Encryption PlainText CipherText PubKey PrivKey genCT getPubKey

  data WithState_receive_return_newState_ : MachineType ((L.A ⊗ L.B) ⊗ L.E) ((S.A ⊗ S.B) ⊗ S.E) (E.Functionality .State) where
  
    EncSend : ∀ {m m' s s'} → E.WithState s
                              receive ⊗-left-intro {In} $ inj₁ (m , pubKey)
                              return just $ ⊗-left-intro {Out} $ inj₁ m'
                              newState s'
                            → WithState s
                              receive ⊗-left-intro {In} $ ⇒-transpose $ ⊗-right-intro $ ⊗-right-intro m 
                              return just $ ⊗-right-intro {Out} $ ⊗-right-intro $ ⊗-right-intro m'
                              newState s'

    DecRcv  : ∀ {m m' s s'} → E.WithState s
                              receive ⊗-left-intro {In} $ inj₂ (m , privKey)
                              return just $ ⊗-left-intro {Out} $ inj₂ $ just m'
                              newState s'
                            → WithState s
                              receive ⊗-right-intro {In} $ ⊗-right-intro $ ⊗-left-intro m
                              return just $ ⊗-left-intro {Out} $ ⇒-transpose $ ⊗-right-intro $ ⊗-left-intro $ m'
                              newState s'

  Functionality : Machine ((L.A ⊗ L.B) ⊗ L.E) ((S.A ⊗ S.B) ⊗ S.E)
  Functionality .State   = E.Functionality .State
  Functionality .stepRel = WithState_receive_return_newState_

module SecureFromAuthenticated (PlainText CipherText PubKey PrivKey : Type)
                               ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                               (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                               (pubKey : PubKey) (privKey : PrivKey)
                               (msgLength : PlainText → ℕ) where

  module L  = LeakyChannel CipherText
  module S  = SecureChannel PlainText msgLength
  module SH = EncryptionShim PlainText CipherText PubKey PrivKey genCT getPubKey pubKey privKey msgLength

  Functionality : Machine I ((S.A ⊗ S.B) ⊗ S.E)
  Functionality = SH.Functionality ∘ L.Functionality

  -- F≤Secure : Functionality ≤'UC S.Functionality msgLength
  -- F≤Secure = {!!}
