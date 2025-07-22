{-# OPTIONS --safe #-}
module CategoricalCrypto.Examples where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)
import abstract-set-theory.Prelude as P

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import CategoricalCrypto.Base

--------------------------------------------------------------------------------
-- Example functionalities

module LeakyChannel (M : Type) where
  -- authenticated, non-lossy, leaks all messages

  open Channel

  A B E : Channel

  -- can receive messages from Alice
  A = simpleChannel ⊥ M

  -- can send messages to Bob
  B = simpleChannel M ⊥

  -- upon request, can send next message to Eve
  E = simpleChannel M ⊤

  open Machine

  data WithState_receive_return_newState_ : MachineType I ((A ⊗ B) ⊗ E) (List M) where

    Send : ∀ {m s} → WithState s
                     receive (honestInputI (sndˡ (-, m)))
                     return just (honestOutputO (rcvʳ (-, m)))
                     newState (s ∷ʳ m)

    Req  : ∀ {m s} → WithState (m ∷ s)
                     receive (adversarialInput _)
                     return just (adversarialOutput (-, m))
                     newState s

  Functionality : Machine I ((A ⊗ B) ⊗ E)
  Functionality .State = List M -- queue of messages
  Functionality .stepRel = WithState_receive_return_newState_



module SecureChannel (M : Type) where
  -- authenticated, non-lossy, leaks only message length

  open Channel

  A B E : Channel

  -- can receive messages from Alice
  A = simpleChannel ⊥ M

  -- can send messages to Bob
  B = simpleChannel M ⊥

  -- upon request, can send next message to Eve
  E = simpleChannel ℕ ⊤

  module _ (msgLen : M → ℕ) where

    open Machine

    data WithState_receive_return_newState_ : MachineType I ((A ⊗ B) ⊗ E) (List M) where

      Send : ∀ {m s} → WithState s
                       receive (honestInputI (sndˡ (-, m)))
                       return just (honestOutputO (rcvʳ (-, m)))
                       newState (s ∷ʳ m)

      Req  : ∀ {m s} → WithState (m ∷ s)
                       receive (adversarialInput _)
                       return just (adversarialOutput (-, msgLen m))
                       newState s

    Functionality : Machine I ((A ⊗ B) ⊗ E)
    Functionality .State = List M -- queue of messages
    Functionality .stepRel = WithState_receive_return_newState_



module Encryption (PlainText CipherText PubKey PrivKey : Type)
                  ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                  (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey) where
  open Channel
  open Machine

  C : Channel
  C = simpleChannel (CipherText ⊎ Maybe PlainText) (PlainText × PubKey ⊎ CipherText × PrivKey)

  S : Type
  S = List (PubKey × PlainText × CipherText)

  lookup : {A : Type} → List A → (A → Bool) → Maybe A
  lookup [] f = nothing
  lookup (x ∷ l) f with f x
  ... | true  = just x
  ... | false = lookup l f

  lookupPlainText : S → CipherText × PubKey → Maybe PlainText
  lookupPlainText s (c , k) = proj₁ <$> (proj₂ <$> lookup s λ where (k' , _ , c') → ¿ k ≡ k' × c ≡ c' ¿ᵇ)

  data WithState_receive_return_newState_ : MachineType I C S where

    Enc : ∀ {p k s} → let c = genCT (length s)
       in WithState s
          receive (rcvʳ (-, inj₁ (p , k)))
          return just (sndʳ (-, inj₁ c))
          newState ((k , p , c) ∷ s)

    Dec : ∀ {c k s} → let p = lookupPlainText s (c , getPubKey k)
       in WithState s
          receive (rcvʳ (-, inj₂ (c , k)))
          return just (sndʳ (-, inj₂ p))
          newState s

  Functionality : Machine I C
  Functionality .State   = S
  Functionality .stepRel = WithState_receive_return_newState_

-- Note: it's a bad idea to do this as a wrapper, just make a shim to
-- compose with Encryption & the channel instead
module EncryptionShim (PlainText CipherText PubKey PrivKey : Type)
                      ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                      (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                      (pubKey : PubKey) (privKey : PrivKey) where
  open Channel
  open Machine

  module L = LeakyChannel CipherText
  module S = SecureChannel PlainText
  module E = Encryption PlainText CipherText PubKey PrivKey genCT getPubKey

  data WithState_receive_return_newState_ : MachineType ((L.A ⊗ L.B) ⊗ L.E) ((S.A ⊗ S.B) ⊗ S.E) (E.Functionality .State) where

    EncSend : ∀ {m m' s s'}
            → E.WithState s
                receive (rcvʳ (-, inj₁ (m , pubKey)))
                return just (sndʳ (-, inj₁ m'))
                newState s'
            → WithState s
              receive (rcvʳ (sndˡ (sndˡ (-, m))))
              return just (sndˡ (sndˡ (sndˡ (-, m'))))
              newState s'

    DecRcv  : ∀ {m m' s s'}
            → E.WithState s
                receive (rcvʳ (-, inj₂ (m , privKey)))
                return just (sndʳ (-, inj₂ (just m')))
                newState s'
            → WithState s
              receive (rcvˡ (rcvˡ (rcvʳ (-, m))))
              return just (sndʳ (rcvˡ (rcvʳ (-, m'))))
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
  module S  = SecureChannel PlainText
  module SH = EncryptionShim PlainText CipherText PubKey PrivKey genCT getPubKey pubKey privKey

  Functionality : Machine I ((S.A ⊗ S.B) ⊗ S.E)
  Functionality = SH.Functionality ∘ L.Functionality

  -- F≤Secure : Functionality ≤'UC S.Functionality msgLength
  -- F≤Secure = {!!}
