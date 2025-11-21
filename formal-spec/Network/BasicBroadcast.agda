{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

open import Leios.Prelude hiding (_⊗_; module Any)
open import CategoricalCrypto

module Network.BasicBroadcast (Participants : ℕ) (Message : Type) where

data NetworkT : Mode → Type where
  RcvMessage : Message → NetworkT In
  Activate   : NetworkT In
  SndMessage : List Message → NetworkT Out

Participant = Fin Participants

private variable buffer buffer₁ buffer₂ : List (Message × Participant)
                 ms : List Message
                 p : Participant
                 m : Message
                 x : Message × Participant

A : Channel
A = (Message × Participant) ⇿ (ℕ ⊎ ℕ)

M : Channel
M = simpleChannel NetworkT

Ms : Channel
Ms = ⨂ const {B = Participant} M

data WithState_receive_return_newState_ : MachineType I (Ms ⊗ A) (List (Message × Participant)) where

  Send : WithState buffer
         receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ app (⨂⇒ p) (SndMessage ms) -- p wants to send messages ms
         return just $ L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ app (⨂⇒ p) Activate -- return control to p
         newState (concatMap (λ m → tabulate (m ,_)) ms ++ buffer) -- buffer a copy of every message for every participant

  Deliver : WithState buffer₁ ++ (m , p) ∷ buffer₂ -- state decomposes appropriately
            receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ inj₁ (length buffer₁) -- adversary wants to deliver k-th message
            return just $ L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ app (⨂⇒ p) (RcvMessage m) -- deliver it
            newState (buffer₁ ++ buffer₂) -- remove message

  Eavesdrop : WithState buffer₁ ++ x ∷ buffer₂ -- state decomposes appropriately
              receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ inj₁ (length buffer₁) -- adversary wants to know k-th message
              return just $ L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ x -- deliver it
              newState (buffer₁ ++ x ∷ buffer₂) -- state remains unchanged

Network : Machine I (Ms ⊗ A)
Network .Machine.State = List (Message × Participant)
Network .Machine.stepRel = WithState_receive_return_newState_
