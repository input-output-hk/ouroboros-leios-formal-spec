open import Leios.Prelude hiding (_⊗_; module Any)
open import CategoricalCrypto

module Network.BasicBroadcast (Participants : ℕ) (Message : Type) where

data NetworkT : ChannelDir → Type where
  RcvMessage : Message → NetworkT In
  Activate   : NetworkT In
  SndMessage : List Message → NetworkT Out

Participant = Fin Participants

private variable buffer buffer₁ buffer₂ : List (Message × Participant)
                 ms : List Message
                 p : Participant
                 k : ℕ
                 m : Message
                 x : Message × Participant

A : Channel
A = simpleChannel (Message × Participant) (ℕ ⊎ ℕ)

M : Channel
M = simpleChannel' NetworkT

Ms : Channel
Ms = ⨂ const {B = Participant} M

data Receive_withState_return_ : MachineType I (Ms ⊗ A) (List (Message × Participant)) where

  Send : Receive (honestInputI $ snd⨂ p (-, SndMessage ms))      -- p wants to send messages ms
         withState buffer
         return (concatMap (λ m → tabulate (m ,_)) ms ++ buffer   -- buffer a copy of every message for every participant
           , just (honestOutputO $ rcv⨂ p (-, Activate)))        -- return control to p

  Deliver : length buffer₁ ≡ k
          → Receive (adversarialInput (-, inj₁ k))                -- adversary wants to deliver k-th message
            withState (buffer₁ ++ (m , p) ∷ buffer₂)              -- state decomposes appropriately
            return    (buffer₁ ++ buffer₂                         -- remove message
              , just (honestOutputO $ rcv⨂ p (-, RcvMessage m))) -- deliver it

  Eavesdrop : length buffer₁ ≡ k
            → Receive (adversarialInput (-, inj₂ k))              -- adversary wants to know k-th message
              withState (buffer₁ ++ x ∷ buffer₂)                  -- state decomposes appropriately
              return    (buffer₁ ++ x ∷ buffer₂
                , just  (adversarialOutput (-, x)))               -- deliver it

Network : Machine I (Ms ⊗ A)
Network .Machine.State = List (Message × Participant)
Network .Machine.stepRel = Receive_withState_return_
