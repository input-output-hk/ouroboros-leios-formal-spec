module Network.BasicBroadcast where

open import Leios.Prelude hiding (_⊗_; module A)
open import CategoricalCrypto

module _ (Participants : ℕ) (Message : Type) where
  Participant = Fin Participants

  A : Channel
  A = simpleChannel (Message × Participant) (ℕ ⊎ ℕ)

  M : Channel
  M = simpleChannel (⊤ ⊎ Message) Message

  Ms : Channel
  Ms = ⨂ const {B = Participant} M

  data Receive_withState_return_ : MachineType I (Ms ⊗ A) (List (Message × Participant)) where

    Send : ∀ {buffer m} → {p : Participant}
         → Receive (honestInputI $ snd⨂ p (-, m)) -- p wants to send message m
           withState buffer
           return (tabulate (m ,_) ++ buffer -- buffer a copy of m for every participant
             , just (honestOutputO $ rcv⨂ p (-, inj₁ _))) -- return control to p

    Deliver : ∀ {buffer₁ m buffer₂ k} → {p : Participant}
            → length buffer₁ ≡ k
            → Receive (adversarialInput (-, inj₁ k)) -- adversary wants to deliver k-th message
              withState (buffer₁ ++ (m , p) ∷ buffer₂) -- state decomposes appropriately
              return (buffer₁ ++ buffer₂ -- remove message
                , just (honestOutputO $ rcv⨂ p (-, inj₂ m))) -- deliver it

    Eavesdrop : ∀ {buffer₁ x buffer₂ k}
            → length buffer₁ ≡ k
            → Receive (adversarialInput (-, inj₂ k)) -- adversary wants to know k-th message
              withState (buffer₁ ++ x ∷ buffer₂) -- state decomposes appropriately
              return (buffer₁ ++ x ∷ buffer₂
                , just (adversarialOutput (-, x))) -- deliver it

  Network : Machine I (Ms ⊗ A)
  Network .Machine.State = List (Message × Participant)
  Network .Machine.stepRel = Receive_withState_return_
