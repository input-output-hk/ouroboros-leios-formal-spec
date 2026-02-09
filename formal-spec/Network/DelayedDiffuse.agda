{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

--------------------------------------------------------------------------------
-- DDiffuseΔ, as described in: Ouroboros Praos: An adaptively-secure,
-- semi-synchronous proof-of-stake blockchain
--------------------------------------------------------------------------------

open import Leios.Prelude hiding (_⊗_; module Any)
open import CategoricalCrypto
open import abstract-set-theory.FiniteSetTheory
open import Class.ToBool
open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Network.DelayedDiffuse (Participants : ℕ) (Message : Type) (Δ : ℕ) ⦃ _ : DecEq Message ⦄ where

Participant = Fin Participants
Message' = Participant × Message

record BufferedMessage : Type where
  field sender recipient : Participant
        m : Message
        round : ℕ

  toMessage' : Message'
  toMessage' = (recipient , m)

unquoteDecl DecEq-BufferedMessage = derive-DecEq ((quote BufferedMessage , DecEq-BufferedMessage) ∷ [])


allParticipants : ℙ (Fin Participants)
allParticipants = fromList (allFin Participants)

Inbox = Participant → List Message'
Buffer = ℙ BufferedMessage

data NetworkT : Mode → Type where
  Diffuse : List Message → NetworkT Out -- this ends the round for the participant
  Deliver : List Message' → NetworkT In

data AdvT : Mode → Type where
  Read : AdvT Out
  ReadRes : Inbox → Buffer → AdvT In
  Deliver : BufferedMessage → AdvT Out
  ReturnA : AdvT In

data EnvT : Mode → Type where
  ActivateE : Participant → EnvT Out
  Next      : EnvT In
  NextRound : EnvT Out

Adv Env M Ms : Channel
Adv = simpleChannel AdvT
M = simpleChannel NetworkT
Ms = ⨂ const {B = Participant} M
Env = simpleChannel EnvT

record State : Type where
  field round  : ℕ
        inbox  : Inbox
        buffer : Buffer
        done   : ℙ Participant

bufferMessages : Participant → List Message → State → State
bufferMessages sender ms s = record s { buffer = buffer ∪ newMessages }
  where open State s
        newMessages = fromList (concatMap (λ m → tabulate (λ r → record { sender = sender ; recipient = r ; m = m ; round = round })) ms)

moveToInbox : BufferedMessage → State → State
moveToInbox m s = let open State s; module m = BufferedMessage m in if m ∈ buffer
  then record s { inbox = λ p → if p ≡ m.recipient then m.toMessage' ∷ inbox p else inbox p
                ; buffer = buffer ＼ ❴ m ❵ }
  else s

private variable ms : List Message
                 p : Participant
                 s : State
                 bm : BufferedMessage

open State
open BufferedMessage

data WithState_receive_return_newState_ : MachineType I (Ms ⊗ Env ⊗ Adv) State where

  ActivateE-step :
    p ∉ s .done →
    WithState s
    receive L⊗ (L⊗ ϵ ⊗R) ᵗ¹ ↑ₒ ActivateE p                          -- the environment says p is next
    return just $ L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ app (⨂⇒ p) (Deliver (s .inbox p)) -- deliver all messages in the inbox
    newState record s { inbox = λ p' → if p ≡ p' then [] else s .inbox p' } -- clear the inbox

  Diffuse-step :
    p ∉ s .done →
    WithState s
    receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ app (⨂⇒ p) (Diffuse ms)  -- p wants to send messages ms
    return just $ L⊗ (L⊗ ϵ ⊗R) ᵗ¹ ↑ᵢ Next             -- ask for the next participant to activate
    newState record (bufferMessages p ms s) { done = s .done ∪ ❴ p ❵ } -- buffer a copy of every message for every participant & mark p as done

  NextRound-step :
    s .done ≡ᵉ allParticipants →
    ∀[ m ∈ s .buffer ] m .round + Δ ≥ s .round → -- the adversary has delivered all sufficiently old messages
    WithState s
    receive L⊗ (L⊗ ϵ ⊗R) ᵗ¹ ↑ₒ NextRound
    return nothing
    newState record s { done = ∅ } -- reset the state

  Read-step :
    WithState s
    receive L⊗ (L⊗ L⊗ ϵ) ᵗ¹ ↑ₒ Read
    return just $ L⊗ (L⊗ L⊗ ϵ) ᵗ¹ ↑ᵢ ReadRes (s .inbox) (s .buffer)
    newState s

  Deliver-step :
    s .done ≡ᵉ allParticipants →
    WithState s
    receive L⊗ (L⊗ L⊗ ϵ) ᵗ¹ ↑ₒ Deliver bm
    return just $ L⊗ (L⊗ L⊗ ϵ) ᵗ¹ ↑ᵢ ReturnA
    newState moveToInbox bm s

Network : Machine I (Ms ⊗ Env ⊗ Adv)
Network .Machine.State = State
Network .Machine.stepRel = WithState_receive_return_newState_
