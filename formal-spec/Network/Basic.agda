open import Leios.Prelude

module Network.Basic where

record Node (M I O : Type) : Type₁ where
  field State : Type
        _-⟦_/_⟧ᵐ⇀_ : State → M → Maybe M → State → Type     -- receiving a message from the network
        _-⟦_/_⟧ⁱ⇀_ : State → I → O × Maybe M → State → Type -- receiving an input locally

--   Participant = HonestParticipant ⊎ AdversarialParticipant

-- This allows for a user-defined `MessageState` type. This can be
-- used to encode extra information such as timing information.

record MessageInterface : Type₁ where
  field MessageBuffer : Type
        Message : Type

record Network (M : Type) : Type₁ where
  field Participant : Type
        ⦃ DecEq-Participant ⦄ : DecEq Participant
        State Input Output : Participant → Type
        NetworkRelation : (p : Participant) → State p → M → Maybe M → State p → Type
        LocalRelation   : (p : Participant) → State p → Input p → Output p × Maybe M → State p → Type

-- This allows for a user-defined `GlobalState` type. This lets a user
-- of this framework encode invariants or extra information in
-- `GlobalState` which might be useful for proofs.

record GlobalStateInterface (mi : MessageInterface) (n : Network (MessageInterface.Message mi)) : Type₁ where
  open Network n
  open MessageInterface mi
  infixl 6 _[_]≔_

  field GlobalState : Type
        _[_]   : GlobalState → (p : Participant) → State p
        _[_]≔_ : GlobalState → (p : Participant) → State p → GlobalState
        queueMessage : GlobalState → Message → GlobalState
        deliverMessage : GlobalState → Message → GlobalState

  maybeQueueMessage : GlobalState → Maybe Message → GlobalState
  maybeQueueMessage s nothing  = s
  maybeQueueMessage s (just m) = queueMessage s m

  -- record GlobalState : Type where
  --   field localStates : (p : Participant) → State p
  --         messages    : List (M × Participant)

  -- _[_]≔_ : GlobalState → (p : Participant) → State p → GlobalState
  -- s@(record { localStates = ss }) [ p ]≔ ls = record s { localStates = λ p′ → if p ≟ p′
  --   then (λ where {refl} → ls)
  --   else ss p′ }

module _ (mi : MessageInterface) (n : Network (MessageInterface.Message mi))
         (gs : GlobalStateInterface mi n) where
  open Network n
  open GlobalStateInterface gs
  open MessageInterface mi

  private variable
    s : GlobalState
    p : Participant

  infix 0 _↝_

  data _↝_ : GlobalState → GlobalState → Type where
    LocalStep : ∀ {ls ls′ : State p} {i} {o} {m} →
      LocalRelation p ls i (o , m) ls′
      ─────────────────────────────────────
      s ↝ maybeQueueMessage (s [ p ]≔ ls′) m

    Deliver : ∀ {ls ls′ : State p} {m} {m′} →
      NetworkRelation p ls m m′ ls′
      ─────────────────────────────────────
      s ↝ deliverMessage (maybeQueueMessage (s [ p ]≔ ls′) m′) m
