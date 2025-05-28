open import Leios.Prelude

module Network.MessageInterface where

record MessageInterface : Type₁ where
  field MessageBuffer : Type
        Message : Type

        queueMessage : MessageBuffer → Message → MessageBuffer
        deliverMessage : MessageBuffer → Message → MessageBuffer
