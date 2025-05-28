open import Leios.Prelude

module Network.Node where

record UnbufferedNode (M I O : Type) : Type₁ where
  field State : Type
        _-⟦_/_⟧ᵐ*⇀_ : State → List M → List M → State → Type -- receiving a message from the network
        _-⟦_/_⟧ⁱ⇀_ : State → I → O × Maybe M → State → Type -- receiving an input locally

record BufferedNode (I O : Type) : Type₁ where
  field State : Type                              -- contains a message buffer
        _-ᵐ⇀_ : State → State → Type         -- receiving a message from the network
        _-⟦_/_⟧ⁱ⇀_ : State → I → O → State → Type -- receiving an input locally

-- unbuffer : ∀ {M I O} → BufferedNode I O → UnbufferedNode M I O
-- unbuffer n = {!!}
--   where open BufferedNode n

buffer : ∀ {M I O} → UnbufferedNode M I O → BufferedNode I O
buffer {M} n = let module n = UnbufferedNode n; open BufferedNode in λ where
  .State → n.State × ℙ M × ℙ M
  ._-ᵐ⇀_ (s , ib , ob) (s' , ib' , ob') → ∃[ ms ] ∃[ ms' ]
    fromList ms ∪ ib' ≡ᵉ ib × fromList ms' ∪ ob ≡ᵉ ob' × s n.-⟦ ms / ms' ⟧ᵐ*⇀ s'
  ._-⟦_/_⟧ⁱ⇀_ (s , ib , ob) i o (s' , ib' , ob') → {!!}
