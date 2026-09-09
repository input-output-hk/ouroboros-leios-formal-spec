{-# OPTIONS --safe #-}

open import Leios.Config
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.SpecStructure

open import CategoricalCrypto hiding (id; _∘_; eval)
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Ext using (Trace-trans)

open import Data.Nat.Properties using (+-suc; +-comm)

-- Progress for the bare Linear Leios node: from any state whose slot upkeep
-- is complete, the node can run through a whole slot.
--
-- Safety and liveness are stated as `Invariant`s, i.e. preservation along
-- `Trace`s, which says nothing if too few traces exist.  This module supplies
-- the traces: `tick` builds one slot, `ticks` iterates it, and `enough-traces`
-- states the result in the form of the requirement, "every future slot is
-- reachable".  The inputs are chosen here (the messages delivered, the ledger
-- fetched); a node in a network gets them from its network adapter and the
-- base layer, and the corresponding lemma for the composite node is future
-- work.
module Leios.Linear.Progress (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params) where

open import Leios.Linear ⋯ params
open Types params
open BaseAbstract B'

open LeiosState using (slot; Upkeep)

private variable
  s s' : LeiosState
  u    : SlotUpkeep
  l    : List SlotUpkeep

-- The block-production rules leave the slot alone.
↝-slot : ∀ {i} → s ↝ (s' , i) → slot s' ≡ slot s
↝-slot (EB-Role _) = refl
↝-slot (VT-Role _) = refl

-- Upkeep facts, transported along an equation for the upkeep list.
private
  -- The state is explicit: reached only through the projection `Upkeep`, an
  -- implicit one would be η-expanded and its other fields left unsolved.
  needs : ∀ s → Upkeep s ≡ l → u ∉ˡ l → LeiosState.needsUpkeep s u
  needs {u = u} _ eq n = subst (u ∉ˡ_) (sym eq) n

  has : ∀ s → Upkeep s ≡ l → u ∈ˡ l → LeiosState.hasUpkeep s u
  has {u = u} _ eq h = subst (u ∈ˡ_) (sym eq) h

  allDone-of : ∀ s → Upkeep s ≡ VT-Role ∷ Base ∷ EB-Role ∷ [] → allDone s
  allDone-of s eq = has s eq (here refl) , has s eq (there (there (here refl))) , has s eq (there (here refl))

  Base∉ : Base ∉ˡ EB-Role ∷ []
  Base∉ (here ())
  Base∉ (there ())

  VT-Role∉ : VT-Role ∉ˡ Base ∷ EB-Role ∷ []
  VT-Role∉ (here ())
  VT-Role∉ (there (here ()))
  VT-Role∉ (there (there ()))

-- One upkeep step for a role, positive (`Roles₁`) if the role can act and
-- negative (`Roles₂`) otherwise; `Dec-↝` decides which.  Either way the role
-- is added to the upkeep and the slot is unchanged.
upkeep-step : ∀ s u → u ≢ Base → LeiosState.needsUpkeep s u
            → ∃[ s' ] ∃[ o ] (s -⟦ (ϵ ⊗R) ⊗R ↑ᵢ SLOT / o ⟧⇀ s')
                    × Upkeep s' ≡ u ∷ Upkeep s
                    × slot s' ≡ slot s
upkeep-step s u u≢Base nu with ¿ ∃[ s'×i ] (s ↝ s'×i × (u ∷ Upkeep s) ≡ Upkeep (proj₁ s'×i)) ¿
... | yes ((s' , i) , st , eq) = s' , _ , Roles₁ st , sym eq , ↝-slot st
... | no ¬p                    = addUpkeep s u , _ , Roles₂ (¬p , nu , u≢Base) , refl , refl

-- The three upkeep items of a slot, in the order `Base₂` requires: the EB
-- role first, then the base step with its round trip through the base layer,
-- then the vote.
upkeep : ∀ s → Upkeep s ≡ []
       → ∃[ s' ] Trace LinearLeios s s' × allDone s' × slot s' ≡ slot s
upkeep s eq₀
  with upkeep-step s EB-Role (λ ()) (needs s eq₀ λ ())
... | s₃ , _ , st₃ , eq₃ , sl₃
  with upkeep-step (addUpkeep s₃ Base) VT-Role (λ ())
         (needs (addUpkeep s₃ Base) (cong (Base ∷_) (trans eq₃ (cong (EB-Role ∷_) eq₀))) VT-Role∉)
... | s₅ , _ , st₅ , eq₅ , sl₅ =
  s₅
  , (((([] ∷ʳ⟨ _ , _ , st₃ ⟩) ∷ʳ⟨ _ , _ , st₄ ⟩) ∷ʳ⟨ _ , _ , Base₃ ⟩) ∷ʳ⟨ _ , _ , st₅ ⟩)
  , allDone-of s₅ (trans eq₅ (cong (λ l → VT-Role ∷ Base ∷ l) eq₃'))
  , trans sl₅ sl₃
  where
    eq₃' : Upkeep s₃ ≡ EB-Role ∷ []
    eq₃' = trans eq₃ (cong (EB-Role ∷_) eq₀)

    st₄ : s₃ -⟦ (ϵ ⊗R) ⊗R ↑ᵢ SLOT / _ ⟧⇀ addUpkeep s₃ Base
    st₄ = Base₂ (needs s₃ eq₃' Base∉ , has s₃ eq₃' (here refl))

-- The slot transition: the network's messages arrive and the ledger is
-- fetched, leaving the upkeep empty and the slot advanced.
slot-step : ∀ s msgs rbs → allDone s
          → ∃[ s' ] Trace LinearLeios s s' × Upkeep s' ≡ [] × slot s' ≡ suc (slot s)
slot-step s msgs rbs done =
  _ , (([] ∷ʳ⟨ _ , _ , Slot₁ {s = s} {msgs = msgs} done ⟩) ∷ʳ⟨ _ , _ , Slot₂ {rbs = rbs} ⟩) , refl , refl

-- One whole slot.
tick : ∀ s msgs rbs → allDone s
     → ∃[ s' ] Trace LinearLeios s s' × allDone s' × slot s' ≡ suc (slot s)
tick s msgs rbs done with slot-step s msgs rbs done
... | s₂ , t₂ , up₂ , sl₂ with upkeep s₂ up₂
... | s' , t' , done' , sl' = s' , Trace-trans t₂ t' , done' , trans sl' sl₂

-- `n` slots, with the inputs of each slot chosen by slot number.
ticks : ∀ n s (msgsAt : ℕ → List (FFDA.Header ⊎ FFDA.Body)) (rbsAt : ℕ → List RankingBlock)
      → allDone s
      → ∃[ s' ] Trace LinearLeios s s' × allDone s' × slot s' ≡ n + slot s
ticks zero    s _      _     done = s , [] , done , refl
ticks (suc n) s msgsAt rbsAt done with tick s (msgsAt (slot s)) (rbsAt (slot s)) done
... | s₁ , t₁ , done₁ , sl₁ with ticks n s₁ msgsAt rbsAt done₁
... | s' , t' , done' , sl' = s' , Trace-trans t₁ t' , done' , trans sl' (trans (cong (n +_) sl₁) (+-suc n _))

-- The requirement itself: every future slot is reachable.
enough-traces : ∀ s n → allDone s → ∃[ s' ] slot s + n ≡ slot s' × Trace LinearLeios s s'
enough-traces s n done =
  let s' , t , _ , eq = ticks n s (λ _ → []) (λ _ → []) done
  in s' , trans (+-comm (slot s) n) (sym eq) , t
