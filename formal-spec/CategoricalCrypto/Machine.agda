{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Machine where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; [_])
import abstract-set-theory.Prelude as P
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection

-- --------------------------------------------------------------------------------
-- -- Machines, which form the morphisms

machine-type : Type → Channel → Type₁
machine-type S (inT ⇿ outT) = S → inT → Maybe outT → S → Type

_⊗ᵀ_ : Fun₂ Channel
A ⊗ᵀ B = A ⊗ B ᵀ

record Machine (A B : Channel) : Type₁ where
  constructor MkMachine

  machine-channel = A ⊗ᵀ B

  field
    {State} : Type
    stepRel : machine-type State machine-channel

-- This module exposes various ways of building machines
-- TODO: all of these are functors from the appropriate categories
module _ {A B : Channel} (let open Channel (A ⊗ᵀ B)) where

  StatelessMachine      : (inType → Maybe outType → Type)           → Machine A B
  FunctionMachine       : (inType → Maybe outType)                  → Machine A B
  TotalFunctionMachine  : A ⊗ B ᵀ [ In ]⇒[ Out ] A ⊗ B ᵀ           → Machine A B
  TotalFunctionMachine' : {@(tactic liftC) p : A [ In ]⇒[ In ] B}   →
                          {@(tactic liftC) q : B [ Out ]⇒[ Out ] A} → Machine A B
  
  StatelessMachine      R       = MkMachine {State = ⊤} $ λ _ i o _ → R i o
  FunctionMachine       f       = StatelessMachine      $ λ i o → f i ≡ o
  TotalFunctionMachine  f       = FunctionMachine       $ just P.∘ f
  TotalFunctionMachine' {f} {g} = TotalFunctionMachine  $ ⊗-combine {In} {Out} (f ⇒ₜ ?) (g ⇒ₜ ?) ⇒ₜ ⊗-sym
  -- TotalFunctionMachine' forces all messages to go 'through' the machine, i.e.
  -- messages on the domain become messages on the codomain and vice versa if
  -- e.g. A ≡ B then it's easy to accidentally send a message the wrong way
  -- which is prevented here

id-machine : ∀ {A} → Machine A A
id-machine = TotalFunctionMachine'

-- given transformation on the channels, transform the machine
modifyStepRel : ∀ {A B C D} → (∀ {m} → C ⊗ D ᵀ [ m ]⇒[ m ] A ⊗ B ᵀ) → Machine A B → Machine C D
modifyStepRel f (MkMachine stepRel) = MkMachine $ \s m m' s' → stepRel s (f {In} m) (f {Out} <$> m') s'

module Tensor {A B C D} (M₁ : Machine A B) (M₂ : Machine C D) where
  open Machine M₁ renaming (State to State₁; stepRel to stepRel₁; machine-channel to machine-channel₁)
  open Machine M₂ renaming (State to State₂; stepRel to stepRel₂; machine-channel to machine-channel₂)

  State = State₁ × State₂
  AllCs = machine-channel₁ ⊗ machine-channel₂

  data CompRel : machine-type State AllCs where
    Step₁ : ∀ {m m' s s' s₂} → stepRel₁ s m m' s' → CompRel (s , s₂) (⊗-right-intro {In} m) (⊗-right-intro {Out} <$> m') (s' , s₂)
    Step₂ : ∀ {m m' s s' s₁} → stepRel₂ s m m' s' → CompRel (s₁ , s) (⊗-left-intro {In} m) (⊗-left-intro {Out} <$> m') (s₁ , s')

  _⊗'_ : Machine (A ⊗ C) (B ⊗ D)
  _⊗'_ = modifyStepRel 
           (⊗-left-double-intro ⊗-ᵀ-distrib ⇒ₜ
            ⊗-left-assoc ⇒ₜ
            ⊗-right-double-intro (⊗-right-assoc ⇒ₜ ⊗-left-double-intro ⊗-sym ⇒ₜ ⊗-left-assoc) ⇒ₜ
            ⊗-right-assoc)
           (MkMachine CompRel)
    
open Tensor using (_⊗'_) public

_⊗ˡ_ : ∀ {A B} (C : Channel) → Machine A B → Machine (C ⊗ A) (C ⊗ B)
C ⊗ˡ M = id-machine ⊗' M

_⊗ʳ_ : ∀ {A B} → Machine A B → (C : Channel) → Machine (A ⊗ C) (B ⊗ C)
M ⊗ʳ C = M ⊗' id-machine

_∣ˡ : ∀ {A B C} → Machine (A ⊗ B) C → Machine A C
_∣ˡ = modifyStepRel $ ⊗-right-double-intro ⊗-right-intro

_∣ʳ : ∀ {A B C} → Machine (A ⊗ B) C → Machine B C
_∣ʳ = modifyStepRel $ ⊗-right-double-intro ⊗-left-intro

_∣^ˡ : ∀ {A B C} → Machine A (B ⊗ C) → Machine A B
_∣^ˡ = modifyStepRel $ ⊗-left-double-intro $ ⊗-right-intro ⇒ₜ ⊗-ᵀ-factor
  
_∣^ʳ : ∀ {A B C} → Machine A (B ⊗ C) → Machine A C
_∣^ʳ = modifyStepRel $ ⊗-left-double-intro $ ⊗-left-intro ⇒ₜ ⊗-ᵀ-factor

-- trace monoidal category?
-- What happens when you compose with a trace ?
-- Product of the traces ?
-- The regular composition "eats" messages
-- Trace: input-output behavior of the machines, list of messages
module _ {A B C} (M : Machine (A ⊗ C) (B ⊗ C)) (let open Machine M) where

  data TraceRel : machine-type State ((A ⊗ C) ⊗ᵀ (B ⊗ C)) where

    Trace[_] : ∀ {s inM outM s'} → stepRel s inM outM s' → TraceRel s inM outM s'

    _Trace∷ₒ_ : ∀ {s s' s'' inM outC outMₘ} → stepRel s inM (just ((L⊗ ϵ) ⊗R ↑ₒ outC)) s' →
                                             TraceRel s' (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ outC) outMₘ s'' →
                                             TraceRel s inM outMₘ s''
                                        
    _Trace∷ᵢ_ : ∀ {s s' s'' inM inC outMₘ} → stepRel s inM (just (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ inC)) s' →
                                            TraceRel s' ((L⊗ ϵ) ⊗R ↑ᵢ inC) outMₘ s'' →
                                            TraceRel s inM outMₘ s''

  tr : Machine A B
  tr = MkMachine TraceRel ∣ˡ ∣^ˡ

infixr 9 _∘_

_∘_ : ∀ {B C A} → Machine B C → Machine A B → Machine A C
M₁ ∘ M₂ = tr $ modifyStepRel (⊗-left-double-intro $ ⊗-ᵀ-distrib ⇒ₜ ⊗-sym ⇒ₜ ⊗-ᵀ-factor) (M₂ ⊗' M₁)

⊗-assoc : ∀ {A B C} → Machine ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
⊗-assoc = TotalFunctionMachine' {_} {_} {{!!}} {{!!}}
  
-- ⊗-assoc⃖ : ∀ {A B C} → Machine (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
-- ⊗-assoc⃖ = TotalFunctionMachine'

-- ⊗-symₘ : ∀ {A B} → Machine (A ⊗ B) (B ⊗ A)
-- ⊗-symₘ = TotalFunctionMachine' ⊗-sym ⊗-sym

-- idᴷ : Machine I (I ⊗ I)
-- idᴷ rewrite ᵀ-identity = TotalFunctionMachine $ ⊗-combine {In} ⇒-transpose $ ⊗-ᵀ-distrib ⇒ₜ ⊗-fusion ⇒ₜ ⇒-transpose ⇒ₜ ⊗-right-intro ⇒ₜ ⊗-ᵀ-factor

-- transpose : ∀ {A B} → Machine A B → Machine (B ᵀ) (A ᵀ)
-- transpose M = modifyStepRel M ⊗-sym
 
-- -- cup : Machine I (A ⊗ A ᵀ)
-- -- cup = StatelessMachine λ x x₁ → {!!}

-- -- cap : Machine (A ᵀ ⊗ A) I
-- -- cap {A} = modifyStepRel (transpose (cup {A})) {!!} {!!}

-- module Machine-Reasoning where
--   open import Relation.Binary.Reasoning.Syntax

--   open begin-syntax Machine P.id public
--   open ⟶-syntax {R = Machine} Machine Machine (λ M₁ M₂ → M₂ ∘ M₁) public
--   open end-syntax Machine id public

-- _∘ᴷ_ : ∀ {A B C E₁ E₂}
--      → Machine B (C ⊗ E₂) → Machine A (B ⊗ E₁) → Machine A (C ⊗ (E₁ ⊗ E₂))
-- _∘ᴷ_ {A} {B} {C} {E₁} {E₂} M₂ M₁ = rew ∘ (M₂ ⊗ʳ E₁ ∘ M₁)
--   where
--     open Machine-Reasoning
--     rew : Machine ((C ⊗ E₂) ⊗ E₁) (C ⊗ (E₁ ⊗ E₂))
--     rew = begin
--       (C ⊗ E₂) ⊗ E₁ ⟶⟨ ⊗-assoc ⟩
--       C ⊗ (E₂ ⊗ E₁) ⟶⟨ C ⊗ˡ ⊗-symₘ ⟩
--       C ⊗ (E₁ ⊗ E₂) ∎

-- _⊗ᴷ_ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂}
--      → Machine A₁ (B₁ ⊗ E₁) → Machine A₂ (B₂ ⊗ E₂) → Machine (A₁ ⊗ A₂) ((B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂))
-- _⊗ᴷ_ {A₁} {B₁} {E₁} {A₂} {B₂} {E₂} M₁ M₂ = rew ∘ M₁ ⊗' M₂
--   where
--     open Machine-Reasoning
--     rew : Machine ((B₁ ⊗ E₁) ⊗ (B₂ ⊗ E₂)) ((B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂))
--     rew = begin
--       (B₁ ⊗ E₁) ⊗ (B₂ ⊗ E₂) ⟶⟨ ⊗-assoc ⟩
--       B₁ ⊗ (E₁ ⊗ (B₂ ⊗ E₂)) ⟶⟨ B₁ ⊗ˡ ⊗-assoc⃖ ⟩
--       B₁ ⊗ ((E₁ ⊗ B₂) ⊗ E₂) ⟶⟨ B₁ ⊗ˡ (⊗-symₘ ⊗ʳ E₂) ⟩
--       B₁ ⊗ ((B₂ ⊗ E₁) ⊗ E₂) ⟶⟨ B₁ ⊗ˡ ⊗-assoc ⟩
--       B₁ ⊗ (B₂ ⊗ (E₁ ⊗ E₂)) ⟶⟨ ⊗-assoc⃖ ⟩
--       (B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂) ∎

-- ⨂ᴷ : ∀ {n} → {A B E : Fin n → Channel} → ((k : Fin n) → Machine (A k) (B k ⊗ E k)) → Machine (⨂ A) (⨂ B ⊗ ⨂ E)
-- ⨂ᴷ {zero} M = idᴷ
-- ⨂ᴷ {suc n} M = M fzero ⊗ᴷ ⨂ᴷ (M P.∘ fsuc)

-- --------------------------------------------------------------------------------
-- -- Open adversarial protocols

-- record OAP (A E₁ B E₂ : Channel) : Type₁ where
--   field Adv        : Channel
--         Protocol   : Machine A (B ⊗ Adv)
--         Adversary  : Machine (Adv ⊗ E₁) E₂

-- --------------------------------------------------------------------------------
-- -- Environment model

-- ℰ-Out : Channel
-- ℰ-Out = Bool ⇿ ⊥

-- -- Presheaf on the category of channels & machines
-- -- we just take machines that output a boolean
-- -- for now, not on the Kleisli construction
-- ℰ : Channel → Type₁
-- ℰ C = Machine C ℰ-Out

-- map-ℰ : ∀ {A B} → Machine A B → ℰ B → ℰ A
-- map-ℰ M E = E ∘ M

-- --------------------------------------------------------------------------------
-- -- UC relations

-- -- perfect equivalence
-- _≈ℰ_ : ∀ {A B} → Machine A B → Machine A B → Type₁
-- _≈ℰ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≡ map-ℰ M' E

-- _≤UC_ : ∀ {A B E E''} → Machine A (B ⊗ E) → Machine A (B ⊗ E'') → Type₁
-- _≤UC_ {B = B} {E} R I = ∀ E' (A : Machine E E') → ∃[ S ] ((B ⊗ˡ A) ∘ R) ≈ℰ ((B ⊗ˡ S) ∘ I)

-- -- equivalent to _≤UC_ by "completeness of the dummy adversary"
-- _≤'UC_ : ∀ {A B E} → Machine A (B ⊗ E) → Machine A (B ⊗ E) → Type₁
-- _≤'UC_ {B = B} R I = ∃[ S ] R ≈ℰ (B ⊗ˡ S ∘ I)
