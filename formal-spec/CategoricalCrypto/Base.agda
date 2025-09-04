{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Base where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; [_])
import abstract-set-theory.Prelude as P

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

-- --------------------------------------------------------------------------------
-- -- Machines, which form the morphisms

-- MachineType : Channel → Channel → Type → Type₁
-- MachineType A B S = let open Channel (A ⊗ B ᵀ) in
--   S → ∃ rcvType → Maybe (∃ sndType) → S → Type

-- record Machine (A B : Channel) : Type₁ where
--   constructor MkMachine
--   field State    : Type
--         stepRel  : MachineType A B State

-- module _ {A B} (let open Channel (A ⊗ B ᵀ)) where
--   MkMachine' : ∀ {State} → MachineType A B State → Machine A B
--   MkMachine' = MkMachine _

--   -- TODO: all of these are functors from the appropriate categories
--   StatelessMachine : (∃ rcvType → Maybe (∃ sndType) → Type) → Machine A B
--   StatelessMachine R = MkMachine ⊤ (λ _ i o _ → R i o)

--   FunctionMachine : (∃ rcvType → Maybe (∃ sndType)) → Machine A B
--   FunctionMachine f = StatelessMachine (λ i o → f i ≡ o)

--   TotalFunctionMachine : (∃ rcvType → ∃ sndType) → Machine A B
--   TotalFunctionMachine f = FunctionMachine (just P.∘ f)

-- -- this forces all messages to go 'through' the machine, i.e.
-- -- messages on the domain become messages on the codomain and vice versa
-- -- if e.g. A ≡ B then it's easy to accidentally send a message the wrong way
-- -- which is prevented here
-- TotalFunctionMachine' : (let open Channel)
--   → (∃ (rcvType A) → ∃ (rcvType B)) → (∃ (sndType B) → ∃ (sndType A)) → Machine A B
-- TotalFunctionMachine' f g = TotalFunctionMachine λ where
--   (inj₁ p , m) → sndʳ (f (p , m))
--   (inj₂ p , m) → sndˡ (g (p , m))

-- id : Machine A A
-- id = TotalFunctionMachine λ where
--   (inj₁ p , m) → (inj₂ p , m)
--   (inj₂ p , m) → (inj₁ p , m)

-- module _ (M : Machine A B) where
--   open Machine M

--   -- given transformation on the channels, transform the machine
--   modifyStepRel : (∃ (Channel.rcvType (C ⊗ D ᵀ)) → ∃ (Channel.rcvType (A ⊗ B ᵀ)))
--                 → (∃ (Channel.sndType (C ⊗ D ᵀ)) → ∃ (Channel.sndType (A ⊗ B ᵀ)))
--                 → Machine C D
--   modifyStepRel _ _ .State   = State
--   modifyStepRel f g .stepRel s m m' s' = stepRel s (f m) (g <$> m') s'

-- module Tensor (M₁ : Machine A B) (M₂ : Machine C D) where
--   open Machine M₁ renaming (State to State₁; stepRel to stepRel₁)
--   open Machine M₂ renaming (State to State₂; stepRel to stepRel₂)

--   State = State₁ × State₂

--   AllCs = (A ⊗ B ᵀ) ⊗ (C ⊗ D ᵀ)

--   data CompRel : State → ∃ (Channel.rcvType AllCs) → Maybe (∃ (Channel.sndType AllCs)) → State → Type where
--     Step₁ : ∀ {p m m' s s' s₂} → stepRel₁ s (p , m) m' s'
--           → CompRel (s , s₂) (inj₁ p , m) (sndˡ <$> m') (s' , s₂)

--     Step₂ : ∀ {p m m' s s' s₁} → stepRel₂ s (p , m) m' s'
--           → CompRel (s₁ , s) (inj₂ p , m) (sndʳ <$> m') (s₁ , s')

--   _⊗'_ : Machine (A ⊗ C) (B ⊗ D)
--   _⊗'_ = modifyStepRel (MkMachine State CompRel)
--     (λ where
--       (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
--       (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
--       (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
--       (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m))
--     (λ where
--       (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
--       (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
--       (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
--       (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m))

-- open Tensor using (_⊗'_) public

-- _⊗ˡ_ : (C : Channel) → Machine A B → Machine (C ⊗ A) (C ⊗ B)
-- C ⊗ˡ M = id ⊗' M

-- _⊗ʳ_ : Machine A B → (C : Channel) → Machine (A ⊗ C) (B ⊗ C)
-- M ⊗ʳ C = M ⊗' id

-- _∣ˡ : Machine (A ⊗ B) C → Machine A C
-- M ∣ˡ = modifyStepRel M
--   (λ where (inj₁ x , y) → rcvˡ (rcvˡ (x , y)) ; (inj₂ x , y) → rcvʳ (x , y))
--   (λ where (inj₁ x , y) → sndˡ (sndˡ (x , y)) ; (inj₂ x , y) → sndʳ (x , y))

-- _∣ʳ : Machine (A ⊗ B) C → Machine B C
-- M ∣ʳ = modifyStepRel M
--   (λ where (inj₁ x , y) → rcvˡ (rcvʳ (x , y)) ; (inj₂ x , y) → rcvʳ (x , y))
--   (λ where (inj₁ x , y) → sndˡ (sndʳ (x , y)) ; (inj₂ x , y) → sndʳ (x , y))

-- _∣^ˡ : Machine A (B ⊗ C) → Machine A B
-- M ∣^ˡ = modifyStepRel M
--   (λ where (inj₁ x , y) → rcvˡ (x , y) ; (inj₂ x , y) → rcvʳ (sndˡ (x , y)))
--   (λ where (inj₁ x , y) → sndˡ (x , y) ; (inj₂ x , y) → sndʳ (rcvˡ (x , y)))

-- _∣^ʳ : Machine A (B ⊗ C) → Machine A C
-- M ∣^ʳ = modifyStepRel M
--   (λ where (inj₁ x , y) → rcvˡ (x , y) ; (inj₂ x , y) → rcvʳ (sndʳ (x , y)))
--   (λ where (inj₁ x , y) → sndˡ (x , y) ; (inj₂ x , y) → sndʳ (rcvʳ (x , y)))

-- module _ (M : Machine (A ⊗ C) (B ⊗ C)) where
--   open Machine M

--   data TraceRel : MachineType (A ⊗ C) (B ⊗ C) State where
--     Trace[_] : ∀ {s m m' s'} → stepRel s m m' s' → TraceRel s m m' s'
--     _Trace∷₁_ : ∀ {s s' s'' m m' m''} → stepRel s m (just (sndˡ (sndʳ m'))) s' → TraceRel s' (rcvʳ (sndʳ m')) m'' s'' → TraceRel s m m'' s''
--     _Trace∷₂_ : ∀ {s s' s'' m m' m''} → stepRel s m (just (sndʳ (rcvʳ m'))) s' → TraceRel s' (rcvˡ (rcvʳ m')) m'' s'' → TraceRel s m m'' s''

--   tr : Machine A B
--   tr = MkMachine State TraceRel ∣ˡ ∣^ˡ

-- infixr 9 _∘_

-- _∘_ : Machine B C → Machine A B → Machine A C
-- _∘_ {B} {C} {A} M₁ M₂ = tr M
--   where
--     M : Machine (A ⊗ B) (C ⊗ B)
--     M = modifyStepRel (M₂ ⊗' M₁)
--       (rcvMapʳ (λ where (inj₁ x , c) → inj₂ x , c ; (inj₂ x , b) → inj₁ x , b))
--       (sndMapʳ (λ where (inj₁ x , b) → inj₂ x , b ; (inj₂ x , c) → inj₁ x , c))

-- ⊗-assoc : ∀ {A B C} → Machine ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
-- ⊗-assoc = TotalFunctionMachine'
--   (λ where (inj₁ (inj₁ p) , m) →       inj₁ p  , m
--            (inj₁ (inj₂ p) , m) → inj₂ (inj₁ p) , m
--            (      inj₂ p  , m) → inj₂ (inj₂ p) , m)
--   (λ where (      inj₁ p  , m) → inj₁ (inj₁ p) , m
--            (inj₂ (inj₁ p) , m) → inj₁ (inj₂ p) , m
--            (inj₂ (inj₂ p) , m) →       inj₂ p  , m)

-- ⊗-assoc⃖ : ∀ {A B C} → Machine (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
-- ⊗-assoc⃖ = TotalFunctionMachine'
--   (λ where (      inj₁ p  , m) → inj₁ (inj₁ p) , m
--            (inj₂ (inj₁ p) , m) → inj₁ (inj₂ p) , m
--            (inj₂ (inj₂ p) , m) →       inj₂ p  , m)
--   (λ where (inj₁ (inj₁ p) , m) →       inj₁ p  , m
--            (inj₁ (inj₂ p) , m) → inj₂ (inj₁ p) , m
--            (      inj₂ p  , m) → inj₂ (inj₂ p) , m)

-- ⊗-sym : ∀ {A B} → Machine (A ⊗ B) (B ⊗ A)
-- ⊗-sym = TotalFunctionMachine'
--   (λ where (inj₁ p , m) → inj₂ p , m
--            (inj₂ p , m) → inj₁ p , m)
--   (λ where (inj₁ p , m) → inj₂ p , m
--            (inj₂ p , m) → inj₁ p , m)

-- idᴷ : Machine I (I ⊗ I)
-- idᴷ = TotalFunctionMachine λ where
--   (inj₂ (inj₁ ()) , _)
--   (inj₂ (inj₂ ()) , _)

-- transpose : Machine A B → Machine (B ᵀ) (A ᵀ)
-- transpose M = modifyStepRel M
--   (λ where (inj₁ x , y) → inj₂ x , y ; (inj₂ x , y) → inj₁ x , y)
--   (λ where (inj₁ x , y) → inj₂ x , y ; (inj₂ x , y) → inj₁ x , y)

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
--       (C ⊗ E₂) ⊗ E₁
--         ⟶⟨ ⊗-assoc ⟩
--       C ⊗ (E₂ ⊗ E₁)
--         ⟶⟨ C ⊗ˡ ⊗-sym ⟩
--       C ⊗ (E₁ ⊗ E₂) ∎

-- _⊗ᴷ_ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂}
--      → Machine A₁ (B₁ ⊗ E₁) → Machine A₂ (B₂ ⊗ E₂) → Machine (A₁ ⊗ A₂) ((B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂))
-- _⊗ᴷ_ {A₁} {B₁} {E₁} {A₂} {B₂} {E₂} M₁ M₂ = rew ∘ M₁ ⊗' M₂
--   where
--     open Machine-Reasoning
--     rew : Machine ((B₁ ⊗ E₁) ⊗ (B₂ ⊗ E₂)) ((B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂))
--     rew = begin
--       (B₁ ⊗ E₁) ⊗ (B₂ ⊗ E₂)
--         ⟶⟨ ⊗-assoc ⟩
--       B₁ ⊗ (E₁ ⊗ (B₂ ⊗ E₂))
--         ⟶⟨ B₁ ⊗ˡ ⊗-assoc⃖ ⟩
--       B₁ ⊗ ((E₁ ⊗ B₂) ⊗ E₂)
--         ⟶⟨ B₁ ⊗ˡ (⊗-sym ⊗ʳ E₂) ⟩
--       B₁ ⊗ ((B₂ ⊗ E₁) ⊗ E₂)
--         ⟶⟨ B₁ ⊗ˡ ⊗-assoc ⟩
--       B₁ ⊗ (B₂ ⊗ (E₁ ⊗ E₂))
--         ⟶⟨ ⊗-assoc⃖ ⟩
--       (B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂) ∎

-- ⨂ᴷ : ∀ {n} → {A B E : Fin n → Channel} → ((k : Fin n) → Machine (A k) (B k ⊗ E k))
--     → Machine (⨂ A) (⨂ B ⊗ ⨂ E)
-- ⨂ᴷ {zero} M = idᴷ
-- ⨂ᴷ {suc n} M = M fzero ⊗ᴷ ⨂ᴷ (M P.∘ fsuc)

-- --------------------------------------------------------------------------------
-- -- Open adersarial protocols
-- record OAP (A E₁ B E₂ : Channel) : Type₁ where
--   field Adv        : Channel
--         Protocol   : Machine A (B ⊗ Adv)
--         Adversary  : Machine (Adv ⊗ E₁) E₂

-- --------------------------------------------------------------------------------
-- -- Environment model

-- ℰ-Out : Channel
-- ℰ-Out .Channel.P = ⊤
-- ℰ-Out .Channel.sndType _ = Bool
-- ℰ-Out .Channel.rcvType _ = ⊥

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
