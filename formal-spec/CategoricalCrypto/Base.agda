{-# OPTIONS --safe #-}
module CategoricalCrypto.Base where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)
import abstract-set-theory.Prelude as P

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

--------------------------------------------------------------------------------
-- Channels, which form the objects

record Channel : Type₁ where
  field P                : Type
        rcvType sndType  : P → Type

infixr 9 _⊗_

I : Channel
I .Channel.P = ⊥

_ᵀ : Channel → Channel
_ᵀ c = let open Channel c in λ where .P → P ; .rcvType → sndType ; .sndType → rcvType

_⊗_ : Channel → Channel → Channel
c₁ ⊗ c₂ = let open Channel c₁ renaming (P to P₁; rcvType to rcvType₁; sndType to sndType₁)
              open Channel c₂ renaming (P to P₂; rcvType to rcvType₂; sndType to sndType₂)
              open Channel
  in λ where
    .P → P₁ ⊎ P₂
    .rcvType (inj₁ a) → rcvType₁ a
    .rcvType (inj₂ b) → rcvType₂ b
    .sndType (inj₁ a) → sndType₁ a
    .sndType (inj₂ b) → sndType₂ b

rcvˡ : ∀ {A B} → ∃ (Channel.rcvType A) → ∃ (Channel.rcvType (A ⊗ B))
rcvˡ (p , x) = inj₁ p , x

rcvʳ : ∀ {A B} → ∃ (Channel.rcvType B) → ∃ (Channel.rcvType (A ⊗ B))
rcvʳ (p , x) = inj₂ p , x

sndˡ : ∀ {A B} → ∃ (Channel.sndType A) → ∃ (Channel.sndType (A ⊗ B))
sndˡ (p , x) = inj₁ p , x

sndʳ : ∀ {A B} → ∃ (Channel.sndType B) → ∃ (Channel.sndType (A ⊗ B))
sndʳ (p , x) = inj₂ p , x

honestInputI : ∀ {A B Adv} → ∃ (Channel.sndType B) → ∃ (Channel.rcvType (A ⊗ (B ⊗ Adv) ᵀ))
honestInputI = rcvʳ P.∘ sndˡ

honestOutputO : ∀ {A B Adv} → ∃ (Channel.rcvType B) → ∃ (Channel.sndType (A ⊗ (B ⊗ Adv) ᵀ))
honestOutputO = sndʳ P.∘ rcvˡ

honestOutputO' : ∀ {A B Adv} → ∃ (Channel.rcvType B) → Maybe (∃ (Channel.sndType (A ⊗ (B ⊗ Adv) ᵀ)))
honestOutputO' = just P.∘ honestOutputO

adversarialInput : ∀ {A B Adv} → ∃ (Channel.sndType Adv) → ∃ (Channel.rcvType (A ⊗ (B ⊗ Adv) ᵀ))
adversarialInput = rcvʳ P.∘ sndʳ

adversarialOutput : ∀ {A B Adv} → ∃ (Channel.rcvType Adv) → ∃ (Channel.sndType (A ⊗ (B ⊗ Adv) ᵀ))
adversarialOutput = sndʳ P.∘ rcvʳ

honestOutputI : ∀ {A B Adv} → ∃ (Channel.rcvType A) → ∃ (Channel.rcvType (A ⊗ (B ⊗ Adv) ᵀ))
honestOutputI = rcvˡ

honestInputO : ∀ {A B Adv} → ∃ (Channel.sndType A) → ∃ (Channel.sndType (A ⊗ (B ⊗ Adv) ᵀ))
honestInputO = sndˡ

honestInputO' : ∀ {A B Adv} → ∃ (Channel.sndType A) → Maybe (∃ (Channel.sndType (A ⊗ (B ⊗ Adv) ᵀ)))
honestInputO' = just P.∘ honestInputO

simpleChannel : Type → Type → Channel
simpleChannel X Y = record { P = ⊤ ; rcvType = const X ; sndType = const Y }

data ChannelDir : Type where
  In Out : ChannelDir

simpleChannel' : (ChannelDir → Type) → Channel
simpleChannel' T = simpleChannel (T In) (T Out)

⨂_ : {n : ℕ} → (F : Fin n → Channel) → Channel
⨂_ {zero} F = I
⨂_ {suc n} F = F fzero ⊗ ⨂ (F P.∘ fsuc)

⨂≡ : ∀ {n} → {A B : Fin n → Channel} → (∀ k → A k ≡ B k) → ⨂ A ≡ ⨂ B
⨂≡ {zero}          eqs = refl
⨂≡ {suc n} {A} {B} eqs = cong₂ _⊗_ (eqs fzero) (⨂≡ {n} {A P.∘ fsuc} {B P.∘ fsuc} (eqs P.∘ fsuc))

rcv⨂ : {n : ℕ} {F : Fin n → Channel} → (k : Fin n) → ∃ (Channel.rcvType (F k)) → ∃ (Channel.rcvType (⨂ F))
rcv⨂ fzero = rcvˡ
rcv⨂ (fsuc k) x = rcvʳ (rcv⨂ k x)

snd⨂ : {n : ℕ} {F : Fin n → Channel} → (k : Fin n) → ∃ (Channel.sndType (F k)) → ∃ (Channel.sndType (⨂ F))
snd⨂ fzero = sndˡ
snd⨂ (fsuc k) x = sndʳ (snd⨂ k x)

--------------------------------------------------------------------------------
-- Machines, which form the morphisms

MachineType : Channel → Channel → Type → Type₁
MachineType A B S = let open Channel (A ⊗ B ᵀ) in
  S → ∃ rcvType → Maybe (∃ sndType) → S → Type

record Machine (A B : Channel) : Type₁ where
  constructor MkMachine
  field State    : Type
        stepRel  : MachineType A B State

module _ {A B} (let open Channel (A ⊗ B ᵀ)) where
  MkMachine' : ∀ {State} → MachineType A B State → Machine A B
  MkMachine' = MkMachine _

  StatelessMachine : (∃ rcvType → Maybe (∃ sndType) → Type) → Machine A B
  StatelessMachine R = MkMachine ⊤ (λ _ i o _ → R i o)

  FunctionMachine : (∃ rcvType → Maybe (∃ sndType)) → Machine A B
  FunctionMachine f = StatelessMachine (λ i o → f i ≡ o)

  TotalFunctionMachine : (∃ rcvType → ∃ sndType) → Machine A B
  TotalFunctionMachine f = FunctionMachine (just P.∘ f)

-- this forces all messages to go 'through' the machine, i.e.
-- messages on the domain become messages on the codomain and vice versa
-- if e.g. A ≡ B then it's easy to accidentally send a message the wrong way
-- which is prevented here
TotalFunctionMachine' : ∀ {A B} (let open Channel)
  → (∃ (rcvType A) → ∃ (rcvType B)) → (∃ (sndType B) → ∃ (sndType A)) → Machine A B
TotalFunctionMachine' f g = TotalFunctionMachine λ where
  (inj₁ p , m) → sndʳ (f (p , m))
  (inj₂ p , m) → sndˡ (g (p , m))

id : ∀ {A} → Machine A A
id = TotalFunctionMachine λ where
  (inj₁ p , m) → (inj₂ p , m)
  (inj₂ p , m) → (inj₁ p , m)

module Tensor {A B C D} (M₁ : Machine A B) (M₂ : Machine C D) where
  open Machine M₁ renaming (State to State₁; stepRel to stepRel₁)
  open Machine M₂ renaming (State to State₂; stepRel to stepRel₂)

  State = State₁ × State₂

  AllCs = (A ⊗ B ᵀ) ⊗ (C ⊗ D ᵀ)

  data CompRel : State → ∃ (Channel.rcvType AllCs) → Maybe (∃ (Channel.sndType AllCs)) → State → Type where
    Step₁ : ∀ {p m m' s s' s₂} → stepRel₁ s (p , m) m' s'
          → CompRel (s , s₂) (inj₁ p , m) (sndˡ <$> m') (s' , s₂)

    Step₂ : ∀ {p m m' s s' s₁} → stepRel₂ s (p , m) m' s'
          → CompRel (s₁ , s) (inj₂ p , m) (sndʳ <$> m') (s₁ , s')

  _⊗'_ : Machine (A ⊗ C) (B ⊗ D)
  _⊗'_ = λ where
    .Machine.State → State
    .Machine.stepRel s m m' s' → CompRel
      s
      (case m of λ where
        (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
        (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
        (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
        (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m))
      ((λ where
        (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
        (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
        (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
        (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m)) <$> m')
      s'

open Tensor using (_⊗'_) public

_⊗ˡ_ : ∀ {A B} → (C : Channel) → Machine A B → Machine (C ⊗ A) (C ⊗ B)
C ⊗ˡ M = id ⊗' M

_⊗ʳ_ : ∀ {A B} → Machine A B → (C : Channel) → Machine (A ⊗ C) (B ⊗ C)
M ⊗ʳ C = M ⊗' id

module Comp {A B C} (M₁ : Machine B C) (M₂ : Machine A B) where
  open Machine M₁ renaming (State to State₁; stepRel to stepRel₁)
  open Machine M₂ renaming (State to State₂; stepRel to stepRel₂)

  State = State₁ × State₂

  AllCs = (A ⊗ B ᵀ) ⊗ (B ⊗ C ᵀ)

  data CompRel : State → ∃ (Channel.rcvType AllCs) → Maybe (∃ (Channel.sndType AllCs)) → State → Type where
    Step₁ : ∀ {p m m' s s' s₂} → stepRel₁ s (p , m) m' s'
          → CompRel (s , s₂) (inj₂ p , m) (sndʳ <$> m') (s' , s₂)

    Step₂ : ∀ {p m m' s s' s₁} → stepRel₂ s (p , m) m' s'
          → CompRel (s₁ , s) (inj₁ p , m) (sndˡ <$> m') (s₁ , s')

    Multi₁ : ∀ {p m m' m'' s s' s''}
           → CompRel s m (just ((inj₂ (inj₁ p) , m'))) s'
           → CompRel s' (inj₁ (inj₂ p) , m') m'' s''
           → CompRel s m m'' s''

    Multi₂ : ∀ {p m m' m'' s s' s''}
           → CompRel s m (just (inj₁ (inj₂ p) , m')) s'
           → CompRel s' (inj₂ (inj₁ p) , m') m'' s''
           → CompRel s m m'' s''

  infixr 9 _∘_

  _∘_ : Machine A C
  _∘_ = λ where
    .Machine.State → State
    .Machine.stepRel s m m' s' →
      CompRel
        s (case m of λ where (inj₁ x , m) → inj₁ (inj₁ x) , m ; (inj₂ y , m) → inj₂ (inj₂ y) , m)
        ((λ where (inj₁ x , m) → inj₁ (inj₁ x) , m ; (inj₂ y , m) → inj₂ (inj₂ y) , m) <$> m') s'

open Comp using (_∘_) public

module Machine-Reasoning where
  open import Relation.Binary.Reasoning.Syntax

  open begin-syntax Machine P.id public
  open ⟶-syntax {R = Machine} Machine Machine (λ M₁ M₂ → M₂ ∘ M₁) public
  open end-syntax Machine id public

⊗-assoc : ∀ {A B C} → Machine ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
⊗-assoc = TotalFunctionMachine'
  (λ where (inj₁ (inj₁ p) , m) →       inj₁ p  , m
           (inj₁ (inj₂ p) , m) → inj₂ (inj₁ p) , m
           (      inj₂ p  , m) → inj₂ (inj₂ p) , m)
  (λ where (      inj₁ p  , m) → inj₁ (inj₁ p) , m
           (inj₂ (inj₁ p) , m) → inj₁ (inj₂ p) , m
           (inj₂ (inj₂ p) , m) →       inj₂ p  , m)

⊗-assoc⃖ : ∀ {A B C} → Machine (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
⊗-assoc⃖ = TotalFunctionMachine'
  (λ where (      inj₁ p  , m) → inj₁ (inj₁ p) , m
           (inj₂ (inj₁ p) , m) → inj₁ (inj₂ p) , m
           (inj₂ (inj₂ p) , m) →       inj₂ p  , m)
  (λ where (inj₁ (inj₁ p) , m) →       inj₁ p  , m
           (inj₁ (inj₂ p) , m) → inj₂ (inj₁ p) , m
           (      inj₂ p  , m) → inj₂ (inj₂ p) , m)

⊗-sym : ∀ {A B} → Machine (A ⊗ B) (B ⊗ A)
⊗-sym = TotalFunctionMachine'
  (λ where (inj₁ p , m) → inj₂ p , m
           (inj₂ p , m) → inj₁ p , m)
  (λ where (inj₁ p , m) → inj₂ p , m
           (inj₂ p , m) → inj₁ p , m)

idᴷ : Machine I (I ⊗ I)
idᴷ = TotalFunctionMachine λ where
  (inj₂ (inj₁ ()) , _)
  (inj₂ (inj₂ ()) , _)

_∘ᴷ_ : ∀ {A B C E₁ E₂}
     → Machine B (C ⊗ E₂) → Machine A (B ⊗ E₁) → Machine A (C ⊗ (E₁ ⊗ E₂))
_∘ᴷ_ {A} {B} {C} {E₁} {E₂} M₂ M₁ = rew ∘ (M₂ ⊗ʳ E₁ ∘ M₁)
  where
    open Machine-Reasoning
    rew : Machine ((C ⊗ E₂) ⊗ E₁) (C ⊗ (E₁ ⊗ E₂))
    rew = begin
      (C ⊗ E₂) ⊗ E₁
        ⟶⟨ ⊗-assoc ⟩
      C ⊗ (E₂ ⊗ E₁)
        ⟶⟨ C ⊗ˡ ⊗-sym ⟩
      C ⊗ (E₁ ⊗ E₂) ∎

_⊗ᴷ_ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂}
     → Machine A₁ (B₁ ⊗ E₁) → Machine A₂ (B₂ ⊗ E₂) → Machine (A₁ ⊗ A₂) ((B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂))
_⊗ᴷ_ {A₁} {B₁} {E₁} {A₂} {B₂} {E₂} M₁ M₂ = rew ∘ M₁ ⊗' M₂
  where
    open Machine-Reasoning
    rew : Machine ((B₁ ⊗ E₁) ⊗ (B₂ ⊗ E₂)) ((B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂))
    rew = begin
      (B₁ ⊗ E₁) ⊗ (B₂ ⊗ E₂)
        ⟶⟨ ⊗-assoc ⟩
      B₁ ⊗ (E₁ ⊗ (B₂ ⊗ E₂))
        ⟶⟨ B₁ ⊗ˡ ⊗-assoc⃖ ⟩
      B₁ ⊗ ((E₁ ⊗ B₂) ⊗ E₂)
        ⟶⟨ B₁ ⊗ˡ (⊗-sym ⊗ʳ E₂) ⟩
      B₁ ⊗ ((B₂ ⊗ E₁) ⊗ E₂)
        ⟶⟨ B₁ ⊗ˡ ⊗-assoc ⟩
      B₁ ⊗ (B₂ ⊗ (E₁ ⊗ E₂))
        ⟶⟨ ⊗-assoc⃖ ⟩
      (B₁ ⊗ B₂) ⊗ (E₁ ⊗ E₂) ∎

⨂ᴷ : ∀ {n} → {A B E : Fin n → Channel} → ((k : Fin n) → Machine (A k) (B k ⊗ E k))
    → Machine (⨂ A) (⨂ B ⊗ ⨂ E)
⨂ᴷ {zero} M = idᴷ
⨂ᴷ {suc n} M = M fzero ⊗ᴷ ⨂ᴷ (M P.∘ fsuc)

--------------------------------------------------------------------------------
-- Open adersarial protocols
record OAP (A E₁ B E₂ : Channel) : Type₁ where
  field Adv        : Channel
        Protocol   : Machine A (B ⊗ Adv)
        Adversary  : Machine (Adv ⊗ E₁) E₂

--------------------------------------------------------------------------------
-- Environment model

ℰ-Out : Channel
ℰ-Out .Channel.P = ⊤
ℰ-Out .Channel.sndType _ = Bool
ℰ-Out .Channel.rcvType _ = ⊥

-- Presheaf on the category of channels & machines
-- we just take machines that output a boolean
-- for now, not on the Kleisli construction
ℰ : Channel → Type₁
ℰ C = Machine C ℰ-Out

map-ℰ : ∀ {A B} → Machine A B → ℰ B → ℰ A
map-ℰ M E = E ∘ M

--------------------------------------------------------------------------------
-- UC relations

-- perfect equivalence
_≈ℰ_ : ∀ {A B} → Machine A B → Machine A B → Type₁
_≈ℰ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≡ map-ℰ M' E

_≤UC_ : ∀ {A B E E''} → Machine A (B ⊗ E) → Machine A (B ⊗ E'') → Type₁
_≤UC_ {B = B} {E} R I = ∀ E' (A : Machine E E') → ∃[ S ] ((B ⊗ˡ A) ∘ R) ≈ℰ ((B ⊗ˡ S) ∘ I)

-- equivalent to _≤UC_ by "completeness of the dummy adversary"
_≤'UC_ : ∀ {A B E} → Machine A (B ⊗ E) → Machine A (B ⊗ E) → Type₁
_≤'UC_ {B = B} R I = ∃[ S ] R ≈ℰ (B ⊗ˡ S ∘ I)
