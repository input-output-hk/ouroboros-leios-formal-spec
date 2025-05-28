module CategoricalCrypto where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)
import abstract-set-theory.Prelude as P
open import Leios.Prelude using (Fin; fzero; fsuc)

--------------------------------------------------------------------------------
-- Channels, which form the objects

record Channel : Set₁ where
  field P : Set
        rcvType sndType : P → Set

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

adversarialInput : ∀ {A B Adv} → ∃ (Channel.sndType Adv) → ∃ (Channel.rcvType (A ⊗ (B ⊗ Adv) ᵀ))
adversarialInput = rcvʳ P.∘ sndʳ

adversarialOutput : ∀ {A B Adv} → ∃ (Channel.rcvType Adv) → ∃ (Channel.sndType (A ⊗ (B ⊗ Adv) ᵀ))
adversarialOutput = sndʳ P.∘ rcvʳ

honestOutputI : ∀ {A B Adv} → ∃ (Channel.rcvType A) → ∃ (Channel.rcvType (A ⊗ (B ⊗ Adv) ᵀ))
honestOutputI = rcvˡ

honestInputO : ∀ {A B Adv} → ∃ (Channel.sndType A) → ∃ (Channel.sndType (A ⊗ (B ⊗ Adv) ᵀ))
honestInputO = sndˡ

simpleChannel : Type → Type → Channel
simpleChannel X Y = record { P = ⊤ ; rcvType = const X ; sndType = const Y }

data ChannelDir : Type where
  In Out : ChannelDir

simpleChannel' : (ChannelDir → Type) → Channel
simpleChannel' T = simpleChannel (T In) (T Out)

⨂_ : {n : ℕ} → (F : Fin n → Channel) → Channel
⨂_ {zero} F = I
⨂_ {suc n} F = F fzero ⊗ ⨂ (F Leios.Prelude.∘ fsuc)

postulate
  ⨂≡ : ∀ {n} → {A B : Fin n → Channel} → (∀ {k} → A k ≡ B k) → ⨂ A ≡ ⨂ B

rcv⨂ : {n : ℕ} {F : Fin n → Channel} → (k : Fin n) → ∃ (Channel.rcvType (F k)) → ∃ (Channel.rcvType (⨂ F))
rcv⨂ fzero = rcvˡ
rcv⨂ (fsuc k) x = rcvʳ (rcv⨂ k x)

snd⨂ : {n : ℕ} {F : Fin n → Channel} → (k : Fin n) → ∃ (Channel.sndType (F k)) → ∃ (Channel.sndType (⨂ F))
snd⨂ fzero = sndˡ
snd⨂ (fsuc k) x = sndʳ (snd⨂ k x)

--------------------------------------------------------------------------------
-- Machines, which form the morphisms

MachineType : Channel → Channel → Type → Type₁
MachineType A B State = let open Channel (A ⊗ B ᵀ) in ∃ rcvType → State → State × Maybe (∃ sndType) → Set

record Machine (A B : Channel) : Set₁ where
  constructor MkMachine
  open Channel (A ⊗ B ᵀ) public

  field State : Set
        stepRel : ∃ rcvType → State → State × Maybe (∃ sndType) → Set

module _ {A B} (let open Channel (A ⊗ B ᵀ)) where
  MkMachine' : ∀ {State} → (∃ rcvType → State → State × Maybe (∃ sndType) → Set) → Machine A B
  MkMachine' = MkMachine _

  StatelessMachine : (∃ rcvType → Maybe (∃ sndType) → Set) → Machine A B
  StatelessMachine R = MkMachine ⊤ (λ i _ (_ , o) → R i o)

  FunctionMachine : (∃ rcvType → Maybe (∃ sndType)) → Machine A B
  FunctionMachine f = StatelessMachine (λ i o → f i ≡ o)

  TotalFunctionMachine : (∃ rcvType → ∃ sndType) → Machine A B
  TotalFunctionMachine f = FunctionMachine (just Leios.Prelude.∘ f)

id : ∀ {A} → Machine A A
id = TotalFunctionMachine λ where
  (inj₁ p , m) → (inj₂ p , m)
  (inj₂ p , m) → (inj₁ p , m)

module Tensor {A B C D} (M₁ : Machine A B) (M₂ : Machine C D) where
  open Machine M₁ renaming (State to State₁; stepRel to stepRel₁)
  open Machine M₂ renaming (State to State₂; stepRel to stepRel₂)

  State = State₁ × State₂

  AllCs = (A ⊗ B ᵀ) ⊗ (C ⊗ D ᵀ)

  data CompRel : ∃ (Channel.rcvType AllCs) → State → State × Maybe (∃ (Channel.sndType AllCs)) → Set where
    Step₁ : ∀ {p m m' s s' s₂} → stepRel₁ (p , m) s (s' , m')
          → CompRel (inj₁ p , m) (s , s₂) ((s' , s₂) , (sndˡ <$> m'))

    Step₂ : ∀ {p m m' s s' s₁} → stepRel₂ (p , m) s (s' , m')
          → CompRel (inj₂ p , m) (s₁ , s) ((s₁ , s') , (sndʳ <$> m'))


  _⊗'_ : Machine (A ⊗ C) (B ⊗ D)
  _⊗'_ = λ where
    .Machine.State → State
    .Machine.stepRel m s (s' , m') → CompRel
      (case m of λ where
        (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
        (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
        (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
        (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m))
      s
      (s' , ((λ where
        (inj₁ (inj₁ p) , m) → (inj₁ (inj₁ p) , m)
        (inj₁ (inj₂ p) , m) → (inj₂ (inj₁ p) , m)
        (inj₂ (inj₁ p) , m) → (inj₁ (inj₂ p) , m)
        (inj₂ (inj₂ p) , m) → (inj₂ (inj₂ p) , m)) <$> m'))

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

  data CompRel : ∃ (Channel.rcvType AllCs) → State → State × Maybe (∃ (Channel.sndType AllCs)) → Set where
    Step₁ : ∀ {p m m' s s' s₂} → stepRel₁ (p , m) s (s' , m')
          → CompRel (inj₂ p , m) (s , s₂) ((s' , s₂) , (sndʳ <$> m'))

    Step₂ : ∀ {p m m' s s' s₁} → stepRel₂ (p , m) s (s' , m')
          → CompRel (inj₁ p , m) (s₁ , s) ((s₁ , s') , (sndˡ <$> m'))

    Multi₁ : ∀ {p m m' m'' s s' s''}
           → CompRel m s (s' , just ((inj₂ (inj₁ p) , m')))
           → CompRel (inj₁ (inj₂ p) , m') s' (s'' , m'')
           → CompRel m s (s'' , m'')

    Multi₂ : ∀ {p m m' m'' s s' s''}
           → CompRel m s (s' , just (inj₁ (inj₂ p) , m'))
           → CompRel (inj₂ (inj₁ p) , m') s' (s'' , m'')
           → CompRel m s (s'' , m'')

  infixr 9 _∘_

  _∘_ : Machine A C
  _∘_ = λ where
    .Machine.State → State
    .Machine.stepRel m s (s' , m') →
      CompRel
        (case m of λ where (inj₁ x , m) → inj₁ (inj₁ x) , m ; (inj₂ y , m) → inj₂ (inj₂ y) , m)
        s (s' ,  ((λ where (inj₁ x , m) → inj₁ (inj₁ x) , m ; (inj₂ y , m) → inj₂ (inj₂ y) , m) <$> m'))

open Comp using (_∘_) public

module Machine-Reasoning where
  open import Relation.Binary.Reasoning.Syntax

  open begin-syntax Machine Leios.Prelude.id public
  open ⟶-syntax {R = Machine} Machine Machine (λ M₁ M₂ → M₂ ∘ M₁) public
  open end-syntax Machine id public

postulate
  ⊗-assoc : ∀ {A B C} → Machine ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  ⊗-assoc⃖ : ∀ {A B C} → Machine (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)

⊗-sym : ∀ {A B} → Machine (A ⊗ B) (B ⊗ A)
⊗-sym = TotalFunctionMachine λ where
  (inj₁ (inj₁ p) , m) → inj₂ (inj₂ p) , m
  (inj₁ (inj₂ p) , m) → inj₂ (inj₁ p) , m
  (inj₂ (inj₁ p) , m) → inj₁ (inj₂ p) , m
  (inj₂ (inj₂ p) , m) → inj₁ (inj₁ p) , m

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
⨂ᴷ {suc n} M = M fzero ⊗ᴷ ⨂ᴷ (M Leios.Prelude.∘ fsuc)

--------------------------------------------------------------------------------
-- Environment model

ℰ-Out : Channel
ℰ-Out .Channel.P = ⊤
ℰ-Out .Channel.sndType _ = Bool
ℰ-Out .Channel.rcvType _ = ⊥

-- Presheaf on the category of channels & machines
-- we just take machines that output a boolean
-- for now, not on the Kleisli construction
ℰ : Channel → Set₁
ℰ C = Machine C ℰ-Out

map-ℰ : ∀ {A B} → Machine A B → ℰ B → ℰ A
map-ℰ M E = E ∘ M

--------------------------------------------------------------------------------
-- UC relations

-- perfect equivalence
_≈ℰ_ : ∀ {A B} → Machine A B → Machine A B → Set₁
_≈ℰ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≡ map-ℰ M' E

_≤UC_ : ∀ {A B E E''} → Machine A (B ⊗ E) → Machine A (B ⊗ E'') → Set₁
_≤UC_ {B = B} {E} R I = ∀ E' (A : Machine E E') → ∃[ S ] ((B ⊗ˡ A) ∘ R) ≈ℰ ((B ⊗ˡ S) ∘ I)

-- equivalent to _≤UC_ by "completeness of the dummy adversary"
_≤'UC_ : ∀ {A B E} → Machine A (B ⊗ E) → Machine A (B ⊗ E) → Set₁
_≤'UC_ {B = B} R I = ∃[ S ] R ≈ℰ (B ⊗ˡ S ∘ I)


--------------------------------------------------------------------------------
-- Example functionalities

module LeakyChannel (M : Set) where
  -- authenticated, non-lossy, leaks all messages

  open Channel

  A B E : Channel

  -- can receive messages from Alice
  A = simpleChannel ⊥ M

  -- can send messages to Bob
  B = simpleChannel M ⊥

  -- upon request, can send next message to Eve
  E = simpleChannel M ⊤

  open Machine hiding (rcvType; sndType)

  data Receive_withState_return_ : MachineType I ((A ⊗ B) ⊗ E) (List M) where

    Send : ∀ {m s} → Receive (honestInputI (sndˡ (-, m)))
                     withState s
                     return (s ∷ʳ m , just (honestOutputO (rcvʳ (-, m))))

    Req  : ∀ {m s} → Receive (adversarialInput _)
                     withState (m ∷ s)
                     return (s , just (adversarialOutput (-, m)))

  Functionality : Machine I ((A ⊗ B) ⊗ E)
  Functionality .State = List M -- queue of messages
  Functionality .stepRel = Receive_withState_return_



module SecureChannel (M : Set) where
  -- authenticated, non-lossy, leaks only message length

  open Channel

  A B E : Channel

  -- can receive messages from Alice
  A = simpleChannel ⊥ M

  -- can send messages to Bob
  B = simpleChannel M ⊥

  -- upon request, can send next message to Eve
  E = simpleChannel ℕ ⊤

  module _ (msgLen : M → ℕ) where

    open Machine hiding (rcvType; sndType)

    data Receive_withState_return_ : MachineType I ((A ⊗ B) ⊗ E) (List M) where

      Send : ∀ {m s} → Receive (honestInputI (sndˡ (-, m)))
                       withState s
                       return (s ∷ʳ m , just (honestOutputO (rcvʳ (-, m))))

      Req  : ∀ {m s} → Receive (adversarialInput _)
                       withState (m ∷ s)
                       return (s , just (adversarialOutput (-, msgLen m)))

    Functionality : Machine I ((A ⊗ B) ⊗ E)
    Functionality .State = List M -- queue of messages
    Functionality .stepRel = Receive_withState_return_



module Encryption (PlainText CipherText PubKey PrivKey : Set)
                  ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                  (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey) where
  open Channel
  open Machine hiding (rcvType; sndType)

  C : Channel
  C = simpleChannel (CipherText ⊎ Maybe PlainText) (PlainText × PubKey ⊎ CipherText × PrivKey)

  S : Set
  S = List (PubKey × PlainText × CipherText)

  lookup : {A : Set} → List A → (A → Bool) → Maybe A
  lookup [] f = nothing
  lookup (x ∷ l) f with f x
  ... | true  = just x
  ... | false = lookup l f

  lookupPlainText : S → CipherText × PubKey → Maybe PlainText
  lookupPlainText s (c , k) = proj₁ <$> (proj₂ <$> lookup s λ where (k' , _ , c') → ¿ k ≡ k' × c ≡ c' ¿ᵇ)

  data Receive_withState_return_ : MachineType I C S where

    Enc : ∀ {p k s} → let c = genCT (length s)
       in Receive (rcvʳ (-, inj₁ (p , k)))
          withState s
          return ((k , p , c) ∷ s , just (sndʳ (-, inj₁ c)))

    Dec : ∀ {c k s} → let p = lookupPlainText s (c , getPubKey k)
       in Receive (rcvʳ (-, inj₂ (c , k)))
          withState s
          return (s , just (sndʳ (-, inj₂ p)))

  Functionality : Machine I C
  Functionality .State   = S
  Functionality .stepRel = Receive_withState_return_

-- Note: it's a bad idea to do this as a wrapper, just make a shim to
-- compose with Encryption & the channel instead
module EncryptionShim (PlainText CipherText PubKey PrivKey : Set)
                      ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                      (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                      (pubKey : PubKey) (privKey : PrivKey) where
  open Channel
  open Machine hiding (rcvType; sndType)

  module L = LeakyChannel CipherText
  module S = SecureChannel PlainText
  module E = Encryption PlainText CipherText PubKey PrivKey genCT getPubKey

  data Receive_withState_return_ : MachineType ((L.A ⊗ L.B) ⊗ L.E) ((S.A ⊗ S.B) ⊗ S.E) (E.Functionality .State) where

    EncSend : ∀ {m m' s s'}
            → E.Receive (rcvʳ (-, inj₁ (m , pubKey)))
                withState s
                return (s' , just (sndʳ (-, inj₁ m')))
            → Receive (rcvʳ (sndˡ (sndˡ (-, m))))
              withState s
              return (s' , just (sndˡ (sndˡ (sndˡ (-, m')))))

    DecRcv  : ∀ {m m' s s'}
            → E.Receive (rcvʳ (-, inj₂ (m , privKey)))
                withState s
                return (s' , just (sndʳ (-, inj₂ (just m'))))
            → Receive (rcvˡ (rcvˡ (rcvʳ (-, m))))
              withState s
              return (s' , just (sndʳ (rcvˡ (rcvʳ (-, m')))))

  Functionality : Machine ((L.A ⊗ L.B) ⊗ L.E) ((S.A ⊗ S.B) ⊗ S.E)
  Functionality .State   = E.Functionality .State
  Functionality .stepRel = Receive_withState_return_

module SecureFromAuthenticated (PlainText CipherText PubKey PrivKey : Set)
                               ⦃ _ : DecEq CipherText ⦄ ⦃ _ : DecEq PubKey ⦄
                               (genCT : ℕ → CipherText) (getPubKey : PrivKey → PubKey)
                               (pubKey : PubKey) (privKey : PrivKey)
                               (msgLength : PlainText → ℕ) where

  module L  = LeakyChannel CipherText
  module S  = SecureChannel PlainText
  module SH = EncryptionShim PlainText CipherText PubKey PrivKey genCT getPubKey pubKey privKey

  Functionality : Machine I ((S.A ⊗ S.B) ⊗ S.E)
  Functionality = SH.Functionality ∘ L.Functionality

  -- F≤Secure : Functionality ≤'UC S.Functionality msgLength
  -- F≤Secure = {!!}
