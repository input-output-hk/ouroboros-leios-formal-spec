{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel.Core where

open import abstract-set-theory.Prelude hiding (_⊗_ ; [_])
open import Data.Sum.Base using (swap ; assocʳ ; assocˡ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

------------------------------------
-- Modes for messages (In or Out) --
------------------------------------

data Mode : Type where
  Out : Mode
  In : Mode

infixr 10 ¬ₘ_

¬ₘ_ : Fun₁ Mode
¬ₘ Out = In
¬ₘ In = Out

¬ₘ-idempotent : ∀ {m} → ¬ₘ ¬ₘ m ≡ m
¬ₘ-idempotent {Out} = refl
¬ₘ-idempotent {In} = refl

-------------------------------
-- Channels of communication --
-------------------------------

infix 10 _⇿_
record Channel : Type₁ where
  constructor _⇿_
  field
    inType outType : Type

open Channel

modeType : Mode → Channel → Type
modeType Out = outType
modeType In = inType

{-# INJECTIVE_FOR_INFERENCE modeType #-}

simpleChannel : (Mode → Type) → Channel
simpleChannel T = T In ⇿ T Out

----------------------------------------
-- Channel identity and transposition --
----------------------------------------

I : Channel
I = ⊥ ⇿ ⊥

_ᵀ : Fun₁ Channel
(receive ⇿ send) ᵀ = send ⇿ receive

ᵀ-identity : I ᵀ ≡ I
ᵀ-identity = refl

ᵀ-idempotent : ∀ {A} → A ᵀ ᵀ ≡ A
ᵀ-idempotent = refl

--------------------------------------------------------
-- Forwarding a message from a given Channel and Mode --
--------------------------------------------------------

infix 4 _[_]⇒[_]_

opaque
  _[_]⇒[_]_ : Channel → Mode → Mode → Channel → Type
  A [ m₁ ]⇒[ m₂ ] B = modeType m₁ A → modeType m₂ B

  app : ∀ {A B m₁ m₂} → A [ m₁ ]⇒[ m₂ ] B → modeType m₁ A → modeType m₂ B
  app f = f

  ⇒-trans : ∀ {A B C m m₁ m₂} → A [ m ]⇒[ m₁ ] B → B [ m₁ ]⇒[ m₂ ] C → A [ m ]⇒[ m₂ ] C
  ⇒-trans p q = q ∘ p

  _⇒ₜ_ : ∀ {A B C m m₁ m₂} → A [ m ]⇒[ m₁ ] B → B [ m₁ ]⇒[ m₂ ] C → A [ m ]⇒[ m₂ ] C
  _⇒ₜ_ = ⇒-trans

  infixr 10 _⇒ₜ_
  
  ⇒-refl' : ∀ {m A B} → A ≡ B → A [ m ]⇒[ m ] B
  ⇒-refl' refl = id

  ⇒-refl : ∀ {m A} → A [ m ]⇒[ m ] A
  ⇒-refl = ⇒-refl' refl

----------------------------------
-- Forwarding and transposition --
----------------------------------

  ⇒-double-transpose-left : ∀ {m A} → A ᵀ ᵀ [ m ]⇒[ m ] A
  ⇒-double-transpose-left {A = A} rewrite ᵀ-idempotent {A} = ⇒-refl

  ⇒-double-transpose-right : ∀ {m A} → A [ m ]⇒[ m ] A ᵀ ᵀ
  ⇒-double-transpose-right {A = A} rewrite ᵀ-idempotent {A} = ⇒-refl

  ⇒-double-negate-left : ∀ {m A} → A [ ¬ₘ ¬ₘ m ]⇒[ m ] A
  ⇒-double-negate-left {m} rewrite (¬ₘ-idempotent {m}) = ⇒-refl

  ⇒-double-negate-right : ∀ {m A} → A [ m ]⇒[ ¬ₘ ¬ₘ m ] A
  ⇒-double-negate-right {m} rewrite (¬ₘ-idempotent {m}) = ⇒-refl

  ⇒-negate-transpose-right : ∀ {m A} → A [ m ]⇒[ ¬ₘ m ] A ᵀ
  ⇒-negate-transpose-right {Out} = id
  ⇒-negate-transpose-right {In} = id

  ⇒-negate-transpose-left : ∀ {m A} → A ᵀ [ ¬ₘ m ]⇒[ m ] A
  ⇒-negate-transpose-left = ⇒-negate-transpose-right ⇒ₜ ⇒-double-negate-left

  ⇒-transpose-left-negate-right : ∀ {m A} → A ᵀ [ m ]⇒[ ¬ₘ m ] A
  ⇒-transpose-left-negate-right {A = A} rewrite ᵀ-idempotent {A} = ⇒-negate-transpose-right {A = A ᵀ}

  ⇒-negate-left-transpose-right : ∀ {m A} → A [ ¬ₘ m ]⇒[ m ] A ᵀ
  ⇒-negate-left-transpose-right {A = A} rewrite ᵀ-idempotent {A} = ⇒-negate-transpose-left {A = A ᵀ}

-----------------------------------
-- Tensorial product on Channels --
-----------------------------------

  infixr 9 _⊗_

  _⊗_ : Fun₂ Channel
  (receive₁ ⇿ send₁) ⊗ (receive₂ ⇿ send₂) = (receive₁ ⊎ receive₂) ⇿ (send₁ ⊎ send₂)

  -----------------------------------
  -- Forwarding tensorial products --
  -----------------------------------

  ⊗-sym : ∀ {m A B} → A ⊗ B [ m ]⇒[ m ] B ⊗ A
  ⊗-sym {Out} = swap
  ⊗-sym {In} = swap

  ⊗-right-assoc : ∀ {m A B C} → (A ⊗ B) ⊗ C [ m ]⇒[ m ] A ⊗ B ⊗ C
  ⊗-right-assoc {Out} = assocʳ
  ⊗-right-assoc {In} = assocʳ

  ⊗-left-assoc : ∀ {m A B C} → A ⊗ B ⊗ C [ m ]⇒[ m ] (A ⊗ B) ⊗ C
  ⊗-left-assoc {Out} = assocˡ
  ⊗-left-assoc {In} = assocˡ

  ⊗-right-intro : ∀ {m A B} → A [ m ]⇒[ m ] A ⊗ B
  ⊗-right-intro {Out} = inj₁
  ⊗-right-intro {In} = inj₁

  ⊗-ᵀ-distrib : ∀ {m A B} → (A ⊗ B) ᵀ [ m ]⇒[ m ] A ᵀ ⊗ B ᵀ
  ⊗-ᵀ-distrib {Out} = id
  ⊗-ᵀ-distrib {In} = id

  ⊗-ᵀ-factor : ∀ {m A B} → A ᵀ ⊗ B ᵀ [ m ]⇒[ m ] (A ⊗ B) ᵀ
  ⊗-ᵀ-factor {Out} = id
  ⊗-ᵀ-factor {In} = id

  ⊗-right-neutral : ∀ {m A} → A ⊗ I [ m ]⇒[ m ] A
  ⊗-right-neutral {Out} (inj₁ x) = x
  ⊗-right-neutral {In} (inj₁ x) = x

  ⊗-fusion : ∀ {m A} → A ⊗ A [ m ]⇒[ m ] A
  ⊗-fusion {Out} = [ id , id ]
  ⊗-fusion {In} = [ id , id ]

  ⊗-combine : ∀ {m m₁ A B C D} → A [ m ]⇒[ m₁ ] B → C [ m ]⇒[ m₁ ] D → A ⊗ C [ m ]⇒[ m₁ ] B ⊗ D
  ⊗-combine {Out} {Out} p q (inj₁ x) = inj₁ (p x)
  ⊗-combine {Out} {Out} p q (inj₂ y) = inj₂ (q y)
  ⊗-combine {Out} {In} p q (inj₁ x) = inj₁ (p x)
  ⊗-combine {Out} {In} p q (inj₂ y) = inj₂ (q y)
  ⊗-combine {In} {Out} p q (inj₁ x) = inj₁ (p x)
  ⊗-combine {In} {Out} p q (inj₂ y) = inj₂ (q y)
  ⊗-combine {In} {In} p q (inj₁ x) = inj₁ (p x)
  ⊗-combine {In} {In} p q (inj₂ y) = inj₂ (q y)

⊗-left-intro : ∀ {m A B} → B [ m ]⇒[ m ] A ⊗ B
⊗-left-intro = ⊗-right-intro ⇒ₜ ⊗-sym

⊗-left-neutral : ∀ {m A} → I ⊗ A [ m ]⇒[ m ] A
⊗-left-neutral = ⊗-sym ⇒ₜ ⊗-right-neutral

⊗-right-double-intro : ∀ {m A B C} → A [ m ]⇒[ m ] B → A ⊗ C [ m ]⇒[ m ] B ⊗ C
⊗-right-double-intro p = ⊗-combine p ⇒-refl

⊗-left-double-intro : ∀ {m A B C} → B [ m ]⇒[ m ] C → A ⊗ B [ m ]⇒[ m ] A ⊗ C
⊗-left-double-intro p = ⊗-sym ⇒ₜ ⊗-right-double-intro p ⇒ₜ ⊗-sym

⊗-merge : ∀ {m m₁ A B C} → A [ m ]⇒[ m₁ ] C → B [ m ]⇒[ m₁ ] C → A ⊗ B [ m ]⇒[ m₁ ] C
⊗-merge p q = ⊗-combine p q ⇒ₜ ⊗-fusion

--------------------------------
-- Additional Channel builder --
--------------------------------

⨂_ : ∀ {n} → (Fin n → Channel) → Channel
⨂_ {zero} _ = I
⨂_ {suc n} f = f fzero ⊗ ⨂ (f ∘ fsuc)

⨂≡ : ∀ {n} → {f g : Fin n → Channel} → (∀ k → f k ≡ g k) → ⨂ f ≡ ⨂ g
⨂≡ {zero} _ = refl
⨂≡ {suc _} p = cong₂ _⊗_ (p fzero) (⨂≡ (p ∘ fsuc))

⨂⇒ : ∀ {n m} {f : Fin n → Channel} k → f k [ m ]⇒[ m ] ⨂ f
⨂⇒ fzero = ⊗-right-intro
⨂⇒ (fsuc k) = ⨂⇒ k ⇒ₜ ⊗-left-intro
