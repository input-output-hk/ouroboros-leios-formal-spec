{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel where

open import abstract-set-theory.Prelude hiding (_⊗_ ; [_])
open import Data.Sum.Base using (swap ; assocʳ ; assocˡ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

------------------------------------
-- Modes for messages (In or Out) --
------------------------------------
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
data Mode : Type where
  Out : Mode
  In : Mode

¬ₘ_ : Fun₁ Mode
¬ₘ Out = In
¬ₘ In = Out

¬ₘ-idempotent : ∀ {m} → ¬ₘ (¬ₘ m) ≡ m
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

  inT = inType
  outT = outType
  
  {-# INJECTIVE_FOR_INFERENCE inT #-}
  {-# INJECTIVE_FOR_INFERENCE outT #-}

open Channel

I : Channel
I = ⊥ ⇿ ⊥

_ᵀ : Fun₁ Channel
(receive ⇿ send) ᵀ = send ⇿ receive

ᵀ-idempotent : ∀ {A} → A ᵀ ᵀ ≡ A
ᵀ-idempotent = refl

ᵀ-identity : I ᵀ ≡ I
ᵀ-identity = refl

modeType : Mode → Channel → Type
modeType Out = outType
modeType In = inType

simpleChannel : (Mode → Type) → Channel
simpleChannel T = T In ⇿ T Out

{-# INJECTIVE_FOR_INFERENCE modeType #-}

--------------------------------------------------------
-- Forwarding a message from a given Channel and Mode --
--------------------------------------------------------

infix 4 _[_]⇒[_]_

_[_]⇒[_]_ : Channel → Mode → Mode → Channel → Type
c₁ [ m₁ ]⇒[ m₂ ] c₂ = modeType m₁ c₁ → modeType m₂ c₂

⇒-trans : ∀ {c₁ c₂ c₃ m₁ m₂ m₃} → c₁ [ m₁ ]⇒[ m₂ ] c₂ → c₂ [ m₂ ]⇒[ m₃ ] c₃ → c₁ [ m₁ ]⇒[ m₃ ] c₃
⇒-trans p q = q ∘ p

infixr 10 _⇒ₜ_

_⇒ₜ_ = ⇒-trans 

⇒-refl : ∀ {m A} → A [ m ]⇒[ m ] A
⇒-refl = id

----------------------------------
-- Forwarding and transposition --
----------------------------------

⇒-double-negate : ∀ {m A} → A [ ¬ₘ (¬ₘ m) ]⇒[ m ] A
⇒-double-negate {m} rewrite (¬ₘ-idempotent {m}) = ⇒-refl

⇒-transpose : ∀ {m A} → A [ m ]⇒[ ¬ₘ m ] A ᵀ
⇒-transpose {Out} = id
⇒-transpose {In} = id

⇒-reduce : ∀ {m A} → A ᵀ [ ¬ₘ m ]⇒[ m ] A
⇒-reduce = ⇒-transpose ⇒ₜ ⇒-double-negate

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

⊗-left-intro : ∀ {m A B} → B [ m ]⇒[ m ] A ⊗ B
⊗-left-intro = ⊗-right-intro ⇒ₜ ⊗-sym

⊗-ᵀ-distrib : ∀ {m A B} → (A ⊗ B) ᵀ [ m ]⇒[ m ] A ᵀ ⊗ B ᵀ
⊗-ᵀ-distrib {Out} = id
⊗-ᵀ-distrib {In} = id

⊗-ᵀ-factor : ∀ {m A B} → A ᵀ ⊗ B ᵀ [ m ]⇒[ m ] (A ⊗ B) ᵀ
⊗-ᵀ-factor {Out} = id
⊗-ᵀ-factor {In} = id

⊗-right-neutral : ∀ {m A} → A ⊗ I [ m ]⇒[ m ] A
⊗-right-neutral {Out} (inj₁ x) = x
⊗-right-neutral {In} (inj₁ x) = x

⊗-left-neutral : ∀ {m A} → I ⊗ A [ m ]⇒[ m ] A
⊗-left-neutral = ⊗-sym ⇒ₜ ⊗-right-neutral

⊗-fusion : ∀ {m A} → A ⊗ A [ m ]⇒[ m ] A
⊗-fusion {Out} = [ id , id ]
⊗-fusion {In} = [ id , id ]

⊗-copy : ∀ {m A} → A [ m ]⇒[ m ] A ⊗ A
⊗-copy {Out} = inj₁
⊗-copy {In} = inj₁

⊗-right-double-intro : ∀ {m A B C} → A [ m ]⇒[ m ] B → A ⊗ C [ m ]⇒[ m ] B ⊗ C
⊗-right-double-intro {Out} = map₁
⊗-right-double-intro {In} = map₁

⊗-left-double-intro : ∀ {m A B C} → B [ m ]⇒[ m ] C → A ⊗ B [ m ]⇒[ m ] A ⊗ C
⊗-left-double-intro p = ⊗-sym ⇒ₜ ⊗-right-double-intro p ⇒ₜ ⊗-sym

-------------------------
-- Adversarial pattern --
-------------------------

honestChannelA : ∀ {m A B Adv} → A [ m ]⇒[ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelA = ⊗-right-intro

honestChannelB : ∀ {m A B Adv} → B [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
honestChannelB = ⇒-transpose ⇒ₜ ⊗-right-intro ⇒ₜ ⊗-ᵀ-factor ⇒ₜ ⊗-left-intro

adversarialChannel : ∀ {m A B Adv} → Adv [ m ]⇒[ ¬ₘ m ] A ⊗ (B ⊗ Adv) ᵀ
adversarialChannel = ⇒-transpose ⇒ₜ ⊗-left-intro ⇒ₜ ⊗-ᵀ-factor ⇒ₜ ⊗-left-intro

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
