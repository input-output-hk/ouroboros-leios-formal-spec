{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel where

open import abstract-set-theory.Prelude hiding (_⊗_ ; [_])
open import Data.Sum.Base using (swap ; assocʳ ; assocˡ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

------------------------------------
-- Modes for messages (In or Out) --
------------------------------------

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

_[_]⇒[_]_ : Channel → Mode → Mode → Channel → Type
A [ m₁ ]⇒[ m₂ ] B = modeType m₁ A → modeType m₂ B

⇒-trans : ∀ {A B C m m₁ m₂} → A [ m ]⇒[ m₁ ] B → B [ m₁ ]⇒[ m₂ ] C → A [ m ]⇒[ m₂ ] C
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

opaque
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

  ⊗-duplicate : ∀ {m A} → A [ m ]⇒[ m ] A ⊗ A
  ⊗-duplicate {Out} = inj₁
  ⊗-duplicate {In} = inj₁

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

-----------------------------------------
-- Building a Category out of Channels --
-----------------------------------------

open import Categories.Category.Core
open import Categories.Category.Helper
open import Relation.Binary.PropositionalEquality

channelCategory : Category (sucˡ zeroˡ) zeroˡ zeroˡ
channelCategory = categoryHelper
  record {
    Obj = Channel;
    _⇒_ = λ A B → ∀ {m} → A [ m ]⇒[ m ] B ;
    _≈_ = λ x y → ∀ {m} v → x {m} v ≡ y v ;
    id = ⇒-refl ;
    _∘_ = λ x x₁ → x₁ ⇒ₜ x ;
    assoc = λ _ → refl ;
    identityˡ = λ _ → refl ;
    identityʳ = λ _ → refl ;
    equiv = record {
              refl = λ _ → refl ;
              sym = λ x → sym ∘ x ;
              trans = λ x y v → trans (x v) (y v)
            } ;
    ∘-resp-≈ = λ where {h = h} {g} x y v → trans (x (g v)) (cong h (y v))
  }

open import Categories.Category.Monoidal

opaque
  unfolding _⊗_

  channelMonoidal : Monoidal channelCategory
  channelMonoidal = monoidalHelper channelCategory $
    record {
      ⊗ = record {
             F₀ = uncurry _⊗_ ;
             F₁ = λ (p₁ , p₂) → ⊗-combine p₁ p₂ ;
             identity = λ where
                            {m = Out} (inj₁ _) → refl
                            {m = Out} (inj₂ _) → refl
                            {m = In} (inj₁ _) → refl
                            {m = In} (inj₂ _) → refl
                        ;
             homomorphism = λ where
                                {m = Out} (inj₁ _) → refl
                                {m = Out} (inj₂ _) → refl
                                {m = In} (inj₁ _) → refl
                                {m = In} (inj₂ _) → refl
                            ;
             F-resp-≈ = λ where
                            (fst , snd) {Out} (inj₁ x) → cong inj₁ (fst {Out} x)
                            (fst , snd) {Out} (inj₂ y) → cong inj₂ (snd {Out} y)
                            (fst , snd) {In} (inj₁ x) → cong inj₁ (fst {In} x)
                            (fst , snd) {In} (inj₂ y) → cong inj₂ (snd {In} y)
           };
      unit = I ;
      unitorˡ = record {
                 from = ⊗-left-neutral ;
                 to = ⊗-left-intro ;
                 iso = record {
                         isoˡ = λ where
                                   {Out} (inj₂ _) → refl
                                   {In} (inj₂ _) → refl
                               ;
                         isoʳ = λ where
                                   {Out} _ → refl
                                   {In} _ → refl
                       }
               };
      unitorʳ = record {
                 from = ⊗-right-neutral ;
                 to = ⊗-right-intro ;
                 iso = record {
                         isoˡ = λ where
                                   {Out} (inj₁ _) → refl
                                   {In} (inj₁ _) → refl
                               ;
                         isoʳ = λ where
                                   {Out} _ → refl
                                   {In} _ → refl
                       }
               };
      associator = record {
                     from = ⊗-right-assoc ;
                     to = ⊗-left-assoc ;
                     iso = record {
                             isoˡ = λ where
                                       {Out} (inj₁ (inj₁ _)) → refl
                                       {Out} (inj₁ (inj₂ _)) → refl
                                       {Out} (inj₂ _) → refl
                                       {In} (inj₁ (inj₁ _)) → refl
                                       {In} (inj₁ (inj₂ _)) → refl
                                       {In} (inj₂ _) → refl
                             ;
                             isoʳ = λ where
                                       {Out} (inj₁ _) → refl
                                       {Out} (inj₂ (inj₁ _)) → refl
                                       {Out} (inj₂ (inj₂ y)) → refl
                                       {In} (inj₁ _) → refl
                                       {In} (inj₂ (inj₁ _)) → refl
                                       {In} (inj₂ (inj₂ _)) → refl
                           }
                   };
      unitorˡ-commute = λ where
                           {m = Out} (inj₂ _) → refl
                           {m = In} (inj₂ _) → refl
                       ;
      unitorʳ-commute = λ where
                           {m = Out} (inj₁ _) → refl
                           {m = In} (inj₁ _) → refl
                       ;
      assoc-commute = λ where
                          {m = Out} (inj₁ (inj₁ _)) → refl
                          {m = Out} (inj₁ (inj₂ _)) → refl
                          {m = Out} (inj₂ _) → refl
                          {m = In} (inj₁ (inj₁ _)) → refl
                          {m = In} (inj₁ (inj₂ _)) → refl
                          {m = In} (inj₂ _) → refl
                      ;
      triangle = λ where
                     {m = Out} (inj₁ (inj₁ _)) → refl
                     {m = Out} (inj₂ _) → refl
                     {m = In} (inj₁ (inj₁ _)) → refl
                     {m = In} (inj₂ _) → refl
                 ;
      pentagon = λ where
                     {m = Out} (inj₁ (inj₁ (inj₁ _))) → refl
                     {m = Out} (inj₁ (inj₁ (inj₂ _))) → refl
                     {m = Out} (inj₁ (inj₂ _)) → refl
                     {m = Out} (inj₂ _) → refl
                     {m = In} (inj₁ (inj₁ (inj₁ _))) → refl
                     {m = In} (inj₁ (inj₁ (inj₂ _))) → refl
                     {m = In} (inj₁ (inj₂ _)) → refl
                     {m = In} (inj₂ _) → refl
    }

  channelMonoidalCategory : MonoidalCategory (sucˡ zeroˡ) zeroˡ zeroˡ
  channelMonoidalCategory =
    record {
      U = channelCategory;
      monoidal = channelMonoidal
    }
