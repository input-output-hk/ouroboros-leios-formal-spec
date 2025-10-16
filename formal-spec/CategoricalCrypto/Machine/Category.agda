{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Machine.Category where

open import CategoricalCrypto.Machine.Core renaming (id to machine-id ; _∘_ to _∘ₘ_)
open import CategoricalCrypto.Channel.Core
open import Categories.Category.Core
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Functor.Bifunctor
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open import abstract-set-theory.Prelude hiding (_⊗_ ; Functor ; Bifunctor)
import abstract-set-theory.Prelude as P

import Function.Bundles

_≤ᵐ_ : ∀ {A B} → Rel (Machine A B) zeroˡ
MkMachine {State} stepRel ≤ᵐ MkMachine {State₁} stepRel₁ =
  ∃ \(f : Func (setoid State) (setoid State₁)) → let open Func f in
    ∀ {s i o s'} → stepRel s i o s' → stepRel₁ (to s) i o (to s')

_≈ᵐ_ : ∀ {A B} → Rel (Machine A B) zeroˡ
MkMachine {State} stepRel ≈ᵐ MkMachine {State₁} stepRel₁ =
  ∃ \(fg : Inverse (setoid State) (setoid State₁)) → let open Inverse fg in
    (∀ {i o s s'} → stepRel s i o s' → stepRel₁ (to s) i o (to s'))
    × (∀ {i o s s'} → stepRel₁ s i o s' → stepRel (from s) i o (from s'))

import Relation.Binary.Structures

≈ᵐ-equivalence : ∀ {A B} → let open Relation.Binary.Structures (_≈ᵐ_ {A} {B}) in IsEquivalence
≈ᵐ-equivalence = record
  { refl = record { to = P.id ; from = P.id ; to-cong = P.id ; from-cong = P.id ; inverse = P.id , P.id } , P.id , P.id
  ; sym = λ where
            (record { to = to ; from = from ; to-cong = to-cong ; from-cong = from-cong ; inverse = (l , r) } , u , v) →
             record
               { to = from
               ; from = to
               ; to-cong = from-cong
               ; from-cong = to-cong
               ; inverse = (r , l) }
             , v
             , u
  ; trans = λ where
              (record { to = to ; from = from ; to-cong = to-cong ; from-cong = from-cong ; inverse = (l , r) } , u , v)
                (record { to = to₁ ; from = from₁ ; to-cong = to-cong₁ ; from-cong = from-cong₁ ; inverse = (l₁ , r₁) } , u₁ , v₁) →
                record
                  { to = to₁ P.∘ to
                  ; from = from P.∘ from₁
                  ; to-cong = to-cong₁ P.∘ to-cong
                  ; from-cong = from-cong P.∘ from-cong₁
                  ; inverse = l₁ P.∘ l , r P.∘ r₁ }
                , u₁ P.∘ u
                , v P.∘ v₁
  }

-- ≈≤ᵐ-partial-order : ∀ {A B} → let open Relation.Binary.Structures (_≈ᵐ_ {A} {B}) in IsPartialOrder _≤ᵐ_
-- ≈≤ᵐ-partial-order = record
--   { isPreorder = record
--     { isEquivalence = ≈ᵐ-equivalence
--     ; reflexive = λ where
--                     (record { to = to ; from = from ; to-cong = to-cong ; from-cong = from-cong ; inverse = (l , r) } , u , v) →
--                       record
--                         { to = to
--                         ; cong = to-cong
--                         }
--                       , u
--     ; trans = λ where
--                 (record { to = to ; cong = cong } , u) (record { to = to₁ ; cong = cong₁ } , u₁) →
--                   record
--                     { to = to₁ P.∘ to
--                     ; cong = cong₁ P.∘ cong
--                   }
--                   , u₁ P.∘ u
--     }
--   ; antisym = λ x x₁ → {!!} }

machine-category : Category (sucˡ zeroˡ) (sucˡ zeroˡ) zeroˡ
machine-category = categoryHelper record
  { Obj = Channel
  ; _⇒_ = Machine
  ; _≈_ = _≈ᵐ_
  ; id = machine-id
  ; _∘_ = _∘ₘ_
  ; assoc = {!!}
  ; identityˡ = λ where
                 {_} {_} {MkMachine stepRel} → record
                                                 { to = proj₁
                                                 ; from = λ z → z , tt
                                                 ; to-cong = λ { refl → refl }
                                                 ; from-cong = λ { refl → refl }
                                                 ; inverse = (λ { refl → refl }) , λ { refl → refl }
                                                 }
                                               , (λ { {i} {o} {fst , tt} {fst₁ , tt} Trace[ x ] → {!x!}
                                               ; {i} {o} {fst , tt} {fst₁ , tt} (x Trace∷ₒ x₁) → {!x₁!}
                                               ; {i} {o} {fst , tt} {fst₁ , tt} (x Trace∷ᵢ x₁) → {!!}})
                                               , {!!}
  ; identityʳ = {!!}
  ; equiv = ≈ᵐ-equivalence
  ; ∘-resp-≈ = {!!}
  }
