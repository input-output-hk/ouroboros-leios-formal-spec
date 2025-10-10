{-# OPTIONS --safe #-}
module CategoricalCrypto.SRel where

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Cocartesian
open import Categories.Category.Discrete
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
open import Categories.Category.Instance.Rels
open import Categories.Category.Monoidal.Instance.Rels
open import Categories.Functor
open import Categories.Functor.Properties

open import CategoricalCrypto.NaturalTransformationHelper

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; [_]; ⊤; ⊥; Functor)
import abstract-set-theory.Prelude as P
import Function.Related.Propositional as R
open import Data.Product.Properties.Ext
open import Data.Product.Function.NonDependent.Propositional
open import Data.Product.Function.Dependent.Propositional renaming (cong to ∃-cong)
open import Function.Related.TypeIsomorphisms
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Empty.Polymorphic using (⊥)


SRelType : Type → Type → Type → Type₁
SRelType A B S = S → A → B → S → Type

record SRel (A B : Type) : Type₁ where
  field
    State : Type
    rel   : SRelType A B State

private variable A B C D : Type

trace : (R : SRel A B) → SRel.State R → List A → List B → Type
trace R s [] [] = ⊤
trace R s [] (_ ∷ _) = ⊥
trace R s (_ ∷ _) [] = ⊥
trace R s (x ∷ xs) (y ∷ ys) = ∃[ s' ] SRel.rel R s x y s' × trace R s xs ys

_≤ᵗ_ : SRel A B → SRel A B → Type
R₁ ≤ᵗ R₂ = ∀ s₁ → ∃[ s₂ ] ∀ a b → trace R₁ s₁ a b ⇔ trace R₂ s₂ a b

_≡ᵗ_ : SRel A B → SRel A B → Type
R₁ ≡ᵗ R₂ = R₁ ≤ᵗ R₂ × R₂ ≤ᵗ R₁

module _ ((record { State = S₁ ; rel = rel₁ }) : SRel A B)
         ((record { State = S₂ ; rel = rel₂ }) : SRel A B) where

  record _≡ᵉ_ : Type where
    field S₁↔S₂ : S₁ ↔ S₂

    open Inverse S₁↔S₂
    rel₂' : SRelType A B S₁
    rel₂' s a b s' = rel₂ (to s) a b (to s')

    field rel₁⇔rel₂' : ∀ {s a b s'} → rel₁ s a b s' ⇔ rel₂' s a b s'

    -- all the other type-correct variants are equivalent as well
    rel₁f⇔rel₂t : ∀ {s a b s'} → rel₁ (from s) a b s' ⇔ rel₂ s a b (to s')
    rel₁f⇔rel₂t {s} {a} {b} {s'} =
      rel₁ (from s) a b s'           ∼⟨ rel₁⇔rel₂' ⟩
      rel₂ (to (from s)) a b (to s') ≡⟨ cong (λ s → rel₂ s _ _ _) (strictlyInverseˡ s) ⟩
      rel₂ s a b (to s') ∎
      where open R.EquationalReasoning

-- ≡ᵉ is much easier to prove, but less general
≡ᵉ⇒≡ᵗ : ∀ {R₁ R₂ : SRel A B} → R₁ ≡ᵉ R₂ → R₁ ≡ᵗ R₂
≡ᵉ⇒≡ᵗ {R₁ = R₁} {R₂} R₁≡ᵉR₂ = < to , trace⇔₁ > , < from , trace⇔₂ >
  where
    open _≡ᵉ_ R₁≡ᵉR₂; open Inverse S₁↔S₂
    trace⇔₁ : ∀ s as bs → trace R₁ s as bs ⇔ trace R₂ (to s) as bs
    trace⇔₁ s [] [] = R.K-refl
    trace⇔₁ s [] (_ ∷ _) = R.K-refl
    trace⇔₁ s (_ ∷ _) [] = R.K-refl
    trace⇔₁ s (a ∷ as) (b ∷ bs) = ∃-cong S₁↔S₂ (rel₁⇔rel₂' ×-cong trace⇔₁ s as bs)

    trace⇔₂ : ∀ s as bs → trace R₂ s as bs ⇔ trace R₁ (from s) as bs
    trace⇔₂ s [] [] = R.K-refl
    trace⇔₂ s [] (_ ∷ _) = R.K-refl
    trace⇔₂ s (_ ∷ _) [] = R.K-refl
    trace⇔₂ s (a ∷ as) (b ∷ bs) = R.SK-sym $ ∃-cong S₁↔S₂ (rel₁f⇔rel₂t ×-cong R.SK-sym (trace⇔₂ s as bs))

module _ ((record { State = S₁ ; rel = rel₁ }) : SRel B C)
         ((record { State = S₂ ; rel = rel₂ }) : SRel A B) where

  record ∘-rel (s : S₁ × S₂) (a : A) (c : C) (s' : S₁ × S₂) : Type where
    field b : B
          ∘-rel₁ : rel₁ (proj₁ s) b c (proj₁ s')
          ∘-rel₂ : rel₂ (proj₂ s) a b (proj₂ s')

  _∘_ : SRel A C
  _∘_ = record { State = _ ; rel = ∘-rel }

SRelC : Category (sucˡ ℓ0) (sucˡ ℓ0) ℓ0
SRelC = categoryHelper record
  { Obj       = Type
  ; _⇒_       = SRel
  ; _≈_       = _≡ᵗ_
  ; id        = record { State = ⊤ ; rel = λ _ a₁ a₂ _ → a₁ ≡ a₂ }
  ; _∘_       = _∘_
  ; assoc     = ≡ᵉ⇒≡ᵗ {!!}
  ; identityˡ = ≡ᵉ⇒≡ᵗ record
    { S₁↔S₂ = ×-identityˡ ℓ0 _
    ; rel₁⇔rel₂' = mk⇔
      (λ where record { b = _ ; ∘-rel₁ = refl ; ∘-rel₂ = ∘-rel₂ } → ∘-rel₂)
      (λ rel → record { b = _ ; ∘-rel₁ = refl ; ∘-rel₂ = rel })
    }
  ; identityʳ = ≡ᵉ⇒≡ᵗ record
    { S₁↔S₂ = ×-identityʳ ℓ0 _
    ; rel₁⇔rel₂' = mk⇔
      (λ where record { b = _ ; ∘-rel₁ = ∘-rel₁ ; ∘-rel₂ = refl } → ∘-rel₁)
      (λ rel → record { b = _ ; ∘-rel₁ = rel ; ∘-rel₂ = refl })
    }
  ; equiv     = {!!}
  ; ∘-resp-≈  = {!!}
  }
  where open R.EquationalReasoning

StatelessRel : Functor (Rels 0ℓ 0ℓ) SRelC
StatelessRel = record
  { F₀ = P.id
  ; F₁ = λ R → record { State = ⊤ ; rel = λ _ a b _ → R a b }
  ; identity = ≡ᵉ⇒≡ᵗ record
    { S₁↔S₂ = R.K-refl
    ; rel₁⇔rel₂' = mk⇔ (λ where (lift refl) → refl) λ where refl → lift refl
    }
  ; homomorphism = ≡ᵉ⇒≡ᵗ record
    { S₁↔S₂ = R.SK-sym $ ×-identityʳ ℓ0 _
    ; rel₁⇔rel₂' = mk⇔
      (λ where (_ , Rab , Rbc) → record { b = _ ; ∘-rel₁ = Rbc ; ∘-rel₂ = Rab })
      (λ where record { b = b ; ∘-rel₁ = ∘-rel₁ ; ∘-rel₂ = ∘-rel₂ } → b , ∘-rel₂ , ∘-rel₁ )
    }
  ; F-resp-≈ = λ where
    (R₁⇒R₂ , R₂⇒R₁) → ≡ᵉ⇒≡ᵗ record { S₁↔S₂ = R.K-refl ; rel₁⇔rel₂' = mk⇔ R₁⇒R₂ R₂⇒R₁ }
  }

module RelsMonoidal where
  open Category (Rels 0ℓ 0ℓ) public
  open Monoidal (CocartesianMonoidal.+-monoidal (Rels 0ℓ 0ℓ) Rels-Cocartesian) public
  open import Categories.Category.Monoidal.Utilities (CocartesianMonoidal.+-monoidal (Rels 0ℓ 0ℓ) Rels-Cocartesian) public
  open Shorthands public

⊗₀ : Type × Type → Type
⊗₀ = uncurry _⊎_

module _ ((record { State = State₁ ; rel = rel₁ }
         , record { State = State₂ ; rel = rel₂ }) : SRel A B × SRel C D) where

  data ⊗-rel : SRelType (A ⊎ C) (B ⊎ D) (State₁ × State₂) where
    ⊗₁₁ : ∀ {s₁ s₁' s₂ a c} → rel₁ s₁ a c s₁' → ⊗-rel (s₁ , s₂) (inj₁ a) (inj₁ c) (s₁' , s₂)
    ⊗₁₂ : ∀ {s₁ s₂ s₂' b d} → rel₂ s₂ b d s₂' → ⊗-rel (s₁ , s₂) (inj₂ b) (inj₂ d) (s₁ , s₂')

  ⊗₁ : SRel (A ⊎ C) (B ⊎ D)
  ⊗₁ = record { State = _ ; rel = ⊗-rel}

Monoidal-SRelC : Monoidal SRelC
Monoidal-SRelC = monoidalHelper SRelC record
  { ⊗               = record
    { F₀ = ⊗₀
    ; F₁ = ⊗₁
    ; identity = ≡ᵉ⇒≡ᵗ record
      { S₁↔S₂ = ×-identityʳ ℓ0 _
      ; rel₁⇔rel₂' = λ {_} {a} → mk⇔
        (λ where (⊗₁₁ refl) → refl ; (⊗₁₂ refl) → refl)
        (λ where refl → case a returning (λ a → ⊗-rel _ _ a a _) of λ where
           (inj₁ x) → ⊗₁₁ refl
           (inj₂ y) → ⊗₁₂ refl)
      }
    ; homomorphism = {!!}
    ; F-resp-≈ = {!!}
    }
  ; unit            = ⊥
  ; unitorˡ         = [ StatelessRel ]-resp-≅ RelsMonoidal.unitorˡ
  ; unitorʳ         = [ StatelessRel ]-resp-≅ RelsMonoidal.unitorʳ
  ; associator      = [ StatelessRel ]-resp-≅ RelsMonoidal.associator
  ; unitorˡ-commute = λ {_} {_} {f} → begin
    -- cannot lift this via `StatelessRel`, since `f` isn't stateless
    -- this is the only reason, for stateless `f`s this can be lifted
    Functor.F₁ StatelessRel RelsMonoidal.λ⇒ SRelC.∘ (⊗₁ (SRelC.id , f))
      ≈⟨ {!!} ⟩
    f SRelC.∘ Functor.F₁ StatelessRel RelsMonoidal.λ⇒ ∎
  ; unitorʳ-commute = {!!}
  ; assoc-commute   = {!!}
  ; triangle        = begin
    ⊗₁ (SRelC.id , Functor.F₁ StatelessRel RelsMonoidal.λ⇒) SRelC.∘ Functor.F₁ StatelessRel RelsMonoidal.α⇒
      ≈⟨ {!!} ⟩ -- by functor laws
    Functor.F₁ StatelessRel (RelsMonoidal.id RelsMonoidal.⊗₁ RelsMonoidal.λ⇒ RelsMonoidal.∘ RelsMonoidal.α⇒)
      ≈⟨ Functor.F-resp-≈ StatelessRel RelsMonoidal.triangle ⟩
    Functor.F₁ StatelessRel (RelsMonoidal.ρ⇒ RelsMonoidal.⊗₁ RelsMonoidal.id)
      ≈⟨ {!!} ⟩ -- by functor laws
    ⊗₁ (Functor.F₁ StatelessRel RelsMonoidal.ρ⇒ , SRelC.id) ∎
  ; pentagon        = {!!} -- same proof as triangle
  }
  where open Category.HomReasoning SRelC
        module SRelC where
          open Category SRelC public

module _ (R : SRel (A ⊎ C) (B ⊎ C)) where
  open SRel R

  data tr-rel : SRelType (A ⊎ C) (B ⊎ C) State where
    tr-[_] : ∀ {s₁ s₂ a b} → rel s₁ a b s₂ → tr-rel s₁ a b s₂
    _tr-∷_ : ∀ {s₁ s₂ s₃ a b c} → rel s₁ a (inj₂ c) s₂ → tr-rel s₂ (inj₂ c) b s₃ → tr-rel s₁ a b s₃

  tr : SRel A B
  tr = record { State = _ ; rel = λ s a b s' → tr-rel s (inj₁ a) (inj₁ b) s' }

TracedMonoidal-SRelC : Traced Monoidal-SRelC
TracedMonoidal-SRelC = record
  { symmetric = {!!}
  ; trace = tr
  ; vanishing₁ = {!!}
  ; vanishing₂ = {!!}
  ; superposing = {!!}
  ; yanking = {!!}
  }
