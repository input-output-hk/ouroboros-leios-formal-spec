open import abstract-set-theory.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_)

open import Class.HasOrder
open import Algebra
open import Relation.Unary

import Data.List.NonEmpty as NE

open import Data.Rational using (ℚ; _/_)
open import Data.Integer using (+_)

module CategoricalCrypto.ProbabilisticLogic where

module ≤-Reasoning {a} (A : Type a) ⦃ po : HasPartialOrder {a} {A} {_≡_} ⦄ where
  open HasPartialOrder po
  open import Relation.Binary.Reasoning.Base.Triple {A = A} {_≈_ = _≡_} {_<_ = _<_}
    ≤-isPreorder
    (HasPartialOrder.<-asymmetric po)
    (HasPartialOrder.<-trans po)
    {!!} --(Strict.<-resp-≈ isEquivalence ≤-resp-≈)
    (proj₁ ∘ HasPreorder.<⇒≤∧≉ hasPreorder)
    {!!} --(Strict.<-≤-trans Eq.sym trans antisym ≤-respʳ-≈)
    {!!} --(Strict.≤-<-trans trans antisym ≤-respˡ-≈)
    public

private variable Ω : Type

disjoint : (P Q : Ω → Type) → Type
disjoint P Q = ∀ {ω} → P ω → Q ω → ⊥

↑_ : (Ω → Bool) → Ω → Type
↑_ X = λ ω → T (X ω)

record AbstractProbability : Type₁ where
  field Probabilityᴿ : CommutativeRing 0ℓ 0ℓ

  open CommutativeRing Probabilityᴿ renaming (Carrier to Probability) public

  field _⁻¹ : (p : Probability) → {p ≢ 0#} → Probability
        ⦃ HasPartialOrder-Probability ⦄ : HasPartialOrder≡ {A = Probability}
        ≤-cong : ∀ {p p' q q' : Probability} → p ≤ p' → q ≤ q' → p * q ≤ p' * q'

  fromℚ : ℚ → Probability
  fromℚ = {!!}

record Abstract : Type₁ where
  field abstractProbability : AbstractProbability

  open AbstractProbability abstractProbability public

  field -- we assume discrete probability distributions, which don't need a σ-algebra
        ProbDistr : Type → Type
        _∣_ : ProbDistr Ω → (X : Ω → Type) → ProbDistr (Σ Ω X)
        extend : ∀ {X} → ProbDistr (Σ Ω X) → ProbDistr Ω
        _∙_ : ProbDistr Ω → (Ω → Type) → Probability
        P∅≡0 : {P : ProbDistr Ω} → P ∙ ∅ ≡ 0#
        PU≡1 : {P : ProbDistr Ω} → P ∙ U ≡ 1#
        P-distrib-disjoint : ∀ {X Y} {P : ProbDistr Ω} → disjoint X Y → P ∙ X + P ∙ Y ≡ P ∙ (X ∪ Y)
        cond-probability : ∀ {P : ProbDistr Ω} {X Y} → P ∙ X * (extend (P ∣ X)) ∙ Y ≡ P ∙ (X ∩ Y)
        prob-monotonous : ∀ {P : ProbDistr Ω} {X Y} → X ⊆ Y → P ∙ X ≤ P ∙ Y
        extend-∣ : ∀ {P : ProbDistr Ω} {X Y} → extend (P ∣ X) ∙ Y ≡ (P ∣ X) ∙ (Y ∘ proj₁)
        uniformFromList : (l : NE.List⁺ Ω) → ProbDistr Ω
        uniform-eq : ∀ {l} {X : Ω → Bool}
                   → uniformFromList l ∙ (↑ X) ≡ fromℚ (+ length (filterᵇ X (NE.toList l)) / NE.length l)

  ∙-cong : {P : ProbDistr Ω} {X Y : Ω → Type} → X ≐ Y → P ∙ X ≡ P ∙ Y
  ∙-cong (X⊆Y , Y⊆X) = ≤-antisym (prob-monotonous X⊆Y) (prob-monotonous Y⊆X)

module Logic (a : Abstract) where
  open Abstract a

  record isSupremum {a} (T : Type a) (f : T → Probability) (p : Probability) : Type a where
    field isUpperBound : ∀ {t} → f t ≤ p
          isLeastUpperBound : ∀ {q} → q < p → ∃[ t ] ¬ f t ≤ q

  dTV_,_≡_ : (P Q : ProbDistr Ω) → (p : Probability) → Type₁
  dTV_,_≡_ {Ω} P Q p = isSupremum (Ω → Type) (λ X → {!∣ P ∙ X - Q ∙ X ∣!}) p

  record ConcreteProbability (P : ProbDistr Ω) : Type₁ where
    field X : Ω → Type
          p : Probability
          PX≡p : P ∙ X ≡ p

  _+ₚ_ : {P : ProbDistr Ω} → ConcreteProbability P → ConcreteProbability P → ConcreteProbability P
  p +ₚ q = let module p = ConcreteProbability p; module q = ConcreteProbability q in
    record { X = p.X ∪ q.X ; p = {!!} ; PX≡p = {!!} }

  record Σ[_][_]_ (P : ProbDistr Ω) (p : Probability) (X : Ω → Type) : Type₁ where
    field p≤PX : p ≤ P ∙ X

  open Σ[_][_]_

  _⇒[_][_]_ : (X : Ω → Type) (P : ProbDistr Ω) (p : Probability) (Y : Ω → Type) → Type₁
  X ⇒[ P ][ p ] Y = Σ[ P ∣ X ][ p ] (Y ∘ proj₁)

  app : {P : ProbDistr Ω} {p q : Probability} {X Y : Ω → Type}
      → X ⇒[ P ][ q ] Y → Σ[ P ][ p ] X → Σ[ P ][ p * q ] Y
  app {P = P} {p} {q} {X} {Y} record { p≤PX = p₁ } record { p≤PX = p₂ } .p≤PX = begin
    p * q                         ≤⟨ ≤-cong p₂ p₁ ⟩
    P ∙ X * (P ∣ X) ∙ (Y ∘ proj₁) ≡⟨ cong (P ∙ X *_) extend-∣ ⟨
    P ∙ X * (extend (P ∣ X)) ∙ Y  ≡⟨ cond-probability ⟩
    P ∙ (X ∩ Y)                   ≤⟨ prob-monotonous proj₂ ⟩
    P ∙ Y ∎
    where open ≤-Reasoning Probability

-- Ω = Bool × Bool, X (ω₁, ω₂) = ω₁ ≡ 1, Y (ω₁, ω₂) = (ω₁, ω₂) ≡ (1, 1)
-- X ⇒[ P ][ 1/2 ] Y

-- P(X ∪ Y) = P(X) + (P(Y) - P(X ∩ Y))



--------------------------------------------------------------------------------
-- Idea

-- Measure Ω = (Ω → Type) → ℚ → Type
-- μ ∙ X ≡ m = μ X m

-- record Meas : Type₁ where
--   field Ω : Type
--         μ : Measure Ω
--         X : Ω → Type

-- _≈ₚ_ : Meas → Meas → Type
-- (Ω₁ , P₁ , X₁) ≈ₚ (Ω₂ , P₂ , X₂) = ∃[ p ] P₁ ∙ X₁ ≡ p × P₂ ∙ X₂ ≡ p

-- fromℚ : ℚ → Meas
-- fromℚ (m / n) = (Fin n , uniform , _≤ m)

-- _∙_ : Measure Ω → (Ω → Type) → Meas
-- P ∙ X = (_ , P , X)

-- pushforward : (Ω₁ → Ω₂) → Meas Ω₁ → Meas Ω₂
-- pushforward f μ X m = μ ∙ (λ ω₂ → ∃[ ω₁ ] f ω₁ ≡ ω₂ × X ω₁) ≡ m

-- _+ₘ_ _*ₘ_ : Meas Ω → Meas Ω → Meas Ω

-- _+ₘ'_ : Meas Ω₁ → Meas Ω₂ → Meas (Ω₁ ⊎ Ω₂)
-- μ₁ +ₘ' μ₂ = pushforward inj₁ μ₁ +ₘ pushforward inj₂ μ₂

-- _+_ : Meas → Meas → Meas
-- (Ω₁ , μ₁ , X₁) + (Ω₂ , μ₂ , X₂) = (Ω₁ ⊎ Ω₂ , μ₁ +ₘ' μ₂ , [ X₁ , X₂ ])






--------------------------------------------------------------------------------
-- Issue: Adding probabilities

-- Problem: Here are the typical options
-- _+_ : [0,1] → [0,1] → Maybe [0,1]
-- _+_ : (p q : [0,1]) → (p +' q ≤ 1) → [0,1]
-- _+_ : [0,1] → [0,1] → [0,1] (cutoff at 1)

-- The first two struggle heavily with reasoning. The third one is
-- just somewhat odd.

--------------------------------------------------------------------------------
-- Idea: Use categories

-- Let ℙ be the category with Ob(ℙ) = [0,1], hom(p,q) = [0,q-p], where
-- g ∘ f := g + f and id := 0.

-- ℙ is some kind of oplax strict symmetric monoidal category, where p ⊗
-- q := p * q and I := 1. The tensor product is not quite a functor:
-- (p ∘ p') ⊗ (q ∘ q') ≥ (p ⊗ q) ∘ (p' ⊗ q').

-- It has products p × q = min(p, q) and coproducts p ⊎ q = max(p, q)
-- and initial and terminal objects 0 and 1.

--------------------------------------------------------------------------------
-- Alternative

-- Let's instead contract define hom(p,q) as {q-p}, and redefine the
-- tensor product on morphisms to be the appropriate formula. Then we
-- do get a strict SMC since the problematic inequality becomes an
-- equality.

-- Arguably, we haven't lost much. It still has all the other
-- structures, and still models addition properly.

--------------------------------------------------------------------------------
-- Conclusion

-- Translating back into the original question, the solution would now
-- be to define
-- _+_ : hom(p,q) → hom(q,r) → hom(p,r)
-- _+_ : (p q : [0,1]) → (p +' q ≤ 1) → [0,1]

-- However, how do we write functions that produce probabilities? We
-- could do something like P : (Ω → Type) → ∃[ p ] hom(0,p). Then,
-- when we want to add two probabilities in hom(0,p) and hom(0,q), we
-- need to shift one of them, e.g. to hom(p,p+q). So we now still have
-- to do the work of proving p+q≤1, but now it's part of forming the
-- types of the things we want to add.
