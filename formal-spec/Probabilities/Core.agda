module Probabilities.Core where

open import Meta.Prelude
open import Relation.Nullary
open import Relation.Unary
open import Relation.Unary.Algebra
open import Data.Rational renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_)
open import Data.Rational.Properties renaming (+-assoc to +ℚ-assoc ; +-comm to +ℚ-comm ; +-identityʳ to +ℚ-identityʳ ; +-inverseʳ to +ℚ-inverseʳ)
open import Relation.Binary.PropositionalEquality.Properties
open import Data.Integer using (1ℤ)

open ≡-Reasoning

record prob : Set₁ where

  field
    Ω : Set

  private
    subset : Set → Set₁
    subset Ω = Pred Ω zeroˡ    

  field
    p : subset Ω → ℚ

  private
    disjoint : ∀ {Ω} (P Q : subset Ω) → Set
    disjoint P Q = ∀ {ω} → P ω → Q ω → ⊥

  field
    p-stable           : ∀ {P Q} → P ≐ Q → p P ≡ p Q
    p-∅≡0              : p ∅ ≡ 0ℚ
    p-⊤≡1              : p U ≡ 1ℚ
    p-distrib-disjoint : ∀ {P Q} → disjoint P Q → p P +ℚ p Q ≡ p (P ∪ Q)

  private
    P∖Q∪P∩Q≐P : ∀ {Ω} {P Q : subset Ω} → Decidable Q → (P ∖ Q) ∪ P ∩ Q ≐ P
    P∖Q∪P∩Q≐P decQ = (λ { (inj₁ (ω∈P , _)) → ω∈P ; (inj₂ (ω∈P , _)) → ω∈P }) ,
                      λ {ω} → case decQ ω of λ { (yes ω∈Q) → inj₂ ∘ (_, ω∈Q) ; (no ω∉Q) → inj₁ ∘ (_, ω∉Q) }

    P∪Q≐P∖Q∪Q∖P∪P∩Q : ∀ {Ω} {P Q : subset Ω} → Decidable P → Decidable Q → P ∪ Q ≐ (P ∖ Q) ∪ (Q ∖ P) ∪ (P ∩ Q)
    P∪Q≐P∖Q∪Q∖P∪P∩Q decP decQ = (λ { {ω} (inj₁ ω∈P) → case decQ ω of λ { (yes ω∈Q) → inj₂ (inj₂ (ω∈P , ω∈Q)) ; (no ω∉Q) → inj₁ (ω∈P , ω∉Q) } ;
                                     {ω} (inj₂ ω∈Q) → case decP ω of λ { (yes ω∈P) → inj₂ (inj₂ (ω∈P , ω∈Q)) ; (no ω∉P) → inj₂ (inj₁ (ω∈Q , ω∉P))} }) ,
                                 λ { (inj₁ (ω∈P , _)) → inj₁ ω∈P ; (inj₂ (inj₁ (ω∈Q , _))) → inj₂ ω∈Q ; (inj₂ (inj₂ (ω∈P , _))) → inj₁ ω∈P}

  p-∅-neutral : ∀ {P} → p (P ∪ ∅) ≡ p P
  p-∅-neutral {P} = 
    begin
      p (P ∪ ∅)   ≡⟨ p-distrib-disjoint (λ _ ()) ⟨
      p P +ℚ p ∅  ≡⟨ cong (p P +ℚ_) p-∅≡0 ⟩
      p P +ℚ 0ℚ   ≡⟨ +ℚ-identityʳ _ ⟩
      p P         ∎
      
  p-combine : ∀ {P Q} → Decidable Q → p (P ∖ Q) +ℚ p (P ∩ Q) ≡ p P
  p-combine {P} {Q} dec =
    begin
      p (P ∖ Q) +ℚ p (P ∩ Q) ≡⟨ p-distrib-disjoint {P ∖ Q} {P ∩ Q} (λ (_ , ω∉Q) (_ , ω∈Q) → ω∉Q ω∈Q) ⟩
      p ((P ∖ Q) ∪ (P ∩ Q))  ≡⟨ p-stable $ P∖Q∪P∩Q≐P dec ⟩
      p P                    ∎

  p-distrib : ∀ {P Q} → Decidable P → Decidable Q → p P +ℚ p Q -ℚ p (P ∩ Q) ≡ p (P ∪ Q)
  p-distrib {P} {Q} decP decQ =
    begin
      p P +ℚ p Q -ℚ p (P ∩ Q)                        ≡⟨ cong (_-ℚ p (P ∩ Q)) $ +ℚ-comm (p P) _ ⟩
      p Q +ℚ p P -ℚ p (P ∩ Q)                        ≡⟨ +ℚ-assoc (p Q) _ _ ⟩
      p Q +ℚ (p P -ℚ p (P ∩ Q))                      ≡⟨ cong ((p Q +ℚ_) ∘ (_-ℚ p (P ∩ Q))) $ sym $ p-combine decQ ⟩
      p Q +ℚ (p (P ∖ Q) +ℚ p (P ∩ Q) -ℚ p (P ∩ Q))   ≡⟨ cong (p Q +ℚ_) $ +ℚ-assoc (p (P ∖ Q)) _ _ ⟩
      p Q +ℚ (p (P ∖ Q) +ℚ (p (P ∩ Q) -ℚ p (P ∩ Q))) ≡⟨ cong ((p Q +ℚ_) ∘ (p (P ∖ Q) +ℚ_)) $ +ℚ-inverseʳ $ p $ P ∩ Q ⟩
      p Q +ℚ (p (P ∖ Q) +ℚ 0ℚ)                       ≡⟨ cong (p Q +ℚ_) $ +ℚ-identityʳ $ p (P ∖ Q) ⟩
      p Q +ℚ p (P ∖ Q)                               ≡⟨ +ℚ-comm (p Q) _ ⟩
      p (P ∖ Q) +ℚ p Q                               ≡⟨ cong (p (P ∖ Q) +ℚ_) $ sym $ p-combine decP ⟩
      p (P ∖ Q) +ℚ (p (Q ∖ P) +ℚ p (Q ∩ P))          ≡⟨ +ℚ-assoc (p (P ∖ Q)) _ _ ⟨
      p (P ∖ Q) +ℚ p (Q ∖ P) +ℚ p (Q ∩ P)            ≡⟨ cong (p (P ∖ Q) +ℚ p (Q ∖ P) +ℚ_) $ p-stable $ ∩-comm _ _ ⟩
      p (P ∖ Q) +ℚ p (Q ∖ P) +ℚ p (P ∩ Q)            ≡⟨ +ℚ-assoc (p (P ∖ Q)) _ _ ⟩
      p (P ∖ Q) +ℚ (p (Q ∖ P) +ℚ p (P ∩ Q))          ≡⟨ cong (p (P ∖ Q) +ℚ_) $ p-distrib-disjoint (λ (_ , ω∉P) (ω∈P , _) → ω∉P ω∈P) ⟩
      p (P ∖ Q) +ℚ p ((Q ∖ P) ∪ (P ∩ Q))             ≡⟨ p-distrib-disjoint (λ { (_ , ω∉Q) (inj₁ (ω∈Q , _)) → ω∉Q ω∈Q ; (_ , ω∉Q) (inj₂ (_ , w∈Q)) → ω∉Q w∈Q}) ⟩
      p ((P ∖ Q) ∪ (Q ∖ P) ∪ (P ∩ Q))                ≡⟨ p-stable $ P∪Q≐P∖Q∪Q∖P∪P∩Q decP decQ ⟨
      p (P ∪ Q)                                      ∎
