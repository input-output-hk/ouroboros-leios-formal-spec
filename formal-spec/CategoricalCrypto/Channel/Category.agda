{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel.Category where

open import CategoricalCrypto.Channel.Core
open import Categories.Category.Core
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Functor.Bifunctor
open import Relation.Binary.PropositionalEquality
open import abstract-set-theory.Prelude hiding (_⊗_ ; Functor ; Bifunctor)

opaque
  unfolding _⊗_

  channel-category : Category (sucˡ zeroˡ) zeroˡ zeroˡ
  ⊗-bifunctor : Bifunctor channel-category channel-category channel-category
  channel-⊗-monoidal : Monoidal channel-category
  channel-⊗-monoidal-category : MonoidalCategory (sucˡ zeroˡ) zeroˡ zeroˡ
  channel-⊗-braided : Braided channel-⊗-monoidal
  channel-⊗-braided-monoidal-category : BraidedMonoidalCategory (sucˡ zeroˡ) zeroˡ zeroˡ
  channel-⊗-symmetric : Symmetric channel-⊗-monoidal
  channel-⊗-symmetric-monoidal-category : SymmetricMonoidalCategory (sucˡ zeroˡ) zeroˡ zeroˡ
  ᵀ-endofunctor : Endofunctor channel-category
  ᵀ-monoidal-functor : MonoidalFunctor channel-⊗-monoidal-category channel-⊗-monoidal-category
  ᵀ-strong-monoidal-functor : StrongMonoidalFunctor channel-⊗-monoidal-category channel-⊗-monoidal-category
      
  channel-category = categoryHelper record
    { Obj = Channel
    ; _⇒_ = λ A B → ∀ {m} → A [ m ]⇒[ m ] B
    ; _≈_ = λ A⇒B₀ A⇒B₁ → ∀ {m} v → A⇒B₀ {m} v ≡ A⇒B₁ v
    ; id = ⇒-refl
    ; _∘_ = λ A⇒B B⇒C → B⇒C ⇒ₜ A⇒B
    ; assoc = λ _ → refl
    ; identityˡ = λ _ → refl
    ; identityʳ = λ _ → refl
    ; equiv = record
        { refl = λ _ → refl
        ; sym = λ A⇒B₀≈A⇒B₁ → sym ∘ A⇒B₀≈A⇒B₁
        ; trans = λ A⇒B₀≈A⇒B₁ A⇒B₁≈A⇒B₂ _ → trans (A⇒B₀≈A⇒B₁ _) (A⇒B₁≈A⇒B₂ _)
        }
    ; ∘-resp-≈ = λ where
        {h = B⇒C} {A⇒B} f≈B⇒C A⇒B≈i _ → trans (f≈B⇒C ∘ A⇒B $ _) (cong B⇒C ∘ A⇒B≈i $ _)
    }
    
  ⊗-bifunctor = record
    { F₀ = uncurry _⊗_
    ; F₁ = λ (A⇒B , C⇒D) → ⊗-combine A⇒B C⇒D
    ; identity = λ where
        {m = Out} (inj₁ _) → refl
        {m = Out} (inj₂ _) → refl
        {m = In } (inj₁ _) → refl
        {m = In } (inj₂ _) → refl
    ; homomorphism = λ where
        {m = Out} (inj₁ _) → refl
        {m = Out} (inj₂ _) → refl
        {m = In } (inj₁ _) → refl
        {m = In } (inj₂ _) → refl
    ; F-resp-≈ = λ where
        (f≈g , _  ) {Out} (inj₁ o) → cong inj₁ (f≈g o)
        (_   , f≈g) {Out} (inj₂ o) → cong inj₂ (f≈g o)
        (f≈g , _  ) {In } (inj₁ i) → cong inj₁ (f≈g i)
        (_   , f≈g) {In } (inj₂ i) → cong inj₂ (f≈g i)
    }

  channel-⊗-monoidal = monoidalHelper channel-category record
    { ⊗ = ⊗-bifunctor
    ; unit = I
    ; unitorˡ = record
        { from = ⊗-left-neutral
        ; to = ⊗-left-intro
        ; iso = record
            { isoˡ = λ where
                {Out} (inj₂ _) → refl
                {In } (inj₂ _) → refl
            ; isoʳ = λ where
                {Out} _ → refl
                {In } _ → refl
            }
        }
    ; unitorʳ = record
        { from = ⊗-right-neutral
        ; to = ⊗-right-intro
        ; iso = record
            { isoˡ = λ where
                {Out} (inj₁ _) → refl
                {In } (inj₁ _) → refl
            ; isoʳ = λ where
                {Out} _ → refl
                {In } _ → refl
            }
        }
      ; associator = record
          { from = ⊗-right-assoc
          ; to = ⊗-left-assoc
          ; iso = record
              { isoˡ = λ where
                  {Out} (inj₁ (inj₁ _)) → refl
                  {Out} (inj₁ (inj₂ _)) → refl
                  {Out} (inj₂ _       ) → refl
                  {In } (inj₁ (inj₁ _)) → refl
                  {In } (inj₁ (inj₂ _)) → refl
                  {In } (inj₂ _       ) → refl
              ; isoʳ = λ where
                  {Out} (inj₁ _       ) → refl
                  {Out} (inj₂ (inj₁ _)) → refl
                  {Out} (inj₂ (inj₂ _)) → refl
                  {In } (inj₁ _       ) → refl
                  {In } (inj₂ (inj₁ _)) → refl
                  {In } (inj₂ (inj₂ _)) → refl
              }
          }
      ; unitorˡ-commute = λ where
          {m = Out} (inj₂ _) → refl
          {m = In } (inj₂ _) → refl
      ; unitorʳ-commute = λ where
          {m = Out} (inj₁ _) → refl
          {m = In } (inj₁ _) → refl
      ; assoc-commute = λ where
          {m = Out} (inj₁ (inj₁ _)) → refl
          {m = Out} (inj₁ (inj₂ _)) → refl
          {m = Out} (inj₂ _       ) → refl
          {m = In } (inj₁ (inj₁ _)) → refl
          {m = In } (inj₁ (inj₂ _)) → refl
          {m = In } (inj₂ _       ) → refl
      ; triangle = λ where
          {m = Out} (inj₁ (inj₁ _)) → refl
          {m = Out} (inj₂ _       ) → refl
          {m = In } (inj₁ (inj₁ _)) → refl
          {m = In } (inj₂ _       ) → refl
      ; pentagon = λ where
          {m = Out} (inj₁ (inj₁ (inj₁ _))) → refl
          {m = Out} (inj₁ (inj₁ (inj₂ _))) → refl
          {m = Out} (inj₁ (inj₂ _       )) → refl
          {m = Out} (inj₂ _              ) → refl
          {m = In } (inj₁ (inj₁ (inj₁ _))) → refl
          {m = In } (inj₁ (inj₁ (inj₂ _))) → refl
          {m = In } (inj₁ (inj₂ _       )) → refl
          {m = In } (inj₂ _              ) → refl
    }

  channel-⊗-symmetric = symmetricHelper channel-⊗-monoidal record
    { braiding = record
        { F⇒G = record
            { η = λ _ → ⊗-sym
            ; commute = λ where
                _ {Out} (inj₁ _) → refl
                _ {Out} (inj₂ _) → refl
                _ {In } (inj₁ _) → refl
                _ {In } (inj₂ _) → refl
            ; sym-commute = λ where
                _ {Out} (inj₁ _) → refl
                _ {Out} (inj₂ _) → refl
                _ {In } (inj₁ _) → refl
                _ {In } (inj₂ _) → refl 
            }
        ; F⇐G = record
            { η = λ _ → ⊗-sym
            ; commute = λ where
                _ {Out} (inj₁ _) → refl
                _ {Out} (inj₂ _) → refl
                _ {In } (inj₁ _) → refl
                _ {In } (inj₂ _) → refl
            ; sym-commute = λ where
                _ {Out} (inj₁ _) → refl
                _ {Out} (inj₂ _) → refl
                _ {In } (inj₁ _) → refl
                _ {In } (inj₂ _) → refl 
            }
        ; iso = λ _ → record
            { isoˡ = λ where
                {Out} (inj₁ _) → refl
                {Out} (inj₂ _) → refl
                {In } (inj₁ _) → refl
                {In } (inj₂ _) → refl
            ; isoʳ = λ where
                {Out} (inj₁ _) → refl
                {Out} (inj₂ _) → refl
                {In } (inj₁ _) → refl
                {In } (inj₂ _) → refl
            }
        }
    ; commutative = λ where
        {m = Out} (inj₁ _) → refl
        {m = Out} (inj₂ _) → refl
        {m = In } (inj₁ _) → refl
        {m = In } (inj₂ _) → refl
    ; hexagon = λ where
        {m = Out} (inj₁ (inj₁ _)) → refl
        {m = Out} (inj₁ (inj₂ _)) → refl
        {m = Out} (inj₂ _       ) → refl
        {m = In } (inj₁ (inj₁ _)) → refl
        {m = In } (inj₁ (inj₂ _)) → refl
        {m = In } (inj₂ _       ) → refl
    }

  channel-⊗-braided = Symmetric.braided channel-⊗-symmetric
  
  channel-⊗-symmetric-monoidal-category = record
    { U = channel-category
    ; monoidal = channel-⊗-monoidal
    ; symmetric = channel-⊗-symmetric
    }

  channel-⊗-monoidal-category = SymmetricMonoidalCategory.monoidalCategory channel-⊗-symmetric-monoidal-category

  channel-⊗-braided-monoidal-category = SymmetricMonoidalCategory.braidedMonoidalCategory channel-⊗-symmetric-monoidal-category

  ᵀ-endofunctor = record
    { F₀ = _ᵀ
    ; F₁ = λ A⇒B → ⇒-transpose ⇒ₜ A⇒B ⇒ₜ ⇒-reduce
    ; identity = λ where
        {m = Out} _ → refl
        {m = In } _ → refl
    ; homomorphism = λ where
        {m = Out} _ → refl
        {m = In } _ → refl
    ; F-resp-≈ = λ where
        f≈g {Out} → f≈g ∘ ⇒-transpose
        f≈g {In } → f≈g ∘ ⇒-transpose
    }

  ᵀ-strong-monoidal-functor = record
    { F = ᵀ-endofunctor
    ; isStrongMonoidal = record
        { ε = record
            { from = ⇒-refl' ᵀ-identity
            ; to = ⇒-refl' ᵀ-identity
            ; iso = record
                { isoˡ = λ _ → refl
                ; isoʳ = λ _ → refl
                }
            }
        ; ⊗-homo = record
            { F⇒G = record
                { η = λ _ → ⊗-ᵀ-factor
                ; commute = λ where
                    _ {Out} (inj₁ _) → refl
                    _ {Out} (inj₂ _) → refl
                    _ {In } (inj₁ _) → refl
                    _ {In } (inj₂ _) → refl
                ; sym-commute = λ where
                    _ {Out} (inj₁ _) → refl
                    _ {Out} (inj₂ _) → refl
                    _ {In } (inj₁ _) → refl
                    _ {In } (inj₂ _) → refl
                }
            ; F⇐G = record
                { η = λ _ → ⊗-ᵀ-distrib
                ; commute = λ where
                    _ {Out} (inj₁ _) → refl
                    _ {Out} (inj₂ _) → refl
                    _ {In } (inj₁ _) → refl
                    _ {In } (inj₂ _) → refl
                ; sym-commute = λ where
                    _ {Out} (inj₁ _) → refl
                    _ {Out} (inj₂ _) → refl
                    _ {In } (inj₁ _) → refl
                    _ {In } (inj₂ _) → refl
                }
            ; iso = λ _ → record
                { isoˡ = λ where
                    {m = Out} (inj₁ _) → refl
                    {m = Out} (inj₂ _) → refl
                    {m = In } (inj₁ _) → refl
                    {m = In } (inj₂ _) → refl
                ; isoʳ = λ where
                    {m = Out} (inj₁ _) → refl
                    {m = Out} (inj₂ _) → refl
                    {m = In } (inj₁ _) → refl
                    {m = In } (inj₂ _) → refl
                }
            }
        ; associativity = λ where
            {m = Out} (inj₁ (inj₁ _)) → refl
            {m = Out} (inj₁ (inj₂ _)) → refl
            {m = Out} (inj₂ _       ) → refl
            {m = In } (inj₁ (inj₁ _)) → refl
            {m = In } (inj₁ (inj₂ _)) → refl
            {m = In } (inj₂ _       ) → refl
        ; unitaryˡ = λ where
            {m = Out} (inj₂ _) → refl
            {m = In } (inj₂ _) → refl
        ; unitaryʳ = λ where
            {m = Out} (inj₁ _) → refl
            {m = In } (inj₁ _) → refl
        }
    }

  ᵀ-monoidal-functor = StrongMonoidalFunctor.monoidalFunctor ᵀ-strong-monoidal-functor

