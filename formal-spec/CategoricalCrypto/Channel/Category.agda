{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel.Category where

open import CategoricalCrypto.Channel.Core
open import Categories.Category.Core
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Relation.Binary.PropositionalEquality
open import abstract-set-theory.Prelude hiding (_⊗_)

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

opaque
  unfolding _⊗_

  channelMonoidal : Monoidal channelCategory
  channelMonoidal = monoidalHelper channelCategory
    record {
      ⊗ = record {
             F₀ = uncurry _⊗_ ;
             F₁ = λ (p₁ , p₂) → ⊗-combine p₁ p₂ ;
             identity = λ where {m = Out} (inj₁ _) → refl
                                {m = Out} (inj₂ _) → refl
                                {m = In } (inj₁ _) → refl
                                {m = In } (inj₂ _) → refl
                        ;
             homomorphism = λ where
                                {m = Out} (inj₁ _) → refl
                                {m = Out} (inj₂ _) → refl
                                {m = In } (inj₁ _) → refl
                                {m = In } (inj₂ _) → refl
                            ;
             F-resp-≈ = λ where
                            (fst , snd) {Out} (inj₁ x) → cong inj₁ (fst {Out} x)
                            (fst , snd) {Out} (inj₂ y) → cong inj₂ (snd {Out} y)
                            (fst , snd) {In } (inj₁ x) → cong inj₁ (fst {In } x)
                            (fst , snd) {In } (inj₂ y) → cong inj₂ (snd {In } y)
           };
      unit = I ;
      unitorˡ = record {
                 from = ⊗-left-neutral ;
                 to = ⊗-left-intro ;
                 iso = record {
                         isoˡ = λ where
                                   {Out} (inj₂ _) → refl
                                   {In } (inj₂ _) → refl
                               ;
                         isoʳ = λ where
                                   {Out} _ → refl
                                   {In } _ → refl
                       }
               };
      unitorʳ = record {
                 from = ⊗-right-neutral ;
                 to = ⊗-right-intro ;
                 iso = record {
                         isoˡ = λ where
                                   {Out} (inj₁ _) → refl
                                   {In } (inj₁ _) → refl
                               ;
                         isoʳ = λ where
                                   {Out} _ → refl
                                   {In } _ → refl
                       }
               };
      associator = record {
                     from = ⊗-right-assoc ;
                     to = ⊗-left-assoc ;
                     iso = record {
                             isoˡ = λ where
                                       {Out} (inj₁ (inj₁ _)) → refl
                                       {Out} (inj₁ (inj₂ _)) → refl
                                       {Out} (inj₂ _       ) → refl
                                       {In } (inj₁ (inj₁ _)) → refl
                                       {In } (inj₁ (inj₂ _)) → refl
                                       {In } (inj₂ _       ) → refl
                             ;
                             isoʳ = λ where
                                       {Out} (inj₁ _       ) → refl
                                       {Out} (inj₂ (inj₁ _)) → refl
                                       {Out} (inj₂ (inj₂ _)) → refl
                                       {In } (inj₁ _       ) → refl
                                       {In } (inj₂ (inj₁ _)) → refl
                                       {In } (inj₂ (inj₂ _)) → refl
                           }
                   };
      unitorˡ-commute = λ where
                           {m = Out} (inj₂ _) → refl
                           {m = In } (inj₂ _) → refl
                       ;
      unitorʳ-commute = λ where
                           {m = Out} (inj₁ _) → refl
                           {m = In } (inj₁ _) → refl
                       ;
      assoc-commute = λ where
                          {m = Out} (inj₁ (inj₁ _)) → refl
                          {m = Out} (inj₁ (inj₂ _)) → refl
                          {m = Out} (inj₂ _       ) → refl
                          {m = In } (inj₁ (inj₁ _)) → refl
                          {m = In } (inj₁ (inj₂ _)) → refl
                          {m = In } (inj₂ _       ) → refl
                      ;
      triangle = λ where
                     {m = Out} (inj₁ (inj₁ _)) → refl
                     {m = Out} (inj₂ _       ) → refl
                     {m = In } (inj₁ (inj₁ _)) → refl
                     {m = In } (inj₂ _       ) → refl
                 ;
      pentagon = λ where
                     {m = Out} (inj₁ (inj₁ (inj₁ _))) → refl
                     {m = Out} (inj₁ (inj₁ (inj₂ _))) → refl
                     {m = Out} (inj₁ (inj₂ _       )) → refl
                     {m = Out} (inj₂ _              ) → refl
                     {m = In } (inj₁ (inj₁ (inj₁ _))) → refl
                     {m = In } (inj₁ (inj₁ (inj₂ _))) → refl
                     {m = In } (inj₁ (inj₂ _       )) → refl
                     {m = In } (inj₂ _              ) → refl
    }

  channelSymmetric : Symmetric channelMonoidal
  channelSymmetric = symmetricHelper channelMonoidal
    record {
      braiding = record {
                   F⇒G = record {
                           η = λ _ → ⊗-sym ;
                           commute = λ where
                                         f {Out} (inj₁ _) → refl
                                         f {Out} (inj₂ _) → refl
                                         f {In } (inj₁ _) → refl
                                         f {In } (inj₂ _) → refl
                                     ;
                           sym-commute = λ where
                                             f {Out} (inj₁ _) → refl
                                             f {Out} (inj₂ _) → refl
                                             f {In } (inj₁ _) → refl
                                             f {In } (inj₂ _) → refl 
                         } ;
                   F⇐G = record {
                           η = λ _ → ⊗-sym ;
                           commute = λ where
                                         f {Out} (inj₁ _) → refl
                                         f {Out} (inj₂ _) → refl
                                         f {In } (inj₁ _) → refl
                                         f {In } (inj₂ _) → refl
                                     ;
                           sym-commute = λ where
                                             f {Out} (inj₁ _) → refl
                                             f {Out} (inj₂ _) → refl
                                             f {In } (inj₁ _) → refl
                                             f {In } (inj₂ _) → refl 
                         } ;                           
                   iso = λ _ → record {
                                 isoˡ = λ where
                                           {Out} (inj₁ _) → refl
                                           {Out} (inj₂ _) → refl
                                           {In } (inj₁ _) → refl
                                           {In } (inj₂ _) → refl
                                       ;
                                 isoʳ = λ where
                                           {Out} (inj₁ _) → refl
                                           {Out} (inj₂ _) → refl
                                           {In } (inj₁ _) → refl
                                           {In } (inj₂ _) → refl
                               }
                 } ;
      commutative = λ where
                        {m = Out} (inj₁ _) → refl
                        {m = Out} (inj₂ _) → refl
                        {m = In } (inj₁ _) → refl
                        {m = In } (inj₂ _) → refl
                    ;
      hexagon = λ where
                    {m = Out} (inj₁ (inj₁ _)) → refl
                    {m = Out} (inj₁ (inj₂ _)) → refl
                    {m = Out} (inj₂ _       ) → refl
                    {m = In } (inj₁ (inj₁ _)) → refl
                    {m = In } (inj₁ (inj₂ _)) → refl
                    {m = In } (inj₂ _       ) → refl
    }
  
channelSymmetricMonoidalCategory : SymmetricMonoidalCategory (sucˡ zeroˡ) zeroˡ zeroˡ
channelSymmetricMonoidalCategory =
  record {
    U = channelCategory ;
    monoidal = channelMonoidal ;
    symmetric = channelSymmetric
  }
