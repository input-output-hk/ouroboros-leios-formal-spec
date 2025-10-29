{-# OPTIONS --safe #-}
module CategoricalCrypto.Pullback where

open import Categories.Category
open import Categories.Category.Helper

open import abstract-set-theory.Prelude
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private variable a b b' c c' : Level

module _ (C : Category a b c) where
  module C = Category C

  module _ (hom' : C.Obj → C.Obj → Setoid b' c') (inv : ∀ A B → Inverse (C.hom-setoid {A} {B}) (hom' A B)) where
    module hom' A B = Setoid (hom' A B)
    module inv {A} {B} = Inverse (inv A B)
    open C.HomReasoning using (_⟩∘⟨refl; refl⟩∘⟨_)

    Pullback : Category a b' c'
    Pullback = categoryHelper record
      { Obj = C.Obj
      ; _⇒_ = hom'.Carrier
      ; _≈_ = hom'._≈_ _ _
      ; id = inv.to C.id
      ; _∘_ = λ f g → inv.to (inv.from f C.∘ inv.from g)
      ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → let open C.HomReasoning in inv.to-cong $ begin
        inv.from (inv.to (inv.from h C.∘ inv.from g)) C.∘ inv.from f
          ≈⟨ inv.strictlyInverseʳ _ ⟩∘⟨refl ⟩
        (inv.from h C.∘ inv.from g) C.∘ inv.from f
          ≈⟨ C.assoc ⟩
        inv.from h C.∘ (inv.from g C.∘ inv.from f)
          ≈⟨ refl⟩∘⟨ inv.strictlyInverseʳ _ ⟨
        inv.from h C.∘ inv.from (inv.to (inv.from g C.∘ inv.from f)) ∎
      ; identityˡ = λ {_} {_} {f} → let open SetoidReasoning (hom' _ _) in begin
        inv.to (inv.from (inv.to C.id) C.∘ inv.from f)
          ≈⟨ inv.to-cong (inv.strictlyInverseʳ _ ⟩∘⟨refl) ⟩
        inv.to (C.id C.∘ inv.from f)
          ≈⟨ inv.to-cong C.identityˡ ⟩
        inv.to (inv.from f)
          ≈⟨ inv.strictlyInverseˡ _ ⟩
        f ∎
      ; identityʳ = λ {_} {_} {f} → let open SetoidReasoning (hom' _ _) in begin
        inv.to (inv.from f C.∘ inv.from (inv.to C.id))
          ≈⟨ inv.to-cong (refl⟩∘⟨ inv.strictlyInverseʳ _) ⟩
        inv.to (inv.from f C.∘ C.id)
          ≈⟨ inv.to-cong C.identityʳ ⟩
        inv.to (inv.from f)
          ≈⟨ inv.strictlyInverseˡ _ ⟩
        f ∎
      ; equiv = hom'.isEquivalence _ _
      ; ∘-resp-≈ = λ {_} {_} {_} {f} {g} {h} {i} f≈g h≈i → let open C.HomReasoning in inv.to-cong $ begin
        inv.from f C.∘ inv.from h
          ≈⟨ inv.from-cong f≈g ⟩∘⟨ inv.from-cong h≈i ⟩
        inv.from g C.∘ inv.from i ∎
      }
