{-# OPTIONS --safe #-}

module LibExt where

open import abstract-set-theory.Prelude hiding (take ; _++_)
open import Relation.Binary
open import Data.Vec
open import Categories.Category
open import Categories.Category.Helper
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Equivalence and Setoid structure for the extentional equality

IsEquivalence-≗ : ∀ {a b} {A : Set a} {B : Set b}
  → IsEquivalence (_≗_ {A = A} {B = B})
IsEquivalence-≗ = record
   { refl = λ _ → refl
   ; sym = λ x≗y → sym ∘ x≗y
   ; trans = λ i≗j j≗k l → trans (i≗j l) (j≗k l)
   }

≗-setoid : ∀ {a b} {A : Set a} {B : Set b} → Setoid _ _
≗-setoid {A = A} {B} = record
  { Carrier = A → B
  ; _≈_ = _
  ; isEquivalence = IsEquivalence-≗ }

-- Take on subvector

take-++ : ∀ {m n} {a} {A : Set a} {as : Vec A n} {as' : Vec A m}
  → take n (as ++ as') ≡ as
take-++ {as = []} = refl
take-++ {as = _ ∷ _} = cong (_ ∷_) take-++

-- A variant of case that remembers the equality proof

case_of-≡_ : ∀ {ℓ ℓ₁} {A : Set ℓ} {B : Set ℓ₁}
  → (a : A) → ((a' : A) → a ≡ a' → B) → B
case a of-≡ f = f a refl

-- Pulling back a categorical structure from an isomorphism

module _ {a b b' c c' : Level} (C : Category a b c) where
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
