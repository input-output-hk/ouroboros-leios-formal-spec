{-# OPTIONS --safe #-}

-- ============================================================================
-- A three-fold rearrangement for `Pair`.
--
-- `Leios.ChannelCat.Interchange` needs the middle-four exchange; the monoidal
-- associator needs this three-leaf cousin, which moves the third component up
-- beside the first and pushes the second to the right:
--
--     Pair M₁ (Pair M₂ M₃)  ≅ᴹ  Pair (Pair M₁ M₃) M₂   (up to relabelling)
--
-- The proof is the same trick as `Pair-mid4`: `Pair` carries its step relation
-- at fully general indices, so `Tensor.CompRel` constructors can be matched
-- directly and every leaf step is simply re-tagged.  Unlike `mid4ᵢ`/`mid4ₒ`,
-- `rot3ᵢ`/`rot3ₒ` are not involutions — source and target trees have different
-- shapes — so the backward direction gets its own matching helper, and the two
-- are tied together by the round-trip laws.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import Leios.ChannelCat.Interchange
open import Tactic.Defaults

module Leios.ChannelCat.PairAssoc where

open _≅ᴹ_

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ

  -- ------------------------------------------------------------------------
  -- The message-level reshuffles.  Both trees have three leaves, so a map is
  -- fixed by where it sends each of them.
  -- ------------------------------------------------------------------------

  rot3ᵢ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
        → Channel.inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
        → Channel.inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₃ ⊗ᵀ B₃)) ⊗₀ (A₂ ⊗ᵀ B₂))
  rot3ᵢ (inj₁ x)        = inj₁ (inj₁ x)
  rot3ᵢ (inj₂ (inj₁ y)) = inj₂ y
  rot3ᵢ (inj₂ (inj₂ z)) = inj₁ (inj₂ z)

  rot3ₒ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
        → Channel.outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
        → Channel.outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₃ ⊗ᵀ B₃)) ⊗₀ (A₂ ⊗ᵀ B₂))
  rot3ₒ (inj₁ x)        = inj₁ (inj₁ x)
  rot3ₒ (inj₂ (inj₁ y)) = inj₂ y
  rot3ₒ (inj₂ (inj₂ z)) = inj₁ (inj₂ z)

  rot3ᵢ⁻ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
         → Channel.inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₃ ⊗ᵀ B₃)) ⊗₀ (A₂ ⊗ᵀ B₂))
         → Channel.inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
  rot3ᵢ⁻ (inj₁ (inj₁ x)) = inj₁ x
  rot3ᵢ⁻ (inj₁ (inj₂ z)) = inj₂ (inj₂ z)
  rot3ᵢ⁻ (inj₂ y)        = inj₂ (inj₁ y)

  rot3ₒ⁻ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
         → Channel.outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₃ ⊗ᵀ B₃)) ⊗₀ (A₂ ⊗ᵀ B₂))
         → Channel.outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃)))
  rot3ₒ⁻ (inj₁ (inj₁ x)) = inj₁ x
  rot3ₒ⁻ (inj₁ (inj₂ z)) = inj₂ (inj₂ z)
  rot3ₒ⁻ (inj₂ y)        = inj₂ (inj₁ y)

  private
    rot3ᵢ⁻-rot3ᵢ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                   (i : Channel.inType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃))))
                 → rot3ᵢ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}
                     (rot3ᵢ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} i) ≡ i
    rot3ᵢ⁻-rot3ᵢ (inj₁ _)        = refl
    rot3ᵢ⁻-rot3ᵢ (inj₂ (inj₁ _)) = refl
    rot3ᵢ⁻-rot3ᵢ (inj₂ (inj₂ _)) = refl

    rot3ₒ⁻-rot3ₒ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                   (o : Channel.outType ((A₁ ⊗ᵀ B₁) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₃ ⊗ᵀ B₃))))
                 → rot3ₒ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}
                     (rot3ₒ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} o) ≡ o
    rot3ₒ⁻-rot3ₒ (inj₁ _)        = refl
    rot3ₒ⁻-rot3ₒ (inj₂ (inj₁ _)) = refl
    rot3ₒ⁻-rot3ₒ (inj₂ (inj₂ _)) = refl

    mapᴹ-∘' : ∀ {X Y Z : Type} (v : Y → Z) (v' : X → Y) (o : Maybe X)
            → mapᴹ v (mapᴹ v' o) ≡ mapᴹ (λ x → v (v' x)) o
    mapᴹ-∘' v v' (just x) = refl
    mapᴹ-∘' v v' nothing  = refl

    mapᴹ-cong' : ∀ {X Y : Type} {v v' : X → Y}
               → (∀ x → v x ≡ v' x) → ∀ o → mapᴹ v o ≡ mapᴹ v' o
    mapᴹ-cong' e (just x) = cong just (e x)
    mapᴹ-cong' e nothing  = refl

    mapᴹ-id' : ∀ {X : Type} (o : Maybe X) → mapᴹ (λ x → x) o ≡ o
    mapᴹ-id' (just _) = refl
    mapᴹ-id' nothing  = refl

  -- The state rearrangement, and its inverse.
  rot3s : ∀ {S₁ S₂ S₃ : Type} → S₁ × (S₂ × S₃) → (S₁ × S₃) × S₂
  rot3s (s₁ , (s₂ , s₃)) = (s₁ , s₃) , s₂

  rot3s⁻ : ∀ {S₁ S₂ S₃ : Type} → (S₁ × S₃) × S₂ → S₁ × (S₂ × S₃)
  rot3s⁻ ((s₁ , s₃) , s₂) = s₁ , (s₂ , s₃)

  -- Each of the three leaves fires on its own, and is re-tagged.  The split on
  -- the output implicit is forced: `mapᴹ rot3ₒ m'` does not determine `m'`.
  Pair-rot3-to : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                 (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂) (M₃ : Machine A₃ B₃)
                 {s i o s'}
               → Tensor.CompRel M₁ (Pair M₂ M₃) s i o s'
               → Tensor.CompRel (Pair M₁ M₃) M₂
                   (rot3s s) (rot3ᵢ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} i)
                   (mapᴹ (rot3ₒ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃})  o) (rot3s s')
  Pair-rot3-to _ _ _ (Tensor.Step₁ {m' = just _}  q) = Tensor.Step₁ (Tensor.Step₁ q)
  Pair-rot3-to _ _ _ (Tensor.Step₁ {m' = nothing} q) = Tensor.Step₁ (Tensor.Step₁ q)
  Pair-rot3-to _ _ _ (Tensor.Step₂ (Tensor.Step₁ {m' = just _}  r)) = Tensor.Step₂ r
  Pair-rot3-to _ _ _ (Tensor.Step₂ (Tensor.Step₁ {m' = nothing} r)) = Tensor.Step₂ r
  Pair-rot3-to _ _ _ (Tensor.Step₂ (Tensor.Step₂ {m' = just _}  r)) = Tensor.Step₁ (Tensor.Step₂ r)
  Pair-rot3-to _ _ _ (Tensor.Step₂ (Tensor.Step₂ {m' = nothing} r)) = Tensor.Step₁ (Tensor.Step₂ r)

  -- The mirror image.  It is stated at the rearranged machines and at fully
  -- general indices, which is what keeps the constructors matchable: writing
  -- the backward direction of the iso directly would present the index as
  -- `rot3ᵢ i` with `i` a variable, and nothing would reduce.
  Pair-rot3-from : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
                   (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂) (M₃ : Machine A₃ B₃)
                   {s i o s'}
                 → Tensor.CompRel (Pair M₁ M₃) M₂ s i o s'
                 → Tensor.CompRel M₁ (Pair M₂ M₃)
                     (rot3s⁻ s) (rot3ᵢ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} i)
                     (mapᴹ (rot3ₒ⁻ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃}) o) (rot3s⁻ s')
  Pair-rot3-from _ _ _ (Tensor.Step₁ (Tensor.Step₁ {m' = just _}  q)) = Tensor.Step₁ q
  Pair-rot3-from _ _ _ (Tensor.Step₁ (Tensor.Step₁ {m' = nothing} q)) = Tensor.Step₁ q
  Pair-rot3-from _ _ _ (Tensor.Step₁ (Tensor.Step₂ {m' = just _}  r)) = Tensor.Step₂ (Tensor.Step₂ r)
  Pair-rot3-from _ _ _ (Tensor.Step₁ (Tensor.Step₂ {m' = nothing} r)) = Tensor.Step₂ (Tensor.Step₂ r)
  Pair-rot3-from _ _ _ (Tensor.Step₂ {m' = just _}  r) = Tensor.Step₂ (Tensor.Step₁ r)
  Pair-rot3-from _ _ _ (Tensor.Step₂ {m' = nothing} r) = Tensor.Step₂ (Tensor.Step₁ r)

  Pair-rot3 : ∀ {A₁ B₁ A₂ B₂ A₃ B₃}
              (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂) (M₃ : Machine A₃ B₃)
            → Pair M₁ (Pair M₂ M₃) ≅ᴹ Reindex (Pair (Pair M₁ M₃) M₂) rot3ᵢ rot3ₒ
  Pair-rot3 {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} M₁ M₂ M₃ =
    MkIso rot3s rot3s⁻ (λ _ → refl) (λ _ → refl)
      (Pair-rot3-to M₁ M₂ M₃)
      (λ {_} {i} {o} p →
        subst₂ (λ x y → Tensor.CompRel M₁ (Pair M₂ M₃) _ x y _)
               (rot3ᵢ⁻-rot3ᵢ i)
               (trans (mapᴹ-∘' rot3ₒ⁻ rot3ₒ o)
                      (trans (mapᴹ-cong' rot3ₒ⁻-rot3ₒ o) (mapᴹ-id' o)))
               (Pair-rot3-from M₁ M₂ M₃ p))
