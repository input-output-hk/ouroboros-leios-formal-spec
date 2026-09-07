{-# OPTIONS --safe #-}

-- ============================================================================
-- Sliding a channel relabelling past a trace, and what it buys.
--
-- `Leios.ChannelCat.Interchange` reduced everything to `Reindex`/`Pair`/`Trc`.
-- One fact about that algebra is missing there and is what the remaining laws
-- of `Leios.ChannelCat.Monoidal` all want:
--
--   `Trc-slide` — a relabelling that FIXES THE TRACED CHANNEL commutes with
--     `Trc`.  A trace chain only ever touches the traced ports, so relabelling
--     the external ones cannot change which chains exist.
--
-- From it: a forwarder is a reindexed identity (`Reindex-Fwd`), a relabelling
-- slides out of either argument of `_∘_` (`∘-collapse-dom`/`∘-collapse-cod`),
-- and hence composing with a forwarder is just a relabelling.  That is what
-- discharges the naturality laws and the two Kleisli laws.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Machine.Iso
  using (∘-identityˡ-≅ᴹ; ∘-identityʳ-≅ᴹ)
open import Leios.ChannelCat.Interchange
open import Tactic.Defaults

module Leios.ChannelCat.Slide where

open _≅ᴹ_

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ

  -- The four traced-channel ports of a machine `Machine (X ⊗₀ Z) (Y ⊗₀ Z)`,
  -- at channel-shaped types.
  dZᵢ : ∀ {X Y Z} → Channel.inType Z → Channel.inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  dZᵢ z = inj₁ (inj₂ z)

  cZₒ : ∀ {X Y Z} → Channel.outType Z → Channel.inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  cZₒ z = inj₂ (inj₂ z)

  dZₒ : ∀ {X Y Z} → Channel.outType Z → Channel.outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  dZₒ z = inj₁ (inj₂ z)

  cZᵢ : ∀ {X Y Z} → Channel.inType Z → Channel.outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  cZᵢ z = inj₂ (inj₂ z)

  -- A relabelling that fixes the traced channel's ports commutes with `Trc`.
  Trc-slide : ∀ {X Y Z X' Y' : Channel} (W : Machine (X ⊗₀ Z) (Y ⊗₀ Z))
              (p : Channel.inType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z))
                 → Channel.inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z)))
              (q : Channel.outType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z))
                 → Channel.outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z)))
            → (∀ z → p (dZᵢ {X'} {Y'} {Z} z) ≡ dZᵢ {X} {Y} {Z} z)
            → (∀ z → p (cZₒ {X'} {Y'} {Z} z) ≡ cZₒ {X} {Y} {Z} z)
            → (∀ z → q (dZₒ {X'} {Y'} {Z} z) ≡ dZₒ {X} {Y} {Z} z)
            → (∀ z → q (cZᵢ {X'} {Y'} {Z} z) ≡ cZᵢ {X} {Y} {Z} z)
            → Trc (Reindex W p q) ≅ᴹ Reindex (Trc W) p q
  Trc-slide {X} {Y} {Z} {X'} {Y'} W p q pi po qo qi =
    MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl) t
          (λ {_} {i} {o} x → f x i o refl refl)
    where
    t : ∀ {s I MO s'} → TraceRel (Reindex W p q) s I MO s'
      → TraceRel W s (p I) (mapᴹ q MO) s'
    t Trace[ x ] = Trace[ x ]
    t (_Trace∷ₒ_ {outC = zc} x rest) =
      subst (λ y → Machine.stepRel W _ (p _) (just y) _) (qo zc) x
      Trace∷ₒ subst (λ y → TraceRel W _ y _ _) (po zc) (t rest)
    t (_Trace∷ᵢ_ {inC = zc} x rest) =
      subst (λ y → Machine.stepRel W _ (p _) (just y) _) (qi zc) x
      Trace∷ᵢ subst (λ y → TraceRel W _ y _ _) (pi zc) (t rest)
    -- The indices are generalised and re-tied by equations, so that the
    -- recursion is on the `TraceRel` itself and the termination checker sees it.
    f : ∀ {s I₀ MO₀ s'} → TraceRel W s I₀ MO₀ s'
      → ∀ I MO → I₀ ≡ p I → MO₀ ≡ mapᴹ q MO
      → TraceRel (Reindex W p q) s I MO s'
    f Trace[ x ] I MO ieq oeq =
      Trace[ subst₂ (λ a b → Machine.stepRel W _ a b _) ieq oeq x ]
    f (_Trace∷ₒ_ {outC = zc} x rest) I MO ieq oeq =
      subst₂ (λ a b → Machine.stepRel W _ a (just b) _) ieq (sym (qo zc)) x
      Trace∷ₒ f rest (cZₒ {X'} {Y'} {Z} zc) MO (sym (po zc)) oeq
    f (_Trace∷ᵢ_ {inC = zc} x rest) I MO ieq oeq =
      subst₂ (λ a b → Machine.stepRel W _ a (just b) _) ieq (sym (qi zc)) x
      Trace∷ᵢ f rest (dZᵢ {X'} {Y'} {Z} zc) MO (sym (pi zc)) oeq

  -- ------------------------------------------------------------------------
  -- Relabellings that touch only one side of a machine.
  -- ------------------------------------------------------------------------

  -- Relabel the codomain of `Machine B C`, leaving the domain alone.
  cdᵢ : ∀ {B C C'} → (Channel.outType C' → Channel.outType C)
      → Channel.inType (B ⊗ᵀ C') → Channel.inType (B ⊗ᵀ C)
  cdᵢ uC (inj₁ b) = inj₁ b
  cdᵢ uC (inj₂ γ) = inj₂ (uC γ)

  cdₒ : ∀ {B C C'} → (Channel.inType C' → Channel.inType C)
      → Channel.outType (B ⊗ᵀ C') → Channel.outType (B ⊗ᵀ C)
  cdₒ vC (inj₁ β) = inj₁ β
  cdₒ vC (inj₂ c) = inj₂ (vC c)

  -- Relabel the domain of `Machine A B`, leaving the codomain alone.
  dmᵢ : ∀ {A A' B} → (Channel.inType A' → Channel.inType A)
      → Channel.inType (A' ⊗ᵀ B) → Channel.inType (A ⊗ᵀ B)
  dmᵢ uA (inj₁ a) = inj₁ (uA a)
  dmᵢ uA (inj₂ β) = inj₂ β

  dmₒ : ∀ {A A' B} → (Channel.outType A' → Channel.outType A)
      → Channel.outType (A' ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B)
  dmₒ vA (inj₁ α) = inj₁ (vA α)
  dmₒ vA (inj₂ b) = inj₂ b

  -- The same, at the traced machine's channel.  These fix the traced ports,
  -- which is what lets `Trc-slide` apply.
  wcᵢ : ∀ {A B C C'} → (Channel.outType C' → Channel.outType C)
      → Channel.inType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)) → Channel.inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wcᵢ uC (inj₁ x)        = inj₁ x
  wcᵢ uC (inj₂ (inj₁ γ)) = inj₂ (inj₁ (uC γ))
  wcᵢ uC (inj₂ (inj₂ β)) = inj₂ (inj₂ β)

  wcₒ : ∀ {A B C C'} → (Channel.inType C' → Channel.inType C)
      → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)) → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wcₒ vC (inj₁ x)        = inj₁ x
  wcₒ vC (inj₂ (inj₁ c)) = inj₂ (inj₁ (vC c))
  wcₒ vC (inj₂ (inj₂ b)) = inj₂ (inj₂ b)

  wdᵢ : ∀ {A A' B C} → (Channel.inType A' → Channel.inType A)
      → Channel.inType ((A' ⊗₀ B) ⊗ᵀ (C ⊗₀ B)) → Channel.inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wdᵢ uA (inj₁ (inj₁ a)) = inj₁ (inj₁ (uA a))
  wdᵢ uA (inj₁ (inj₂ b)) = inj₁ (inj₂ b)
  wdᵢ uA (inj₂ y)        = inj₂ y

  wdₒ : ∀ {A A' B C} → (Channel.outType A' → Channel.outType A)
      → Channel.outType ((A' ⊗₀ B) ⊗ᵀ (C ⊗₀ B)) → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wdₒ vA (inj₁ (inj₁ α)) = inj₁ (inj₁ (vA α))
  wdₒ vA (inj₁ (inj₂ β)) = inj₁ (inj₂ β)
  wdₒ vA (inj₂ y)        = inj₂ y

private
  mapᴹ-idᵖ : ∀ {X : Type} (o : Maybe X) → mapᴹ (λ x → x) o ≡ o
  mapᴹ-idᵖ (just _) = refl
  mapᴹ-idᵖ nothing  = refl

Reindex-id : ∀ {A B} (M : Machine A B)
           → Reindex M (λ i → i) (λ o → o) ≅ᴹ M
Reindex-id M = MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl)
  (λ {_} {_} {o} x → subst (λ y → Machine.stepRel M _ _ y _) (mapᴹ-idᵖ o) x)
  (λ {_} {_} {o} x → subst (λ y → Machine.stepRel M _ _ y _) (sym (mapᴹ-idᵖ o)) x)
