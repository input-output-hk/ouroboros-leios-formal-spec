{-# OPTIONS --safe #-}

-- ============================================================================
-- A forwarder is a relabelled identity.
--
-- `Leios.ChannelCat.Fwd` shows that forwarders are closed under the machine
-- builders, and `Leios.ChannelCat.Interchange` pushes every channel reshuffle
-- into `Reindex`.  Put together, the two say something sharper than either:
-- a stateless machine carries no information beyond the relabelling it applies
-- to its messages, so up to `≅ᴹ` there is only ONE forwarder per channel pair,
-- namely `CC.id` seen through a change of coordinates.
--
-- `Reindex-Fwd` is the general statement — reindexing a forwarder gives a
-- forwarder, as soon as the output relabelling is injective (the same side
-- condition `modifyStepRel-Fwd` needs, and for the same reason: a `nothing`
-- output must stay distinguishable from a `just`).  `Xfwd-dom` and `Xfwd-cod`
-- are the two ways to read a crossing forwarder `Xfwd f g : Machine A B` as a
-- reindexed identity: either fix the codomain and relabel the domain, or fix
-- the domain and relabel the codomain.  Each orientation gets to keep only one
-- of `f`, `g` verbatim, and so needs the other to be invertible — a crossing
-- forwarder with a non-invertible backward map is genuinely not `CC.id` in
-- disguise.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import Leios.ChannelCat.Fwd
open import Leios.ChannelCat.Interchange
open import Leios.ChannelCat.Slide
open import Tactic.Defaults

module Leios.ChannelCat.FwdId where

open _≅ᴹ_

private
  just-injᴵ : ∀ {a} {X : Type a} {x y : X} → just x ≡ just y → x ≡ y
  just-injᴵ refl = refl

  inj₁-injᴵ : ∀ {a b} {X : Type a} {Y : Type b} {x y : X}
            → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y) → x ≡ y
  inj₁-injᴵ refl = refl

  inj₂-injᴵ : ∀ {a b} {X : Type a} {Y : Type b} {x y : Y}
            → _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y) → x ≡ y
  inj₂-injᴵ refl = refl

  inj₁≢inj₂ᴵ : ∀ {a b} {X : Type a} {Y : Type b} {x : X} {y : Y} {ℓ} {W : Type ℓ}
             → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
  inj₁≢inj₂ᴵ ()

-- Reindexing a forwarder is a forwarder.  Stated with `χ`, `κ`, `u` and `v`
-- all explicit: `Reindex` is a function, so nothing here can be recovered by
-- unification from the goal.
Reindex-Fwd : ∀ {A B C D} (χ : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B))
                          (κ : Channel.inType (C ⊗ᵀ D) → Channel.outType (C ⊗ᵀ D))
              (u : Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
              (v : Channel.outType (C ⊗ᵀ D) → Channel.outType (A ⊗ᵀ B))
            → (∀ i → v (κ i) ≡ χ (u i))
            → (∀ {x y} → v x ≡ v y → x ≡ y)
            → Reindex (Fwd χ) u v ≅ᴹ Fwd κ
Reindex-Fwd {A} {B} {C} {D} χ κ u v sq inj =
  MkIso _ _ (λ _ → refl) (λ _ → refl)
    (λ {_} {i} {o} e → t i o e) (λ {_} {i} {o} e → f i o e)
  where
  t : (i : Channel.inType (C ⊗ᵀ D)) (o : Maybe (Channel.outType (C ⊗ᵀ D)))
    → just (χ (u i)) ≡ mapᴹ v o → just (κ i) ≡ o
  t i (just y)  e = cong just (inj (trans (sq i) (just-injᴵ e)))
  t i nothing  ()
  f : (i : Channel.inType (C ⊗ᵀ D)) (o : Maybe (Channel.outType (C ⊗ᵀ D)))
    → just (κ i) ≡ o → just (χ (u i)) ≡ mapᴹ v o
  f i _ refl = cong just (sym (sq i))

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ Xφ dmᵢ dmₒ cdᵢ cdₒ

  private
    -- The relay `CC.id` forwards, named at a fixed channel; `id-is-Xfwd`
    -- identifies `CC.id {X}` with `Fwd (relay {X})`.
    relay : ∀ {X} → Channel.inType (X ⊗ᵀ X) → Channel.outType (X ⊗ᵀ X)
    relay {X} = Xφ (λ (x : Channel.inType X) → x) (λ (x : Channel.outType X) → x)

    -- A map with a right inverse is injective; this is what turns the
    -- surjectivity halves of the hypotheses below into `Reindex-Fwd`'s side
    -- condition.
    right-inv-inj : ∀ {X Y : Type} (h : X → Y) (k : Y → X)
                  → (∀ x → k (h x) ≡ x) → ∀ {x y} → h x ≡ h y → x ≡ y
    right-inv-inj h k ri e = trans (sym (ri _)) (trans (cong k e) (ri _))

  -- Fixing the codomain `B` and relabelling the domain `A` keeps `f` verbatim,
  -- so it is `g` that must be invertible.
  Xfwd-dom : ∀ {A B} (f : Channel.inType A → Channel.inType B)
                     (g : Channel.outType B → Channel.outType A)
                     (g⁻ : Channel.outType A → Channel.outType B)
           → (∀ β → g⁻ (g β) ≡ β) → (∀ α → g (g⁻ α) ≡ α)
           → Xfwd f g ≅ᴹ Reindex (CC.id {B}) (dmᵢ f) (dmₒ g⁻)
  Xfwd-dom {A} {B} f g g⁻ gl gr =
    ≅ᴹ-trans
      (≅ᴹ-sym (Reindex-Fwd (relay {B}) (Xφ f g)
                           (dmᵢ {B} {A} {B} f) (dmₒ {B} {A} {B} g⁻) sq inj))
      (Reindex-resp-≅ᴹ (dmᵢ {B} {A} {B} f) (dmₒ {B} {A} {B} g⁻) (≅ᴹ-sym id-is-Xfwd))
    where
    sq : ∀ i → dmₒ {B} {A} {B} g⁻ (Xφ f g i) ≡ relay {B} (dmᵢ {B} {A} {B} f i)
    sq (inj₁ a) = refl
    sq (inj₂ β) = cong inj₁ (gl β)
    inj : ∀ {x y} → dmₒ {B} {A} {B} g⁻ x ≡ dmₒ {B} {A} {B} g⁻ y → x ≡ y
    inj {inj₁ _} {inj₁ _} e =
      cong inj₁ (right-inv-inj g⁻ g gr (inj₁-injᴵ e))
    inj {inj₂ _} {inj₂ _} e = cong inj₂ (inj₂-injᴵ e)
    inj {inj₁ _} {inj₂ _} e = inj₁≢inj₂ᴵ e
    inj {inj₂ _} {inj₁ _} e = inj₁≢inj₂ᴵ (sym e)

  -- The mirror image: fixing the domain `A` keeps `g` verbatim and asks `f` to
  -- be invertible instead.
  Xfwd-cod : ∀ {A B} (f : Channel.inType A → Channel.inType B)
                     (g : Channel.outType B → Channel.outType A)
                     (f⁻ : Channel.inType B → Channel.inType A)
           → (∀ a → f⁻ (f a) ≡ a) → (∀ b → f (f⁻ b) ≡ b)
           → Xfwd f g ≅ᴹ Reindex (CC.id {A}) (cdᵢ g) (cdₒ f⁻)
  Xfwd-cod {A} {B} f g f⁻ fl fr =
    ≅ᴹ-trans
      (≅ᴹ-sym (Reindex-Fwd (relay {A}) (Xφ f g)
                           (cdᵢ {A} {A} {B} g) (cdₒ {A} {A} {B} f⁻) sq inj))
      (Reindex-resp-≅ᴹ (cdᵢ {A} {A} {B} g) (cdₒ {A} {A} {B} f⁻) (≅ᴹ-sym id-is-Xfwd))
    where
    sq : ∀ i → cdₒ {A} {A} {B} f⁻ (Xφ f g i) ≡ relay {A} (cdᵢ {A} {A} {B} g i)
    sq (inj₁ a) = cong inj₂ (fl a)
    sq (inj₂ β) = refl
    inj : ∀ {x y} → cdₒ {A} {A} {B} f⁻ x ≡ cdₒ {A} {A} {B} f⁻ y → x ≡ y
    inj {inj₁ _} {inj₁ _} e = cong inj₁ (inj₁-injᴵ e)
    inj {inj₂ _} {inj₂ _} e =
      cong inj₂ (right-inv-inj f⁻ f fr (inj₂-injᴵ e))
    inj {inj₁ _} {inj₂ _} e = inj₁≢inj₂ᴵ e
    inj {inj₂ _} {inj₁ _} e = inj₁≢inj₂ᴵ (sym e)
