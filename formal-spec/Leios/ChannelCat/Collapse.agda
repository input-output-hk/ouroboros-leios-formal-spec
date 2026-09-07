{-# OPTIONS --safe #-}

-- ============================================================================
-- A relabelling of the OUTER side of one argument of `_∘_` slides out of the
-- composition.
--
-- `Leios.ChannelCat.Slide` reduced `_∘_` to `Reindex`/`Pair`/`Trc` and showed
-- that a relabelling fixing the traced channel commutes with `Trc`.  Both
-- lemmas here are that fact applied twice over: `∘-Reindex` turns each side
-- into the same `Trc` of the same `Pair`, the relabelling is pushed through
-- `Pair` by `Pair-Reindex` and through `Trc` by `Trc-slide`, and what is left
-- is two pointwise equations between composites of channel permutations.
--
-- These are what let a forwarder be absorbed into its neighbour, which is how
-- the naturality and Kleisli laws of `Leios.ChannelCat.Monoidal` are
-- discharged.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import Leios.ChannelCat.Interchange
open import Leios.ChannelCat.Slide
open import Tactic.Defaults

module Leios.ChannelCat.Collapse where

open _≅ᴹ_

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ ∘κᵢ cdᵢ

  -- ------------------------------------------------------------------------
  -- The codomain case.
  -- ------------------------------------------------------------------------

  -- Inside the `Pair`, relabelling `N`'s codomain is a sum map; at the traced
  -- machine's channel it is `wcᵢ`/`wcₒ`.  These two lemmas say the routing is
  -- the same either way, which is the only thing `∘κ` contributes.
  cod-routeᵢ : ∀ {A B C C'} (uC : Channel.outType C' → Channel.outType C)
               (i : Channel.inType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)))
             → ⊎ᵢ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdᵢ {B} {C} {C'} uC)
                 (∘κᵢ {A} {B} {C'} i)
               ≡ ∘κᵢ {A} {B} {C} (wcᵢ {A} {B} {C} {C'} uC i)
  cod-routeᵢ uC (inj₁ (inj₁ _)) = refl
  cod-routeᵢ uC (inj₁ (inj₂ _)) = refl
  cod-routeᵢ uC (inj₂ (inj₁ _)) = refl
  cod-routeᵢ uC (inj₂ (inj₂ _)) = refl

  cod-routeₒ : ∀ {A B C C'} (vC : Channel.inType C' → Channel.inType C)
               (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)))
             → ⊎ₒ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdₒ {B} {C} {C'} vC)
                 (∘κₒ {A} {B} {C'} o)
               ≡ ∘κₒ {A} {B} {C} (wcₒ {A} {B} {C} {C'} vC o)
  cod-routeₒ vC (inj₁ (inj₁ _)) = refl
  cod-routeₒ vC (inj₁ (inj₂ _)) = refl
  cod-routeₒ vC (inj₂ (inj₁ _)) = refl
  cod-routeₒ vC (inj₂ (inj₂ _)) = refl

  -- Sliding the relabelling out of the `Pair`.  The identity on `M`'s half has
  -- to be introduced explicitly, because `Pair-Reindex` only speaks about a
  -- `Pair` of two `Reindex`es.
  cod-pairR : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
              (uC : Channel.outType C' → Channel.outType C)
              (vC : Channel.inType C' → Channel.inType C)
            → Pair M (Reindex N (cdᵢ {B} {C} {C'} uC) (cdₒ {B} {C} {C'} vC))
              ≅ᴹ Reindex (Pair M N)
                   (⊎ᵢ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdᵢ {B} {C} {C'} uC))
                   (⊎ₒ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdₒ {B} {C} {C'} vC))
  cod-pairR {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (Pair-resp-≅ᴹ (≅ᴹ-sym (Reindex-id M)) ≅ᴹ-refl)
             (Pair-Reindex M N (λ x → x) (λ x → x)
                           (cdᵢ {B} {C} {C'} uC) (cdₒ {B} {C} {C'} vC))

  -- The composite of the two relabellings on the inner machine, refactored so
  -- that the outer one is `wcᵢ`/`wcₒ` — the form `Trc-slide` accepts.
  cod-inner : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
              (uC : Channel.outType C' → Channel.outType C)
              (vC : Channel.inType C' → Channel.inType C)
            → Reindex (Pair M (Reindex N (cdᵢ {B} {C} {C'} uC) (cdₒ {B} {C} {C'} vC)))
                      (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'})
              ≅ᴹ Reindex (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C}))
                         (wcᵢ {A} {B} {C} {C'} uC) (wcₒ {A} {B} {C} {C'} vC)
  cod-inner {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'})
                              (cod-pairR M N uC vC))
    (≅ᴹ-trans (Reindex-fuse (Pair M N)
                 (⊎ᵢ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdᵢ {B} {C} {C'} uC))
                 (⊎ₒ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdₒ {B} {C} {C'} vC))
                 (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'}))
    (≅ᴹ-trans (Reindex-cong (Pair M N)
                 (λ i → ⊎ᵢ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x)
                           (cdᵢ {B} {C} {C'} uC) (∘κᵢ {A} {B} {C'} i))
                 (λ i → ∘κᵢ {A} {B} {C} (wcᵢ {A} {B} {C} {C'} uC i))
                 (λ o → ⊎ₒ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x)
                           (cdₒ {B} {C} {C'} vC) (∘κₒ {A} {B} {C'} o))
                 (λ o → ∘κₒ {A} {B} {C} (wcₒ {A} {B} {C} {C'} vC o))
                 (cod-routeᵢ {A} {B} {C} {C'} uC) (cod-routeₒ {A} {B} {C} {C'} vC))
              (≅ᴹ-sym (Reindex-fuse (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})
                         (wcᵢ {A} {B} {C} {C'} uC) (wcₒ {A} {B} {C} {C'} vC)))))

  -- `wcᵢ`/`wcₒ` fix the traced channel `B` — that is the whole point of their
  -- definition — so the four hypotheses of `Trc-slide` are all `refl`.
  cod-trc : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
            (uC : Channel.outType C' → Channel.outType C)
            (vC : Channel.inType C' → Channel.inType C)
          → Trc (Reindex (Pair M (Reindex N (cdᵢ {B} {C} {C'} uC) (cdₒ {B} {C} {C'} vC)))
                         (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'}))
            ≅ᴹ Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                       (wcᵢ {A} {B} {C} {C'} uC) (wcₒ {A} {B} {C} {C'} vC)
  cod-trc {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (Trc-resp-≅ᴹ (cod-inner M N uC vC))
             (Trc-slide (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C}))
                        (wcᵢ {A} {B} {C} {C'} uC) (wcₒ {A} {B} {C} {C'} vC)
                        (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl))

  -- Past the trace, `wcᵢ ∘ tιᵢ` is `tιᵢ ∘ cdᵢ`: the relabelling only ever sees
  -- the external ports, which is where `cdᵢ` acts.
  cod-outᵢ : ∀ {A B C C'} (uC : Channel.outType C' → Channel.outType C)
             (i : Channel.inType (A ⊗ᵀ C'))
           → wcᵢ {A} {B} {C} {C'} uC (tιᵢ {A} {C'} {B} i)
             ≡ tιᵢ {A} {C} {B} (cdᵢ {A} {C} {C'} uC i)
  cod-outᵢ uC (inj₁ _) = refl
  cod-outᵢ uC (inj₂ _) = refl

  cod-outₒ : ∀ {A B C C'} (vC : Channel.inType C' → Channel.inType C)
             (o : Channel.outType (A ⊗ᵀ C'))
           → wcₒ {A} {B} {C} {C'} vC (tιₒ {A} {C'} {B} o)
             ≡ tιₒ {A} {C} {B} (cdₒ {A} {C} {C'} vC o)
  cod-outₒ vC (inj₁ _) = refl
  cod-outₒ vC (inj₂ _) = refl

  -- Refactor the outer relabelling so that `cdᵢ`/`cdₒ` sit outermost, ready to
  -- be split off by `Reindex-fuse`.
  cod-outer : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
              (uC : Channel.outType C' → Channel.outType C)
              (vC : Channel.inType C' → Channel.inType C)
            → Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                      (λ i → wcᵢ {A} {B} {C} {C'} uC (tιᵢ {A} {C'} {B} i))
                      (λ o → wcₒ {A} {B} {C} {C'} vC (tιₒ {A} {C'} {B} o))
              ≅ᴹ Reindex (Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                                  (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B}))
                         (cdᵢ {A} {C} {C'} uC) (cdₒ {A} {C} {C'} vC)
  cod-outer {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (Reindex-cong (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                (λ i → wcᵢ {A} {B} {C} {C'} uC (tιᵢ {A} {C'} {B} i))
                (λ i → tιᵢ {A} {C} {B} (cdᵢ {A} {C} {C'} uC i))
                (λ o → wcₒ {A} {B} {C} {C'} vC (tιₒ {A} {C'} {B} o))
                (λ o → tιₒ {A} {C} {B} (cdₒ {A} {C} {C'} vC o))
                (cod-outᵢ {A} {B} {C} {C'} uC) (cod-outₒ {A} {B} {C} {C'} vC))
             (≅ᴹ-sym (Reindex-fuse
                        (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                        (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
                        (cdᵢ {A} {C} {C'} uC) (cdₒ {A} {C} {C'} vC)))

  ∘-collapse-cod : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
                   (uC : Channel.outType C' → Channel.outType C)
                   (vC : Channel.inType C' → Channel.inType C)
                 → ((Reindex N (cdᵢ {B} {C} {C'} uC) (cdₒ {B} {C} {C'} vC)) CC.∘ M)
                   ≅ᴹ Reindex (N CC.∘ M) (cdᵢ {A} {C} {C'} uC) (cdₒ {A} {C} {C'} vC)
  ∘-collapse-cod {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (∘-Reindex M (Reindex N (cdᵢ {B} {C} {C'} uC) (cdₒ {B} {C} {C'} vC)))
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (tιᵢ {A} {C'} {B}) (tιₒ {A} {C'} {B})
                               (cod-trc M N uC vC))
    (≅ᴹ-trans (Reindex-fuse
                 (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                 (wcᵢ {A} {B} {C} {C'} uC) (wcₒ {A} {B} {C} {C'} vC)
                 (tιᵢ {A} {C'} {B}) (tιₒ {A} {C'} {B}))
    (≅ᴹ-trans (cod-outer M N uC vC)
              (Reindex-resp-≅ᴹ (cdᵢ {A} {C} {C'} uC) (cdₒ {A} {C} {C'} vC)
                               (≅ᴹ-sym (∘-Reindex M N))))))

  -- ------------------------------------------------------------------------
  -- The domain case.  Mirror image of the above: the relabelling is on `M`'s
  -- domain rather than `N`'s codomain, so `wdᵢ`/`wdₒ` and `dmᵢ`/`dmₒ` take
  -- over from `wcᵢ`/`wcₒ` and `cdᵢ`/`cdₒ`.  The traced channel is `B` either
  -- way, which is why the same `Trc-slide` closes both.
  -- ------------------------------------------------------------------------

  dom-routeᵢ : ∀ {A A' B C} (uA : Channel.inType A' → Channel.inType A)
               (i : Channel.inType ((A' ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
             → ⊎ᵢ {A} {B} {B} {C} {A'} {B} {B} {C} (dmᵢ {A} {A'} {B} uA) (λ x → x)
                 (∘κᵢ {A'} {B} {C} i)
               ≡ ∘κᵢ {A} {B} {C} (wdᵢ {A} {A'} {B} {C} uA i)
  dom-routeᵢ uA (inj₁ (inj₁ _)) = refl
  dom-routeᵢ uA (inj₁ (inj₂ _)) = refl
  dom-routeᵢ uA (inj₂ (inj₁ _)) = refl
  dom-routeᵢ uA (inj₂ (inj₂ _)) = refl

  dom-routeₒ : ∀ {A A' B C} (vA : Channel.outType A' → Channel.outType A)
               (o : Channel.outType ((A' ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
             → ⊎ₒ {A} {B} {B} {C} {A'} {B} {B} {C} (dmₒ {A} {A'} {B} vA) (λ x → x)
                 (∘κₒ {A'} {B} {C} o)
               ≡ ∘κₒ {A} {B} {C} (wdₒ {A} {A'} {B} {C} vA o)
  dom-routeₒ vA (inj₁ (inj₁ _)) = refl
  dom-routeₒ vA (inj₁ (inj₂ _)) = refl
  dom-routeₒ vA (inj₂ (inj₁ _)) = refl
  dom-routeₒ vA (inj₂ (inj₂ _)) = refl

  dom-pairR : ∀ {A A' B C} (M : Machine A B) (N : Machine B C)
              (uA : Channel.inType A' → Channel.inType A)
              (vA : Channel.outType A' → Channel.outType A)
            → Pair (Reindex M (dmᵢ {A} {A'} {B} uA) (dmₒ {A} {A'} {B} vA)) N
              ≅ᴹ Reindex (Pair M N)
                   (⊎ᵢ {A} {B} {B} {C} {A'} {B} {B} {C} (dmᵢ {A} {A'} {B} uA) (λ x → x))
                   (⊎ₒ {A} {B} {B} {C} {A'} {B} {B} {C} (dmₒ {A} {A'} {B} vA) (λ x → x))
  dom-pairR {A} {A'} {B} {C} M N uA vA =
    ≅ᴹ-trans (Pair-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym (Reindex-id N)))
             (Pair-Reindex M N (dmᵢ {A} {A'} {B} uA) (dmₒ {A} {A'} {B} vA)
                           (λ x → x) (λ x → x))

  dom-inner : ∀ {A A' B C} (M : Machine A B) (N : Machine B C)
              (uA : Channel.inType A' → Channel.inType A)
              (vA : Channel.outType A' → Channel.outType A)
            → Reindex (Pair (Reindex M (dmᵢ {A} {A'} {B} uA) (dmₒ {A} {A'} {B} vA)) N)
                      (∘κᵢ {A'} {B} {C}) (∘κₒ {A'} {B} {C})
              ≅ᴹ Reindex (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C}))
                         (wdᵢ {A} {A'} {B} {C} uA) (wdₒ {A} {A'} {B} {C} vA)
  dom-inner {A} {A'} {B} {C} M N uA vA =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (∘κᵢ {A'} {B} {C}) (∘κₒ {A'} {B} {C})
                              (dom-pairR M N uA vA))
    (≅ᴹ-trans (Reindex-fuse (Pair M N)
                 (⊎ᵢ {A} {B} {B} {C} {A'} {B} {B} {C} (dmᵢ {A} {A'} {B} uA) (λ x → x))
                 (⊎ₒ {A} {B} {B} {C} {A'} {B} {B} {C} (dmₒ {A} {A'} {B} vA) (λ x → x))
                 (∘κᵢ {A'} {B} {C}) (∘κₒ {A'} {B} {C}))
    (≅ᴹ-trans (Reindex-cong (Pair M N)
                 (λ i → ⊎ᵢ {A} {B} {B} {C} {A'} {B} {B} {C} (dmᵢ {A} {A'} {B} uA)
                           (λ x → x) (∘κᵢ {A'} {B} {C} i))
                 (λ i → ∘κᵢ {A} {B} {C} (wdᵢ {A} {A'} {B} {C} uA i))
                 (λ o → ⊎ₒ {A} {B} {B} {C} {A'} {B} {B} {C} (dmₒ {A} {A'} {B} vA)
                           (λ x → x) (∘κₒ {A'} {B} {C} o))
                 (λ o → ∘κₒ {A} {B} {C} (wdₒ {A} {A'} {B} {C} vA o))
                 (dom-routeᵢ {A} {A'} {B} {C} uA) (dom-routeₒ {A} {A'} {B} {C} vA))
              (≅ᴹ-sym (Reindex-fuse (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})
                         (wdᵢ {A} {A'} {B} {C} uA) (wdₒ {A} {A'} {B} {C} vA)))))

  dom-trc : ∀ {A A' B C} (M : Machine A B) (N : Machine B C)
            (uA : Channel.inType A' → Channel.inType A)
            (vA : Channel.outType A' → Channel.outType A)
          → Trc (Reindex (Pair (Reindex M (dmᵢ {A} {A'} {B} uA) (dmₒ {A} {A'} {B} vA)) N)
                         (∘κᵢ {A'} {B} {C}) (∘κₒ {A'} {B} {C}))
            ≅ᴹ Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                       (wdᵢ {A} {A'} {B} {C} uA) (wdₒ {A} {A'} {B} {C} vA)
  dom-trc {A} {A'} {B} {C} M N uA vA =
    ≅ᴹ-trans (Trc-resp-≅ᴹ (dom-inner M N uA vA))
             (Trc-slide (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C}))
                        (wdᵢ {A} {A'} {B} {C} uA) (wdₒ {A} {A'} {B} {C} vA)
                        (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl))

  dom-outᵢ : ∀ {A A' B C} (uA : Channel.inType A' → Channel.inType A)
             (i : Channel.inType (A' ⊗ᵀ C))
           → wdᵢ {A} {A'} {B} {C} uA (tιᵢ {A'} {C} {B} i)
             ≡ tιᵢ {A} {C} {B} (dmᵢ {A} {A'} {C} uA i)
  dom-outᵢ uA (inj₁ _) = refl
  dom-outᵢ uA (inj₂ _) = refl

  dom-outₒ : ∀ {A A' B C} (vA : Channel.outType A' → Channel.outType A)
             (o : Channel.outType (A' ⊗ᵀ C))
           → wdₒ {A} {A'} {B} {C} vA (tιₒ {A'} {C} {B} o)
             ≡ tιₒ {A} {C} {B} (dmₒ {A} {A'} {C} vA o)
  dom-outₒ vA (inj₁ _) = refl
  dom-outₒ vA (inj₂ _) = refl

  dom-outer : ∀ {A A' B C} (M : Machine A B) (N : Machine B C)
              (uA : Channel.inType A' → Channel.inType A)
              (vA : Channel.outType A' → Channel.outType A)
            → Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                      (λ i → wdᵢ {A} {A'} {B} {C} uA (tιᵢ {A'} {C} {B} i))
                      (λ o → wdₒ {A} {A'} {B} {C} vA (tιₒ {A'} {C} {B} o))
              ≅ᴹ Reindex (Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                                  (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B}))
                         (dmᵢ {A} {A'} {C} uA) (dmₒ {A} {A'} {C} vA)
  dom-outer {A} {A'} {B} {C} M N uA vA =
    ≅ᴹ-trans (Reindex-cong (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                (λ i → wdᵢ {A} {A'} {B} {C} uA (tιᵢ {A'} {C} {B} i))
                (λ i → tιᵢ {A} {C} {B} (dmᵢ {A} {A'} {C} uA i))
                (λ o → wdₒ {A} {A'} {B} {C} vA (tιₒ {A'} {C} {B} o))
                (λ o → tιₒ {A} {C} {B} (dmₒ {A} {A'} {C} vA o))
                (dom-outᵢ {A} {A'} {B} {C} uA) (dom-outₒ {A} {A'} {B} {C} vA))
             (≅ᴹ-sym (Reindex-fuse
                        (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                        (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
                        (dmᵢ {A} {A'} {C} uA) (dmₒ {A} {A'} {C} vA)))

  ∘-collapse-dom : ∀ {A A' B C} (M : Machine A B) (N : Machine B C)
                   (uA : Channel.inType A' → Channel.inType A)
                   (vA : Channel.outType A' → Channel.outType A)
                 → (N CC.∘ (Reindex M (dmᵢ {A} {A'} {B} uA) (dmₒ {A} {A'} {B} vA)))
                   ≅ᴹ Reindex (N CC.∘ M) (dmᵢ {A} {A'} {C} uA) (dmₒ {A} {A'} {C} vA)
  ∘-collapse-dom {A} {A'} {B} {C} M N uA vA =
    ≅ᴹ-trans (∘-Reindex (Reindex M (dmᵢ {A} {A'} {B} uA) (dmₒ {A} {A'} {B} vA)) N)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (tιᵢ {A'} {C} {B}) (tιₒ {A'} {C} {B})
                               (dom-trc M N uA vA))
    (≅ᴹ-trans (Reindex-fuse
                 (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                 (wdᵢ {A} {A'} {B} {C} uA) (wdₒ {A} {A'} {B} {C} vA)
                 (tιᵢ {A'} {C} {B}) (tιₒ {A'} {C} {B}))
    (≅ᴹ-trans (dom-outer M N uA vA)
              (Reindex-resp-≅ᴹ (dmᵢ {A} {A'} {C} uA) (dmₒ {A} {A'} {C} vA)
                               (≅ᴹ-sym (∘-Reindex M N))))))
