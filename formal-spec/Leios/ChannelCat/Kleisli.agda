{-# OPTIONS --safe #-}

-- ============================================================================
-- The two Kleisli laws of `Leios.ChannelCat.Monoidal`, derived: `_∘ᴷ_`
-- associates, and `_⊗ᴷ_` and `_∘ᴷ_` interchange.
--
-- Both laws say the same thing twice: `_∘ᴷ_` and `_⊗ᴷ_` are `_∘_` and `_⊗₁_`
-- followed by a fixed stateless shuffle, so an equation between two Kleisli
-- composites is an equation between two ordinary composites in which the
-- abstract machines occur in the SAME order on both sides and only the
-- shuffles differ.  Getting there takes three moves:
--
--   * `⊗ʳ-∘` distributes `_⊗ʳ E` over a composition, which is what turns the
--     right-hand sides — where a Kleisli composite is itself tensored with an
--     environment — into a flat composite;
--   * `∘-assoc-≅ᴹ` re-brackets everything to the right, so that both sides
--     share a common suffix and `∘-resp-≅ᴹ` reduces the goal to the heads;
--   * the two naturality laws of the shuffles move the abstract machines
--     across them, leaving heads that are composites of forwarders only.
--
-- A head equation is then a finite message-level computation: `Fwd`'s algebra
-- collapses each side to a single `Xfwd` and `Xfwd-≅ᴹ` compares the two
-- routings pointwise.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.IsoExt using (⊗₁-resp-≅ᴹ)
open import CategoricalCrypto.Machine.Iso
  using (_≅ᴹ_; ≅ᴹ-refl; ≅ᴹ-sym; ≅ᴹ-trans; ∘-resp-≅ᴹ; ∘-assoc-≅ᴹ;
         ∘-identityˡ-≅ᴹ)
open import Leios.ChannelCat using (absorb-regroup; mid4)
open import Leios.ChannelCat.Fwd
  using (∘ᴷ-fwd; ⊗ᴷ-fwd; ⊗₁-id; ∘-Xfwd; ⊗₁-Xfwd; Xfwd-≅ᴹ; Xφ; Xfwd; ⊗mapᵢ; ⊗mapₒ;
         tfm'-is-Xfwd; id-is-Xfwd; ∘ᴷ-fwdᵢ; ∘ᴷ-fwdₒ)
open import Leios.ChannelCat.Interchange using (⊗₁-interchange)
open import Leios.ChannelCat.Naturality using (∘ᴷ-fwd-natural; ⊗ᴷ-fwd-natural; ⊗ᴷ-fwdᵢ; ⊗ᴷ-fwdₒ)
open import Tactic.Defaults

module Leios.ChannelCat.Kleisli where

-- ----------------------------------------------------------------------------
-- Tensoring with an identity distributes over composition.  This is the only
-- place `⊗₁-interchange` is needed in the shape `_⊗ʳ E`; the `CC.id` has to be
-- seen as `CC.id CC.∘ CC.id` first, which is what the unitor does.
-- ----------------------------------------------------------------------------

⊗ʳ-∘ : ∀ {A B C E} (X : Machine B C) (Y : Machine A B)
     → ((X CC.∘ Y) ⊗₁ CC.id {E}) ≅ᴹ ((X ⊗₁ CC.id {E}) CC.∘ (Y ⊗₁ CC.id {E}))
⊗ʳ-∘ X Y = ≅ᴹ-trans (⊗₁-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-identityˡ-≅ᴹ))
                    (⊗₁-interchange Y X CC.id CC.id)

-- ----------------------------------------------------------------------------
-- The head equations.  Both sides are composites of forwarders, so `Fwd`'s
-- algebra collapses each to a single `Xfwd` and what remains is a pointwise
-- equation between two routings of the same channel atoms.  Each of those
-- routings is the atom-preserving bijection between the two channel
-- bracketings, and there is only one, which is why every case is `refl`.
-- These computations are what needs the `unfolding`: `app` of a `⇒-solver`
-- term does not reduce until `_⊗₀_` does, and `⊗mapᵢ`/`⊗mapₒ` sit inside
-- `Leios.ChannelCat.Fwd`'s own `opaque` block, which `Xφ` opens.
-- ----------------------------------------------------------------------------

-- The `⇒-solver` halves of `mid4` and `absorb-regroup`, named.  The solver is
-- deterministic, so the `-named` lemmas hold by `refl`.  The head lemmas below
-- pass these by name rather than letting unification fill in the solver terms.
mid4σᵢ : ∀ {P Q R S} → ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) [ In ]⇒[ In ] ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
mid4σᵢ = ⇒-solver

mid4σₒ : ∀ {P Q R S} → ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S)) [ Out ]⇒[ Out ] ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S))
mid4σₒ = ⇒-solver

mid4-named : ∀ {P Q R S} → mid4 {P} {Q} {R} {S} ≡ TotalFunctionMachine' mid4σᵢ mid4σₒ
mid4-named = refl

absorb-regroupσᵢ : ∀ {X Y Z W} → ((X ⊗₀ Y) ⊗₀ (W ⊗₀ Z)) [ In ]⇒[ In ] (X ⊗₀ (W ⊗₀ (Z ⊗₀ Y)))
absorb-regroupσᵢ = ⇒-solver

absorb-regroupσₒ : ∀ {X Y Z W} → (X ⊗₀ (W ⊗₀ (Z ⊗₀ Y))) [ Out ]⇒[ Out ] ((X ⊗₀ Y) ⊗₀ (W ⊗₀ Z))
absorb-regroupσₒ = ⇒-solver

absorb-regroup-named : ∀ {X Y Z W}
  → absorb-regroup {X} {Y} {Z} {W} ≡ TotalFunctionMachine' absorb-regroupσᵢ absorb-regroupσₒ
absorb-regroup-named = refl

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
            ⊗-combine Xφ

  head₁ : ∀ {D E E₁ E₂}
        → (absorb-regroup {D} {E₂} {E₁} {E} CC.∘ ∘ᴷ-fwd {D ⊗₀ E₂} {E} {E₁})
          ≅ᴹ (∘ᴷ-fwd {D} {E} {E₁ ⊗₀ E₂}
              CC.∘ (∘ᴷ-fwd {D} {E₁} {E₂} ⊗₁ CC.id {E}))
  head₁ {D} {E} {E₁} {E₂} =
    ≅ᴹ-trans {M₂ = Xfwd (λ a → (app (absorb-regroupσᵢ {D} {E₂} {E₁} {E})) ((app (∘ᴷ-fwdᵢ {D ⊗₀ E₂} {E} {E₁})) a)) (λ o → (app (∘ᴷ-fwdₒ {D ⊗₀ E₂} {E} {E₁})) ((app (absorb-regroupσₒ {D} {E₂} {E₁} {E})) o))} L (≅ᴹ-trans {M₂ = Xfwd (λ a → (app (∘ᴷ-fwdᵢ {D} {E} {E₁ ⊗₀ E₂})) (⊗mapᵢ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdᵢ {D} {E₁} {E₂})) (λ (x : Channel.inType E) → x) a)) (λ o → ⊗mapₒ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdₒ {D} {E₁} {E₂})) (λ (x : Channel.outType E) → x) ((app (∘ᴷ-fwdₒ {D} {E} {E₁ ⊗₀ E₂})) o))} P (≅ᴹ-sym R))
    where
    -- Named, typed steps, for the same reason as in `head₂` below.
    L : (absorb-regroup {D} {E₂} {E₁} {E} CC.∘ ∘ᴷ-fwd {D ⊗₀ E₂} {E} {E₁}) ≅ᴹ Xfwd (λ a → (app (absorb-regroupσᵢ {D} {E₂} {E₁} {E})) ((app (∘ᴷ-fwdᵢ {D ⊗₀ E₂} {E} {E₁})) a)) (λ o → (app (∘ᴷ-fwdₒ {D ⊗₀ E₂} {E} {E₁})) ((app (absorb-regroupσₒ {D} {E₂} {E₁} {E})) o))
    L = ≅ᴹ-trans (∘-resp-≅ᴹ (tfm'-is-Xfwd (absorb-regroupσᵢ {D} {E₂} {E₁} {E})
                                          (absorb-regroupσₒ {D} {E₂} {E₁} {E}))
                            (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {D ⊗₀ E₂} {E} {E₁}) (∘ᴷ-fwdₒ {D ⊗₀ E₂} {E} {E₁})))
                 ∘-Xfwd

    r₁ : (∘ᴷ-fwd {D} {E₁} {E₂} ⊗₁ CC.id {E}) ≅ᴹ Xfwd (⊗mapᵢ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdᵢ {D} {E₁} {E₂})) (λ (x : Channel.inType E) → x)) (⊗mapₒ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdₒ {D} {E₁} {E₂})) (λ (x : Channel.outType E) → x))
    r₁ = ≅ᴹ-trans (⊗₁-resp-≅ᴹ (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {D} {E₁} {E₂}) (∘ᴷ-fwdₒ {D} {E₁} {E₂}))
                              id-is-Xfwd)
                  ⊗₁-Xfwd

    R : (∘ᴷ-fwd {D} {E} {E₁ ⊗₀ E₂} CC.∘ (∘ᴷ-fwd {D} {E₁} {E₂} ⊗₁ CC.id {E})) ≅ᴹ Xfwd (λ a → (app (∘ᴷ-fwdᵢ {D} {E} {E₁ ⊗₀ E₂})) (⊗mapᵢ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdᵢ {D} {E₁} {E₂})) (λ (x : Channel.inType E) → x) a)) (λ o → ⊗mapₒ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdₒ {D} {E₁} {E₂})) (λ (x : Channel.outType E) → x) ((app (∘ᴷ-fwdₒ {D} {E} {E₁ ⊗₀ E₂})) o))
    R = ≅ᴹ-trans (∘-resp-≅ᴹ (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {D} {E} {E₁ ⊗₀ E₂}) (∘ᴷ-fwdₒ {D} {E} {E₁ ⊗₀ E₂}))
                            r₁)
                 ∘-Xfwd

    -- The two routings agree pointwise.
    P : Xfwd (λ a → (app (absorb-regroupσᵢ {D} {E₂} {E₁} {E})) ((app (∘ᴷ-fwdᵢ {D ⊗₀ E₂} {E} {E₁})) a)) (λ o → (app (∘ᴷ-fwdₒ {D ⊗₀ E₂} {E} {E₁})) ((app (absorb-regroupσₒ {D} {E₂} {E₁} {E})) o)) ≅ᴹ Xfwd (λ a → (app (∘ᴷ-fwdᵢ {D} {E} {E₁ ⊗₀ E₂})) (⊗mapᵢ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdᵢ {D} {E₁} {E₂})) (λ (x : Channel.inType E) → x) a)) (λ o → ⊗mapₒ {(D ⊗₀ E₂) ⊗₀ E₁} {D ⊗₀ (E₁ ⊗₀ E₂)} {E} {E} (app (∘ᴷ-fwdₒ {D} {E₁} {E₂})) (λ (x : Channel.outType E) → x) ((app (∘ᴷ-fwdₒ {D} {E} {E₁ ⊗₀ E₂})) o))
    P = Xfwd-≅ᴹ (λ { (inj₁ (inj₁ (inj₁ _))) → refl
                   ; (inj₁ (inj₁ (inj₂ _))) → refl
                   ; (inj₁ (inj₂ _))        → refl
                   ; (inj₂ _)               → refl })
                (λ { (inj₁ _)                → refl
                   ; (inj₂ (inj₁ _))         → refl
                   ; (inj₂ (inj₂ (inj₁ _)))  → refl
                   ; (inj₂ (inj₂ (inj₂ _)))  → refl })

  head₂ : ∀ {C₁ E₁ᵃ E₁ᵇ C₂ E₂ᵃ E₂ᵇ}
        → ((CC.id {C₁ ⊗₀ C₂} ⊗₁ mid4 {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})
           CC.∘ (∘ᴷ-fwd {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ}
                 CC.∘ ((⊗ᴷ-fwd {C₁} {E₁ᵇ} {C₂} {E₂ᵇ} ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ})
                       CC.∘ ⊗ᴷ-fwd {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})))
          ≅ᴹ (⊗ᴷ-fwd {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ}
              CC.∘ (∘ᴷ-fwd {C₁} {E₁ᵃ} {E₁ᵇ} ⊗₁ ∘ᴷ-fwd {C₂} {E₂ᵃ} {E₂ᵇ}))
  head₂ {C₁} {E₁ᵃ} {E₁ᵇ} {C₂} {E₂ᵃ} {E₂ᵇ} =
    ≅ᴹ-trans {M₂ = Xfwd (λ a → ⊗mapᵢ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.inType (C₁ ⊗₀ C₂)) → x) (app (mid4σᵢ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})) ((app (∘ᴷ-fwdᵢ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.inType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (⊗ᴷ-fwdᵢ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) a)))) (λ o → (app (⊗ᴷ-fwdₒ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) (⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdₒ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.outType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (∘ᴷ-fwdₒ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) (⊗mapₒ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.outType (C₁ ⊗₀ C₂)) → x) (app (mid4σₒ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})) o))))} L (≅ᴹ-trans {M₂ = Xfwd (λ a → (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ})) (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdᵢ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdᵢ {C₂} {E₂ᵃ} {E₂ᵇ})) a)) (λ o → ⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdₒ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdₒ {C₂} {E₂ᵃ} {E₂ᵇ})) ((app (⊗ᴷ-fwdₒ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ})) o))} P (≅ᴹ-sym R))
    where
    -- Every node of the two collapse chains is a NAMED, TYPED step.  The GHC
    -- backend inlines `≅ᴹ-trans`/`≅ᴹ-sym`, copying each child into several
    -- record fields; with inline children that is exponential in the depth
    -- of the chain (this lemma, written as one expression, exhausted 48 GB
    -- in the backend), with named children it is linear.
    l₀ : (CC.id {C₁ ⊗₀ C₂} ⊗₁ mid4 {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ}) ≅ᴹ Xfwd (⊗mapᵢ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.inType (C₁ ⊗₀ C₂)) → x) (app (mid4σᵢ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ}))) (⊗mapₒ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.outType (C₁ ⊗₀ C₂)) → x) (app (mid4σₒ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})))
    l₀ = ≅ᴹ-trans (⊗₁-resp-≅ᴹ id-is-Xfwd (tfm'-is-Xfwd (mid4σᵢ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ}) (mid4σₒ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ}))) ⊗₁-Xfwd

    l₁ : (⊗ᴷ-fwd {C₁} {E₁ᵇ} {C₂} {E₂ᵇ} ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ}) ≅ᴹ Xfwd (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.inType (E₁ᵃ ⊗₀ E₂ᵃ)) → x)) (⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdₒ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.outType (E₁ᵃ ⊗₀ E₂ᵃ)) → x))
    l₁ = ≅ᴹ-trans (⊗₁-resp-≅ᴹ (tfm'-is-Xfwd (⊗ᴷ-fwdᵢ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ}) (⊗ᴷ-fwdₒ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) id-is-Xfwd) ⊗₁-Xfwd

    l₂ : ((⊗ᴷ-fwd {C₁} {E₁ᵇ} {C₂} {E₂ᵇ} ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ}) CC.∘ ⊗ᴷ-fwd {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ}) ≅ᴹ Xfwd (λ a → ⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.inType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (⊗ᴷ-fwdᵢ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) a)) (λ o → (app (⊗ᴷ-fwdₒ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) (⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdₒ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.outType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) o))
    l₂ = ≅ᴹ-trans (∘-resp-≅ᴹ l₁ (tfm'-is-Xfwd (⊗ᴷ-fwdᵢ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ}) (⊗ᴷ-fwdₒ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ}))) ∘-Xfwd

    l₃ : (∘ᴷ-fwd {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ} CC.∘ ((⊗ᴷ-fwd {C₁} {E₁ᵇ} {C₂} {E₂ᵇ} ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ}) CC.∘ ⊗ᴷ-fwd {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) ≅ᴹ Xfwd (λ a → (app (∘ᴷ-fwdᵢ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.inType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (⊗ᴷ-fwdᵢ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) a))) (λ o → (app (⊗ᴷ-fwdₒ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) (⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdₒ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.outType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (∘ᴷ-fwdₒ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) o)))
    l₃ = ≅ᴹ-trans (∘-resp-≅ᴹ (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ}) (∘ᴷ-fwdₒ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) l₂) ∘-Xfwd

    L : ((CC.id {C₁ ⊗₀ C₂} ⊗₁ mid4 {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ}) CC.∘ (∘ᴷ-fwd {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ} CC.∘ ((⊗ᴷ-fwd {C₁} {E₁ᵇ} {C₂} {E₂ᵇ} ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ}) CC.∘ ⊗ᴷ-fwd {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ}))) ≅ᴹ Xfwd (λ a → ⊗mapᵢ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.inType (C₁ ⊗₀ C₂)) → x) (app (mid4σᵢ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})) ((app (∘ᴷ-fwdᵢ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.inType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (⊗ᴷ-fwdᵢ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) a)))) (λ o → (app (⊗ᴷ-fwdₒ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) (⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdₒ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.outType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (∘ᴷ-fwdₒ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) (⊗mapₒ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.outType (C₁ ⊗₀ C₂)) → x) (app (mid4σₒ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})) o))))
    L = ≅ᴹ-trans (∘-resp-≅ᴹ l₀ l₃) ∘-Xfwd

    r₁ : (∘ᴷ-fwd {C₁} {E₁ᵃ} {E₁ᵇ} ⊗₁ ∘ᴷ-fwd {C₂} {E₂ᵃ} {E₂ᵇ}) ≅ᴹ Xfwd (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdᵢ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdᵢ {C₂} {E₂ᵃ} {E₂ᵇ}))) (⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdₒ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdₒ {C₂} {E₂ᵃ} {E₂ᵇ})))
    r₁ = ≅ᴹ-trans (⊗₁-resp-≅ᴹ (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {C₁} {E₁ᵃ} {E₁ᵇ}) (∘ᴷ-fwdₒ {C₁} {E₁ᵃ} {E₁ᵇ})) (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {C₂} {E₂ᵃ} {E₂ᵇ}) (∘ᴷ-fwdₒ {C₂} {E₂ᵃ} {E₂ᵇ}))) ⊗₁-Xfwd

    R : (⊗ᴷ-fwd {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ} CC.∘ (∘ᴷ-fwd {C₁} {E₁ᵃ} {E₁ᵇ} ⊗₁ ∘ᴷ-fwd {C₂} {E₂ᵃ} {E₂ᵇ})) ≅ᴹ Xfwd (λ a → (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ})) (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdᵢ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdᵢ {C₂} {E₂ᵃ} {E₂ᵇ})) a)) (λ o → ⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdₒ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdₒ {C₂} {E₂ᵃ} {E₂ᵇ})) ((app (⊗ᴷ-fwdₒ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ})) o))
    R = ≅ᴹ-trans (∘-resp-≅ᴹ (tfm'-is-Xfwd (⊗ᴷ-fwdᵢ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ}) (⊗ᴷ-fwdₒ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ})) r₁) ∘-Xfwd

    -- The two routings agree pointwise.
    P : Xfwd (λ a → ⊗mapᵢ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.inType (C₁ ⊗₀ C₂)) → x) (app (mid4σᵢ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})) ((app (∘ᴷ-fwdᵢ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.inType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (⊗ᴷ-fwdᵢ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) a)))) (λ o → (app (⊗ᴷ-fwdₒ {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})) (⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ (C₂ ⊗₀ E₂ᵇ)} {(C₁ ⊗₀ C₂) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵃ ⊗₀ E₂ᵃ} (app (⊗ᴷ-fwdₒ {C₁} {E₁ᵇ} {C₂} {E₂ᵇ})) (λ (x : Channel.outType (E₁ᵃ ⊗₀ E₂ᵃ)) → x) ((app (∘ᴷ-fwdₒ {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ})) (⊗mapₒ {C₁ ⊗₀ C₂} {C₁ ⊗₀ C₂} {(E₁ᵃ ⊗₀ E₂ᵃ) ⊗₀ (E₁ᵇ ⊗₀ E₂ᵇ)} {(E₁ᵃ ⊗₀ E₁ᵇ) ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (λ (x : Channel.outType (C₁ ⊗₀ C₂)) → x) (app (mid4σₒ {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})) o)))) ≅ᴹ Xfwd (λ a → (app (⊗ᴷ-fwdᵢ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ})) (⊗mapᵢ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdᵢ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdᵢ {C₂} {E₂ᵃ} {E₂ᵇ})) a)) (λ o → ⊗mapₒ {(C₁ ⊗₀ E₁ᵇ) ⊗₀ E₁ᵃ} {C₁ ⊗₀ (E₁ᵃ ⊗₀ E₁ᵇ)} {(C₂ ⊗₀ E₂ᵇ) ⊗₀ E₂ᵃ} {C₂ ⊗₀ (E₂ᵃ ⊗₀ E₂ᵇ)} (app (∘ᴷ-fwdₒ {C₁} {E₁ᵃ} {E₁ᵇ})) (app (∘ᴷ-fwdₒ {C₂} {E₂ᵃ} {E₂ᵇ})) ((app (⊗ᴷ-fwdₒ {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ})) o))
    P = Xfwd-≅ᴹ (λ { (inj₁ (inj₁ (inj₁ _))) → refl
                   ; (inj₁ (inj₁ (inj₂ _))) → refl
                   ; (inj₁ (inj₂ _))        → refl
                   ; (inj₂ (inj₁ (inj₁ _))) → refl
                   ; (inj₂ (inj₁ (inj₂ _))) → refl
                   ; (inj₂ (inj₂ _))        → refl })
                (λ { (inj₁ (inj₁ _))        → refl
                   ; (inj₁ (inj₂ _))        → refl
                   ; (inj₂ (inj₁ (inj₁ _))) → refl
                   ; (inj₂ (inj₁ (inj₂ _))) → refl
                   ; (inj₂ (inj₂ (inj₁ _))) → refl
                   ; (inj₂ (inj₂ (inj₂ _))) → refl })

-- ----------------------------------------------------------------------------
-- `∘ᴷ-assoc`.
-- ----------------------------------------------------------------------------

-- The left-hand side, flattened: the `F` is carried across `∘ᴷ-fwd` by
-- naturality, which is what exposes the same suffix as the right-hand side.
∘ᴷ-assoc-L : ∀ {A B C D E E₁ E₂}
  (F : Machine C (D ⊗₀ E₂)) (G : Machine B (C ⊗₀ E₁)) (h : Machine A (B ⊗₀ E))
  → ((absorb-regroup CC.∘ (F ⊗₁ CC.id {E ⊗₀ E₁})) CC.∘ (G ∘ᴷ h))
    ≅ᴹ ((absorb-regroup {D} {E₂} {E₁} {E} CC.∘ ∘ᴷ-fwd {D ⊗₀ E₂} {E} {E₁})
        CC.∘ (((F ⊗₁ CC.id {E₁}) ⊗₁ CC.id {E})
              CC.∘ ((G ⊗₁ CC.id {E}) CC.∘ h)))
∘ᴷ-assoc-L {E = E} {E₁} F G h =
  ≅ᴹ-trans ∘-assoc-≅ᴹ
  (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-assoc-≅ᴹ))
  (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl
              (∘-resp-≅ᴹ (≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ⊗₁-id))
                                              ≅ᴹ-refl)
                                   (∘ᴷ-fwd-natural F (CC.id {E}) (CC.id {E₁})))
                         ≅ᴹ-refl))
  (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl ∘-assoc-≅ᴹ)
            (≅ᴹ-sym ∘-assoc-≅ᴹ))))

-- The right-hand side, flattened: `_⊗ʳ E` is distributed over the inner
-- Kleisli composite.
∘ᴷ-assoc-R : ∀ {A B C D E E₁ E₂}
  (F : Machine C (D ⊗₀ E₂)) (G : Machine B (C ⊗₀ E₁)) (h : Machine A (B ⊗₀ E))
  → ((F ∘ᴷ G) ∘ᴷ h)
    ≅ᴹ ((∘ᴷ-fwd {D} {E} {E₁ ⊗₀ E₂} CC.∘ (∘ᴷ-fwd {D} {E₁} {E₂} ⊗₁ CC.id {E}))
        CC.∘ (((F ⊗₁ CC.id {E₁}) ⊗₁ CC.id {E})
              CC.∘ ((G ⊗₁ CC.id {E}) CC.∘ h)))
∘ᴷ-assoc-R {E = E} {E₁} F G h =
  ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl
             (∘-resp-≅ᴹ (≅ᴹ-trans (⊗ʳ-∘ (∘ᴷ-fwd {E₁ = E₁}) ((F ⊗₁ CC.id {E₁}) CC.∘ G))
                                  (∘-resp-≅ᴹ ≅ᴹ-refl (⊗ʳ-∘ (F ⊗₁ CC.id {E₁}) G)))
                        ≅ᴹ-refl))
  (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl ∘-assoc-≅ᴹ)
  (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ ≅ᴹ-refl ∘-assoc-≅ᴹ))
            (≅ᴹ-sym ∘-assoc-≅ᴹ)))

∘ᴷ-assoc : ∀ {A B C D E E₁ E₂}
  (F : Machine C (D ⊗₀ E₂)) (G : Machine B (C ⊗₀ E₁)) (h : Machine A (B ⊗₀ E))
  → ((absorb-regroup CC.∘ (F ⊗₁ CC.id)) CC.∘ (G ∘ᴷ h)) ≅ᴹ ((F ∘ᴷ G) ∘ᴷ h)
∘ᴷ-assoc F G h =
  ≅ᴹ-trans (∘ᴷ-assoc-L F G h)
  (≅ᴹ-trans (∘-resp-≅ᴹ head₁ ≅ᴹ-refl)
            (≅ᴹ-sym (∘ᴷ-assoc-R F G h)))

-- ----------------------------------------------------------------------------
-- `⊗ᴷ-∘ᴷ`.
-- ----------------------------------------------------------------------------

-- The left-hand side, flattened.  The `_⊗ᴷ_` shuffle of the two second-stage
-- machines is carried across the one of the first stage by naturality, which
-- puts the four machines in the same order and bracketing as on the right.
⊗ᴷ-∘ᴷ-L : ∀ {A₁ B₁ C₁ E₁ᵃ E₁ᵇ A₂ B₂ C₂ E₂ᵃ E₂ᵇ}
  (a : Machine B₁ (C₁ ⊗₀ E₁ᵇ)) (b : Machine A₁ (B₁ ⊗₀ E₁ᵃ))
  (c : Machine B₂ (C₂ ⊗₀ E₂ᵇ)) (d : Machine A₂ (B₂ ⊗₀ E₂ᵃ))
  → ((CC.id ⊗₁ mid4) CC.∘ ((a ⊗ᴷ c) ∘ᴷ (b ⊗ᴷ d)))
    ≅ᴹ (((CC.id {C₁ ⊗₀ C₂} ⊗₁ mid4 {E₁ᵃ} {E₂ᵃ} {E₁ᵇ} {E₂ᵇ})
         CC.∘ (∘ᴷ-fwd {C₁ ⊗₀ C₂} {E₁ᵃ ⊗₀ E₂ᵃ} {E₁ᵇ ⊗₀ E₂ᵇ}
               CC.∘ ((⊗ᴷ-fwd {C₁} {E₁ᵇ} {C₂} {E₂ᵇ} ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ})
                     CC.∘ ⊗ᴷ-fwd {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})))
        CC.∘ ((((a ⊗₁ CC.id {E₁ᵃ}) ⊗₁ (c ⊗₁ CC.id {E₂ᵃ}))) CC.∘ (b ⊗₁ d)))
⊗ᴷ-∘ᴷ-L {C₁ = C₁} {E₁ᵃ = E₁ᵃ} {E₁ᵇ = E₁ᵇ} {C₂ = C₂} {E₂ᵃ = E₂ᵃ} {E₂ᵇ = E₂ᵇ} a b c d =
  ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ ≅ᴹ-refl inner))
  (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-assoc-≅ᴹ))
            (≅ᴹ-sym ∘-assoc-≅ᴹ))
  where
  -- `_⊗ʳ Eᵃ` distributed, then the shuffle carried across `a ⊗₁ c`.
  inner : ((((⊗ᴷ-fwd {E₁ = E₁ᵇ}) CC.∘ (a ⊗₁ c)) ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ})
           CC.∘ ((⊗ᴷ-fwd {E₁ = E₁ᵃ}) CC.∘ (b ⊗₁ d)))
        ≅ᴹ (((⊗ᴷ-fwd {E₁ = E₁ᵇ} ⊗₁ CC.id {E₁ᵃ ⊗₀ E₂ᵃ})
             CC.∘ ⊗ᴷ-fwd {C₁ ⊗₀ E₁ᵇ} {E₁ᵃ} {C₂ ⊗₀ E₂ᵇ} {E₂ᵃ})
            CC.∘ (((a ⊗₁ CC.id {E₁ᵃ}) ⊗₁ (c ⊗₁ CC.id {E₂ᵃ})) CC.∘ (b ⊗₁ d)))
  inner =
    ≅ᴹ-trans (∘-resp-≅ᴹ (⊗ʳ-∘ (⊗ᴷ-fwd {E₁ = E₁ᵇ}) (a ⊗₁ c)) ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
    (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-assoc-≅ᴹ))
    (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl
                (∘-resp-≅ᴹ (≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ⊗₁-id))
                                                ≅ᴹ-refl)
                                     (⊗ᴷ-fwd-natural a (CC.id {E₁ᵃ}) c (CC.id {E₂ᵃ})))
                           ≅ᴹ-refl))
    (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl ∘-assoc-≅ᴹ)
              (≅ᴹ-sym ∘-assoc-≅ᴹ)))))

-- The right-hand side, flattened: `_⊗₁_` distributed over both stages.
⊗ᴷ-∘ᴷ-R : ∀ {A₁ B₁ C₁ E₁ᵃ E₁ᵇ A₂ B₂ C₂ E₂ᵃ E₂ᵇ}
  (a : Machine B₁ (C₁ ⊗₀ E₁ᵇ)) (b : Machine A₁ (B₁ ⊗₀ E₁ᵃ))
  (c : Machine B₂ (C₂ ⊗₀ E₂ᵇ)) (d : Machine A₂ (B₂ ⊗₀ E₂ᵃ))
  → ((a ∘ᴷ b) ⊗ᴷ (c ∘ᴷ d))
    ≅ᴹ ((⊗ᴷ-fwd {C₁} {E₁ᵃ ⊗₀ E₁ᵇ} {C₂} {E₂ᵃ ⊗₀ E₂ᵇ}
         CC.∘ (∘ᴷ-fwd {C₁} {E₁ᵃ} {E₁ᵇ} ⊗₁ ∘ᴷ-fwd {C₂} {E₂ᵃ} {E₂ᵇ}))
        CC.∘ ((((a ⊗₁ CC.id {E₁ᵃ}) ⊗₁ (c ⊗₁ CC.id {E₂ᵃ}))) CC.∘ (b ⊗₁ d)))
⊗ᴷ-∘ᴷ-R {E₁ᵃ = E₁ᵃ} {E₂ᵃ = E₂ᵃ} a b c d =
  ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl
             (≅ᴹ-trans (⊗₁-interchange ((a ⊗₁ CC.id {E₁ᵃ}) CC.∘ b) (∘ᴷ-fwd {E₁ = E₁ᵃ})
                                       ((c ⊗₁ CC.id {E₂ᵃ}) CC.∘ d) (∘ᴷ-fwd {E₁ = E₂ᵃ}))
                       (∘-resp-≅ᴹ ≅ᴹ-refl
                         (⊗₁-interchange b (a ⊗₁ CC.id {E₁ᵃ}) d (c ⊗₁ CC.id {E₂ᵃ})))))
            (≅ᴹ-sym ∘-assoc-≅ᴹ)

⊗ᴷ-∘ᴷ : ∀ {A₁ B₁ C₁ E₁ᵃ E₁ᵇ A₂ B₂ C₂ E₂ᵃ E₂ᵇ}
  (a : Machine B₁ (C₁ ⊗₀ E₁ᵇ)) (b : Machine A₁ (B₁ ⊗₀ E₁ᵃ))
  (c : Machine B₂ (C₂ ⊗₀ E₂ᵇ)) (d : Machine A₂ (B₂ ⊗₀ E₂ᵃ))
  → ((CC.id ⊗₁ mid4) CC.∘ ((a ⊗ᴷ c) ∘ᴷ (b ⊗ᴷ d))) ≅ᴹ ((a ∘ᴷ b) ⊗ᴷ (c ∘ᴷ d))
⊗ᴷ-∘ᴷ a b c d =
  ≅ᴹ-trans (⊗ᴷ-∘ᴷ-L a b c d)
  (≅ᴹ-trans (∘-resp-≅ᴹ head₂ ≅ᴹ-refl)
            (≅ᴹ-sym (⊗ᴷ-∘ᴷ-R a b c d)))

-- ----------------------------------------------------------------------------
-- Both laws together.  Nothing downstream uses this definition; it is here so
-- that the two statements above are checked against the fields they discharge,
-- rather than against a hand-copied version of them.
-- ----------------------------------------------------------------------------
