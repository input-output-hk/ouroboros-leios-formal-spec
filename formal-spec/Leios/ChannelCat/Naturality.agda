{-# OPTIONS --safe #-}

-- ============================================================================
-- Naturality of the two structural forwarders of the Kleisli composition:
-- `∘ᴷ-fwd` and `⊗ᴷ-fwd`.
--
-- Both laws have the shape `M ∘ Φ ≅ᴹ Φ' ∘ M'`, with `Φ`, `Φ'` forwarders and
-- `M`, `M'` differently-grouped tensors of the SAME machines.  A crossing
-- forwarder is a reindexed identity (`Xfwd-dom`/`Xfwd-cod`), so composing with
-- one is a pure relabelling (`∘-collapse-dom`/`∘-collapse-cod`), and each side
-- collapses to a `Reindex` of the tensor.  Normalising the two tensors to
-- `Pair`-nests then leaves a single pointwise equation between two routings,
-- which is a finite case split closed by `refl`.
--
-- The two nests differ, and are bridged by the only two structural facts about
-- `Pair` that are needed: `Pair-rot3` for the three-fold law and `Pair-mid4`
-- for the four-fold one.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Machine.Iso using (∘-identityˡ-≅ᴹ; ∘-identityʳ-≅ᴹ)
open import Leios.ChannelCat.Interchange
open import Leios.ChannelCat.Slide
open import Leios.ChannelCat.Fwd
open import Leios.ChannelCat.FwdId
open import Leios.ChannelCat.Collapse
open import Leios.ChannelCat.PairAssoc
open import Tactic.Defaults

module Leios.ChannelCat.Naturality where

-- `⊗ᴷ-fwd`'s two halves, named by re-elaborating `⇒-solver` at their types.
-- The solver is deterministic, so this really is the same machine.
⊗ᴷ-fwdᵢ : ∀ {B₁ E₁ B₂ E₂}
        → ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) [ In ]⇒[ In ] ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
⊗ᴷ-fwdᵢ = ⇒-solver

⊗ᴷ-fwdₒ : ∀ {B₁ E₁ B₂ E₂}
        → ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)) [ Out ]⇒[ Out ] ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂))
⊗ᴷ-fwdₒ = ⇒-solver

⊗ᴷ-fwd-named : ∀ {B₁ E₁ B₂ E₂}
             → ⊗ᴷ-fwd {B₁} {E₁} {B₂} {E₂} ≡ TotalFunctionMachine' ⊗ᴷ-fwdᵢ ⊗ᴷ-fwdₒ
⊗ᴷ-fwd-named = refl

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
            ⊗-combine πᵢ ∘κᵢ cdᵢ Xφ rot3ᵢ

  -- ========================================================================
  -- `Pair` absorbs a `Reindex` in either argument.  `Pair-Reindex` wants both
  -- arguments reindexed, and a machine is its own identity reindexing.
  -- ========================================================================

  Pair-Reindexʳ : ∀ {A B Cc Dd C₂ D₂} (M₁ : Machine A B) (M₂ : Machine Cc Dd)
                  (u : Channel.inType (C₂ ⊗ᵀ D₂) → Channel.inType (Cc ⊗ᵀ Dd))
                  (v : Channel.outType (C₂ ⊗ᵀ D₂) → Channel.outType (Cc ⊗ᵀ Dd))
                → Pair M₁ (Reindex M₂ u v)
                  ≅ᴹ Reindex (Pair M₁ M₂)
                       (⊎ᵢ {A} {B} {Cc} {Dd} {A} {B} {C₂} {D₂} (λ x → x) u)
                       (⊎ₒ {A} {B} {Cc} {Dd} {A} {B} {C₂} {D₂} (λ x → x) v)
  Pair-Reindexʳ M₁ M₂ u v =
    ≅ᴹ-trans (Pair-resp-≅ᴹ (≅ᴹ-sym (Reindex-id M₁)) ≅ᴹ-refl)
             (Pair-Reindex M₁ M₂ (λ x → x) (λ x → x) u v)

  Pair-Reindexˡ : ∀ {A B Cc Dd A₂ B₂} (M₁ : Machine A B) (M₂ : Machine Cc Dd)
                  (u : Channel.inType (A₂ ⊗ᵀ B₂) → Channel.inType (A ⊗ᵀ B))
                  (v : Channel.outType (A₂ ⊗ᵀ B₂) → Channel.outType (A ⊗ᵀ B))
                → Pair (Reindex M₁ u v) M₂
                  ≅ᴹ Reindex (Pair M₁ M₂)
                       (⊎ᵢ {A} {B} {Cc} {Dd} {A₂} {B₂} {Cc} {Dd} u (λ x → x))
                       (⊎ₒ {A} {B} {Cc} {Dd} {A₂} {B₂} {Cc} {Dd} v (λ x → x))
  Pair-Reindexˡ M₁ M₂ u v =
    ≅ᴹ-trans (Pair-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym (Reindex-id M₂)))
             (Pair-Reindex M₁ M₂ u v (λ x → x) (λ x → x))

  -- ========================================================================
  -- Normalising a tensor to a `Pair`-nest.  `_⊗₁_` IS a `Reindex` of a `Pair`
  -- (definitionally), so all that happens here is that the nested `Reindex`es
  -- are fused and the composite routing is replaced by the permutation it
  -- computes to.
  -- ========================================================================

  -- ---- the right-nested three-fold case, `m ⊗₁ (n₁ ⊗₁ n₂)` ---------------

  nrᵢ : ∀ {A A' B B' D D'}
      → Channel.inType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D')))
      → Channel.inType ((A ⊗ᵀ A') ⊗₀ ((B ⊗ᵀ B') ⊗₀ (D ⊗ᵀ D')))
  nrᵢ (inj₁ (inj₁ x))        = inj₁ (inj₁ x)
  nrᵢ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  nrᵢ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  nrᵢ (inj₂ (inj₁ x))        = inj₁ (inj₂ x)
  nrᵢ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  nrᵢ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  nrₒ : ∀ {A A' B B' D D'}
      → Channel.outType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D')))
      → Channel.outType ((A ⊗ᵀ A') ⊗₀ ((B ⊗ᵀ B') ⊗₀ (D ⊗ᵀ D')))
  nrₒ (inj₁ (inj₁ x))        = inj₁ (inj₁ x)
  nrₒ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  nrₒ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  nrₒ (inj₂ (inj₁ x))        = inj₁ (inj₂ x)
  nrₒ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  nrₒ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  pt-nrᵢ : ∀ {A A' B B' D D'}
           (i : Channel.inType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D'))))
         → ⊎ᵢ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
              (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {In}))
              (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}) i)
           ≡ nrᵢ {A} {A'} {B} {B'} {D} {D'} i
  pt-nrᵢ (inj₁ (inj₁ _))        = refl
  pt-nrᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-nrᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-nrᵢ (inj₂ (inj₁ _))        = refl
  pt-nrᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-nrᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-nrₒ : ∀ {A A' B B' D D'}
           (o : Channel.outType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D'))))
         → ⊎ₒ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
              (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {Out}))
              (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out}) o)
           ≡ nrₒ {A} {A'} {B} {B'} {D} {D'} o
  pt-nrₒ (inj₁ (inj₁ _))        = refl
  pt-nrₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-nrₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-nrₒ (inj₂ (inj₁ _))        = refl
  pt-nrₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-nrₒ (inj₂ (inj₂ (inj₂ _))) = refl

  ⊗₁-norm-r : ∀ {A A' B B' D D'}
              (m : Machine A A') (n₁ : Machine B B') (n₂ : Machine D D')
            → (m ⊗₁ (n₁ ⊗₁ n₂))
              ≅ᴹ Reindex (Pair m (Pair n₁ n₂)) (nrᵢ {A} {A'} {B} {B'} {D} {D'})
                                               (nrₒ {A} {A'} {B} {B'} {D} {D'})
  ⊗₁-norm-r {A} {A'} {B} {B'} {D} {D'} m n₁ n₂ =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}))
                              (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out}))
                (Pair-Reindexʳ m (Pair n₁ n₂) (app (⊗σ {B} {B'} {D} {D'} {In}))
                                              (app (⊗σ {B} {B'} {D} {D'} {Out}))))
    (≅ᴹ-trans (Reindex-fuse (Pair m (Pair n₁ n₂))
                 (⊎ᵢ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                     (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {In})))
                 (⊎ₒ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                     (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {Out})))
                 (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}))
                 (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out})))
              (Reindex-cong (Pair m (Pair n₁ n₂))
                 (λ i → ⊎ᵢ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                           (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {In}))
                           (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}) i))
                 (nrᵢ {A} {A'} {B} {B'} {D} {D'})
                 (λ o → ⊎ₒ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                           (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {Out}))
                           (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out}) o))
                 (nrₒ {A} {A'} {B} {B'} {D} {D'}) pt-nrᵢ pt-nrₒ))

  -- ---- the left-nested three-fold case, `(m ⊗₁ n₁) ⊗₁ n₂` ---------------

  nlᵢ : ∀ {A A' B B' D D'}
      → Channel.inType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D'))
      → Channel.inType (((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B')) ⊗₀ (D ⊗ᵀ D'))
  nlᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  nlᵢ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  nlᵢ (inj₁ (inj₂ x))        = inj₂ (inj₁ x)
  nlᵢ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  nlᵢ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  nlᵢ (inj₂ (inj₂ x))        = inj₂ (inj₂ x)

  nlₒ : ∀ {A A' B B' D D'}
      → Channel.outType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D'))
      → Channel.outType (((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B')) ⊗₀ (D ⊗ᵀ D'))
  nlₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  nlₒ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  nlₒ (inj₁ (inj₂ x))        = inj₂ (inj₁ x)
  nlₒ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  nlₒ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  nlₒ (inj₂ (inj₂ x))        = inj₂ (inj₂ x)

  pt-nlᵢ : ∀ {A A' B B' D D'}
           (i : Channel.inType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → ⊎ᵢ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
              (app (⊗σ {A} {A'} {B} {B'} {In})) (λ x → x)
              (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}) i)
           ≡ nlᵢ {A} {A'} {B} {B'} {D} {D'} i
  pt-nlᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-nlᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-nlᵢ (inj₁ (inj₂ _))        = refl
  pt-nlᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-nlᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-nlᵢ (inj₂ (inj₂ _))        = refl

  pt-nlₒ : ∀ {A A' B B' D D'}
           (o : Channel.outType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → ⊎ₒ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
              (app (⊗σ {A} {A'} {B} {B'} {Out})) (λ x → x)
              (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out}) o)
           ≡ nlₒ {A} {A'} {B} {B'} {D} {D'} o
  pt-nlₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-nlₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-nlₒ (inj₁ (inj₂ _))        = refl
  pt-nlₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-nlₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-nlₒ (inj₂ (inj₂ _))        = refl

  ⊗₁-norm-l : ∀ {A A' B B' D D'}
              (m : Machine A A') (n₁ : Machine B B') (n₂ : Machine D D')
            → ((m ⊗₁ n₁) ⊗₁ n₂)
              ≅ᴹ Reindex (Pair (Pair m n₁) n₂) (nlᵢ {A} {A'} {B} {B'} {D} {D'})
                                               (nlₒ {A} {A'} {B} {B'} {D} {D'})
  ⊗₁-norm-l {A} {A'} {B} {B'} {D} {D'} m n₁ n₂ =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}))
                              (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out}))
                (Pair-Reindexˡ (Pair m n₁) n₂ (app (⊗σ {A} {A'} {B} {B'} {In}))
                                              (app (⊗σ {A} {A'} {B} {B'} {Out}))))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair m n₁) n₂)
                 (⊎ᵢ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                     (app (⊗σ {A} {A'} {B} {B'} {In})) (λ x → x))
                 (⊎ₒ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                     (app (⊗σ {A} {A'} {B} {B'} {Out})) (λ x → x))
                 (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}))
                 (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out})))
              (Reindex-cong (Pair (Pair m n₁) n₂)
                 (λ i → ⊎ᵢ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                           (app (⊗σ {A} {A'} {B} {B'} {In})) (λ x → x)
                           (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}) i))
                 (nlᵢ {A} {A'} {B} {B'} {D} {D'})
                 (λ o → ⊎ₒ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                           (app (⊗σ {A} {A'} {B} {B'} {Out})) (λ x → x)
                           (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out}) o))
                 (nlₒ {A} {A'} {B} {B'} {D} {D'}) pt-nlᵢ pt-nlₒ))

  -- ========================================================================
  -- The first law: `∘ᴷ-fwd` is natural.
  -- ========================================================================

  -- ---- `∘ᴷ-fwd`'s message maps, and their inverses ----------------------

  ∘fᵢ : ∀ {C E₁ E₂} → Channel.inType ((C ⊗₀ E₂) ⊗₀ E₁)
                    → Channel.inType (C ⊗₀ (E₁ ⊗₀ E₂))
  ∘fᵢ {C} {E₁} {E₂} = app (∘ᴷ-fwdᵢ {C} {E₁} {E₂})

  ∘fₒ : ∀ {C E₁ E₂} → Channel.outType (C ⊗₀ (E₁ ⊗₀ E₂))
                    → Channel.outType ((C ⊗₀ E₂) ⊗₀ E₁)
  ∘fₒ {C} {E₁} {E₂} = app (∘ᴷ-fwdₒ {C} {E₁} {E₂})

  ∘fᵢ⁻ : ∀ {C E₁ E₂} → Channel.inType (C ⊗₀ (E₁ ⊗₀ E₂))
                     → Channel.inType ((C ⊗₀ E₂) ⊗₀ E₁)
  ∘fᵢ⁻ (inj₁ x)        = inj₁ (inj₁ x)
  ∘fᵢ⁻ (inj₂ (inj₁ y)) = inj₂ y
  ∘fᵢ⁻ (inj₂ (inj₂ z)) = inj₁ (inj₂ z)

  ∘fₒ⁻ : ∀ {C E₁ E₂} → Channel.outType ((C ⊗₀ E₂) ⊗₀ E₁)
                     → Channel.outType (C ⊗₀ (E₁ ⊗₀ E₂))
  ∘fₒ⁻ (inj₁ (inj₁ x)) = inj₁ x
  ∘fₒ⁻ (inj₁ (inj₂ y)) = inj₂ (inj₂ y)
  ∘fₒ⁻ (inj₂ z)        = inj₂ (inj₁ z)

  ∘fₒ-l : ∀ {C E₁ E₂} β → ∘fₒ⁻ {C} {E₁} {E₂} (∘fₒ {C} {E₁} {E₂} β) ≡ β
  ∘fₒ-l (inj₁ _)        = refl
  ∘fₒ-l (inj₂ (inj₁ _)) = refl
  ∘fₒ-l (inj₂ (inj₂ _)) = refl

  ∘fₒ-r : ∀ {C E₁ E₂} α → ∘fₒ {C} {E₁} {E₂} (∘fₒ⁻ {C} {E₁} {E₂} α) ≡ α
  ∘fₒ-r (inj₁ (inj₁ _)) = refl
  ∘fₒ-r (inj₁ (inj₂ _)) = refl
  ∘fₒ-r (inj₂ _)        = refl

  ∘fᵢ-l : ∀ {C E₁ E₂} a → ∘fᵢ⁻ {C} {E₁} {E₂} (∘fᵢ {C} {E₁} {E₂} a) ≡ a
  ∘fᵢ-l (inj₁ (inj₁ _)) = refl
  ∘fᵢ-l (inj₁ (inj₂ _)) = refl
  ∘fᵢ-l (inj₂ _)        = refl

  ∘fᵢ-r : ∀ {C E₁ E₂} b → ∘fᵢ {C} {E₁} {E₂} (∘fᵢ⁻ {C} {E₁} {E₂} b) ≡ b
  ∘fᵢ-r (inj₁ _)        = refl
  ∘fᵢ-r (inj₂ (inj₁ _)) = refl
  ∘fᵢ-r (inj₂ (inj₂ _)) = refl

  -- ---- the forwarder as a reindexed identity, both ways -----------------

  ∘ᴷ-Φdom : ∀ {C E₁ E₂}
          → ∘ᴷ-fwd {C} {E₁} {E₂}
            ≅ᴹ Reindex (CC.id {C ⊗₀ (E₁ ⊗₀ E₂)})
                 (dmᵢ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C ⊗₀ (E₁ ⊗₀ E₂)}
                      (∘fᵢ {C} {E₁} {E₂}))
                 (dmₒ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C ⊗₀ (E₁ ⊗₀ E₂)}
                      (∘fₒ⁻ {C} {E₁} {E₂}))
  ∘ᴷ-Φdom {C} {E₁} {E₂} =
    ≅ᴹ-trans (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {C} {E₁} {E₂}) (∘ᴷ-fwdₒ {C} {E₁} {E₂}))
             (Xfwd-dom (∘fᵢ {C} {E₁} {E₂}) (∘fₒ {C} {E₁} {E₂}) (∘fₒ⁻ {C} {E₁} {E₂})
                       ∘fₒ-l ∘fₒ-r)

  ∘ᴷ-Φcod : ∀ {C E₁ E₂}
          → ∘ᴷ-fwd {C} {E₁} {E₂}
            ≅ᴹ Reindex (CC.id {(C ⊗₀ E₂) ⊗₀ E₁})
                 (cdᵢ {(C ⊗₀ E₂) ⊗₀ E₁} {(C ⊗₀ E₂) ⊗₀ E₁} {C ⊗₀ (E₁ ⊗₀ E₂)}
                      (∘fₒ {C} {E₁} {E₂}))
                 (cdₒ {(C ⊗₀ E₂) ⊗₀ E₁} {(C ⊗₀ E₂) ⊗₀ E₁} {C ⊗₀ (E₁ ⊗₀ E₂)}
                      (∘fᵢ⁻ {C} {E₁} {E₂}))
  ∘ᴷ-Φcod {C} {E₁} {E₂} =
    ≅ᴹ-trans (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {C} {E₁} {E₂}) (∘ᴷ-fwdₒ {C} {E₁} {E₂}))
             (Xfwd-cod (∘fᵢ {C} {E₁} {E₂}) (∘fₒ {C} {E₁} {E₂}) (∘fᵢ⁻ {C} {E₁} {E₂})
                       ∘fᵢ-l ∘fᵢ-r)

  -- ---- the two collapses ------------------------------------------------

  ∘ᴷ-lhs : ∀ {C C' E₁ E₁' E₂ E₂'}
           (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
         → ((c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd {C} {E₁} {E₂})
           ≅ᴹ Reindex (c ⊗₁ (u₁ ⊗₁ u₂))
                (dmᵢ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                     (∘fᵢ {C} {E₁} {E₂}))
                (dmₒ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                     (∘fₒ⁻ {C} {E₁} {E₂}))
  ∘ᴷ-lhs {C} {C'} {E₁} {E₁'} {E₂} {E₂'} c u₁ u₂ =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (∘ᴷ-Φdom {C} {E₁} {E₂}))
    (≅ᴹ-trans (∘-collapse-dom (CC.id {C ⊗₀ (E₁ ⊗₀ E₂)}) (c ⊗₁ (u₁ ⊗₁ u₂))
                              (∘fᵢ {C} {E₁} {E₂}) (∘fₒ⁻ {C} {E₁} {E₂}))
              (Reindex-resp-≅ᴹ
                 (dmᵢ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fᵢ {C} {E₁} {E₂}))
                 (dmₒ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fₒ⁻ {C} {E₁} {E₂}))
                 ∘-identityʳ-≅ᴹ))

  ∘ᴷ-rhs : ∀ {C C' E₁ E₁' E₂ E₂'}
           (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
         → (∘ᴷ-fwd {C'} {E₁'} {E₂'} CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁))
           ≅ᴹ Reindex ((c ⊗₁ u₂) ⊗₁ u₁)
                (cdᵢ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                     (∘fₒ {C'} {E₁'} {E₂'}))
                (cdₒ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                     (∘fᵢ⁻ {C'} {E₁'} {E₂'}))
  ∘ᴷ-rhs {C} {C'} {E₁} {E₁'} {E₂} {E₂'} c u₁ u₂ =
    ≅ᴹ-trans (∘-resp-≅ᴹ (∘ᴷ-Φcod {C'} {E₁'} {E₂'}) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-collapse-cod ((c ⊗₁ u₂) ⊗₁ u₁) (CC.id {(C' ⊗₀ E₂') ⊗₀ E₁'})
                              (∘fₒ {C'} {E₁'} {E₂'}) (∘fᵢ⁻ {C'} {E₁'} {E₂'}))
              (Reindex-resp-≅ᴹ
                 (cdᵢ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fₒ {C'} {E₁'} {E₂'}))
                 (cdₒ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fᵢ⁻ {C'} {E₁'} {E₂'}))
                 ∘-identityˡ-≅ᴹ))

  -- ---- the two routings, and the fact that they agree -------------------

  -- The routing the left-hand side produces, into the right-nested nest.
  ∘Lᵢ : ∀ {C C' E₁ E₁' E₂ E₂'}
      → Channel.inType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.inType ((C ⊗ᵀ C') ⊗₀ ((E₁ ⊗ᵀ E₁') ⊗₀ (E₂ ⊗ᵀ E₂')))
  ∘Lᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ x)
  ∘Lᵢ (inj₁ (inj₁ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  ∘Lᵢ (inj₁ (inj₂ x))        = inj₂ (inj₁ (inj₁ x))
  ∘Lᵢ (inj₂ (inj₁ x))        = inj₁ (inj₂ x)
  ∘Lᵢ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  ∘Lᵢ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  ∘Lₒ : ∀ {C C' E₁ E₁' E₂ E₂'}
      → Channel.outType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.outType ((C ⊗ᵀ C') ⊗₀ ((E₁ ⊗ᵀ E₁') ⊗₀ (E₂ ⊗ᵀ E₂')))
  ∘Lₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ x)
  ∘Lₒ (inj₁ (inj₁ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  ∘Lₒ (inj₁ (inj₂ x))        = inj₂ (inj₁ (inj₁ x))
  ∘Lₒ (inj₂ (inj₁ x))        = inj₁ (inj₂ x)
  ∘Lₒ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  ∘Lₒ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  -- The routing the right-hand side produces, into the left-nested nest.
  ∘Rᵢ : ∀ {C C' E₁ E₁' E₂ E₂'}
      → Channel.inType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.inType (((C ⊗ᵀ C') ⊗₀ (E₂ ⊗ᵀ E₂')) ⊗₀ (E₁ ⊗ᵀ E₁'))
  ∘Rᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  ∘Rᵢ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  ∘Rᵢ (inj₁ (inj₂ x))        = inj₂ (inj₁ x)
  ∘Rᵢ (inj₂ (inj₁ x))        = inj₁ (inj₁ (inj₂ x))
  ∘Rᵢ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₂ x)
  ∘Rᵢ (inj₂ (inj₂ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))

  ∘Rₒ : ∀ {C C' E₁ E₁' E₂ E₂'}
      → Channel.outType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.outType (((C ⊗ᵀ C') ⊗₀ (E₂ ⊗ᵀ E₂')) ⊗₀ (E₁ ⊗ᵀ E₁'))
  ∘Rₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  ∘Rₒ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  ∘Rₒ (inj₁ (inj₂ x))        = inj₂ (inj₁ x)
  ∘Rₒ (inj₂ (inj₁ x))        = inj₁ (inj₁ (inj₂ x))
  ∘Rₒ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₂ x)
  ∘Rₒ (inj₂ (inj₂ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))

  pt-∘Lᵢ : ∀ {C C' E₁ E₁' E₂ E₂'}
           (i : Channel.inType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂'))))
         → nrᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
             (dmᵢ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                  (∘fᵢ {C} {E₁} {E₂}) i)
           ≡ ∘Lᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} i
  pt-∘Lᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-∘Lᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-∘Lᵢ (inj₁ (inj₂ _))        = refl
  pt-∘Lᵢ (inj₂ (inj₁ _))        = refl
  pt-∘Lᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-∘Lᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-∘Lₒ : ∀ {C C' E₁ E₁' E₂ E₂'}
           (o : Channel.outType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂'))))
         → nrₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
             (dmₒ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                  (∘fₒ⁻ {C} {E₁} {E₂}) o)
           ≡ ∘Lₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} o
  pt-∘Lₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-∘Lₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-∘Lₒ (inj₁ (inj₂ _))        = refl
  pt-∘Lₒ (inj₂ (inj₁ _))        = refl
  pt-∘Lₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-∘Lₒ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-∘Rᵢ : ∀ {C C' E₁ E₁' E₂ E₂'}
           (i : Channel.inType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂'))))
         → nlᵢ {C} {C'} {E₂} {E₂'} {E₁} {E₁'}
             (cdᵢ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                  (∘fₒ {C'} {E₁'} {E₂'}) i)
           ≡ ∘Rᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} i
  pt-∘Rᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-∘Rᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-∘Rᵢ (inj₁ (inj₂ _))        = refl
  pt-∘Rᵢ (inj₂ (inj₁ _))        = refl
  pt-∘Rᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-∘Rᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-∘Rₒ : ∀ {C C' E₁ E₁' E₂ E₂'}
           (o : Channel.outType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂'))))
         → nlₒ {C} {C'} {E₂} {E₂'} {E₁} {E₁'}
             (cdₒ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                  (∘fᵢ⁻ {C'} {E₁'} {E₂'}) o)
           ≡ ∘Rₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} o
  pt-∘Rₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-∘Rₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-∘Rₒ (inj₁ (inj₂ _))        = refl
  pt-∘Rₒ (inj₂ (inj₁ _))        = refl
  pt-∘Rₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-∘Rₒ (inj₂ (inj₂ (inj₂ _))) = refl

  -- The whole message-level content of the law: the rotation takes the one
  -- routing to the other.
  pt-rot3ᵢ : ∀ {C C' E₁ E₁' E₂ E₂'}
             (i : Channel.inType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂'))))
           → rot3ᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
               (∘Lᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} i)
             ≡ ∘Rᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} i
  pt-rot3ᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-rot3ᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-rot3ᵢ (inj₁ (inj₂ _))        = refl
  pt-rot3ᵢ (inj₂ (inj₁ _))        = refl
  pt-rot3ᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-rot3ᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-rot3ₒ : ∀ {C C' E₁ E₁' E₂ E₂'}
             (o : Channel.outType (((C ⊗₀ E₂) ⊗₀ E₁) ⊗ᵀ (C' ⊗₀ (E₁' ⊗₀ E₂'))))
           → rot3ₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
               (∘Lₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} o)
             ≡ ∘Rₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} o
  pt-rot3ₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-rot3ₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-rot3ₒ (inj₁ (inj₂ _))        = refl
  pt-rot3ₒ (inj₂ (inj₁ _))        = refl
  pt-rot3ₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-rot3ₒ (inj₂ (inj₂ (inj₂ _))) = refl

  -- ---- the two sides, normalised to the same `Reindex` -------------------

  ∘ᴷ-lhs-norm : ∀ {C C' E₁ E₁' E₂ E₂'}
                (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
              → ((c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd {C} {E₁} {E₂})
                ≅ᴹ Reindex (Pair (Pair c u₂) u₁) (∘Rᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                                                 (∘Rₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
  ∘ᴷ-lhs-norm {C} {C'} {E₁} {E₁'} {E₂} {E₂'} c u₁ u₂ =
    ≅ᴹ-trans (∘ᴷ-lhs c u₁ u₂)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (dmᵢ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fᵢ {C} {E₁} {E₂}))
                 (dmₒ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fₒ⁻ {C} {E₁} {E₂}))
                 (⊗₁-norm-r c u₁ u₂))
    (≅ᴹ-trans (Reindex-fuse (Pair c (Pair u₁ u₂))
                 (nrᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (nrₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (dmᵢ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fᵢ {C} {E₁} {E₂}))
                 (dmₒ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fₒ⁻ {C} {E₁} {E₂})))
    (≅ᴹ-trans (Reindex-cong (Pair c (Pair u₁ u₂))
                 (λ i → nrᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
                            (dmᵢ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                                 (∘fᵢ {C} {E₁} {E₂}) i))
                 (∘Lᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (λ o → nrₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
                            (dmₒ {C ⊗₀ (E₁ ⊗₀ E₂)} {(C ⊗₀ E₂) ⊗₀ E₁} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                                 (∘fₒ⁻ {C} {E₁} {E₂}) o))
                 (∘Lₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}) pt-∘Lᵢ pt-∘Lₒ)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (∘Lᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                               (∘Lₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                               (Pair-rot3 c u₁ u₂))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair c u₂) u₁)
                 (rot3ᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (rot3ₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (∘Lᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (∘Lₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}))
              (Reindex-cong (Pair (Pair c u₂) u₁)
                 (λ i → rot3ᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
                              (∘Lᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} i))
                 (∘Rᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (λ o → rot3ₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}
                              (∘Lₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'} o))
                 (∘Rₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}) pt-rot3ᵢ pt-rot3ₒ))))))

  ∘ᴷ-rhs-norm : ∀ {C C' E₁ E₁' E₂ E₂'}
                (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
              → (∘ᴷ-fwd {C'} {E₁'} {E₂'} CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁))
                ≅ᴹ Reindex (Pair (Pair c u₂) u₁) (∘Rᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                                                 (∘Rₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
  ∘ᴷ-rhs-norm {C} {C'} {E₁} {E₁'} {E₂} {E₂'} c u₁ u₂ =
    ≅ᴹ-trans (∘ᴷ-rhs c u₁ u₂)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (cdᵢ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fₒ {C'} {E₁'} {E₂'}))
                 (cdₒ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fᵢ⁻ {C'} {E₁'} {E₂'}))
                 (⊗₁-norm-l c u₂ u₁))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair c u₂) u₁)
                 (nlᵢ {C} {C'} {E₂} {E₂'} {E₁} {E₁'})
                 (nlₒ {C} {C'} {E₂} {E₂'} {E₁} {E₁'})
                 (cdᵢ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fₒ {C'} {E₁'} {E₂'}))
                 (cdₒ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                      (∘fᵢ⁻ {C'} {E₁'} {E₂'})))
              (Reindex-cong (Pair (Pair c u₂) u₁)
                 (λ i → nlᵢ {C} {C'} {E₂} {E₂'} {E₁} {E₁'}
                            (cdᵢ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                                 (∘fₒ {C'} {E₁'} {E₂'}) i))
                 (∘Rᵢ {C} {C'} {E₁} {E₁'} {E₂} {E₂'})
                 (λ o → nlₒ {C} {C'} {E₂} {E₂'} {E₁} {E₁'}
                            (cdₒ {(C ⊗₀ E₂) ⊗₀ E₁} {(C' ⊗₀ E₂') ⊗₀ E₁'} {C' ⊗₀ (E₁' ⊗₀ E₂')}
                                 (∘fᵢ⁻ {C'} {E₁'} {E₂'}) o))
                 (∘Rₒ {C} {C'} {E₁} {E₁'} {E₂} {E₂'}) pt-∘Rᵢ pt-∘Rₒ)))

  -- ========================================================================
  -- `∘ᴷ-fwd` is natural.
  -- ========================================================================

  ∘ᴷ-fwd-natural : ∀ {C C' E₁ E₁' E₂ E₂'}
                   (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
                 → ((c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd)
                   ≅ᴹ (∘ᴷ-fwd CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁))
  ∘ᴷ-fwd-natural c u₁ u₂ =
    ≅ᴹ-trans (∘ᴷ-lhs-norm c u₁ u₂) (≅ᴹ-sym (∘ᴷ-rhs-norm c u₁ u₂))

  -- ========================================================================
  -- The second law: `⊗ᴷ-fwd` is natural.  Same shape, but both sides are
  -- four-fold, so the bridge between the nests is `Pair-mid4`.
  -- ========================================================================

  -- ---- the four-fold normalisation, `(m₁ ⊗₁ m₂) ⊗₁ (m₃ ⊗₁ m₄)` ----------

  n4ᵢ : ∀ {A₁ A₁' A₂ A₂' A₃ A₃' A₄ A₄'}
      → Channel.inType (((A₁ ⊗₀ A₂) ⊗₀ (A₃ ⊗₀ A₄)) ⊗ᵀ ((A₁' ⊗₀ A₂') ⊗₀ (A₃' ⊗₀ A₄')))
      → Channel.inType (((A₁ ⊗ᵀ A₁') ⊗₀ (A₂ ⊗ᵀ A₂')) ⊗₀ ((A₃ ⊗ᵀ A₃') ⊗₀ (A₄ ⊗ᵀ A₄')))
  n4ᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  n4ᵢ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  n4ᵢ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  n4ᵢ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  n4ᵢ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  n4ᵢ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  n4ᵢ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  n4ᵢ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  n4ₒ : ∀ {A₁ A₁' A₂ A₂' A₃ A₃' A₄ A₄'}
      → Channel.outType (((A₁ ⊗₀ A₂) ⊗₀ (A₃ ⊗₀ A₄)) ⊗ᵀ ((A₁' ⊗₀ A₂') ⊗₀ (A₃' ⊗₀ A₄')))
      → Channel.outType (((A₁ ⊗ᵀ A₁') ⊗₀ (A₂ ⊗ᵀ A₂')) ⊗₀ ((A₃ ⊗ᵀ A₃') ⊗₀ (A₄ ⊗ᵀ A₄')))
  n4ₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  n4ₒ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  n4ₒ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  n4ₒ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  n4ₒ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  n4ₒ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  n4ₒ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  n4ₒ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  pt-n4ᵢ : ∀ {A₁ A₁' A₂ A₂' A₃ A₃' A₄ A₄'}
           (i : Channel.inType (((A₁ ⊗₀ A₂) ⊗₀ (A₃ ⊗₀ A₄)) ⊗ᵀ
                                ((A₁' ⊗₀ A₂') ⊗₀ (A₃' ⊗₀ A₄'))))
         → ⊎ᵢ {A₁ ⊗₀ A₁' ᵀ} {(A₂ ⊗₀ A₂' ᵀ) ᵀ} {A₃ ⊗₀ A₃' ᵀ} {(A₄ ⊗₀ A₄' ᵀ) ᵀ}
              {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'}
              (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {In}))
              (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {In}))
              (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {In}) i)
           ≡ n4ᵢ {A₁} {A₁'} {A₂} {A₂'} {A₃} {A₃'} {A₄} {A₄'} i
  pt-n4ᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-n4ᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-n4ᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-n4ᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-n4ᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-n4ᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-n4ᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-n4ᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-n4ₒ : ∀ {A₁ A₁' A₂ A₂' A₃ A₃' A₄ A₄'}
           (o : Channel.outType (((A₁ ⊗₀ A₂) ⊗₀ (A₃ ⊗₀ A₄)) ⊗ᵀ
                                 ((A₁' ⊗₀ A₂') ⊗₀ (A₃' ⊗₀ A₄'))))
         → ⊎ₒ {A₁ ⊗₀ A₁' ᵀ} {(A₂ ⊗₀ A₂' ᵀ) ᵀ} {A₃ ⊗₀ A₃' ᵀ} {(A₄ ⊗₀ A₄' ᵀ) ᵀ}
              {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'}
              (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {Out}))
              (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {Out}))
              (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {Out}) o)
           ≡ n4ₒ {A₁} {A₁'} {A₂} {A₂'} {A₃} {A₃'} {A₄} {A₄'} o
  pt-n4ₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-n4ₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-n4ₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-n4ₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-n4ₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-n4ₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-n4ₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-n4ₒ (inj₂ (inj₂ (inj₂ _))) = refl

  ⊗₁-norm-4 : ∀ {A₁ A₁' A₂ A₂' A₃ A₃' A₄ A₄'}
              (m₁ : Machine A₁ A₁') (m₂ : Machine A₂ A₂')
              (m₃ : Machine A₃ A₃') (m₄ : Machine A₄ A₄')
            → ((m₁ ⊗₁ m₂) ⊗₁ (m₃ ⊗₁ m₄))
              ≅ᴹ Reindex (Pair (Pair m₁ m₂) (Pair m₃ m₄))
                   (n4ᵢ {A₁} {A₁'} {A₂} {A₂'} {A₃} {A₃'} {A₄} {A₄'})
                   (n4ₒ {A₁} {A₁'} {A₂} {A₂'} {A₃} {A₃'} {A₄} {A₄'})
  ⊗₁-norm-4 {A₁} {A₁'} {A₂} {A₂'} {A₃} {A₃'} {A₄} {A₄'} m₁ m₂ m₃ m₄ =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {In}))
                 (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {Out}))
                 (Pair-Reindex (Pair m₁ m₂) (Pair m₃ m₄)
                    (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {In}))
                    (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {Out}))
                    (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {In}))
                    (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {Out}))))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair m₁ m₂) (Pair m₃ m₄))
                 (⊎ᵢ {A₁ ⊗₀ A₁' ᵀ} {(A₂ ⊗₀ A₂' ᵀ) ᵀ} {A₃ ⊗₀ A₃' ᵀ} {(A₄ ⊗₀ A₄' ᵀ) ᵀ}
                     {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'}
                     (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {In}))
                     (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {In})))
                 (⊎ₒ {A₁ ⊗₀ A₁' ᵀ} {(A₂ ⊗₀ A₂' ᵀ) ᵀ} {A₃ ⊗₀ A₃' ᵀ} {(A₄ ⊗₀ A₄' ᵀ) ᵀ}
                     {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'}
                     (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {Out}))
                     (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {Out})))
                 (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {In}))
                 (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {Out})))
              (Reindex-cong (Pair (Pair m₁ m₂) (Pair m₃ m₄))
                 (λ i → ⊎ᵢ {A₁ ⊗₀ A₁' ᵀ} {(A₂ ⊗₀ A₂' ᵀ) ᵀ} {A₃ ⊗₀ A₃' ᵀ} {(A₄ ⊗₀ A₄' ᵀ) ᵀ}
                           {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'}
                           (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {In}))
                           (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {In}))
                           (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {In}) i))
                 (n4ᵢ {A₁} {A₁'} {A₂} {A₂'} {A₃} {A₃'} {A₄} {A₄'})
                 (λ o → ⊎ₒ {A₁ ⊗₀ A₁' ᵀ} {(A₂ ⊗₀ A₂' ᵀ) ᵀ} {A₃ ⊗₀ A₃' ᵀ} {(A₄ ⊗₀ A₄' ᵀ) ᵀ}
                           {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'}
                           (app (⊗σ {A₁} {A₁'} {A₂} {A₂'} {Out}))
                           (app (⊗σ {A₃} {A₃'} {A₄} {A₄'} {Out}))
                           (app (⊗σ {A₁ ⊗₀ A₂} {A₁' ⊗₀ A₂'} {A₃ ⊗₀ A₄} {A₃' ⊗₀ A₄'} {Out}) o))
                 (n4ₒ {A₁} {A₁'} {A₂} {A₂'} {A₃} {A₃'} {A₄} {A₄'}) pt-n4ᵢ pt-n4ₒ))

  -- ---- `⊗ᴷ-fwd`'s message maps, and their inverses ----------------------

  ⊗fᵢ : ∀ {B₁ E₁ B₂ E₂} → Channel.inType ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂))
                        → Channel.inType ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
  ⊗fᵢ {B₁} {E₁} {B₂} {E₂} = app (⊗ᴷ-fwdᵢ {B₁} {E₁} {B₂} {E₂})

  ⊗fₒ : ∀ {B₁ E₁ B₂ E₂} → Channel.outType ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
                        → Channel.outType ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂))
  ⊗fₒ {B₁} {E₁} {B₂} {E₂} = app (⊗ᴷ-fwdₒ {B₁} {E₁} {B₂} {E₂})

  ⊗fᵢ⁻ : ∀ {B₁ E₁ B₂ E₂} → Channel.inType ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
                         → Channel.inType ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂))
  ⊗fᵢ⁻ (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
  ⊗fᵢ⁻ (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
  ⊗fᵢ⁻ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  ⊗fᵢ⁻ (inj₂ (inj₂ x)) = inj₂ (inj₂ x)

  ⊗fₒ⁻ : ∀ {B₁ E₁ B₂ E₂} → Channel.outType ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂))
                         → Channel.outType ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
  ⊗fₒ⁻ (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
  ⊗fₒ⁻ (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
  ⊗fₒ⁻ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  ⊗fₒ⁻ (inj₂ (inj₂ x)) = inj₂ (inj₂ x)

  ⊗fₒ-l : ∀ {B₁ E₁ B₂ E₂} β
        → ⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂} (⊗fₒ {B₁} {E₁} {B₂} {E₂} β) ≡ β
  ⊗fₒ-l (inj₁ (inj₁ _)) = refl
  ⊗fₒ-l (inj₁ (inj₂ _)) = refl
  ⊗fₒ-l (inj₂ (inj₁ _)) = refl
  ⊗fₒ-l (inj₂ (inj₂ _)) = refl

  ⊗fₒ-r : ∀ {B₁ E₁ B₂ E₂} α
        → ⊗fₒ {B₁} {E₁} {B₂} {E₂} (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂} α) ≡ α
  ⊗fₒ-r (inj₁ (inj₁ _)) = refl
  ⊗fₒ-r (inj₁ (inj₂ _)) = refl
  ⊗fₒ-r (inj₂ (inj₁ _)) = refl
  ⊗fₒ-r (inj₂ (inj₂ _)) = refl

  ⊗fᵢ-l : ∀ {B₁ E₁ B₂ E₂} a
        → ⊗fᵢ⁻ {B₁} {E₁} {B₂} {E₂} (⊗fᵢ {B₁} {E₁} {B₂} {E₂} a) ≡ a
  ⊗fᵢ-l (inj₁ (inj₁ _)) = refl
  ⊗fᵢ-l (inj₁ (inj₂ _)) = refl
  ⊗fᵢ-l (inj₂ (inj₁ _)) = refl
  ⊗fᵢ-l (inj₂ (inj₂ _)) = refl

  ⊗fᵢ-r : ∀ {B₁ E₁ B₂ E₂} b
        → ⊗fᵢ {B₁} {E₁} {B₂} {E₂} (⊗fᵢ⁻ {B₁} {E₁} {B₂} {E₂} b) ≡ b
  ⊗fᵢ-r (inj₁ (inj₁ _)) = refl
  ⊗fᵢ-r (inj₁ (inj₂ _)) = refl
  ⊗fᵢ-r (inj₂ (inj₁ _)) = refl
  ⊗fᵢ-r (inj₂ (inj₂ _)) = refl

  -- ---- the forwarder as a reindexed identity, both ways -----------------

  ⊗ᴷ-Φdom : ∀ {B₁ E₁ B₂ E₂}
          → ⊗ᴷ-fwd {B₁} {E₁} {B₂} {E₂}
            ≅ᴹ Reindex (CC.id {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)})
                 (dmᵢ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} (⊗fᵢ {B₁} {E₁} {B₂} {E₂}))
                 (dmₒ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}))
  ⊗ᴷ-Φdom {B₁} {E₁} {B₂} {E₂} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗ᴷ-fwdᵢ {B₁} {E₁} {B₂} {E₂}) (⊗ᴷ-fwdₒ {B₁} {E₁} {B₂} {E₂}))
             (Xfwd-dom (⊗fᵢ {B₁} {E₁} {B₂} {E₂}) (⊗fₒ {B₁} {E₁} {B₂} {E₂})
                       (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}) ⊗fₒ-l ⊗fₒ-r)

  ⊗ᴷ-Φcod : ∀ {B₁ E₁ B₂ E₂}
          → ⊗ᴷ-fwd {B₁} {E₁} {B₂} {E₂}
            ≅ᴹ Reindex (CC.id {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)})
                 (cdᵢ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} (⊗fₒ {B₁} {E₁} {B₂} {E₂}))
                 (cdₒ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} (⊗fᵢ⁻ {B₁} {E₁} {B₂} {E₂}))
  ⊗ᴷ-Φcod {B₁} {E₁} {B₂} {E₂} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗ᴷ-fwdᵢ {B₁} {E₁} {B₂} {E₂}) (⊗ᴷ-fwdₒ {B₁} {E₁} {B₂} {E₂}))
             (Xfwd-cod (⊗fᵢ {B₁} {E₁} {B₂} {E₂}) (⊗fₒ {B₁} {E₁} {B₂} {E₂})
                       (⊗fᵢ⁻ {B₁} {E₁} {B₂} {E₂}) ⊗fᵢ-l ⊗fᵢ-r)

  -- ---- the two collapses ------------------------------------------------

  ⊗ᴷ-lhs : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
           (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
           (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
         → (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd {B₁} {E₁} {B₂} {E₂})
           ≅ᴹ Reindex ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂))
                (dmᵢ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                     {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ {B₁} {E₁} {B₂} {E₂}))
                (dmₒ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                     {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}))
  ⊗ᴷ-lhs {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} b₁ u₁ b₂ u₂ =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (⊗ᴷ-Φdom {B₁} {E₁} {B₂} {E₂}))
    (≅ᴹ-trans (∘-collapse-dom (CC.id {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)})
                              ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂))
                              (⊗fᵢ {B₁} {E₁} {B₂} {E₂}) (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}))
              (Reindex-resp-≅ᴹ
                 (dmᵢ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ {B₁} {E₁} {B₂} {E₂}))
                 (dmₒ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}))
                 ∘-identityʳ-≅ᴹ))

  ⊗ᴷ-rhs : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
           (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
           (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
         → (⊗ᴷ-fwd {B₁'} {E₁'} {B₂'} {E₂'} CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
           ≅ᴹ Reindex ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
                (cdᵢ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                     {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ {B₁'} {E₁'} {B₂'} {E₂'}))
                (cdₒ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                     {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ⁻ {B₁'} {E₁'} {B₂'} {E₂'}))
  ⊗ᴷ-rhs {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} b₁ u₁ b₂ u₂ =
    ≅ᴹ-trans (∘-resp-≅ᴹ (⊗ᴷ-Φcod {B₁'} {E₁'} {B₂'} {E₂'}) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-collapse-cod ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
                              (CC.id {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')})
                              (⊗fₒ {B₁'} {E₁'} {B₂'} {E₂'}) (⊗fᵢ⁻ {B₁'} {E₁'} {B₂'} {E₂'}))
              (Reindex-resp-≅ᴹ
                 (cdᵢ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ {B₁'} {E₁'} {B₂'} {E₂'}))
                 (cdₒ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ⁻ {B₁'} {E₁'} {B₂'} {E₂'}))
                 ∘-identityˡ-≅ᴹ))

  -- ---- the two routings, and the fact that they agree -------------------

  ⊗Lᵢ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
      → Channel.inType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                        ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.inType (((B₁ ⊗ᵀ B₁') ⊗₀ (B₂ ⊗ᵀ B₂')) ⊗₀ ((E₁ ⊗ᵀ E₁') ⊗₀ (E₂ ⊗ᵀ E₂')))
  ⊗Lᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  ⊗Lᵢ (inj₁ (inj₁ (inj₂ x))) = inj₂ (inj₁ (inj₁ x))
  ⊗Lᵢ (inj₁ (inj₂ (inj₁ x))) = inj₁ (inj₂ (inj₁ x))
  ⊗Lᵢ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  ⊗Lᵢ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  ⊗Lᵢ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  ⊗Lᵢ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  ⊗Lᵢ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  ⊗Lₒ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
      → Channel.outType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                         ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.outType (((B₁ ⊗ᵀ B₁') ⊗₀ (B₂ ⊗ᵀ B₂')) ⊗₀ ((E₁ ⊗ᵀ E₁') ⊗₀ (E₂ ⊗ᵀ E₂')))
  ⊗Lₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  ⊗Lₒ (inj₁ (inj₁ (inj₂ x))) = inj₂ (inj₁ (inj₁ x))
  ⊗Lₒ (inj₁ (inj₂ (inj₁ x))) = inj₁ (inj₂ (inj₁ x))
  ⊗Lₒ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  ⊗Lₒ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  ⊗Lₒ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  ⊗Lₒ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  ⊗Lₒ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  ⊗Rᵢ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
      → Channel.inType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                        ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.inType (((B₁ ⊗ᵀ B₁') ⊗₀ (E₁ ⊗ᵀ E₁')) ⊗₀ ((B₂ ⊗ᵀ B₂') ⊗₀ (E₂ ⊗ᵀ E₂')))
  ⊗Rᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  ⊗Rᵢ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  ⊗Rᵢ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  ⊗Rᵢ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  ⊗Rᵢ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  ⊗Rᵢ (inj₂ (inj₁ (inj₂ x))) = inj₂ (inj₁ (inj₂ x))
  ⊗Rᵢ (inj₂ (inj₂ (inj₁ x))) = inj₁ (inj₂ (inj₂ x))
  ⊗Rᵢ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  ⊗Rₒ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
      → Channel.outType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                         ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')))
      → Channel.outType (((B₁ ⊗ᵀ B₁') ⊗₀ (E₁ ⊗ᵀ E₁')) ⊗₀ ((B₂ ⊗ᵀ B₂') ⊗₀ (E₂ ⊗ᵀ E₂')))
  ⊗Rₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  ⊗Rₒ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  ⊗Rₒ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  ⊗Rₒ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  ⊗Rₒ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  ⊗Rₒ (inj₂ (inj₁ (inj₂ x))) = inj₂ (inj₁ (inj₂ x))
  ⊗Rₒ (inj₂ (inj₂ (inj₁ x))) = inj₁ (inj₂ (inj₂ x))
  ⊗Rₒ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  pt-⊗Lᵢ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
           (i : Channel.inType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                                ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂'))))
         → n4ᵢ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
             (dmᵢ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                  {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ {B₁} {E₁} {B₂} {E₂}) i)
           ≡ ⊗Lᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} i
  pt-⊗Lᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-⊗Lᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-⊗Lᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-⊗Lᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-⊗Lᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-⊗Lᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-⊗Lᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-⊗Lᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-⊗Lₒ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
           (o : Channel.outType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                                 ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂'))))
         → n4ₒ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
             (dmₒ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                  {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}) o)
           ≡ ⊗Lₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} o
  pt-⊗Lₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-⊗Lₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-⊗Lₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-⊗Lₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-⊗Lₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-⊗Lₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-⊗Lₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-⊗Lₒ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-⊗Rᵢ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
           (i : Channel.inType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                                ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂'))))
         → n4ᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'}
             (cdᵢ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                  {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ {B₁'} {E₁'} {B₂'} {E₂'}) i)
           ≡ ⊗Rᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} i
  pt-⊗Rᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-⊗Rᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-⊗Rᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-⊗Rᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-⊗Rᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-⊗Rᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-⊗Rᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-⊗Rᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-⊗Rₒ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
           (o : Channel.outType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                                 ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂'))))
         → n4ₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'}
             (cdₒ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                  {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ⁻ {B₁'} {E₁'} {B₂'} {E₂'}) o)
           ≡ ⊗Rₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} o
  pt-⊗Rₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-⊗Rₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-⊗Rₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-⊗Rₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-⊗Rₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-⊗Rₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-⊗Rₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-⊗Rₒ (inj₂ (inj₂ (inj₂ _))) = refl

  -- The message-level content of the law: the middle-four exchange takes the
  -- one routing to the other.
  pt-mid4ᵢ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
             (i : Channel.inType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                                  ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂'))))
           → mid4ᵢ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
               (⊗Lᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} i)
             ≡ ⊗Rᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} i
  pt-mid4ᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-mid4ᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-mid4ᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-mid4ᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-mid4ᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-mid4ᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-mid4ᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-mid4ᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-mid4ₒ : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
             (o : Channel.outType (((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ⊗ᵀ
                                   ((B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂'))))
           → mid4ₒ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
               (⊗Lₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} o)
             ≡ ⊗Rₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} o
  pt-mid4ₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-mid4ₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-mid4ₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-mid4ₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-mid4ₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-mid4ₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-mid4ₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-mid4ₒ (inj₂ (inj₂ (inj₂ _))) = refl

  -- ---- the two sides, normalised to the same `Reindex` -------------------

  ⊗ᴷ-lhs-norm : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
                (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
                (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
              → (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd {B₁} {E₁} {B₂} {E₂})
                ≅ᴹ Reindex (Pair (Pair b₁ u₁) (Pair b₂ u₂))
                     (⊗Rᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                     (⊗Rₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
  ⊗ᴷ-lhs-norm {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} b₁ u₁ b₂ u₂ =
    ≅ᴹ-trans (⊗ᴷ-lhs b₁ u₁ b₂ u₂)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (dmᵢ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ {B₁} {E₁} {B₂} {E₂}))
                 (dmₒ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}))
                 (⊗₁-norm-4 b₁ b₂ u₁ u₂))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair b₁ b₂) (Pair u₁ u₂))
                 (n4ᵢ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'})
                 (n4ₒ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'})
                 (dmᵢ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ {B₁} {E₁} {B₂} {E₂}))
                 (dmₒ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂})))
    (≅ᴹ-trans (Reindex-cong (Pair (Pair b₁ b₂) (Pair u₁ u₂))
                 (λ i → n4ᵢ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
                            (dmᵢ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                                 {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')}
                                 (⊗fᵢ {B₁} {E₁} {B₂} {E₂}) i))
                 (⊗Lᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                 (λ o → n4ₒ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
                            (dmₒ {(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)} {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)}
                                 {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')}
                                 (⊗fₒ⁻ {B₁} {E₁} {B₂} {E₂}) o))
                 (⊗Lₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'}) pt-⊗Lᵢ pt-⊗Lₒ)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (⊗Lᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                               (⊗Lₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                               (Pair-mid4 b₁ b₂ u₁ u₂))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair b₁ u₁) (Pair b₂ u₂))
                 (mid4ᵢ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'})
                 (mid4ₒ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'})
                 (⊗Lᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                 (⊗Lₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'}))
              (Reindex-cong (Pair (Pair b₁ u₁) (Pair b₂ u₂))
                 (λ i → mid4ᵢ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
                              (⊗Lᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} i))
                 (⊗Rᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                 (λ o → mid4ₒ {B₁} {B₁'} {B₂} {B₂'} {E₁} {E₁'} {E₂} {E₂'}
                              (⊗Lₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} o))
                 (⊗Rₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                 pt-mid4ᵢ pt-mid4ₒ))))))

  ⊗ᴷ-rhs-norm : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
                (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
                (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
              → (⊗ᴷ-fwd {B₁'} {E₁'} {B₂'} {E₂'} CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
                ≅ᴹ Reindex (Pair (Pair b₁ u₁) (Pair b₂ u₂))
                     (⊗Rᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                     (⊗Rₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
  ⊗ᴷ-rhs-norm {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} b₁ u₁ b₂ u₂ =
    ≅ᴹ-trans (⊗ᴷ-rhs b₁ u₁ b₂ u₂)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (cdᵢ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ {B₁'} {E₁'} {B₂'} {E₂'}))
                 (cdₒ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ⁻ {B₁'} {E₁'} {B₂'} {E₂'}))
                 (⊗₁-norm-4 b₁ u₁ b₂ u₂))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair b₁ u₁) (Pair b₂ u₂))
                 (n4ᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                 (n4ₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                 (cdᵢ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fₒ {B₁'} {E₁'} {B₂'} {E₂'}))
                 (cdₒ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                      {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')} (⊗fᵢ⁻ {B₁'} {E₁'} {B₂'} {E₂'})))
              (Reindex-cong (Pair (Pair b₁ u₁) (Pair b₂ u₂))
                 (λ i → n4ᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'}
                            (cdᵢ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                                 {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')}
                                 (⊗fₒ {B₁'} {E₁'} {B₂'} {E₂'}) i))
                 (⊗Rᵢ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'})
                 (λ o → n4ₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'}
                            (cdₒ {(B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)} {(B₁' ⊗₀ E₁') ⊗₀ (B₂' ⊗₀ E₂')}
                                 {(B₁' ⊗₀ B₂') ⊗₀ (E₁' ⊗₀ E₂')}
                                 (⊗fᵢ⁻ {B₁'} {E₁'} {B₂'} {E₂'}) o))
                 (⊗Rₒ {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'}) pt-⊗Rᵢ pt-⊗Rₒ)))

  -- ========================================================================
  -- `⊗ᴷ-fwd` is natural.
  -- ========================================================================

  ⊗ᴷ-fwd-natural : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
                   (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
                   (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
                 → (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd)
                   ≅ᴹ (⊗ᴷ-fwd CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
  ⊗ᴷ-fwd-natural b₁ u₁ b₂ u₂ =
    ≅ᴹ-trans (⊗ᴷ-lhs-norm b₁ u₁ b₂ u₂) (≅ᴹ-sym (⊗ᴷ-rhs-norm b₁ u₁ b₂ u₂))
