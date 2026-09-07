{-# OPTIONS --safe #-}

-- ============================================================================
-- Forwarders: the stateless, total, deterministic machines.
--
-- `TotalFunctionMachine'` builds a machine whose state is `⊤` and whose step
-- relation is a function: on input `i` it emits `just (φ i)`, always.  Every
-- structural machine of `Leios.ChannelCat` — `ρ⇒`, `λ⇒`, `σ`, `α⇒`, `α⇐`,
-- `mid4`, `absorb-regroup`, `∘ᴷ-fwd`, `⊗ᴷ-fwd` — is one, and so are `CC.id`
-- and `idᴷ`.
--
-- The point of this module is that forwarders are CLOSED under the three
-- machine builders: `_⊗₁_` (`⊗₁-Xfwd`), `modifyStepRel` (`modifyStepRel-Fwd`)
-- and `_∘_` (`∘-Xfwd`), with the composite forwarder computed explicitly in
-- each case.  An equation between two composites of forwarders therefore
-- reduces to a pointwise equation between two message-level functions, which
-- is a finite case split closed by `refl`.
--
-- That is what discharges the `Forwarders` tier of `Leios.ChannelCat.Monoidal`
-- (`ρ-∘ᴷ-fwd`, `ρ-idᴷ`, `λ-zip-idᴷ`) and the `MonoidalLaws` field `⊗₁-id`.
--
-- The hard case is `_∘_`, because it traces: a message bounces between the two
-- copies of the shared channel until it lands on an external port.  `Run`
-- below is that bouncing, `tr-Fwd` turns a total and deterministic `Run` into
-- a forwarder, and `∘-Xfwd` instantiates it — a crossing forwarder always
-- converges in exactly two hops.
--
-- Nothing here is specific to Leios; it belongs in `categorical-crypto`
-- proper, and lives here only because `_⊗₀_` has to be unfolded in the same
-- `opaque` block as the proofs that use it.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (id)
open import CategoricalCrypto.IsoExt using (⊗₁-resp-≅ᴹ)
import CategoricalCrypto as CC
open import Leios.ChannelCat using (ρ⇒; λ⇒)
open import Tactic.Defaults

module Leios.ChannelCat.Fwd where

open _≅ᴹ_

private
  just-inj : ∀ {a} {X : Type a} {x y : X} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  mapₘ : ∀ {X Y : Type} → (X → Y) → Maybe X → Maybe Y
  mapₘ f (just x) = just (f x)
  mapₘ f nothing  = nothing

  inj₁-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : X}
           → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y) → x ≡ y
  inj₁-inj refl = refl

  inj₂-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : Y}
           → _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y) → x ≡ y
  inj₂-inj refl = refl

  inj₁≢inj₂ : ∀ {a b} {X : Type a} {Y : Type b} {x : X} {y : Y} {ℓ} {W : Type ℓ}
            → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
  inj₁≢inj₂ ()

  -- Inversion view for `CompRel` at fully general indices.
  comp-view :
    ∀ {A B C D} {M₁ : Machine A B} {M₂ : Machine C D}
      {sp : Machine.State M₁ × Machine.State M₂} {x y sp'}
    → Tensor.CompRel M₁ M₂ sp x y sp'
    → (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (ϵ ⊗R) ↑ᵢ mᵢ) × (y ≡ ((ϵ ⊗R) ↑ₒ_ <$> mo))
         × (proj₂ sp' ≡ proj₂ sp)
         × Machine.stepRel M₁ (proj₁ sp) mᵢ mo (proj₁ sp'))
    ⊎ (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (L⊗ ϵ) ↑ᵢ mᵢ) × (y ≡ ((L⊗ ϵ) ↑ₒ_ <$> mo))
         × (proj₁ sp' ≡ proj₁ sp)
         × Machine.stepRel M₂ (proj₂ sp) mᵢ mo (proj₂ sp'))
  comp-view (Tensor.Step₁ q) = inj₁ (_ , _ , refl , refl , refl , q)
  comp-view (Tensor.Step₂ q) = inj₂ (_ , _ , refl , refl , refl , q)

-- Congruences for the two machine builders `_∘_` is made of.
modifyStepRel-resp-≅ᴹ : ∀ {A B C D} {M N : Machine A B}
    (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
  → M ≅ᴹ N → modifyStepRel p M ≅ᴹ modifyStepRel p N
modifyStepRel-resp-≅ᴹ p φ =
  MkIso (to φ) (from φ) (from∘to φ) (to∘from φ) (step-to φ) (step-from φ)

tr-resp-≅ᴹ : ∀ {A B C} {M N : Machine (A ⊗₀ C) (B ⊗₀ C)}
           → M ≅ᴹ N → tr M ≅ᴹ tr N
tr-resp-≅ᴹ {M = M} {N} φ = MkIso (to φ) (from φ) (from∘to φ) (to∘from φ)
  (go φ) (go (≅ᴹ-sym φ))
  where
  go : ∀ {M N : Machine (_ ⊗₀ _) (_ ⊗₀ _)} (ρ : M ≅ᴹ N) {s i mo s'}
     → TraceRel M s i mo s' → TraceRel N (to ρ s) i mo (to ρ s')
  go ρ Trace[ p ]      = Trace[ step-to ρ p ]
  go ρ (p Trace∷ₒ tr₀) = step-to ρ p Trace∷ₒ go ρ tr₀
  go ρ (p Trace∷ᵢ tr₀) = step-to ρ p Trace∷ᵢ go ρ tr₀

-- A stateless, total, deterministic machine.
Fwd : ∀ {A B} → (Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B)) → Machine A B
Fwd φ = MkMachine {State = ⊤} (λ _ i o _ → just (φ i) ≡ o)

-- Every `TotalFunctionMachine` is one, definitionally.
tfm-is-Fwd : ∀ {A B} (p : (A ⊗ᵀ B) [ In ]⇒[ Out ] (A ⊗ᵀ B))
           → TotalFunctionMachine {A} {B} p ≡ Fwd (app p)
tfm-is-Fwd _ = refl

-- Pointwise-equal forwarders are isomorphic.
Fwd-≅ᴹ : ∀ {A B} {φ ψ : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B)}
       → (∀ x → φ x ≡ ψ x) → Fwd φ ≅ᴹ Fwd ψ
Fwd-≅ᴹ {φ = φ} {ψ} eq = MkIso _ _ (λ _ → refl) (λ _ → refl)
  (λ {_} {i} p → trans (cong just (sym (eq i))) p)
  (λ {_} {i} p → trans (cong just (eq i)) p)

-- Relabelling a forwarder is a forwarder, whenever the output relabelling is
-- injective (it need not be surjective — `_∣ˡ` and `_∣^ˡ` are not).
modifyStepRel-Fwd : ∀ {A B C D} (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
    (χ : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B))
    (κ : Channel.inType (C ⊗ᵀ D) → Channel.outType (C ⊗ᵀ D))
  → (∀ i → app (p {Out}) (κ i) ≡ χ (app (p {In}) i))
  → (∀ {x y} → app (p {Out}) x ≡ app (p {Out}) y → x ≡ y)
  → modifyStepRel p (Fwd χ) ≅ᴹ Fwd κ
modifyStepRel-Fwd {A} {B} {C} {D} p χ κ sq inj =
  MkIso _ _ (λ _ → refl) (λ _ → refl)
    (λ {_} {i} {o} e → t i o e) (λ {_} {i} {o} e → f i o e)
  where
  t : (i : Channel.inType (C ⊗ᵀ D)) (o : Maybe (Channel.outType (C ⊗ᵀ D)))
    → just (χ (app (p {In}) i)) ≡ (app (p {Out}) <$> o) → just (κ i) ≡ o
  t i (just y)  e = cong just (inj (trans (sq i) (just-inj e)))
  t i nothing  ()
  f : (i : Channel.inType (C ⊗ᵀ D)) (o : Maybe (Channel.outType (C ⊗ᵀ D)))
    → just (κ i) ≡ o → just (χ (app (p {In}) i)) ≡ (app (p {Out}) <$> o)
  f i _ refl = cong just (sym (sq i))

∘ᴷ-fwdᵢ : ∀ {C E₁ E₂} → ((C ⊗₀ E₂) ⊗₀ E₁) [ In ]⇒[ In ] (C ⊗₀ (E₁ ⊗₀ E₂))
∘ᴷ-fwdᵢ = ⇒-solver

∘ᴷ-fwdₒ : ∀ {C E₁ E₂} → (C ⊗₀ (E₁ ⊗₀ E₂)) [ Out ]⇒[ Out ] ((C ⊗₀ E₂) ⊗₀ E₁)
∘ᴷ-fwdₒ = ⇒-solver

-- The two shuffles inside `_∘ᴷ_` and `_⊗ᴷ_`, named (moved here from
-- `Leios.ChannelCat.Monoidal`, which re-exports them).
∘ᴷ-fwd : ∀ {C E₁ E₂} → Machine ((C ⊗₀ E₂) ⊗₀ E₁) (C ⊗₀ (E₁ ⊗₀ E₂))
∘ᴷ-fwd = TotalFunctionMachine' ⇒-solver ⇒-solver

⊗ᴷ-fwd : ∀ {B₁ E₁ B₂ E₂} → Machine ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
⊗ᴷ-fwd = TotalFunctionMachine' ⇒-solver ⇒-solver

∘ᴷ-fwd-named : ∀ {C E₁ E₂} → ∘ᴷ-fwd {C} {E₁} {E₂} ≡ TotalFunctionMachine' ∘ᴷ-fwdᵢ ∘ᴷ-fwdₒ
∘ᴷ-fwd-named = refl

-- The internal run of `tr`: a message bounces between the two copies of the
-- traced channel until it lands on an external port.  Stated over the raw
-- message sums, since a `data` declaration is not affected by `opaque`.
data Run {aᵢ bₒ cᵢ cₒ aₒ bᵢ : Type}
         (κ : (aᵢ ⊎ cᵢ) ⊎ (bₒ ⊎ cₒ) → (aₒ ⊎ cₒ) ⊎ (bᵢ ⊎ cᵢ))
     : (aᵢ ⊎ cᵢ) ⊎ (bₒ ⊎ cₒ) → (aₒ ⊎ cₒ) ⊎ (bᵢ ⊎ cᵢ) → Type where
  stop : ∀ {m} → Run κ m (κ m)
  goₒ  : ∀ {m v x} → κ m ≡ inj₁ (inj₂ x) → Run κ (inj₂ (inj₂ x)) v → Run κ m v
  goᵢ  : ∀ {m v y} → κ m ≡ inj₂ (inj₂ y) → Run κ (inj₁ (inj₂ y)) v → Run κ m v

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

  private
    tag₁ : ∀ {W X Y Z : Type} → W ⊎ X → (W ⊎ Y) ⊎ (X ⊎ Z)
    tag₁ (inj₁ w) = inj₁ (inj₁ w)
    tag₁ (inj₂ x) = inj₂ (inj₁ x)

    tag₂ : ∀ {W X Y Z : Type} → Y ⊎ Z → (W ⊎ Y) ⊎ (X ⊎ Z)
    tag₂ (inj₁ y) = inj₁ (inj₂ y)
    tag₂ (inj₂ z) = inj₂ (inj₂ z)

  -- The forwarder underlying a tensor of two forwarders.
  ⊗Fwd : ∀ {A B C D}
       → (Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B))
       → (Channel.inType (C ⊗ᵀ D) → Channel.outType (C ⊗ᵀ D))
       → Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D))
       → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D))
  ⊗Fwd φ ψ (inj₁ (inj₁ a)) = tag₁ (φ (inj₁ a))
  ⊗Fwd φ ψ (inj₁ (inj₂ c)) = tag₂ (ψ (inj₁ c))
  ⊗Fwd φ ψ (inj₂ (inj₁ b)) = tag₁ (φ (inj₂ b))
  ⊗Fwd φ ψ (inj₂ (inj₂ d)) = tag₂ (ψ (inj₂ d))

  private
    ⊗Fwd-to : ∀ {A B C D}
              (φ : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B))
              (ψ : Channel.inType (C ⊗ᵀ D) → Channel.outType (C ⊗ᵀ D))
              {s s'} (i : Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D)))
              (o : Maybe (Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D))))
            → Machine.stepRel (Fwd φ ⊗₁ Fwd ψ) s i o s' → just (⊗Fwd φ ψ i) ≡ o
    -- ── left column (A-in, B-out): only `Step₁` can fire ──
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) o p with comp-view p
    ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) (just (inj₁ (inj₁ ao))) p | inj₁ (_ , just w , xeq , yeq , _ , q)
      with inj₁-inj xeq | inj₁-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₁ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) (just (inj₂ (inj₁ bi))) p | inj₁ (_ , just w , xeq , yeq , _ , q)
      with inj₁-inj xeq | inj₁-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₁ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) (just (inj₁ (inj₂ co))) p | inj₁ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (sym (just-inj yeq))
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) (just (inj₂ (inj₂ di))) p | inj₁ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (sym (just-inj yeq))
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) (just _) p | inj₁ (_ , nothing , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) nothing  p | inj₁ (_ , just w , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₁ (inj₁ a)) nothing  p | inj₁ (_ , nothing , xeq , yeq , _ , ())
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) o p with comp-view p
    ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) (just (inj₁ (inj₁ ao))) p | inj₁ (_ , just w , xeq , yeq , _ , q)
      with inj₁-inj xeq | inj₁-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₁ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) (just (inj₂ (inj₁ bi))) p | inj₁ (_ , just w , xeq , yeq , _ , q)
      with inj₁-inj xeq | inj₁-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₁ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) (just (inj₁ (inj₂ co))) p | inj₁ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (sym (just-inj yeq))
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) (just (inj₂ (inj₂ di))) p | inj₁ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (sym (just-inj yeq))
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) (just _) p | inj₁ (_ , nothing , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) nothing  p | inj₁ (_ , just w , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₂ (inj₁ b)) nothing  p | inj₁ (_ , nothing , xeq , yeq , _ , ())
    -- ── right column (C-in, D-out): only `Step₂` can fire ──
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) o p with comp-view p
    ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) (just (inj₁ (inj₂ co))) p | inj₂ (_ , just w , xeq , yeq , _ , q)
      with inj₂-inj xeq | inj₂-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₂ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) (just (inj₂ (inj₂ di))) p | inj₂ (_ , just w , xeq , yeq , _ , q)
      with inj₂-inj xeq | inj₂-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₂ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) (just (inj₁ (inj₁ ao))) p | inj₂ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (just-inj yeq)
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) (just (inj₂ (inj₁ bi))) p | inj₂ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (just-inj yeq)
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) (just _) p | inj₂ (_ , nothing , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) nothing  p | inj₂ (_ , just w , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₁ (inj₂ c)) nothing  p | inj₂ (_ , nothing , xeq , yeq , _ , ())
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) o p with comp-view p
    ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) (just (inj₁ (inj₂ co))) p | inj₂ (_ , just w , xeq , yeq , _ , q)
      with inj₂-inj xeq | inj₂-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₂ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) (just (inj₂ (inj₂ di))) p | inj₂ (_ , just w , xeq , yeq , _ , q)
      with inj₂-inj xeq | inj₂-inj (just-inj yeq)
    ... | refl | refl = cong (λ x → just (tag₂ x)) (just-inj q)
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) (just (inj₁ (inj₁ ao))) p | inj₂ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (just-inj yeq)
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) (just (inj₂ (inj₁ bi))) p | inj₂ (_ , just w , xeq , yeq , _ , q) =
      inj₁≢inj₂ (just-inj yeq)
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) (just _) p | inj₂ (_ , nothing , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) nothing  p | inj₂ (_ , just w , xeq , () , _ , q)
    ⊗Fwd-to φ ψ (inj₂ (inj₂ d)) nothing  p | inj₂ (_ , nothing , xeq , yeq , _ , ())

    ⊗Fwd-from : ∀ {A B C D}
                (φ : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B))
                (ψ : Channel.inType (C ⊗ᵀ D) → Channel.outType (C ⊗ᵀ D))
                {s s'} (i : Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D)))
                (o : Maybe (Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ D))))
              → just (⊗Fwd φ ψ i) ≡ o → Machine.stepRel (Fwd φ ⊗₁ Fwd ψ) s i o s'
    ⊗Fwd-from φ ψ (inj₁ (inj₁ a)) _ refl with φ (inj₁ a) in eq
    ... | inj₁ ao = Tensor.Step₁ (cong just eq)
    ... | inj₂ bi = Tensor.Step₁ (cong just eq)
    ⊗Fwd-from φ ψ (inj₂ (inj₁ b)) _ refl with φ (inj₂ b) in eq
    ... | inj₁ ao = Tensor.Step₁ (cong just eq)
    ... | inj₂ bi = Tensor.Step₁ (cong just eq)
    ⊗Fwd-from φ ψ (inj₁ (inj₂ c)) _ refl with ψ (inj₁ c) in eq
    ... | inj₁ co = Tensor.Step₂ (cong just eq)
    ... | inj₂ di = Tensor.Step₂ (cong just eq)
    ⊗Fwd-from φ ψ (inj₂ (inj₂ d)) _ refl with ψ (inj₂ d) in eq
    ... | inj₁ co = Tensor.Step₂ (cong just eq)
    ... | inj₂ di = Tensor.Step₂ (cong just eq)

  -- A tensor of forwarders is a forwarder.
  ⊗₁-Fwd : ∀ {A B C D} {φ : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B)}
                       {ψ : Channel.inType (C ⊗ᵀ D) → Channel.outType (C ⊗ᵀ D)}
         → (Fwd φ ⊗₁ Fwd ψ) ≅ᴹ Fwd (⊗Fwd φ ψ)
  ⊗₁-Fwd {φ = φ} {ψ} = MkIso (λ _ → tt) (λ _ → tt , tt) (λ _ → refl) (λ _ → refl)
    (λ {_} {i} {o} p → ⊗Fwd-to φ ψ i o p)
    (λ {_} {i} {o} p → ⊗Fwd-from φ ψ i o p)

  -- `_⊗₁_` preserves the identity.
  ⊗₁-id : ∀ {A B} → (CC.id {A} ⊗₁ CC.id {B}) ≅ᴹ CC.id {A ⊗₀ B}
  ⊗₁-id = ≅ᴹ-trans ⊗₁-Fwd (Fwd-≅ᴹ λ { (inj₁ (inj₁ a)) → refl
                                     ; (inj₁ (inj₂ c)) → refl
                                     ; (inj₂ (inj₁ b)) → refl
                                     ; (inj₂ (inj₂ d)) → refl })

  -- ══════════════════════════════════════════════════════════════════════
  -- Tracing a forwarder.
  -- ══════════════════════════════════════════════════════════════════════

  -- `Run` at the channel-shaped indices (all six type arguments pinned, so that
  -- nothing has to be inverted through `_⊗₀_`).
  Runᶜ : ∀ {A B C} (κ : Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
                     → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C)))
       → Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
       → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C)) → Type
  Runᶜ {A} {B} {C} = Run {Channel.inType A} {Channel.outType B} {Channel.inType C}
                         {Channel.outType C} {Channel.outType A} {Channel.inType B}

  private
    Run→Trace : ∀ {A B C} {κ : Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
                             → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))} {m v}
              → Runᶜ κ m v → TraceRel (Fwd κ) tt m (just v) tt
    Run→Trace stop        = Trace[ refl ]
    Run→Trace (goₒ eq r)  = cong just eq Trace∷ₒ Run→Trace r
    Run→Trace (goᵢ eq r)  = cong just eq Trace∷ᵢ Run→Trace r

    Trace→Run : ∀ {A B C} {κ : Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
                             → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))} {m mo}
              → TraceRel (Fwd κ) tt m mo tt
              → ∃ λ v → (mo ≡ just v) × Runᶜ κ m v
    Trace→Run Trace[ p ]     = _ , sym p , stop
    Trace→Run (p Trace∷ₒ r)  = let (v , e , r') = Trace→Run r in v , e , goₒ (just-inj p) r'
    Trace→Run (p Trace∷ᵢ r)  = let (v , e , r') = Trace→Run r in v , e , goᵢ (just-inj p) r'

  -- The external ports of the traced machine, as seen from inside.
  ιₜ : ∀ {A B C} → Channel.inType (A ⊗ᵀ B) → Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
  ιₜ (inj₁ a)  = inj₁ (inj₁ a)
  ιₜ (inj₂ bo) = inj₂ (inj₁ bo)

  εₜ : ∀ {A B C} → Channel.outType (A ⊗ᵀ B) → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
  εₜ (inj₁ ao) = inj₁ (inj₁ ao)
  εₜ (inj₂ bi) = inj₂ (inj₁ bi)

  private
    εₜ-inj : ∀ {A B C} {x y : Channel.outType (A ⊗ᵀ B)} → εₜ {A} {B} {C} x ≡ εₜ y → x ≡ y
    εₜ-inj {x = inj₁ _} {inj₁ _} e = cong inj₁ (inj₁-inj (inj₁-inj e))
    εₜ-inj {x = inj₂ _} {inj₂ _} e = cong inj₂ (inj₁-inj (inj₂-inj e))
    εₜ-inj {x = inj₁ _} {inj₂ _} e = inj₁≢inj₂ e
    εₜ-inj {x = inj₂ _} {inj₁ _} e = inj₁≢inj₂ (sym e)

    -- `tr`'s two `modifyStepRel` layers, computed away.
    tr-unfold : ∀ {A B C} (κ : Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
                             → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C)))
                (i : Channel.inType (A ⊗ᵀ B))
                (o : Maybe (Channel.outType (A ⊗ᵀ B)))
              → Machine.stepRel (tr {A} {B} {C} (Fwd κ)) tt i o tt
              ≡ TraceRel (Fwd κ) tt (ιₜ i) (mapₘ εₜ o) tt
    tr-unfold κ (inj₁ a)  (just (inj₁ ao)) = refl
    tr-unfold κ (inj₁ a)  (just (inj₂ bi)) = refl
    tr-unfold κ (inj₁ a)  nothing          = refl
    tr-unfold κ (inj₂ bo) (just (inj₁ ao)) = refl
    tr-unfold κ (inj₂ bo) (just (inj₂ bi)) = refl
    tr-unfold κ (inj₂ bo) nothing          = refl

  -- Tracing a forwarder yields the forwarder that runs it to an external port.
  tr-Fwd : ∀ {A B C : Channel}
             {κ : Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
                → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))}
             {κ° : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B)}
         → (∀ i → Runᶜ κ (ιₜ {A} {B} {C} i) (εₜ {A} {B} {C} (κ° i)))
         → (∀ i v → Runᶜ κ (ιₜ {A} {B} {C} i) (εₜ {A} {B} {C} v) → v ≡ κ° i)
         → tr {A} {B} {C} (Fwd κ) ≅ᴹ Fwd κ°
  tr-Fwd {A} {B} {C} {κ} {κ°} total uniq =
    MkIso _ _ (λ _ → refl) (λ _ → refl)
      (λ {_} {i} {o} p → t i o (subst (λ X → X) (tr-unfold κ i o) p))
      (λ {_} {i} {o} p → subst (λ X → X) (sym (tr-unfold κ i o)) (f i o p))
    where
    t : ∀ i o → TraceRel (Fwd κ) tt (ιₜ {A} {B} {C} i) (mapₘ (εₜ {A} {B} {C}) o) tt → just (κ° i) ≡ o
    t i (just y) tr₀ with Trace→Run tr₀
    ... | v , e , r =
      cong just (sym (uniq i y (subst (Runᶜ κ (ιₜ {A} {B} {C} i)) (sym (just-inj e)) r)))
    t i nothing tr₀ with Trace→Run tr₀
    ... | v , () , r
    f : ∀ i o → just (κ° i) ≡ o → TraceRel (Fwd κ) tt (ιₜ {A} {B} {C} i) (mapₘ (εₜ {A} {B} {C}) o) tt
    f i _ refl = Run→Trace (total i)

  -- ══════════════════════════════════════════════════════════════════════
  -- Crossing forwarders, and their composition.
  -- ══════════════════════════════════════════════════════════════════════

  -- The forwarder that relays every domain input to the codomain and back.
  -- This is exactly what `TotalFunctionMachine'` builds.
  Xφ : ∀ {A B} → (Channel.inType A → Channel.inType B)
                → (Channel.outType B → Channel.outType A)
     → Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B)
  Xφ f g (inj₁ a)  = inj₂ (f a)
  Xφ f g (inj₂ bo) = inj₁ (g bo)

  Xfwd : ∀ {A B} → (Channel.inType A → Channel.inType B)
                 → (Channel.outType B → Channel.outType A) → Machine A B
  Xfwd f g = Fwd (Xφ f g)

  tfm'-is-Xfwd : ∀ {A B} (p : A [ In ]⇒[ In ] B) (q : B [ Out ]⇒[ Out ] A)
               → TotalFunctionMachine' p q ≅ᴹ Xfwd (app p) (app q)
  tfm'-is-Xfwd p q = Fwd-≅ᴹ λ { (inj₁ a) → refl ; (inj₂ bo) → refl }

  id-is-Xfwd : ∀ {A} → CC.id {A} ≅ᴹ Xfwd (λ (a : Channel.inType A) → a) (λ o → o)
  id-is-Xfwd = tfm'-is-Xfwd _ _

  -- `_∘_`'s own reshuffle, re-elaborated (the solver is deterministic).
  ∘σ : ∀ {A B C m} → (A ⊗₀ B) ⊗₀ (C ⊗₀ B) ᵀ [ m ]⇒[ m ] (A ⊗₀ B) ⊗₀ (B ⊗₀ C) ᵀ
  ∘σ = ⇒-solver

  ∘σ-ok : ∀ {A B C} (M : Machine A B) (N : Machine B C)
        → (N CC.∘ M) ≡ tr {A} {C} {B} (modifyStepRel ∘σ (M ⊗₁ N))
  ∘σ-ok M N = refl

  -- The traced core of `Xfwd f₂ g₂ ∘ Xfwd f₁ g₁`, as a forwarder.
  ∘κ : ∀ {A B C}
       (f₁ : Channel.inType A → Channel.inType B) (g₁ : Channel.outType B → Channel.outType A)
       (f₂ : Channel.inType B → Channel.inType C) (g₂ : Channel.outType C → Channel.outType B)
     → Channel.inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)) → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  ∘κ f₁ g₁ f₂ g₂ (inj₁ (inj₁ a))  = inj₂ (inj₂ (f₁ a))
  ∘κ f₁ g₁ f₂ g₂ (inj₁ (inj₂ b))  = inj₂ (inj₁ (f₂ b))
  ∘κ f₁ g₁ f₂ g₂ (inj₂ (inj₁ co)) = inj₁ (inj₂ (g₂ co))
  ∘κ f₁ g₁ f₂ g₂ (inj₂ (inj₂ bo)) = inj₁ (inj₁ (g₁ bo))

  private
    ∘sq : ∀ {A B C}
          (f₁ : Channel.inType A → Channel.inType B) (g₁ : Channel.outType B → Channel.outType A)
          (f₂ : Channel.inType B → Channel.inType C) (g₂ : Channel.outType C → Channel.outType B)
        → ∀ i → app (∘σ {A} {B} {C} {Out}) (∘κ f₁ g₁ f₂ g₂ i)
              ≡ ⊗Fwd (Xφ f₁ g₁) (Xφ f₂ g₂) (app (∘σ {A} {B} {C} {In}) i)
    ∘sq f₁ g₁ f₂ g₂ (inj₁ (inj₁ a))  = refl
    ∘sq f₁ g₁ f₂ g₂ (inj₁ (inj₂ b))  = refl
    ∘sq f₁ g₁ f₂ g₂ (inj₂ (inj₁ co)) = refl
    ∘sq f₁ g₁ f₂ g₂ (inj₂ (inj₂ bo)) = refl

    ∘σ-inj : ∀ {A B C} {x y : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))}
           → app (∘σ {A} {B} {C} {Out}) x ≡ app (∘σ {A} {B} {C} {Out}) y → x ≡ y
    ∘σ-inj {x = inj₁ (inj₁ _)} {inj₁ (inj₁ _)} e = cong (λ z → inj₁ (inj₁ z)) (inj₁-inj (inj₁-inj e))
    ∘σ-inj {x = inj₁ (inj₁ _)} {inj₁ (inj₂ _)} e = inj₁≢inj₂ (inj₁-inj e)
    ∘σ-inj {x = inj₁ (inj₁ _)} {inj₂ (inj₁ _)} e = inj₁≢inj₂ e
    ∘σ-inj {x = inj₁ (inj₁ _)} {inj₂ (inj₂ _)} e = inj₁≢inj₂ e
    ∘σ-inj {x = inj₁ (inj₂ _)} {inj₁ (inj₁ _)} e = inj₁≢inj₂ (sym (inj₁-inj e))
    ∘σ-inj {x = inj₁ (inj₂ _)} {inj₁ (inj₂ _)} e = cong (λ z → inj₁ (inj₂ z)) (inj₂-inj (inj₁-inj e))
    ∘σ-inj {x = inj₁ (inj₂ _)} {inj₂ (inj₁ _)} e = inj₁≢inj₂ e
    ∘σ-inj {x = inj₁ (inj₂ _)} {inj₂ (inj₂ _)} e = inj₁≢inj₂ e
    ∘σ-inj {x = inj₂ (inj₁ _)} {inj₁ (inj₁ _)} e = inj₁≢inj₂ (sym e)
    ∘σ-inj {x = inj₂ (inj₁ _)} {inj₁ (inj₂ _)} e = inj₁≢inj₂ (sym e)
    ∘σ-inj {x = inj₂ (inj₁ _)} {inj₂ (inj₁ _)} e = cong (λ z → inj₂ (inj₁ z)) (inj₂-inj (inj₂-inj e))
    ∘σ-inj {x = inj₂ (inj₁ _)} {inj₂ (inj₂ _)} e = inj₁≢inj₂ (sym (inj₂-inj e))
    ∘σ-inj {x = inj₂ (inj₂ _)} {inj₁ (inj₁ _)} e = inj₁≢inj₂ (sym e)
    ∘σ-inj {x = inj₂ (inj₂ _)} {inj₁ (inj₂ _)} e = inj₁≢inj₂ (sym e)
    ∘σ-inj {x = inj₂ (inj₂ _)} {inj₂ (inj₁ _)} e = inj₁≢inj₂ (inj₂-inj e)
    ∘σ-inj {x = inj₂ (inj₂ _)} {inj₂ (inj₂ _)} e = cong (λ z → inj₂ (inj₂ z)) (inj₁-inj (inj₂-inj e))

    ∘total : ∀ {A B C}
             (f₁ : Channel.inType A → Channel.inType B) (g₁ : Channel.outType B → Channel.outType A)
             (f₂ : Channel.inType B → Channel.inType C) (g₂ : Channel.outType C → Channel.outType B)
           → ∀ i → Runᶜ {A} {C} {B} (∘κ f₁ g₁ f₂ g₂) (ιₜ {A} {C} {B} i)
                        (εₜ {A} {C} {B} (Xφ (λ a → f₂ (f₁ a)) (λ co → g₁ (g₂ co)) i))
    ∘total f₁ g₁ f₂ g₂ (inj₁ a)  = goᵢ refl stop
    ∘total f₁ g₁ f₂ g₂ (inj₂ co) = goₒ refl stop

    ∘uniq : ∀ {A B C}
            (f₁ : Channel.inType A → Channel.inType B) (g₁ : Channel.outType B → Channel.outType A)
            (f₂ : Channel.inType B → Channel.inType C) (g₂ : Channel.outType C → Channel.outType B)
          → ∀ i v → Runᶜ {A} {C} {B} (∘κ f₁ g₁ f₂ g₂) (ιₜ {A} {C} {B} i) (εₜ {A} {C} {B} v)
          → v ≡ Xφ (λ a → f₂ (f₁ a)) (λ co → g₁ (g₂ co)) i
    ∘uniq f₁ g₁ f₂ g₂ (inj₁ a)  (inj₁ ao) (goₒ () _)
    ∘uniq f₁ g₁ f₂ g₂ (inj₁ a)  (inj₁ ao) (goᵢ refl (goₒ () _))
    ∘uniq f₁ g₁ f₂ g₂ (inj₁ a)  (inj₁ ao) (goᵢ refl (goᵢ () _))
    ∘uniq f₁ g₁ f₂ g₂ (inj₁ a)  (inj₂ ci) (goₒ () _)
    ∘uniq f₁ g₁ f₂ g₂ (inj₁ a)  (inj₂ ci) (goᵢ refl stop) = refl
    ∘uniq f₁ g₁ f₂ g₂ (inj₁ a)  (inj₂ ci) (goᵢ refl (goₒ () _))
    ∘uniq f₁ g₁ f₂ g₂ (inj₁ a)  (inj₂ ci) (goᵢ refl (goᵢ () _))
    ∘uniq f₁ g₁ f₂ g₂ (inj₂ co) (inj₁ ao) (goᵢ () _)
    ∘uniq f₁ g₁ f₂ g₂ (inj₂ co) (inj₁ ao) (goₒ refl stop) = refl
    ∘uniq f₁ g₁ f₂ g₂ (inj₂ co) (inj₁ ao) (goₒ refl (goₒ () _))
    ∘uniq f₁ g₁ f₂ g₂ (inj₂ co) (inj₁ ao) (goₒ refl (goᵢ () _))
    ∘uniq f₁ g₁ f₂ g₂ (inj₂ co) (inj₂ ci) (goᵢ () _)
    ∘uniq f₁ g₁ f₂ g₂ (inj₂ co) (inj₂ ci) (goₒ refl (goₒ () _))
    ∘uniq f₁ g₁ f₂ g₂ (inj₂ co) (inj₂ ci) (goₒ refl (goᵢ () _))

  -- Crossing forwarders compose, and the composite is the obvious one: forward
  -- maps compose in order, backward maps in the other.  Everything below is a
  -- corollary of this together with `⊗₁-Xfwd`.
  ∘-Xfwd : ∀ {A B C}
           {f₁ : Channel.inType A → Channel.inType B} {g₁ : Channel.outType B → Channel.outType A}
           {f₂ : Channel.inType B → Channel.inType C} {g₂ : Channel.outType C → Channel.outType B}
         → (Xfwd f₂ g₂ CC.∘ Xfwd f₁ g₁) ≅ᴹ Xfwd (λ a → f₂ (f₁ a)) (λ co → g₁ (g₂ co))
  ∘-Xfwd {A} {B} {C} {f₁} {g₁} {f₂} {g₂} =
    ≅ᴹ-trans (tr-resp-≅ᴹ (≅ᴹ-trans (modifyStepRel-resp-≅ᴹ ∘σ ⊗₁-Fwd)
                                   (modifyStepRel-Fwd ∘σ (⊗Fwd (Xφ f₁ g₁) (Xφ f₂ g₂)) (∘κ f₁ g₁ f₂ g₂)
                                                      (∘sq f₁ g₁ f₂ g₂) ∘σ-inj)))
             (tr-Fwd (∘total f₁ g₁ f₂ g₂) (∘uniq f₁ g₁ f₂ g₂))

  -- A tensor of crossing forwarders is a crossing forwarder.
  ⊗mapᵢ : ∀ {A B C D} → (Channel.inType A → Channel.inType B)
                      → (Channel.inType C → Channel.inType D)
        → Channel.inType (A ⊗₀ C) → Channel.inType (B ⊗₀ D)
  ⊗mapᵢ f g (inj₁ a) = inj₁ (f a)
  ⊗mapᵢ f g (inj₂ c) = inj₂ (g c)

  ⊗mapₒ : ∀ {A B C D} → (Channel.outType B → Channel.outType A)
                      → (Channel.outType D → Channel.outType C)
        → Channel.outType (B ⊗₀ D) → Channel.outType (A ⊗₀ C)
  ⊗mapₒ f g (inj₁ b) = inj₁ (f b)
  ⊗mapₒ f g (inj₂ d) = inj₂ (g d)

  ⊗₁-Xfwd : ∀ {A B C D}
            {f₁ : Channel.inType A → Channel.inType B} {g₁ : Channel.outType B → Channel.outType A}
            {f₂ : Channel.inType C → Channel.inType D} {g₂ : Channel.outType D → Channel.outType C}
          → (Xfwd f₁ g₁ ⊗₁ Xfwd f₂ g₂) ≅ᴹ Xfwd (⊗mapᵢ f₁ f₂) (⊗mapₒ g₁ g₂)
  ⊗₁-Xfwd = ≅ᴹ-trans ⊗₁-Fwd (Fwd-≅ᴹ λ { (inj₁ (inj₁ _)) → refl
                                       ; (inj₁ (inj₂ _)) → refl
                                       ; (inj₂ (inj₁ _)) → refl
                                       ; (inj₂ (inj₂ _)) → refl })

  Xfwd-≅ᴹ : ∀ {A B} {f f' : Channel.inType A → Channel.inType B}
                    {g g' : Channel.outType B → Channel.outType A}
          → (∀ a → f a ≡ f' a) → (∀ o → g o ≡ g' o) → Xfwd f g ≅ᴹ Xfwd f' g'
  Xfwd-≅ᴹ ef eg = Fwd-≅ᴹ λ { (inj₁ a) → cong inj₂ (ef a) ; (inj₂ bo) → cong inj₁ (eg bo) }

  -- ══════════════════════════════════════════════════════════════════════
  -- `ρ-∘ᴷ-fwd`, discharged.  Both sides are composites of forwarders, so both
  -- reduce to a single `Xfwd` and the equation becomes two pointwise ones.
  -- ══════════════════════════════════════════════════════════════════════

  ρ∘ᴷ-rhs : ∀ {C E₁} → (ρ⇒ {C} ⊗₁ CC.id {E₁})
           ≅ᴹ Xfwd (⊗mapᵢ (app (⊗-right-neutral {In} {C})) (λ (x : Channel.inType E₁) → x))
                   (⊗mapₒ (app (⊗-right-intro {Out} {C} {I})) (λ (x : Channel.outType E₁) → x))
  ρ∘ᴷ-rhs = ≅ᴹ-trans (⊗₁-resp-≅ᴹ (tfm'-is-Xfwd _ _) id-is-Xfwd) ⊗₁-Xfwd

  ρ∘ᴷ-lhs : ∀ {C E₁} → ((CC.id {C} ⊗₁ ρ⇒ {E₁}) CC.∘ ∘ᴷ-fwd {C} {E₁} {I})
           ≅ᴹ Xfwd (λ a → ⊗mapᵢ (λ (x : Channel.inType C) → x)
                                 (app (⊗-right-neutral {In} {E₁}))
                                 (app (∘ᴷ-fwdᵢ {C} {E₁} {I}) a))
                   (λ o → app (∘ᴷ-fwdₒ {C} {E₁} {I})
                              (⊗mapₒ (λ (x : Channel.outType C) → x)
                                     (app (⊗-right-intro {Out} {E₁} {I})) o))
  ρ∘ᴷ-lhs = ≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-trans (⊗₁-resp-≅ᴹ id-is-Xfwd (tfm'-is-Xfwd _ _)) ⊗₁-Xfwd)
                                  (tfm'-is-Xfwd _ _))
                      ∘-Xfwd

  ρ-∘ᴷ-fwd : ∀ {C E₁}
           → ((CC.id {C} ⊗₁ ρ⇒ {E₁}) CC.∘ ∘ᴷ-fwd {C} {E₁} {I}) ≅ᴹ (ρ⇒ ⊗₁ CC.id {E₁})
  ρ-∘ᴷ-fwd {C} {E₁} =
    ≅ᴹ-trans ρ∘ᴷ-lhs
      (≅ᴹ-trans (Xfwd-≅ᴹ (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ ())) ; (inj₂ _) → refl })
                         (λ { (inj₁ _) → refl ; (inj₂ _) → refl }))
                (≅ᴹ-sym ρ∘ᴷ-rhs))

  -- ══════════════════════════════════════════════════════════════════════
  -- `ρ-idᴷ`, discharged.
  -- ══════════════════════════════════════════════════════════════════════

  ∣ˡσ : ∀ {A B C m} → A ⊗₀ C ᵀ [ m ]⇒[ m ] (A ⊗₀ B) ⊗₀ C ᵀ
  ∣ˡσ = ⇒-solver

  ∣ˡ-named : ∀ {A B C} (M : Machine (A ⊗₀ B) C) → (M ∣ˡ) ≡ modifyStepRel ∣ˡσ M
  ∣ˡ-named _ = refl

  idᴷ-f : ∀ {A} → Channel.inType A → Channel.inType (A ⊗₀ I)
  idᴷ-f a = inj₁ a

  idᴷ-g : ∀ {A} → Channel.outType (A ⊗₀ I) → Channel.outType A
  idᴷ-g (inj₁ ao) = ao
  idᴷ-g (inj₂ ())

  private
    idᴷ-sq : ∀ {A} i → app (∣ˡσ {A} {I} {A ⊗₀ I} {Out}) (Xφ idᴷ-f idᴷ-g i)
                     ≡ Xφ (⊗mapᵢ (λ (x : Channel.inType A) → x) (λ (x : Channel.inType I) → x))
                          (⊗mapₒ (λ (x : Channel.outType A) → x) (λ (x : Channel.outType I) → x))
                          (app (∣ˡσ {A} {I} {A ⊗₀ I} {In}) i)
    idᴷ-sq (inj₁ a)        = refl
    idᴷ-sq (inj₂ (inj₁ _)) = refl
    idᴷ-sq (inj₂ (inj₂ ()))

    ∣ˡσ-inj : ∀ {A} {x y : Channel.outType (A ⊗ᵀ (A ⊗₀ I))}
            → app (∣ˡσ {A} {I} {A ⊗₀ I} {Out}) x ≡ app (∣ˡσ {A} {I} {A ⊗₀ I} {Out}) y → x ≡ y
    ∣ˡσ-inj {x = inj₁ _}        {inj₁ _}        e = cong inj₁ (inj₁-inj (inj₁-inj e))
    ∣ˡσ-inj {x = inj₁ _}        {inj₂ (inj₁ _)} e = inj₁≢inj₂ e
    ∣ˡσ-inj {x = inj₁ _}        {inj₂ (inj₂ ())}
    ∣ˡσ-inj {x = inj₂ (inj₁ _)} {inj₁ _}        e = inj₁≢inj₂ (sym e)
    ∣ˡσ-inj {x = inj₂ (inj₁ _)} {inj₂ (inj₁ _)} e = cong (λ z → inj₂ (inj₁ z)) (inj₁-inj (inj₂-inj e))
    ∣ˡσ-inj {x = inj₂ (inj₁ _)} {inj₂ (inj₂ ())}
    ∣ˡσ-inj {x = inj₂ (inj₂ ())} {_}

  idᴷ-Xfwd : ∀ {A} → idᴷ {A} ≅ᴹ Xfwd idᴷ-f idᴷ-g
  idᴷ-Xfwd {A} =
    ≅ᴹ-trans (modifyStepRel-resp-≅ᴹ ∣ˡσ (≅ᴹ-trans (⊗₁-resp-≅ᴹ id-is-Xfwd id-is-Xfwd) ⊗₁-Xfwd))
             (modifyStepRel-Fwd ∣ˡσ
                (Xφ (⊗mapᵢ (λ (x : Channel.inType A) → x) (λ (x : Channel.inType I) → x))
                    (⊗mapₒ (λ (x : Channel.outType A) → x) (λ (x : Channel.outType I) → x)))
                (Xφ (idᴷ-f {A}) (idᴷ-g {A})) idᴷ-sq ∣ˡσ-inj)

  ρ-idᴷ : ∀ {C} → (ρ⇒ CC.∘ idᴷ {C}) ≅ᴹ CC.id {C}
  ρ-idᴷ {C} =
    ≅ᴹ-trans (∘-resp-≅ᴹ (tfm'-is-Xfwd _ _) idᴷ-Xfwd)
      (≅ᴹ-trans ∘-Xfwd
        (≅ᴹ-trans (Xfwd-≅ᴹ (λ _ → refl) (λ _ → refl)) (≅ᴹ-sym id-is-Xfwd)))

  -- ══════════════════════════════════════════════════════════════════════
  -- `λ-zip-idᴷ`, discharged.  Every port of the channels involved is `I`,
  -- so the machines have no possible input and only the states must match.
  -- ══════════════════════════════════════════════════════════════════════

  no-input-≅ᴹ : ∀ {A B} {M N : Machine A B}
    (t : Machine.State M → Machine.State N) (f : Machine.State N → Machine.State M)
    → (∀ s → f (t s) ≡ s) → (∀ s → t (f s) ≡ s)
    → ((i : Channel.inType (A ⊗ᵀ B)) → ⊥)
    → M ≅ᴹ N
  no-input-≅ᴹ t f p q ni =
    MkIso t f p q (λ {_} {i} _ → ⊥-elim (ni i)) (λ {_} {i} _ → ⊥-elim (ni i))

  λ-zip-idᴷ : ((CC.id {I} ⊗₁ λ⇒ {I}) CC.∘ (idᴷ {I} ∘ᴷ idᴷ {I})) ≅ᴹ idᴷ {I}
  λ-zip-idᴷ = no-input-≅ᴹ _ _ (λ _ → refl) (λ _ → refl)
    λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }
