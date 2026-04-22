{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import Blockchain.Safety
import Blockchain.Liveness
open import Leios.ChannelCat

open import CategoricalCrypto hiding (id)

import Data.Rational as ℚ
import Data.Rational.Properties as ℚP
open ℚ using (ℚ)

open import Data.List.Properties using (∷-injective; map-++; length-map; filter-≐)
import Data.List.Relation.Unary.Any.Properties as AnyP
import Data.List as L
open import Relation.Unary using (Decidable)

-- | Generic liveness transfer.
--
-- Same shape as `Blockchain.Safety.Transfer`, plus two extra parameters
-- (`producer-compat` and `slotOf-compat`) witnessing that the ext spec's
-- `producer`/`slotOf` factor through `getBaseBlock`.  HCG and ∃CQ transfer
-- from base to ext.
module Blockchain.Liveness.Transfer
  {BlockExt BlockBase : Type}
  (ext                : Safety BlockExt)
  (let module Ext = Safety ext)
  (base-spec          : Spec BlockBase Ext.n Ext.Network)
  (cc                 : ChannelCat)
  (extension          : IsExtension base-spec (Safety.spec ext))
  (producer-compat    : ∀ b → Safety.producer ext b
                            ≡ Spec.producer base-spec (IsExtension.getBaseBlock extension b))
  (slotOf-compat      : ∀ b → Safety.slotOf ext b
                            ≡ Spec.slotOf base-spec (IsExtension.getBaseBlock extension b))
  where

open IsExtension extension

import Blockchain.Safety.Transfer as ST
module Tr = ST ext base-spec cc extension

open Tr using (extPart; base-all-nodes)

module Base = Tr.Base

private
  -- Generic lemma: filtering after mapping equals mapping after filtering
  -- with the pulled-back predicate.
  filter-map : ∀ {A B : Type} {P : B → Type} (P? : Decidable P) (f : A → B)
               (xs : List A)
             → L.filter P? (L.map f xs) ≡ L.map f (L.filter (λ x → P? (f x)) xs)
  filter-map P? f [] = refl
  filter-map P? f (x ∷ xs) with P? (f x)
  ... | yes _ = cong (f x ∷_) (filter-map P? f xs)
  ... | no  _ = filter-map P? f xs

-- A splitting of `map f l` lifts to a splitting of `l`.
private
  map-split : ∀ {A B : Type} {f : A → B} (l : List A) (pref : List B) (b : B) (suff : List B)
    → map f l ≡ pref ++ b ∷ suff
    → Σ[ pref' ∈ List A ] Σ[ b' ∈ A ] Σ[ suff' ∈ List A ]
         (l ≡ pref' ++ b' ∷ suff')
       × (map f pref' ≡ pref)
       × (f b' ≡ b)
       × (map f suff' ≡ suff)
  map-split (x ∷ xs) []         b suff eq =
    case ∷-injective eq of λ where
      (fx≡b , mxs≡suff) → [] , x , xs , refl , refl , fx≡b , mxs≡suff
  map-split (x ∷ xs) (p ∷ pref) b suff eq =
    case ∷-injective eq of λ where
      (fx≡p , rest-eq) →
        case map-split xs pref b suff rest-eq of λ where
          (pref' , b' , suff' , xs≡ , mpref≡ , fb'≡ , msuff≡) →
            (x ∷ pref') , b' , suff'
              , cong (x ∷_) xs≡
              , cong₂ _∷_ fx≡p mpref≡
              , fb'≡
              , msuff≡

module BL = Blockchain.Liveness BlockBase Tr.base
module EL = Blockchain.Liveness BlockExt   ext
open BL using (ℕ→ℚ)

module Main where

  module TrM = Tr.Main
  open TrM using (transEnv; transState; transTrace; ChainLemma-ty)

  -- Slot lemma: the base-side slot query agrees with the ext-side slot query.
  SlotLemma-ty : ∀ {A : Channel} → Ext.Environment A → Type
  SlotLemma-ty {A} E = ∀ {p : Fin Ext.n} {s} (p-honest : p ∈ Ext.honest-nodes)
    → Base.getSlot (transEnv E) (transState E s) p-honest
    ≡ Ext.getSlot E s p-honest

  -- `recent` commutes with `map getBaseBlock`.  Follows from the generic
  -- `filter-map` lemma together with `slotOf-compat`.
  recent-map : ∀ T s (l : List BlockExt)
    → BL.recent T s (map getBaseBlock l) ≡ map getBaseBlock (EL.recent T s l)
  recent-map T s l =
    trans (filter-map ¿ _ ¿¹ getBaseBlock l)
          (cong (map getBaseBlock)
            (filter-≐ (λ x → ¿ Base.slotOf (getBaseBlock x) + T ≥ s ¿)
                      ¿ _ ¿¹
                      ( (λ {x} p → subst (λ y → y + T ≥ s) (sym (slotOf-compat x)) p)
                      , (λ {x} q → subst (λ y → y + T ≥ s) (slotOf-compat x) q))
                      l))

  module _ {A : Channel} (E : Ext.Environment A)
           (CL : ChainLemma-ty E) (SL : SlotLemma-ty E)
           (s : Machine.State (Ext.protocol E)) where

    -- HCG -----------------------------------------------------------------

    hcgState-ext⇒base : ∀ τ
      → EL.hcgState τ E s
      → BL.hcgState τ (transEnv E) (transState E s)
    hcgState-ext⇒base τ ext-hcg-s {p} hp {pref} {suff} {b} base-eq honest-b =
      case map-split (Ext.getChain E s hp) pref b suff
             (trans (sym (CL hp)) base-eq) of λ where
        (pref' , b' , suff' , ext-eq , _ , fb'≡ , msuff≡) →
          H.result pref' b' suff' ext-eq fb'≡ msuff≡
      where
        module H (pref' : List BlockExt) (b' : BlockExt) (suff' : List BlockExt)
                 (ext-eq  : Ext.getChain E s hp ≡ pref' ++ b' ∷ suff')
                 (fb'≡    : getBaseBlock b' ≡ b)
                 (msuff≡  : map getBaseBlock suff' ≡ suff) where

          honest-b' : EL.isHonestBlock b'
          honest-b' = subst (λ x → x ∈ Ext.honest-nodes)
                            (trans (producer-compat b') (cong Base.producer fb'≡) |> sym)
                            honest-b

          ext-bound : τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ Ext.slotOf b')
                    ℚ.≤ ℕ→ℚ (length suff')
          ext-bound = ext-hcg-s hp ext-eq honest-b'

          slot-eq : Ext.getSlot E s hp
                  ≡ Base.getSlot (transEnv E) (transState E s) hp
          slot-eq = sym (SL hp)

          slotOf-eq : Ext.slotOf b' ≡ Base.slotOf b
          slotOf-eq = trans (slotOf-compat b') (cong Base.slotOf fb'≡)

          length-eq : length suff' ≡ length suff
          length-eq = trans (sym (length-map getBaseBlock suff'))
                            (cong length msuff≡)

          result : τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp
                               ∸ Base.slotOf b)
                 ℚ.≤ ℕ→ℚ (length suff)
          result = let open ℚP.≤-Reasoning in
            begin
              τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp ∸ Base.slotOf b)
            ≡⟨ cong (λ x → τ ℚ.* ℕ→ℚ (x ∸ Base.slotOf b)) (sym slot-eq) ⟩
              τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ Base.slotOf b)
            ≡⟨ cong (λ y → τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ y)) (sym slotOf-eq) ⟩
              τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ Ext.slotOf b')
            ≤⟨ ext-bound ⟩
              ℕ→ℚ (length suff')
            ≡⟨ cong ℕ→ℚ length-eq ⟩
              ℕ→ℚ (length suff)
            ∎

    hcgState-base⇒ext : ∀ τ
      → BL.hcgState τ (transEnv E) (transState E s)
      → EL.hcgState τ E s
    hcgState-base⇒ext τ base-hcg-s {p} hp {pref} {suff} {b} ext-eq honest-b =
      H.result
      where
        module H where

          honest-base-b : Base.producer (getBaseBlock b) ∈ Ext.honest-nodes
          honest-base-b = subst (λ x → x ∈ Ext.honest-nodes)
                                 (producer-compat b)
                                 honest-b

          base-eq : Base.getChain (transEnv E) (transState E s) hp
                  ≡ map getBaseBlock pref ++ getBaseBlock b ∷ map getBaseBlock suff
          base-eq = trans (CL hp)
                          (trans (cong (map getBaseBlock) ext-eq)
                                 (map-++ getBaseBlock pref (b ∷ suff)))

          bound : τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp
                              ∸ Base.slotOf (getBaseBlock b))
                ℚ.≤ ℕ→ℚ (length (map getBaseBlock suff))
          bound = base-hcg-s hp base-eq honest-base-b

          slot-eq : Base.getSlot (transEnv E) (transState E s) hp
                  ≡ Ext.getSlot E s hp
          slot-eq = SL hp

          length-eq : length (map getBaseBlock suff) ≡ length suff
          length-eq = length-map getBaseBlock suff

          slotOf-eq : Base.slotOf (getBaseBlock b) ≡ Ext.slotOf b
          slotOf-eq = sym (slotOf-compat b)

          result : τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ Ext.slotOf b)
                 ℚ.≤ ℕ→ℚ (length suff)
          result = let open ℚP.≤-Reasoning in
            begin
              τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ Ext.slotOf b)
            ≡⟨ cong (λ x → τ ℚ.* ℕ→ℚ (x ∸ Ext.slotOf b)) (sym slot-eq) ⟩
              τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp ∸ Ext.slotOf b)
            ≡⟨ cong (λ y → τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp ∸ y)) (sym slotOf-eq) ⟩
              τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp ∸ Base.slotOf (getBaseBlock b))
            ≤⟨ bound ⟩
              ℕ→ℚ (length (map getBaseBlock suff))
            ≡⟨ cong ℕ→ℚ length-eq ⟩
              ℕ→ℚ (length suff)
            ∎

    -- ∃CQ -----------------------------------------------------------------

    ∃cqState-ext⇒base : ∀ T
      → EL.∃cqState T E s
      → BL.∃cqState T (transEnv E) (transState E s)
    ∃cqState-ext⇒base T ext-∃cq-s {p} hp =
      let ext-any = ext-∃cq-s hp

          mapped-any = subst (λ x → Any.Any EL.isHonestBlock
                                       (EL.recent T x (Ext.getChain E s hp)))
                             (sym (SL hp)) ext-any

          -- Transport honesty along `producer-compat`.
          any-base-honest = Any.map
            (λ {b} hb → subst (λ x → x ∈ Ext.honest-nodes) (producer-compat b) hb)
            mapped-any

          -- Push `map getBaseBlock` inside `recent` via `recent-map`.
          any-on-map = AnyP.map⁺ any-base-honest

          any-base-recent =
            subst (Any.Any BL.isHonestBlock)
                  (sym (recent-map T (Base.getSlot (transEnv E) (transState E s) hp)
                                   (Ext.getChain E s hp)))
                  any-on-map

      in subst (λ cs → Any.Any BL.isHonestBlock
                         (BL.recent T (Base.getSlot (transEnv E) (transState E s) hp) cs))
               (sym (CL hp))
               any-base-recent

    ∃cqState-base⇒ext : ∀ T
      → BL.∃cqState T (transEnv E) (transState E s)
      → EL.∃cqState T E s
    ∃cqState-base⇒ext T base-∃cq-s {p} hp =
      let base-any = base-∃cq-s hp

          -- Rewrite base chain → map getBaseBlock of ext chain.
          step₁ = subst (λ cs → Any.Any BL.isHonestBlock
                                  (BL.recent T (Base.getSlot (transEnv E) (transState E s) hp) cs))
                        (CL hp) base-any

          -- Pull `map getBaseBlock` out of `recent`.
          step₂ = subst (Any.Any BL.isHonestBlock)
                        (recent-map T (Base.getSlot (transEnv E) (transState E s) hp)
                                     (Ext.getChain E s hp))
                        step₁

          -- Any (P ∘ f) on original list.
          step₃ = AnyP.map⁻ step₂

          -- Transport honesty back through `producer-compat`.
          step₄ = Any.map
            (λ {b} hb → subst (λ x → x ∈ Ext.honest-nodes) (sym (producer-compat b)) hb)
            step₃
      in subst (λ x → Any.Any EL.isHonestBlock
                         (EL.recent T x (Ext.getChain E s hp)))
               (SL hp) step₄

  -- Transfer the hcg and ∃cq invariants.

  hcg-transfer : ∀ τ
    → (∀ {A} (E : Ext.Environment A) → ChainLemma-ty E)
    → (∀ {A} (E : Ext.Environment A) → SlotLemma-ty E)
    → BL.hcg τ → EL.hcg τ
  hcg-transfer τ CL SL base-hcg E init final trace hcg-init =
    hcgState-base⇒ext E (CL E) (SL E) final τ
      (base-hcg (transEnv E) (transState E init) (transState E final)
                (transTrace E trace)
                (hcgState-ext⇒base E (CL E) (SL E) init τ hcg-init))

  ∃cq-transfer : ∀ T
    → (∀ {A} (E : Ext.Environment A) → ChainLemma-ty E)
    → (∀ {A} (E : Ext.Environment A) → SlotLemma-ty E)
    → BL.∃cq T → EL.∃cq T
  ∃cq-transfer T CL SL base-∃cq E init final trace ∃cq-init =
    ∃cqState-base⇒ext E (CL E) (SL E) final T
      (base-∃cq (transEnv E) (transState E init) (transState E final)
                (transTrace E trace)
                (∃cqState-ext⇒base E (CL E) (SL E) init T ∃cq-init))
