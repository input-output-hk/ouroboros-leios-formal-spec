{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import Blockchain.Safety
open import Blockchain.Liveness
open import Leios.ChannelCat

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC

import Data.Integer as ℤ
import Data.Rational as ℚ
open ℚ using (ℚ)

open import Data.List.Properties using (∷-injective; map-++; length-map; filter-accept; filter-reject)
import Data.List.Relation.Unary.Any.Properties as AnyP
import Data.List as L

-- | Generic liveness transfer.
--
-- Given the same ingredients as `Blockchain.Safety.Transfer` (an extended
-- blockchain spec `ext`, a chain-projection `getBaseBlock` into a base
-- blockchain spec, and an honest upper layer `ext-spec`) and a `Liveness`
-- record for the derived base spec, we derive a `Liveness` record for the
-- ext spec by pulling back `producer` and `slotOf` along `getBaseBlock`,
-- and show that HCG and ∃CQ transfer from base to ext.
module Blockchain.Liveness.Transfer
  {BlockExt BlockBase   : Type}
  (getBaseBlock         : BlockExt → BlockBase)
  (getBaseBlock-inj     : Injective _≡_ _≡_ getBaseBlock)
  (ext                  : Safety BlockExt)
  (cc                   : ChannelCat)
  (base-IO base-Adv     : Channel)
  (base-spec            : Machine (Safety.Network ext) (base-IO ⊗₀ base-Adv))
  (base-IsBlockchain    : IsBlockchain BlockBase base-spec)
  (ext-Adv≡base-Adv     : Safety.Adv ext ≡ base-Adv)
  (ext-spec             : Machine base-IO (Safety.IO ext ⊗₀ I))
  where

import Blockchain.Safety.Transfer as ST
module Tr = ST
  getBaseBlock getBaseBlock-inj ext cc
  base-IO base-Adv base-spec base-IsBlockchain
  ext-Adv≡base-Adv ext-spec

open Tr using (extPart; base-all-nodes)

module Ext  = Tr.Ext
module Base = Tr.Base

private
  ℕ→ℚ : ℕ → ℚ
  ℕ→ℚ n = (ℤ.+ n) ℚ./ 1

-- A splitting of `map f l` lifts to a splitting of `l`.
private
  map-split : ∀ {A B} {f : A → B} (l : List A) (pref : List B) (b : B) (suff : List B)
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

-- Given a Liveness for the derived base spec, we derive a Liveness for the
-- ext spec by pulling back `producer` and `slotOf` along `getBaseBlock`.
module _ (baseLiv : BL.Liveness) where

  private
    module LB = BL.Liveness baseLiv

  extLiv : EL.Liveness
  extLiv = record
    { producer = λ b → LB.producer (getBaseBlock b)
    ; slotOf   = λ b → LB.slotOf   (getBaseBlock b)
    }

  private
    module LE = EL.Liveness extLiv

  module Main (single-protocol-≡ : ∀ p
                                 → idᴷ ∘ᴷ Ext.all-nodes p
                                 ≡ extPart p ∘ᴷ base-all-nodes p) where

    module TrM = Tr.Main single-protocol-≡
    open TrM using (transEnv; transState; transTrace; ChainLemma-ty)

    -- Slot lemma: the base-side slot query agrees with the ext-side slot query.
    SlotLemma-ty : ∀ {A : Channel} → Ext.Environment A → Type
    SlotLemma-ty {A} E = ∀ {p : Fin Ext.n} {s} (p-honest : p ∈ Ext.honest-nodes)
      → Base.getSlot (transEnv E) (transState E s) p-honest
      ≡ Ext.getSlot E s p-honest

    -- `recent` commutes with `map getBaseBlock`. The predicate
    -- `λ b → slotOf b + T ≥ s` is decidable on ℕ and the decidability
    -- instance used on the ext and base sides agrees up to `getBaseBlock`,
    -- since `LE.slotOf` is defined as `LB.slotOf ∘ getBaseBlock`.
    recent-map : ∀ T s (l : List BlockExt)
      → LB.recent T s (map getBaseBlock l) ≡ map getBaseBlock (LE.recent T s l)
    recent-map T s [] = refl
    recent-map T s (x ∷ xs)
      with ¿ LB.slotOf (getBaseBlock x) + T ≥ s ¿
    ... | yes p =
      let lhs-eq : LB.recent T s (getBaseBlock x ∷ map getBaseBlock xs)
                 ≡ getBaseBlock x ∷ LB.recent T s (map getBaseBlock xs)
          lhs-eq = filter-accept ¿ _ ¿¹ p
          rhs-eq : LE.recent T s (x ∷ xs) ≡ x ∷ LE.recent T s xs
          rhs-eq = filter-accept ¿ _ ¿¹ p
      in trans lhs-eq
               (trans (cong (getBaseBlock x ∷_) (recent-map T s xs))
                      (cong (map getBaseBlock) (sym rhs-eq)))
    ... | no ¬p =
      let lhs-eq : LB.recent T s (getBaseBlock x ∷ map getBaseBlock xs)
                 ≡ LB.recent T s (map getBaseBlock xs)
          lhs-eq = filter-reject ¿ _ ¿¹ ¬p
          rhs-eq : LE.recent T s (x ∷ xs) ≡ LE.recent T s xs
          rhs-eq = filter-reject ¿ _ ¿¹ ¬p
      in trans lhs-eq (trans (recent-map T s xs) (cong (map getBaseBlock) (sym rhs-eq)))

    module _ {A : Channel} (E : Ext.Environment A)
             (CL : ChainLemma-ty E) (SL : SlotLemma-ty E)
             (s : Machine.State (Ext.protocol E)) where

      -- HCG -----------------------------------------------------------------

      hcgState-ext⇒base : ∀ τ
        → LE.hcgState τ E s
        → LB.hcgState τ (transEnv E) (transState E s)
      hcgState-ext⇒base τ ext-hcg-s {p} hp {pref} {suff} {b} base-eq honest-b =
        let mapped-eq : map getBaseBlock (Ext.getChain E s hp) ≡ pref ++ b ∷ suff
            mapped-eq = trans (sym (CL hp)) base-eq
        in case map-split (Ext.getChain E s hp) pref b suff mapped-eq of λ where
          (pref' , b' , suff' , ext-eq , _ , fb'≡ , msuff≡) →
            let honest-b' : LE.isHonestBlock b'
                honest-b' = subst (λ x → LB.producer x ∈ Ext.honest-nodes)
                              (sym fb'≡) honest-b

                ext-bound : τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ LE.slotOf b')
                          ℚ.≤ ℕ→ℚ (length suff')
                ext-bound = ext-hcg-s hp ext-eq honest-b'

                slot-eq : Ext.getSlot E s hp
                        ≡ Base.getSlot (transEnv E) (transState E s) hp
                slot-eq = sym (SL hp)

                slotOf-eq : LE.slotOf b' ≡ LB.slotOf b
                slotOf-eq = cong LB.slotOf fb'≡

                length-eq : length suff' ≡ length suff
                length-eq = trans (sym (length-map getBaseBlock suff'))
                                  (cong length msuff≡)

                step₁ : τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ LB.slotOf b)
                      ℚ.≤ ℕ→ℚ (length suff')
                step₁ = subst (λ y → τ ℚ.* ℕ→ℚ (Ext.getSlot E s hp ∸ y)
                                   ℚ.≤ ℕ→ℚ (length suff'))
                              slotOf-eq ext-bound

                step₂ : τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp
                                    ∸ LB.slotOf b)
                      ℚ.≤ ℕ→ℚ (length suff')
                step₂ = subst (λ x → τ ℚ.* ℕ→ℚ (x ∸ LB.slotOf b)
                                   ℚ.≤ ℕ→ℚ (length suff'))
                              slot-eq step₁
            in subst (λ y → τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp
                                        ∸ LB.slotOf b) ℚ.≤ ℕ→ℚ y)
                     length-eq step₂

      hcgState-base⇒ext : ∀ τ
        → LB.hcgState τ (transEnv E) (transState E s)
        → LE.hcgState τ E s
      hcgState-base⇒ext τ base-hcg-s {p} hp {pref} {suff} {b} ext-eq honest-b =
        let base-eq : Base.getChain (transEnv E) (transState E s) hp
                    ≡ map getBaseBlock pref ++ getBaseBlock b ∷ map getBaseBlock suff
            base-eq = trans (CL hp)
                            (trans (cong (map getBaseBlock) ext-eq)
                                   (map-++ getBaseBlock pref (b ∷ suff)))

            bound : τ ℚ.* ℕ→ℚ (Base.getSlot (transEnv E) (transState E s) hp
                                ∸ LB.slotOf (getBaseBlock b))
                  ℚ.≤ ℕ→ℚ (length (map getBaseBlock suff))
            bound = base-hcg-s hp base-eq honest-b

            slot-eq : Base.getSlot (transEnv E) (transState E s) hp
                    ≡ Ext.getSlot E s hp
            slot-eq = SL hp

            length-eq : length (map getBaseBlock suff) ≡ length suff
            length-eq = length-map getBaseBlock suff
        in subst₂ (λ x y → τ ℚ.* ℕ→ℚ (x ∸ LE.slotOf b) ℚ.≤ ℕ→ℚ y)
                  slot-eq length-eq bound

      -- ∃CQ -----------------------------------------------------------------

      ∃cqState-ext⇒base : ∀ T
        → LE.∃cqState T E s
        → LB.∃cqState T (transEnv E) (transState E s)
      ∃cqState-ext⇒base T ext-∃cq-s {p} hp =
        let ext-any : Any.Any LE.isHonestBlock
                        (LE.recent T (Ext.getSlot E s hp) (Ext.getChain E s hp))
            ext-any = ext-∃cq-s hp

            mapped-any : Any.Any LE.isHonestBlock
                          (LE.recent T (Base.getSlot (transEnv E) (transState E s) hp)
                                       (Ext.getChain E s hp))
            mapped-any = subst (λ x → Any.Any LE.isHonestBlock
                                         (LE.recent T x (Ext.getChain E s hp)))
                               (sym (SL hp)) ext-any

            -- Push `map getBaseBlock` inside `recent` via `recent-map`.
            any-on-map : Any.Any LB.isHonestBlock
                          (map getBaseBlock
                            (LE.recent T (Base.getSlot (transEnv E) (transState E s) hp)
                                        (Ext.getChain E s hp)))
            any-on-map = AnyP.map⁺ mapped-any

            any-base-recent : Any.Any LB.isHonestBlock
                                (LB.recent T (Base.getSlot (transEnv E) (transState E s) hp)
                                             (map getBaseBlock (Ext.getChain E s hp)))
            any-base-recent =
              subst (Any.Any LB.isHonestBlock)
                    (sym (recent-map T (Base.getSlot (transEnv E) (transState E s) hp)
                                     (Ext.getChain E s hp)))
                    any-on-map

        in subst (λ cs → Any.Any LB.isHonestBlock
                           (LB.recent T (Base.getSlot (transEnv E) (transState E s) hp) cs))
                 (sym (CL hp))
                 any-base-recent

      ∃cqState-base⇒ext : ∀ T
        → LB.∃cqState T (transEnv E) (transState E s)
        → LE.∃cqState T E s
      ∃cqState-base⇒ext T base-∃cq-s {p} hp =
        let base-any : Any.Any LB.isHonestBlock
                        (LB.recent T (Base.getSlot (transEnv E) (transState E s) hp)
                                     (Base.getChain (transEnv E) (transState E s) hp))
            base-any = base-∃cq-s hp

            -- Rewrite base chain → map getBaseBlock of ext chain.
            step₁ : Any.Any LB.isHonestBlock
                     (LB.recent T (Base.getSlot (transEnv E) (transState E s) hp)
                                  (map getBaseBlock (Ext.getChain E s hp)))
            step₁ = subst (λ cs → Any.Any LB.isHonestBlock
                                    (LB.recent T (Base.getSlot (transEnv E) (transState E s) hp) cs))
                          (CL hp) base-any

            -- Pull `map getBaseBlock` out of `recent`.
            step₂ : Any.Any LB.isHonestBlock
                     (map getBaseBlock
                       (LE.recent T (Base.getSlot (transEnv E) (transState E s) hp)
                                   (Ext.getChain E s hp)))
            step₂ = subst (Any.Any LB.isHonestBlock)
                          (recent-map T (Base.getSlot (transEnv E) (transState E s) hp)
                                       (Ext.getChain E s hp))
                          step₁

            -- Any (P ∘ f) on original list.
            step₃ : Any.Any LE.isHonestBlock
                     (LE.recent T (Base.getSlot (transEnv E) (transState E s) hp)
                                 (Ext.getChain E s hp))
            step₃ = AnyP.map⁻ step₂
        in subst (λ x → Any.Any LE.isHonestBlock
                           (LE.recent T x (Ext.getChain E s hp)))
                 (SL hp) step₃

    -- Transfer the hcg and ∃cq invariants.

    hcg-transfer : ∀ τ
      → (∀ {A} (E : Ext.Environment A) → ChainLemma-ty E)
      → (∀ {A} (E : Ext.Environment A) → SlotLemma-ty E)
      → LB.hcg τ → LE.hcg τ
    hcg-transfer τ CL SL base-hcg E init final trace hcg-init =
      hcgState-base⇒ext E (CL E) (SL E) final τ
        (base-hcg (transEnv E) (transState E init) (transState E final)
                  (transTrace E trace)
                  (hcgState-ext⇒base E (CL E) (SL E) init τ hcg-init))

    ∃cq-transfer : ∀ T
      → (∀ {A} (E : Ext.Environment A) → ChainLemma-ty E)
      → (∀ {A} (E : Ext.Environment A) → SlotLemma-ty E)
      → LB.∃cq T → LE.∃cq T
    ∃cq-transfer T CL SL base-∃cq E init final trace ∃cq-init =
      ∃cqState-base⇒ext E (CL E) (SL E) final T
        (base-∃cq (transEnv E) (transState E init) (transState E final)
                  (transTrace E trace)
                  (∃cqState-ext⇒base E (CL E) (SL E) init T ∃cq-init))
