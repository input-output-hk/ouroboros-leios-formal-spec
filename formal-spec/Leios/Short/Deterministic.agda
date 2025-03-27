-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

--------------------------------------------------------------------------------
-- Deterministic variant of short Leios
--------------------------------------------------------------------------------

open import Leios.Prelude hiding (id)
open import Prelude.Init using (∃₂-syntax)
open import Leios.FFD

import Data.List as L
open import Data.List.Relation.Unary.Any using (here)

open import Leios.SpecStructure

module Leios.Short.Deterministic (⋯ : SpecStructure 1) (let open SpecStructure ⋯) where

import Leios.Short
open import Leios.Short ⋯ hiding (_-⟦_/_⟧⇀_)
module ND = Leios.Short ⋯

open import Class.Computational
open import Class.Computational22
open import StateMachine

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open GenFFD

open FFD hiding (_-⟦_/_⟧⇀_)

private variable s s' s0 s1 s2 s3 s4 : LeiosState
                 i      : LeiosInput
                 o      : LeiosOutput
                 ffds'  : FFD.State
                 π      : VrfPf
                 bs'    : B.State
                 ks ks' : K.State
                 msgs   : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 eb     : EndorserBlock
                 rbs    : List RankingBlock
                 txs    : List Tx
                 V      : VTy
                 SD     : StakeDistr
                 pks    : List PubKey

lemma : ∀ {u} → u ∈ LeiosState.Upkeep (addUpkeep s u)
lemma = to ∈-∪ (inj₂ (to ∈-singleton refl))
  where open Equivalence

addUpkeep⇒¬needsUpkeep : ∀ {u} → ¬ LeiosState.needsUpkeep (addUpkeep s u) u
addUpkeep⇒¬needsUpkeep {s = s} = λ x → x (lemma {s = s})

data _⊢_ : LeiosInput → LeiosState → Type where
  Init :
       ∙ ks K.-⟦ K.INIT pk-IB pk-EB pk-V / K.PUBKEYS pks ⟧⇀ ks'
       ∙ initBaseState B.-⟦ B.INIT (V-chkCerts pks) / B.STAKE SD ⟧⇀ bs'
       ────────────────────────────────────────────────────────────────
       INIT V ⊢ initLeiosState V SD bs' pks

data _-⟦Base⟧⇀_ : LeiosState → LeiosState → Type where

  Base₂a  : ∀ {ebs} → let open LeiosState s renaming (BaseState to bs) in
          ∙ eb ∷ ebs ≡ filter (λ eb → ND.isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (this eb) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

  Base₂b  : let open LeiosState s renaming (BaseState to bs) in
          ∙ [] ≡ filter (λ eb → ND.isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs
          ∙ bs B.-⟦ B.SUBMIT (that ToPropose) / B.EMPTY ⟧⇀ bs'
          ───────────────────────────────────────────────────────────────────────
          s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs' } Base

Base⇒ND : LeiosState.needsUpkeep s Base → s -⟦Base⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
Base⇒ND u (Base₂a x₁ x₂) = Base₂a u (subst (_ ∈_) x₁ (Equivalence.to ∈-fromList (here refl))) x₂
Base⇒ND u (Base₂b x₁ x₂) = Base₂b u x₁ x₂

Base-Upkeep : ∀ {u} → u ≢ Base → LeiosState.needsUpkeep s u → s -⟦Base⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
Base-Upkeep u≢Base h (Base₂a _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢Base (Equivalence.from ∈-singleton y)
Base-Upkeep u≢Base h (Base₂b _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢Base (Equivalence.from ∈-singleton y)

opaque
  Base-total : ∃[ s' ] s -⟦Base⟧⇀ s'
  Base-total {s = s} with
    (let open LeiosState s in filter (λ eb → ND.isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs)
    in eq
  ... | []    = -, Base₂b (sym eq) (proj₂ B.SUBMIT-total)
  ... | x ∷ l = -, Base₂a (sym eq) (proj₂ B.SUBMIT-total)

  Base-total' : ⦃ Computational-B : Computational22 B._-⟦_/_⟧⇀_ String ⦄
              → ∃[ bs ] s -⟦Base⟧⇀ addUpkeep record s { BaseState = bs } Base
  Base-total' {s = s} = let open LeiosState s in
    case ∃[ ebs ] ebs ≡ filter (λ eb → ND.isVoteCertified s eb × eb ∈ᴮ slice L slot 2) EBs ∋ -, refl
      of λ where
        (eb ∷ _ , eq) → -, Base₂a eq (proj₂ B.SUBMIT-total)
        ([]     , eq) → -, Base₂b eq (proj₂ B.SUBMIT-total)

data _-⟦IB-Role⟧⇀_ : LeiosState → LeiosState → Type where

  IB-Role : let open LeiosState s renaming (FFDState to ffds)
                b = ibBody (record { txs = ToPropose })
                h = ibHeader (mkIBHeader slot id π sk-IB ToPropose)
          in
          ∙ canProduceIB slot sk-IB (stake s) π
          ∙ ffds FFD.-⟦ Send h (just b) / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦IB-Role⟧⇀ addUpkeep record s { FFDState = ffds' } IB-Role

  No-IB-Role : let open LeiosState s in
          ∙ (∀ π → ¬ canProduceIB slot sk-IB (stake s) π)
          ────────────────────────────────────────
          s -⟦IB-Role⟧⇀ addUpkeep s IB-Role

IB-Role⇒ND : LeiosState.needsUpkeep s IB-Role → s -⟦IB-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
IB-Role⇒ND u (IB-Role x₁ x₂) = Roles (IB-Role u x₁ x₂)
IB-Role⇒ND u (No-IB-Role x₁) = Roles (No-IB-Role u x₁)

IB-Role-Upkeep : ∀ {u} → u ≢ IB-Role → LeiosState.needsUpkeep s u → s -⟦IB-Role⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
IB-Role-Upkeep u≢IB-Role h (IB-Role _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢IB-Role (Equivalence.from ∈-singleton y)
IB-Role-Upkeep u≢IB-Role h (No-IB-Role _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢IB-Role (Equivalence.from ∈-singleton y)

opaque
  IB-Role-total : ∃[ s' ] s -⟦IB-Role⟧⇀ s'
  IB-Role-total {s = s} = let open LeiosState s in case Dec-canProduceIB of λ where
    (inj₁ (π , pf)) → -, IB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-IB-Role pf

  IB-Role-total' : ∃[ ffds ] s -⟦IB-Role⟧⇀ addUpkeep record s { FFDState = ffds } IB-Role
  IB-Role-total' {s = s} = let open LeiosState s in case Dec-canProduceIB of λ where
    (inj₁ (π , pf)) → -, IB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-IB-Role pf

data _-⟦EB-Role⟧⇀_ : LeiosState → LeiosState → Type where

  EB-Role : let open LeiosState s renaming (FFDState to ffds)
                LI = map getIBRef $ filter (_∈ᴮ slice L slot 3) IBs
                h = mkEB slot id π sk-EB LI []
          in
          ∙ canProduceEB slot sk-EB (stake s) π
          ∙ ffds FFD.-⟦ Send (ebHeader h) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦EB-Role⟧⇀ addUpkeep record s { FFDState = ffds' } EB-Role

  No-EB-Role : let open LeiosState s in
          ∙ (∀ π → ¬ canProduceEB slot sk-EB (stake s) π)
          ────────────────────────────────────────
          s -⟦EB-Role⟧⇀ addUpkeep s EB-Role

EB-Role⇒ND : LeiosState.needsUpkeep s EB-Role → s -⟦EB-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
EB-Role⇒ND u (EB-Role x₁ x₂) = Roles (EB-Role u x₁ x₂)
EB-Role⇒ND u (No-EB-Role x₁) = Roles (No-EB-Role u x₁)

EB-Role-Upkeep : ∀ {u} → u ≢ EB-Role → LeiosState.needsUpkeep s u → s -⟦EB-Role⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
EB-Role-Upkeep u≢EB-Role h (EB-Role _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢EB-Role (Equivalence.from ∈-singleton y)
EB-Role-Upkeep u≢EB-Role h (No-EB-Role _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢EB-Role (Equivalence.from ∈-singleton y)

opaque
  EB-Role-total : ∃[ s' ] s -⟦EB-Role⟧⇀ s'
  EB-Role-total {s = s} = let open LeiosState s in case Dec-canProduceEB of λ where
    (inj₁ (π , pf)) → -, EB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-EB-Role pf

  EB-Role-total' : ∃[ ffds ] s -⟦EB-Role⟧⇀ addUpkeep record s { FFDState = ffds } EB-Role
  EB-Role-total' {s = s} = let open LeiosState s in case Dec-canProduceEB of λ where
    (inj₁ (π , pf)) → -, EB-Role    pf (proj₂ FFD.FFD-Send-total)
    (inj₂ pf)       → -, No-EB-Role pf

data _-⟦V-Role⟧⇀_ : LeiosState → LeiosState → Type where

  V-Role : let open LeiosState s renaming (FFDState to ffds)
               EBs' = filter (allIBRefsKnown s) $ filter (_∈ᴮ slice L slot 1) EBs
               votes = map (vote sk-V ∘ hash) EBs'
          in
          ∙ canProduceV slot sk-V (stake s)
          ∙ ffds FFD.-⟦ Send (vHeader votes) nothing / SendRes ⟧⇀ ffds'
          ────────────────────────────────────────────────────────────────────
          s -⟦V-Role⟧⇀ addUpkeep record s { FFDState = ffds' } VT-Role

  No-V-Role : let open LeiosState s in
          ∙ ¬ canProduceV slot sk-V (stake s)
          ────────────────────────────────────────
          s -⟦V-Role⟧⇀ addUpkeep s VT-Role

V-Role⇒ND : LeiosState.needsUpkeep s VT-Role → s -⟦V-Role⟧⇀ s' → just s ND.-⟦ SLOT / EMPTY ⟧⇀ s'
V-Role⇒ND u (V-Role x₁ x₂) = Roles (VT-Role u x₁ x₂)
V-Role⇒ND u (No-V-Role x₁) = Roles (No-VT-Role u x₁)

V-Role-Upkeep : ∀ {u} → u ≢ VT-Role → LeiosState.needsUpkeep s u → s -⟦V-Role⟧⇀ s'
                  → LeiosState.needsUpkeep s' u
V-Role-Upkeep u≢V-Role h (V-Role _ _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢V-Role (Equivalence.from ∈-singleton y)
V-Role-Upkeep u≢V-Role h (No-V-Role _) u∈su = case Equivalence.from ∈-∪ u∈su of λ where
  (inj₁ x) → h x
  (inj₂ y) → u≢V-Role (Equivalence.from ∈-singleton y)

opaque
  V-Role-total : ∃[ s' ] s -⟦V-Role⟧⇀ s'
  V-Role-total {s = s} = let open LeiosState s in case Dec-canProduceV of λ where
    (yes p) → -, V-Role p (proj₂ FFD.FFD-Send-total)
    (no ¬p) → -, No-V-Role ¬p

  V-Role-total' : ∃[ ffds ] s -⟦V-Role⟧⇀ addUpkeep record s { FFDState = ffds } VT-Role
  V-Role-total' {s = s} = let open LeiosState s in case Dec-canProduceV of λ where
    (yes p) → -, V-Role    p (proj₂ FFD.FFD-Send-total)
    (no ¬p) → -, No-V-Role ¬p

upd-Upkeep : ∀ {x} → LeiosState.Upkeep s ≡ LeiosState.Upkeep (upd s x)
upd-Upkeep {record { IBBodies = bds }} {inj₁ (ibHeader h)} with A.any? (matchIB? h) bds
... | yes p = refl
... | no ¬p = refl
upd-Upkeep {_} {inj₁ (ebHeader _)} = refl
upd-Upkeep {_} {inj₁ (vHeader _)} = refl
upd-Upkeep {record { IBHeaders = hds }} {inj₂ (ibBody b)} with A.any? (flip matchIB? b) hds
... | yes p = refl
... | no ¬p = refl

data _-⟦_/_⟧⇀_ : LeiosState → LeiosInput → LeiosOutput → LeiosState → Type where

  -- Network and Ledger

  Slot : let open LeiosState s renaming (FFDState to ffds; BaseState to bs)
             s0 = record s
                    { FFDState = ffds'
                    ; Ledger   = constructLedger rbs
                    ; slot     = suc slot
                    ; Upkeep   = ∅
                    ; BaseState = bs'
                    } ↑ L.filter (isValid? s) msgs
       in
       ∙ Upkeep ≡ᵉ allUpkeep
       ∙ bs B.-⟦ B.FTCH-LDG / B.BASE-LDG rbs ⟧⇀ bs'
       ∙ ffds FFD.-⟦ Fetch / FetchRes msgs ⟧⇀ ffds'
       ∙ s0 -⟦Base⟧⇀    s1
       ∙ s1 -⟦IB-Role⟧⇀ s2
       ∙ s2 -⟦EB-Role⟧⇀ s3
       ∙ s3 -⟦V-Role⟧⇀  s4
       ───────────────────────────────────────────────────────────────────────
       s -⟦ SLOT / EMPTY ⟧⇀ s4

  Ftch :
       ───────────────────────────────────────────────────
       s -⟦ FTCH-LDG / FTCH-LDG (LeiosState.Ledger s) ⟧⇀ s

  -- Base chain
  --
  -- Note: Submitted data to the base chain is only taken into account
  --       if the party submitting is the block producer on the base chain
  --       for the given slot

  Base₁   :
          ──────────────────────────────────────────────────────────────
          s -⟦ SUBMIT (inj₂ txs) / EMPTY ⟧⇀ record s { ToPropose = txs }

  -- Protocol rules

_-⟦_/_⟧ⁿᵈ⇀_ : LeiosState → LeiosInput → LeiosOutput → LeiosState → Type
s -⟦ i / o ⟧ⁿᵈ⇀ s' = just s ND.-⟦ i / o ⟧⇀ s'

_-⟦_/_⟧ⁿᵈ*⇀_ : LeiosState → List LeiosInput → List LeiosOutput → LeiosState → Type
_-⟦_/_⟧ⁿᵈ*⇀_ = ReflexiveTransitiveClosure _-⟦_/_⟧ⁿᵈ⇀_

-- Key fact: stepping with the deterministic relation means we can
-- also step with the non-deterministic one
-- TODO: this is a lot like a weak simulation, can we do something prettier?
-⟦/⟧⇀⇒ND : s -⟦ i / o ⟧⇀ s' → ∃₂[ i , o ] (s -⟦ i / o ⟧ⁿᵈ*⇀ s')
-⟦/⟧⇀⇒ND (Slot {s = s} {msgs = msgs} {s1 = s1} {s2 = s2} {s3 = s3} x x₁ x₂ hB hIB hEB hV) = replicate 5 SLOT , replicate 5 EMPTY ,
  let
    s0 = _
    upkeep≡∅ : LeiosState.Upkeep s0 ≡ ∅
    upkeep≡∅ = sym (↑-preserves-Upkeep {x = L.filter (isValid? s) msgs})
    needsAllUpkeep : ∀ {u} → LeiosState.needsUpkeep s0 u
    needsAllUpkeep {u} = subst (u ∉_) (sym upkeep≡∅) Properties.∉-∅
    needsUpkeep1 : ∀ {u} → u ≢ Base → LeiosState.needsUpkeep s1 u
    needsUpkeep1 h1 = Base-Upkeep h1 needsAllUpkeep hB
    needsUpkeep2 : ∀ {u} → u ≢ Base → u ≢ IB-Role → LeiosState.needsUpkeep s2 u
    needsUpkeep2 h1 h2 = IB-Role-Upkeep h2 (needsUpkeep1 h1) hIB
    needsUpkeep3 : ∀ {u} → u ≢ Base → u ≢ IB-Role → u ≢ EB-Role → LeiosState.needsUpkeep s3 u
    needsUpkeep3 h1 h2 h3 = EB-Role-Upkeep h3 (needsUpkeep2 h1 h2) hEB
  in (BS-ind (ND.Slot x x₁ x₂) $
      BS-ind (Base⇒ND {s = s0} needsAllUpkeep hB) $
      BS-ind (IB-Role⇒ND (needsUpkeep1 (λ ())) hIB) $
      BS-ind (EB-Role⇒ND (needsUpkeep2 (λ ()) (λ ())) hEB) $
      STS⇒RTC (V-Role⇒ND (needsUpkeep3 (λ ()) (λ ()) (λ ())) hV))
-⟦/⟧⇀⇒ND Ftch = _ , _ , STS⇒RTC Ftch
-⟦/⟧⇀⇒ND Base₁ = _ , _ , STS⇒RTC Base₁

open Computational22 ⦃...⦄

open import Function.Related.TypeIsomorphisms
open import Function.Bundles using (Equivalence)
open Equivalence

a≢b→a∉b : ∀ {A} {a b : A} → a ≢ b → a ∉ singleton b
a≢b→a∉b = to (¬-cong-⇔ ∈-singleton)

module _ ⦃ Computational-B : Computational22 B._-⟦_/_⟧⇀_ String ⦄
         ⦃ Computational-FFD : Computational22 FFD._-⟦_/_⟧⇀_ String ⦄ where
  instance
    Computational--⟦/⟧⇀ : Computational22 _-⟦_/_⟧⇀_ String
    Computational--⟦/⟧⇀ .computeProof s (INIT x) = failure "No handling of INIT here"
    Computational--⟦/⟧⇀ .computeProof s (SUBMIT (inj₁ eb)) = failure "Cannot submit EB here"
    Computational--⟦/⟧⇀ .computeProof s (SUBMIT (inj₂ txs)) = success (-, Base₁)
    Computational--⟦/⟧⇀ .computeProof s* SLOT = let open LeiosState s* in
      case (¿ Upkeep ≡ᵉ allUpkeep ¿ ,′ computeProof BaseState B.FTCH-LDG ,′ computeProof FFDState FFD.Fetch) of λ where
        (yes p , success ((B.BASE-LDG l , bs) , p₁) , success ((FFD.FetchRes msgs , ffds) , p₂)) →
          success ((_ , (Slot p p₁ p₂ (proj₂ Base-total) (proj₂ IB-Role-total) (proj₂ EB-Role-total) (proj₂ V-Role-total))))
        (yes p , _ , _) → failure "Subsystem failed"
        (no ¬p , _) → failure "Upkeep incorrect"
    Computational--⟦/⟧⇀ .computeProof s FTCH-LDG = success (-, Ftch)
    Computational--⟦/⟧⇀ .completeness = {!!}
