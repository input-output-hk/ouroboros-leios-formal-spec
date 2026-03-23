{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
import Leios.Prelude as PL
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
open import CategoricalCrypto.Channel.Selection
import CategoricalCrypto as CC
open import Categories.Category
open import Categories.Category.Helper
import Categories.Morphism.Reasoning

open import Leios.Safety

module Network.Leios
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂) where

open import Leios.Linear ⋯ params
open Types params hiding (Network)

open import Leios.NetworkShim ⋯ params
open BaseAbstract B'

import Relation.Binary.Reasoning.PartialOrder
open import Relation.Binary using (Poset)

module ≼-Reasoning {A} = Relation.Binary.Reasoning.PartialOrder (Poset-≼ {A})

LeiosMsg = FFDA.Header ⊎ FFDA.Body
Message  = LeiosMsg ⊎ BaseMsg

import Network.DelayedDiffuse numberOfParties Message k as DD

-- multiplexing the network for the base & leios functionality
-- this is somewhat awkward because we require a strict order on
-- the messages going through it
module NetTranslate where
  record State : Type where
    field inBuffer  : Maybe (List LeiosMsg)
          outBuffer : Maybe (List BaseMsg)

  private variable s : State

  data WithState_receive_return_newState_ : MachineType DD.M (Network ⊗ BaseNetwork) State where

    Receive : ∀ {l} → let (leios , base) = partitionSumsWith proj₂ l in
      WithState record { inBuffer = nothing ; outBuffer = nothing }
      receive ϵ ⊗R ↑ᵢ DD.Deliver l
      return just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ base)
      newState record { inBuffer = just leios ; outBuffer = nothing }

    SendB : ∀ {m leios} →
      WithState record { inBuffer = just leios ; outBuffer = nothing }
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ m
      return just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ Activate leios)
      newState record { inBuffer = nothing ; outBuffer = just m }

    SendL : ∀ {m m'} →
      WithState record { inBuffer = nothing ; outBuffer = just m }
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ Done m'
      return just (ϵ ⊗R ↑ₒ DD.Diffuse (map inj₂ m ++ map inj₁ m'))
      newState record { inBuffer = nothing ; outBuffer = nothing }

NetTranslate : Machine DD.M (Network ⊗ BaseNetwork)
NetTranslate .Machine.State   = _
NetTranslate .Machine.stepRel = NetTranslate.WithState_receive_return_newState_

Leios1 : Machine DD.M (IO ⊗ ((I ⊗ I ⊗ BaseAdv) ⊗ Adv))
Leios1 = LinearLeios ∘ᴷ (liftᴷ Shim ⊗ᴷ B.m) ∘ᴷ liftᴷ NetTranslate

-- the optional EB is the one determined by the RB, _not_ the one announced by it
record LeiosBlock : Type where
  field rb : RankingBlock
        eb : Maybe EndorserBlock
        correct : HashCorrectB rb eb

open import Data.Product.Properties

hash-unique' : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
  → (hc₁ : HashCorrectB rb eb₁) → (hc₂ : HashCorrectB rb eb₂) → (eb₁ , hc₁) ≡ (eb₂ , hc₂)
hash-unique' rb eb₁ eb₂ hc₁ hc₂ =
  Σ-≡,≡→≡ (hash-unique rb eb₁ eb₂ hc₁ hc₂ , HashCorrect-irrel _ _ _ _)

LeiosBlock-Injective : Injective _≡_ _≡_ LeiosBlock.rb
LeiosBlock-Injective
  {record { rb = rb ; eb = eb₁ ; correct = correct₁ }}
  {record { rb = rb ; eb = eb₂ ; correct = correct₂ }} refl =
  subst (λ (eb , correct) → _ ≡ record { rb = rb ; eb = eb ; correct = correct })
    (hash-unique' rb eb₁ eb₂ correct₁ correct₂) refl

private variable A B C D E E₁ E₂ E₃ : Channel

record ChannelCat : Type₁ where
  field
    ⊗-injectiveˡ : A ⊗ B ≡ C ⊗ D → A ≡ C
    ⊗-injectiveʳ : A ⊗ B ≡ C ⊗ D → B ≡ D
    ⊗-identityˡ : I ⊗ A ≡ A
    ⊗-identityʳ : A ⊗ I ≡ A
    I-helper : ∀ {n} → (⨂_ {n} (const I)) ≡ I
    ∘-assoc : {M₁ : Machine C D} {M₂ : Machine B C} {M₃ : Machine A B} → (M₁ ∘ M₂) ∘ M₃ ≡ M₁ ∘ M₂ ∘ M₃
    idᴹ : Machine A A
    _∘ᴹ_ : Machine B C → Machine A B → Machine A C
    ∘ᴹ-assoc : {M₃ : Machine A B} {M₂ : Machine B C} {M₁ : Machine C D}
      → (M₁ ∘ᴹ M₂) ∘ᴹ M₃ ≡ M₁ ∘ᴹ (M₂ ∘ᴹ M₃)
    ∘ᴹ-identityˡ : {f : Machine A B} → (idᴹ ∘ᴹ f) ≡ f
    ∘ᴹ-identityʳ : {f : Machine A B} → (f ∘ᴹ idᴹ) ≡ f
    ∘ᴹ-resp-≡ : {f h : Machine B C} {g i : Machine A B} → f ≡ h → g ≡ i → (f ∘ᴹ g) ≡ (h ∘ᴹ i)

    assoc²γδ : {f : Machine A B} {g : Machine B C} {h : Machine C D} {i : Machine D E}
      → (i ∘ h) ∘ (g ∘ f) ≡ i ∘ ((h ∘ g) ∘ f)
    σ : Machine (A ⊗ B) (B ⊗ A)
    α⇒ : Machine ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
    α⇐ : Machine (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
    λ⇒ : Machine (I ⊗ A) A
    ρ⇒ : Machine (A ⊗ I) A
    ρ⇐ : Machine A (A ⊗ I)

    ⨂ᴷ-⊗-∘ : ∀ {n} {f : Fin n → Machine B C} {g : Fin n → Machine E₁ E₂} {h : Fin n → Machine A (B ⊗ E₁)}
      → ⨂ᴷ (λ k → (f k ⊗' g k) ∘ h k) ≡ ((⨂₁ f) ⊗' ⨂₁ g) ∘ ⨂ᴷ h

    ∘ᴷ-assoc : {M₁ : Machine C (D ⊗ E₃)} {M₂ : Machine B (C ⊗ E₂)} {M₃ : Machine A (B ⊗ E₁)}
      → (M₁ ∘ᴷ M₂) ∘ᴷ M₃ ≡ (CC.id ⊗' α⇒) ∘ (M₁ ∘ᴷ M₂ ∘ᴷ M₃)

    ∘ᴷ-assoc' : {M₁ : Machine C (D ⊗ E₃)} {M₂ : Machine B (C ⊗ E₂)} {M₃ : Machine A (B ⊗ E₁)}
      → M₁ ∘ᴷ M₂ ∘ᴷ M₃ ≡ (CC.id ⊗' α⇐) ∘ ((M₁ ∘ᴷ M₂) ∘ᴷ M₃)

    ⨂-⊗-swap : {n : ℕ} {F₁ F₂ : Fin n → Channel} → Machine ((⨂ F₁) ⊗ (⨂ F₂)) (⨂ (λ k → F₁ k ⊗ F₂ k))

    ⨂-⊗-swap' : {n : ℕ} {F₁ F₂ : Fin n → Channel} → Machine (⨂ (λ k → F₁ k ⊗ F₂ k)) ((⨂ F₁) ⊗ (⨂ F₂))

    ⨂ᴷ-∘ᴷ-⨂ᴷ : ∀ {n} {f : Fin n → Machine A (B ⊗ E₁)} {g : Fin n → Machine B (C ⊗ E₂)}
      → ⨂ᴷ (λ k → g k ∘ᴷ f k) ≡ (CC.id ⊗' (⨂-⊗-swap {n = n} {F₁ = const E₁} {F₂ = const E₂})) ∘ (⨂ᴷ g ∘ᴷ ⨂ᴷ f)

    ⨂ᴷ-∘ᴷ-⨂ᴷ' : ∀ {n} {f : Fin n → Machine A (B ⊗ E₁)} {g : Fin n → Machine B (C ⊗ E₂)}
      → (⨂ᴷ g ∘ᴷ ⨂ᴷ f) ≡ (CC.id ⊗' (⨂-⊗-swap' {n = n} {F₁ = const E₁} {F₂ = const E₂})) ∘ ⨂ᴷ (λ k → g k ∘ᴷ f k)

    liftᴷ-∘ᴷ : {f : Machine A (B ⊗ E₁)} {g : Machine B (C ⊗ E₂)}
      → liftᴷ g ∘ᴷ f ≡ ((CC.id ⊗' ρ⇐) ∘ α⇐ ∘ (CC.id ⊗' σ)) ∘ (g ∘ᴷ f)

    ⨂-absorb-env-helper : ∀ {n} (D : Fin n → Channel) {E₁ E₂ : Fin n → Channel}
      → Machine ((⨂ D ⊗ ⨂ E₂) ⊗ E ⊗ (⨂ E₁)) ((⨂ D) ⊗ E ⊗ (⨂ (λ k → E₁ k ⊗ E₂ k)))

    ⨂-absorb-env : ∀ {n} {B C D E₁ E₂ : Fin n → Channel} {F : Channel}
      (f : (k : Fin n) → Machine (C k) (D k ⊗ E₂ k)) (g : (k : Fin n) → Machine (B k) (C k ⊗ E₁ k)) (h : Machine A (⨂ B ⊗ E))
      (α : Machine (⨂ D ⊗ E ⊗ ⨂ (λ k → E₁ k ⊗ E₂ k)) F)
      → α ∘ (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h) ≡ (α ∘ (⨂-absorb-env-helper D) ∘ ⨂ᴷ f ⊗' CC.id) ∘ (⨂ᴷ g ∘ᴷ h)

    ⨂ᴷ-cong : ∀ {n} {A B E : Fin n → Channel} {f g : (k : Fin n) → Machine (A k) (B k ⊗ E k)}
      → (∀ k → f k ≡ g k) → ⨂ᴷ f ≡ ⨂ᴷ g

    ⨂-cong : ∀ {n} {A B : Fin n → Channel} → (∀ k → A k ≡ B k) → Machine (⨂ A) (⨂ B)

  insert-id-helper : ∀ {n} (C : Fin n → Channel)
    → Machine (A ⊗ B ⊗ (⨂ (λ k → C k ⊗ I))) (A ⊗ B ⊗ (⨂ C))
  insert-id-helper {n = n} _ = CC.id ⊗' CC.id ⊗' ⨂₁ {n = n} (λ _ → ρ⇒)

  field
    insert-id : ∀ {n} {E₁} {B C E₂ : Fin n → Channel}
      → (f : (k : Fin n) → Machine (B k) (C k ⊗ E₂ k)) (g : Machine A (⨂ B ⊗ E₁))
      → (α : Machine (⨂ C ⊗ E₁ ⊗ ⨂ E₂) D)
      → α ∘ (⨂ᴷ f ∘ᴷ g) ≡ (α ∘ insert-id-helper E₂) ∘ (⨂ᴷ (λ k → idᴷ ∘ᴷ f k) ∘ᴷ g)

  MACHINE : Category (sucˡ zeroˡ) (sucˡ zeroˡ) (sucˡ zeroˡ)
  MACHINE = categoryHelper record
    { Obj = Channel
    ; _⇒_ = Machine
    ; _≈_ = _≡_
    ; id = idᴹ
    ; _∘_ = _∘ᴹ_
    ; assoc = ∘ᴹ-assoc
    ; identityˡ = ∘ᴹ-identityˡ
    ; identityʳ = ∘ᴹ-identityʳ
    ; equiv = record { refl = refl ; sym = sym ; trans = trans }
    ; ∘-resp-≈ = ∘ᴹ-resp-≡
    }

  module M = Categories.Morphism.Reasoning MACHINE

  ⊗-identityʳ-helper : B ≡ I → Machine A C → Machine (A ⊗ B) C
  ⊗-identityʳ-helper {A = A} refl M = M ∘ subst (λ x → Machine x A) (sym ⊗-identityʳ) CategoricalCrypto.id

  ⊗ᴷ-⊗ : {M₁ : Machine A (B ⊗ E₁)} {M₂ : Machine C (D ⊗ E₂)}
    → ∃[ π ] M₁ ⊗ᴷ M₂ ≡ π ∘ M₁ ⊗' M₂
  ⊗ᴷ-⊗ = -, refl

  -- this is a structure iso
  ⊗ᴷ-⊗₁ : Machine ((A ⊗ B) ⊗ C ⊗ D) ((A ⊗ C) ⊗ B ⊗ D)
  ⊗ᴷ-⊗₁ = proj₁ (⊗ᴷ-⊗ {M₁ = CategoricalCrypto.id} {CategoricalCrypto.id})

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗ AdvF p)) honestNodes
  (honest-Node : {p : Participant} → p ∈ honestNodes → nodesF p ≡ᴹ Leios1)
  (cc : ChannelCat) (let open ChannelCat cc)
  (IsBlockchain-Leios : IsBlockchain LeiosBlock Leios1)
  where

  module LS {Block : Type} (Leios-IsBlockchain : IsBlockchain Block Leios1) where
    honest-node-spec = Leios1
    spec-IsBlockchain = Leios-IsBlockchain
    all-nodes = nodesF
    honest-nodes = honestNodes
    network = DD.Network
    honest-nodes-≡-spec = honest-Node

  opaque
    safetyS : Safety LeiosBlock
    safetyS = record { LS IsBlockchain-Leios }

  module S = Safety safetyS

  opaque
    unfolding safetyS
    spec : Machine S.Network ((Network ⊗ BaseIO) ⊗ (I ⊗ I ⊗ BaseAdv))
    spec = (idᴷ ⊗ᴷ B.m) ∘ᴷ liftᴷ NetTranslate

  module Base (p : Participant) where
    opaque
      unfolding safetyS
      -- Reducing `nodesF` to only the `Base` part. We can only do this to honest nodes.

      IOFP : Channel
      IOFP = case p ∈? honestNodes of λ where
        (yes q) → Network ⊗ BaseIO
        (no ¬q) → IOF p

      AdvFP : Channel
      AdvFP = case p ∈? honestNodes of λ where
        (yes q) → I ⊗ I ⊗ BaseAdv
        (no ¬q) → AdvF p

      advTrans : AdvFP ≡ AdvF p
      advTrans with p ∈? honestNodes
      ... | (yes q) = trans (sym ⊗-identityʳ) (sym (⊗-injectiveʳ (_≡ᴹ_.B≡D (honest-Node q))))
      ... | (no ¬q) = refl

      praosNetwork' : Machine DD.M (IOFP ⊗ AdvFP)
      praosNetwork' with p ∈? honestNodes
      ... | (yes q) = spec
      ... | (no ¬q) = nodesF p

      praosNetwork : Machine DD.M (IOFP ⊗ AdvF p)
      praosNetwork = subst (λ x → Machine DD.M (IOFP ⊗ x)) advTrans praosNetwork'

      subst-≡ᴹ : ∀ {x y : Channel} {A B : Channel → Channel} → (eq : x ≡ y)
        → (M : Machine (A x) (B x)) → subst (λ x → Machine (A x) (B x)) eq M ≡ᴹ M
      subst-≡ᴹ refl _ = ≡ᴹ-refl

      honest-nodes : p ∈ honestNodes → praosNetwork ≡ᴹ spec
      honest-nodes p∈honestNodes with p ∈? honestNodes
      ... | (yes q) = subst-≡ᴹ (trans (sym ⊗-identityʳ) (sym (⊗-injectiveʳ (_≡ᴹ_.B≡D (honest-Node q))))) spec
      ... | (no ¬q) = contradiction p∈honestNodes ¬q

      honest⇒IOF≡IO : p ∈ honestNodes → IOF p ⊗ I ≡ IO ⊗ (I ⊗ I) ⊗ I
      honest⇒IOF≡IO p∈honestNodes = begin
        IOF p ⊗ I ≡⟨ cong (_⊗ I) (⊗-injectiveˡ (_≡ᴹ_.B≡D (honest-Node p∈honestNodes))) ⟩
        IO ⊗ I ≡⟨ cong (IO ⊗_) (sym ⊗-identityʳ) ⟩
        IO ⊗ I ⊗ I ≡⟨ cong (IO ⊗_) (cong (_⊗ I) (sym ⊗-identityʳ)) ⟩
        IO ⊗ (I ⊗ I) ⊗ I ∎
        where open ≡-Reasoning

      leiosPart : Machine IOFP (IOF p ⊗ I)
      leiosPart with p ∈? honestNodes
      ... | (yes q) rewrite honest⇒IOF≡IO q = LinearLeios ∘ᴷ (liftᴷ Shim ⊗ᴷ idᴷ)
      ... | (no ¬q) = idᴷ

  module _ (IsBlockchain-spec : IsBlockchain RankingBlock spec) where

    opaque
      unfolding safetyS Base.honest-nodes
      safetyB : Safety RankingBlock
      safetyB = record
        { honest-node-spec = spec
        ; spec-IsBlockchain = IsBlockchain-spec
        ; all-nodes = Base.praosNetwork
        ; honest-nodes = honestNodes
        ; honest-nodes-≡-spec = Base.honest-nodes _
        ; network = DD.Network
        }

    module B' = Safety safetyB

    opaque
      unfolding safetyB

      honest-isoʳᵖ : Fin B'.n → Fin S.n
      honest-isoʳᵖ = PL.id

      honest-isoʳ : {p : Fin B'.n} → p ∈ B'.honest-nodes → honest-isoʳᵖ p ∈ S.honest-nodes
      honest-isoʳ = PL.id

      honest-isoˡᵖ : Fin S.n → Fin B'.n
      honest-isoˡᵖ = PL.id

      honest-isoˡ : {p : Fin S.n} → p ∈ S.honest-nodes → honest-isoˡᵖ p ∈ B'.honest-nodes
      honest-isoˡ = PL.id

      single-protocol-≡-ty : Type₁
      single-protocol-≡-ty = ∀ p → idᴷ ∘ᴷ S.all-nodes p ≡ Base.leiosPart p ∘ᴷ B'.all-nodes p

    module H (single-protocol-≡ : single-protocol-≡-ty) where
      module _ {A : Channel} (E : S.Environment A) where
        opaque
          unfolding safetyS safetyB single-protocol-≡-ty

          -- this is a structure isomorphism
          transId : Machine
            ((⨂ IOF ⊗ (⨂_ {n = numberOfParties} (const I))) ⊗ (DD.Env ⊗ DD.Adv) ⊗ (⨂ AdvF))
            (⨂ IOF ⊗ (DD.Env ⊗ DD.Adv) ⊗ (⨂ AdvF))
          transId = insert-id-helper AdvF ∘ (⨂-absorb-env-helper IOF)

          -- this is `E`, but we absorb the Leios part of the honest participants
          transEnv : B'.Environment A
          transEnv = E ∘ transId ∘ ⨂ᴷ Base.leiosPart ⊗' CC.id

          transProtocol : S.protocol E ≡ᴹ B'.protocol transEnv
          transProtocol = flip (subst (S.protocol E ≡ᴹ_)) ≡ᴹ-refl $
            E ∘ (S.nodes ∘ᴷ S.network) ≡⟨ insert-id S.all-nodes S.network E ⟩
            (E ∘ insert-id-helper AdvF) ∘ (⨂ᴷ (λ p → idᴷ ∘ᴷ S.all-nodes p) ∘ᴷ S.network)
              ≡⟨ cong (λ x → (E ∘ insert-id-helper AdvF) ∘ x ∘ᴷ S.network) (⨂ᴷ-cong single-protocol-≡) ⟩
            (E ∘ insert-id-helper AdvF) ∘ (⨂ᴷ (λ p → Base.leiosPart p ∘ᴷ B'.all-nodes p) ∘ᴷ S.network)
              ≡⟨ ⨂-absorb-env Base.leiosPart B'.all-nodes S.network (E ∘ insert-id-helper AdvF) ⟩
            ((E ∘ insert-id-helper AdvF) ∘ (⨂-absorb-env-helper IOF) ∘ ⨂ᴷ Base.leiosPart ⊗' CC.id) ∘ ((⨂ᴷ B'.all-nodes) ∘ᴷ S.network)
              ≡⟨ cong (_∘ (B'.nodes ∘ᴷ S.network)) (assoc²γδ {g = ⨂-absorb-env-helper IOF} {h = insert-id-helper AdvF}) ⟩
            (E ∘ transId ∘ ⨂ᴷ Base.leiosPart ⊗' CC.id) ∘ (B'.nodes ∘ᴷ B'.network) ∎
            where
              open ≡-Reasoning

          transState : Machine.State (S.protocol E) → Machine.State (B'.protocol transEnv)
          transState = state-subst transProtocol

          transTrace : {s₁ s₂ : Machine.State (S.protocol E)} → Trace (S.protocol E) s₁ s₂
            → Trace (B'.protocol transEnv) (transState s₁) (transState s₂)
          transTrace = Trace-subst transProtocol

        LPChainLemma-ty : Type
        LPChainLemma-ty = ∀ {p : Fin B'.n} {s} (p-honest : p ∈ B'.honest-nodes)
          → B'.getChain transEnv (transState s) p-honest
          ≡ map LeiosBlock.rb (S.getChain E s (honest-isoʳ p-honest))

        hashCorrect-≼ : {l₁ l₂ : List LeiosBlock}
          → map LeiosBlock.rb l₁ ≼ map LeiosBlock.rb l₂ → l₁ ≼ l₂
        hashCorrect-≼ = inj-map-≼ LeiosBlock-Injective

        module _ (LPChainLemma : LPChainLemma-ty) (s : Machine.State (S.protocol E)) where
          open ≼-Reasoning
          open Equivalence

          opaque
            unfolding safetyB honest-isoʳᵖ honest-isoˡᵖ

            getChain-irrel : {p : Fin S.n} (hp : p ∈ S.honest-nodes)
              → S.getChain E s hp ≡ S.getChain E s (honest-isoʳ (honest-isoˡ hp))
            getChain-irrel _ = refl

          safeState-S⇒B' : S.safeState k E s → B'.safeState k transEnv (transState s)
          safeState-S⇒B' safe hp hp' = begin
              prune k (B'.getChain transEnv (transState s) hp) ≡⟨ cong (prune k) (LPChainLemma hp) ⟩
              prune k (map LeiosBlock.rb (S.getChain E s shp)) ≡⟨ prune-map {k = k} ⟩
              map LeiosBlock.rb (prune k (S.getChain E s shp)) ≤⟨ map-≼ (safe shp shp') ⟩
              map LeiosBlock.rb (S.getChain E s shp')          ≡⟨ LPChainLemma hp' ⟨
              B'.getChain transEnv (transState s) hp' ∎
            where
              shp  = honest-isoʳ hp
              shp' = honest-isoʳ hp'

          safeState-B'⇒S : B'.safeState k transEnv (transState s) → S.safeState k E s
          safeState-B'⇒S safe shp shp' = hashCorrect-≼ $ begin
              map LeiosBlock.rb (prune k (S.getChain E s shp))              ≡⟨ prune-map {k = k} ⟨
              prune k (map LeiosBlock.rb (S.getChain E s shp))              ≡⟨ cong (λ x → prune k (map {F = List} LeiosBlock.rb x)) (getChain-irrel shp) ⟩
              prune k (map LeiosBlock.rb (S.getChain E s (honest-isoʳ hp))) ≡⟨ cong (prune k) (LPChainLemma hp) ⟨
              prune k (B'.getChain transEnv (transState s) hp)              ≤⟨ safe hp hp' ⟩
              B'.getChain transEnv (transState s) hp'                       ≡⟨ LPChainLemma hp' ⟩
              map LeiosBlock.rb (S.getChain E s (honest-isoʳ hp'))          ≡⟨ cong (map LeiosBlock.rb) (getChain-irrel shp') ⟨
              map LeiosBlock.rb (S.getChain E s shp') ∎
            where
              hp  = honest-isoˡ shp
              hp' = honest-isoˡ shp'

      leiosSafety : ({A : Channel} → (E : S.Environment A) → LPChainLemma-ty E)
        → B'.safety k → S.safety k
      leiosSafety LPChainLemma praosSafety E init final trace safeInit = safeState-B'⇒S E (LPChainLemma E) final
          (praosSafety (transEnv E) (transState E init) (transState E final)
            (transTrace E trace) (safeState-S⇒B' E (LPChainLemma E) init safeInit))
