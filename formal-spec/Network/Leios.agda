{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id; α-isoˡ; α-isoʳ; ρ-isoˡ; ρ-isoʳ; λ-isoˡ; λ-isoʳ)
open import CategoricalCrypto.Channel.Selection

open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
import Blockchain.Safety.TransferTrace as STT
import Blockchain.Safety.ProtocolEquiv as PE
import Blockchain.Liveness.TransferTrace as LTT
import Blockchain.Liveness.TransferTraceDischarge as LD

open import Data.Product.Properties

module Network.Leios
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂)
    where

open import Leios.Linear ⋯ params
open Types params hiding (Network)

open import Leios.NetworkShim ⋯ params
open BaseAbstract B'

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

  data WithState_receive_return_newState_ : MachineType DD.M (Network ⊗₀ BaseNetwork) State where

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

NetTranslate : Machine DD.M (Network ⊗₀ BaseNetwork)
NetTranslate .Machine.State   = _
NetTranslate .Machine.stepRel = NetTranslate.WithState_receive_return_newState_

Leios1 : Machine DD.M (IO ⊗₀ ((I ⊗₀ I ⊗₀ BaseAdv) ⊗₀ Adv))
Leios1 = LinearLeios ∘ᴷ (liftᴷ Shim ⊗ᴷ B.m) ∘ᴷ liftᴷ NetTranslate

-- the optional EB is the one determined by the RB, _not_ the one announced by it
record LeiosBlock : Type where
  field rb : RankingBlock
        eb : Maybe EndorserBlock
        correct : HashCorrectB rb eb

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

spec : Machine DD.M ((Network ⊗₀ BaseIO) ⊗₀ (I ⊗₀ I ⊗₀ BaseAdv))
spec = (idᴷ ⊗ᴷ B.m) ∘ᴷ liftᴷ NetTranslate

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗₀ AdvF p)) honestNodes
  (honest-Node : {p : Participant} → p ∈ honestNodes → nodesF p ≡ᴹ Leios1)
  (honest-IOF≡  : {p : Participant} → p ∈ honestNodes → IOF p ≡ IO)
  (honest-AdvF≡ : {p : Participant} → p ∈ honestNodes → AdvF p ≡ ((I ⊗₀ I ⊗₀ BaseAdv) ⊗₀ Adv))
  (isConstrained-Leios : IsConstrained Leios1 (IsBC.bciQueryType Participant {Block = LeiosBlock}))
  (isPure-Leios        : IsPure isConstrained-Leios)
  (IsBlockchain-base : IsBC.IsBlockchain Participant RankingBlock spec)
  -- the EB-layer (B.IO → E.IO) witnessing that leios extends praos; the
  -- companion `≈`-fact is the tc-module's `is-extension≈` parameter below.
  (ext-layer : Machine (Network ⊗₀ BaseIO) IO)
    where

  private
    module IBB = IsBC.IsBlockchain IsBlockchain-base

  IsBlockchain-Leios : IsBC.IsBlockchain Participant LeiosBlock Leios1
  IsBlockchain-Leios = record
    { isConstrained = isConstrained-Leios
    ; isPure        = isPure-Leios
    ; producer      = λ b → IBB.producer (LeiosBlock.rb b)
    ; slotOf        = λ b → IBB.slotOf   (LeiosBlock.rb b)
    }

  safetyS : Deployment LeiosBlock
  safetyS = record
    { n                   = numberOfParties
    ; Network             = _
    ; spec                = record
        { IO                = _
        ; Adv               = _
        ; honest-node-spec  = Leios1
        ; spec-IsBlockchain = IsBlockchain-Leios
        }
    ; NAdv                = _
    ; IOF                 = IOF
    ; AdvF                = AdvF
    ; all-nodes           = nodesF
    ; honest-nodes        = honestNodes
    ; honest-nodes-≡-spec = honest-Node
    ; honest-IOF≡         = honest-IOF≡
    ; honest-AdvF≡        = honest-AdvF≡
    ; network             = DD.Network
    }

  module S = Deployment safetyS

  base-spec : Spec RankingBlock S.n S.Network
  base-spec = record
    { IO                = _
    ; Adv               = _
    ; honest-node-spec  = spec
    ; spec-IsBlockchain = IsBlockchain-base
    }

  -- ── Trace-equivalence (observation-based) transfer, via the explicit Machine
  --    category.  `tc` is the categorical obligation bundle (TraceCat),
  --    `is-extension≈` the protocol-specific leios-extends-praos fact at `≈`
  --    (the `≈`-analogue of the retired `is-extension-eq`), and `reindex` the
  --    protocol backbone-projection obligation; cf. the legacy `leiosSafety`/….
  module _ (tc : STT.TraceCat numberOfParties)
           (let open STT.TraceCat tc using (_≈_; ρ⇒; ρ⇐; ρ-isoˡ; ρ-isoʳ))
           (is-extension≈ : Leios1 ≈ ((ext-layer ⊗₁ ρ⇐) ∘ spec))
           where
    open STT numberOfParties using (Obs; mapObs)
    module STr = STT.Transfer numberOfParties tc
    open STr using (Safe; transfer)
    open STT.TraceCat tc using (Reachable)

    -- adv-iso: `E.Adv = B.Adv ⊗₀ I ≅ B.Adv` via the right unitor (replaces the
    -- old `ext-Adv≡base-Adv = ⊗-identityʳ` propositional channel equality).
    adv-iso : STr._≅_ (Spec.Adv (Deployment.spec safetyS)) (Spec.Adv base-spec)
    adv-iso = record { to = ρ⇒ ; from = ρ⇐ ; to-from = ρ-isoˡ ; from-to = ρ-isoʳ }

    extension≈ : STr.IsExtension≈ base-spec (Deployment.spec safetyS)
    extension≈ = record
      { ext-layer        = ext-layer
      ; getBaseBlock     = LeiosBlock.rb
      ; getBaseBlock-inj = LeiosBlock-Injective
      ; adv-iso          = adv-iso
      ; is-extension     = is-extension≈
      }

    module PEt = PE safetyS base-spec tc extension≈

    -- the per-E backbone-projection obligation (II), kept abstract
    reindexᵗ : ∀ {A} → S.Environment A → Type
    reindexᵗ E = ∀ {o : Obs LeiosBlock}
               → Reachable (PEt.Base.protocol (PEt.transEnv E)) o
               → Reachable (PEt.Base.protocol (PEt.transEnv E)) (mapObs LeiosBlock.rb o)

    leiosSafetyᵗ :
        (∀ {A} (E : S.Environment A) → reindexᵗ E)
      → (∀ {A} (E : S.Environment A) → Safe {Block = RankingBlock} k (PEt.Base.protocol (PEt.transEnv E)))
      → (∀ {A} (E : S.Environment A) → Safe {Block = LeiosBlock}   k (S.protocol E))
    leiosSafetyᵗ reindex base-safe E =
      transfer {k = k} LeiosBlock-Injective (PEt.chainLemma E (reindex E)) (base-safe E)

    module LDn  = LD  numberOfParties
    module LTTn = LTT numberOfParties

    leiosHCGᵗ : (∀ {A} (E : S.Environment A) → reindexᵗ E) → ∀ {τ}
              → (∀ {A} (E : S.Environment A) → LTTn.LiveHCG tc PEt.Base.producer S.honest-nodes PEt.Base.slotOf τ (PEt.Base.protocol (PEt.transEnv E)))
              → (∀ {A} (E : S.Environment A) → LTTn.LiveHCG tc S.producer       S.honest-nodes S.slotOf       τ (S.protocol E))
    leiosHCGᵗ reindex {τ} base-live E =
      LDn.live-hcg tc {gB = LeiosBlock.rb} {producerₑ = S.producer} {producer-b = PEt.Base.producer}
                   S.honest-nodes {slotₑ = S.slotOf} {slot-b = PEt.Base.slotOf}
                   (λ _ → refl) (λ _ → refl)
                   (PEt.chainLemma E (reindex E)) {τ = τ} (base-live E)

    leios∃CQᵗ : (∀ {A} (E : S.Environment A) → reindexᵗ E) → ∀ {T}
              → (∀ {A} (E : S.Environment A) → LTTn.Live∃CQ tc PEt.Base.producer S.honest-nodes (LDn.recent PEt.Base.slotOf) T (PEt.Base.protocol (PEt.transEnv E)))
              → (∀ {A} (E : S.Environment A) → LTTn.Live∃CQ tc S.producer       S.honest-nodes (LDn.recent S.slotOf)       T (S.protocol E))
    leios∃CQᵗ reindex {T} base-live E =
      LDn.live-∃cq tc {gB = LeiosBlock.rb} {producerₑ = S.producer} {producer-b = PEt.Base.producer}
                   S.honest-nodes {slotₑ = S.slotOf} {slot-b = PEt.Base.slotOf}
                   (λ _ → refl) (λ _ → refl)
                   (PEt.chainLemma E (reindex E)) {T = T} (base-live E)
