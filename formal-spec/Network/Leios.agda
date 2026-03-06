{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
import Leios.Prelude as PL
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
open import CategoricalCrypto.Channel.Selection

open import Leios.Safety

module Network.Leios (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params)
  (validityCheckTime : EndorserBlock → ℕ) (Participants : ℕ) (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂) where

open import Leios.Linear ⋯ params validityCheckTime
open Types params hiding (Network)

open import Leios.NetworkShim ⋯ params validityCheckTime
open BaseAbstract B'

import Relation.Binary.Reasoning.PartialOrder
open import Relation.Binary using (Poset)

module ≼-Reasoning {A} = Relation.Binary.Reasoning.PartialOrder (Poset-≼ {A})

LeiosMsg = FFDA.Header ⊎ FFDA.Body
Message  = LeiosMsg ⊎ BaseMsg

import Network.DelayedDiffuse Participants Message k as DD

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

Leios1 : Machine DD.M (IO ⊗ ((I ⊗ BaseAdv) ⊗ Adv))
Leios1 = LinearLeios ∘ᴷ ((liftᴷ Shim ⊗ᴷ B.m) ∘ NetTranslate)

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

IsBlockchain-Leios : IsBlockchain LeiosBlock Leios1
IsBlockchain-Leios = {!!}

module _ (IOF AdvF : Fin Participants → Channel)
  (nodesF : (p : Fin Participants) → Machine DD.M (IOF p ⊗ AdvF p)) honestNodes
  (honest-Node : {p : Fin Participants} → p ∈ honestNodes → nodesF p ≡ᴹ Leios1)
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
    spec : Machine S.Network ((Network ⊗ BaseIO) ⊗ (I ⊗ BaseAdv))
    spec = (liftᴷ CategoricalCrypto.id ⊗ᴷ B.m) ∘ NetTranslate

  module Base (p : Fin Participants) where
    opaque
      unfolding safetyS
      -- Reducing `nodesF` to only the `Base` part. We can only do this to honest nodes.

      IOFP : Channel
      IOFP = case p ∈? honestNodes of λ where
        (yes q) → Network ⊗ BaseIO
        (no ¬q) → IOF p

      AdvFP : Channel
      AdvFP = case p ∈? honestNodes of λ where
        (yes q) → I ⊗ BaseAdv
        (no ¬q) → AdvF p

      praosNetwork : Machine DD.M (IOFP ⊗ AdvFP)
      praosNetwork with p ∈? honestNodes
      ... | (yes q) = spec
      ... | (no ¬q) = nodesF p

      honest-nodes : p ∈ honestNodes → praosNetwork ≡ᴹ spec
      honest-nodes p∈honestNodes with p ∈? honestNodes
      ... | (yes q) = ≡ᴹ-refl
      ... | (no ¬q) = contradiction p∈honestNodes ¬q

      honest⇒IOF≡IO : p ∈ honestNodes → IOF p ≡ IO ⊗ I
      honest⇒IOF≡IO p∈honestNodes = {!_≡ᴹ_.B≡D (honest-nodes p∈honestNodes)!}

      leiosPart : Machine IOFP (IOF p)
      leiosPart with p ∈? honestNodes
      ... | (yes q) rewrite honest⇒IOF≡IO q = LinearLeios ∘ (Shim ⊗' CategoricalCrypto.id)
      ... | (no ¬q) = CategoricalCrypto.id

  opaque
    unfolding safetyS Base.honest-nodes
    safetyB : Safety RankingBlock
    safetyB = record
      { honest-node-spec = spec
      ; spec-IsBlockchain = {!!}
      ; all-nodes = Base.praosNetwork
      ; honest-nodes = honestNodes
      ; honest-nodes-≡-spec = Base.honest-nodes _
      ; network = DD.Network
      }

  module B' = Safety safetyB

  opaque
    unfolding safetyB

    safetyB-n : B'.n ≡ Participants
    safetyB-n = refl

    honest-isoʳᵖ : Fin B'.n → Fin S.n
    honest-isoʳᵖ = PL.id

    honest-isoʳ : {p : Fin B'.n} → p ∈ B'.honest-nodes → honest-isoʳᵖ p ∈ S.honest-nodes
    honest-isoʳ = PL.id

    honest-isoˡᵖ : Fin S.n → Fin B'.n
    honest-isoˡᵖ = PL.id

    honest-isoˡ : {p : Fin S.n} → p ∈ S.honest-nodes → honest-isoˡᵖ p ∈ B'.honest-nodes
    honest-isoˡ = PL.id

    honest-iso-isoˡ : ∀ p → honest-isoʳᵖ (honest-isoˡᵖ p) ≡ p
    honest-iso-isoˡ p = refl

  module _ {A : Channel} (E : S.Environment A) where
    -- this is `E`, but we absorb the Leios part of the honest participants
    transEnv : B'.Environment A
    transEnv = {!!}

    -- this is essentially associativity
    transProtocol : S.protocol E ≡ᴹ B'.protocol transEnv
    transProtocol = {!!}

    opaque
      transState : Machine.State (S.protocol E) → Machine.State (B'.protocol transEnv)
      transState = state-subst transProtocol

      transTrace : {s₁ s₂ : Machine.State (S.protocol E)} → Trace (S.protocol E) s₁ s₂
        → Trace (B'.protocol transEnv) (transState s₁) (transState s₂)
      transTrace = Trace-subst transProtocol

    LPChainLemma : ∀ {p : Fin B'.n} {s} (p-honest : p ∈ B'.honest-nodes)
      → B'.getChain transEnv (transState s) p-honest
      ≡ map LeiosBlock.rb (S.getChain E s (honest-isoʳ p-honest))
    LPChainLemma = {!!}

    hashCorrect-≼ : {l₁ l₂ : List LeiosBlock}
      → map LeiosBlock.rb l₁ ≼ map LeiosBlock.rb l₂ → l₁ ≼ l₂
    hashCorrect-≼ = inj-map-≼ LeiosBlock-Injective

    module _ (s : Machine.State (S.protocol E)) where
      open ≼-Reasoning
      open Equivalence

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
          map LeiosBlock.rb (prune k (S.getChain E s shp)) ≡⟨ prune-map {k = k} ⟨
          prune k (map LeiosBlock.rb (S.getChain E s shp)) ≡⟨ cong (prune k) {!LPChainLemma hp!} ⟩
          prune k (B'.getChain transEnv (transState s) hp) ≤⟨ safe hp hp' ⟩
          B'.getChain transEnv (transState s) hp'  ≡⟨ {!LPChainLemma hp'!} ⟩
          map LeiosBlock.rb (S.getChain E s shp') ∎
        where
          hp  = honest-isoˡ shp
          hp' = honest-isoˡ shp'

  leiosSafety : B'.safety k → S.safety k
  leiosSafety praosSafety E init final trace safeInit = safeState-B'⇒S E final
    (praosSafety (transEnv E) (transState E init) (transState E final)
      (transTrace E trace) (safeState-S⇒B' E init safeInit))
