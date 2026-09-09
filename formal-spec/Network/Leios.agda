{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_; ≅ᴹ-refl)

open import Tactic.Defaults

open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
import Blockchain.Safety.Transfer as Transfer
import Blockchain.Liveness.Transfer as LTransfer

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

open BaseAbstract B'

LeiosMsg = FFDA.Header ⊎ FFDA.Body
Message  = LeiosMsg ⊎ BaseMsg

import Network.DelayedDiffuse numberOfParties Message k as DD

-- The node's clock, driven by the environment: `Tick` asks the node for one
-- upkeep step, `EndSlot` ends the slot and releases the node's messages to
-- the network.  Nothing is acknowledged on it.
data ClockT : Mode → Type where
  Tick EndSlot : ClockT Out

Clock : Channel
Clock = simpleChannel ClockT

-- The adapter between the delayed-diffusion network and the node.  It splits
-- the multiplexed network messages between the base functionality and the
-- Leios node, forwards the environment's clock to the node, and collects
-- what the node sends into the single `Diffuse` that ends the node's network
-- round.  It counts nothing: how many upkeep steps a slot has is the node's
-- business, and when the slot ends is the environment's.
module NetTranslate where

  data State : Type where
    Idle      : State
    Receiving : List LeiosMsg → State              -- Leios messages held while the base functionality answers
    Active    : List BaseMsg → List LeiosMsg → State  -- the base functionality's and the node's outgoing messages

  messages : FFDA.Input → List LeiosMsg
  messages (FFDAbstract.Send h b) = [ inj₁ h ] ++ L.fromMaybe (inj₂ <$> b)
  messages FFDAbstract.Fetch      = []

  private variable
    l      : List DD.Message'
    m      : List BaseMsg
    leios  : List LeiosMsg
    buffer : List LeiosMsg
    i      : FFDA.Input

  data WithState_receive_return_newState_ : MachineType DD.M ((FFD ⊗₀ BaseNetwork) ⊗₀ Clock) State where

    Receive : let (leios , base) = partitionSumsWith proj₂ l in
      WithState Idle
      receive ϵ ⊗R ↑ᵢ DD.Deliver l
      return just (L⊗ ((L⊗ ϵ) ⊗R) ᵗ¹ ↑ᵢ base)       -- the base functionality's share
      newState Receiving leios

    Begin :
      WithState Receiving leios
      receive L⊗ ((L⊗ ϵ) ⊗R) ᵗ¹ ↑ₒ m                -- the base functionality's outgoing messages
      return just (L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ᵢ FFD-OUT leios)
      newState Active m []

    Step :
      WithState Active m buffer
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ Tick
      return just (L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ᵢ SLOT)
      newState Active m buffer

    Collect :
      WithState Active m buffer
      receive L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ₒ FFD-IN i
      return nothing
      newState Active m (buffer ++ messages i)

    Finish :
      WithState Active m buffer
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ EndSlot
      return just (ϵ ⊗R ↑ₒ DD.Diffuse (map inj₂ m ++ map inj₁ buffer))
      newState Idle

NetTranslate : Machine DD.M ((FFD ⊗₀ BaseNetwork) ⊗₀ Clock)
NetTranslate .Machine.State   = _
NetTranslate .Machine.stepRel = NetTranslate.WithState_receive_return_newState_

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

-- The base functionality as seen through the multiplexed network, with the
-- node's clock passed along.  Its adversary channel is moved out to the
-- Kleisli slot.
spec : Machine DD.M (((FFD ⊗₀ BaseIO) ⊗₀ Clock) ⊗₀ BaseAdv)
spec = regroup CC.∘ ((CC.id ⊗₁ B.m) ⊗₁ CC.id) CC.∘ NetTranslate
  where
    regroup : Machine ((FFD ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ Clock) (((FFD ⊗₀ BaseIO) ⊗₀ Clock) ⊗₀ BaseAdv)
    regroup = TotalFunctionMachine' ⇒-solver ⇒-solver

-- The extension layer, with `Adv` as its adversary channel; the clock passes
-- through untouched.
ext-spec : Machine ((FFD ⊗₀ BaseIO) ⊗₀ Clock) ((IO ⊗₀ Clock) ⊗₀ Adv)
ext-spec = regroup CC.∘ (LinearLeios ⊗₁ CC.id)
  where
    regroup : Machine ((IO ⊗₀ Adv) ⊗₀ Clock) ((IO ⊗₀ Clock) ⊗₀ Adv)
    regroup = TotalFunctionMachine' ⇒-solver ⇒-solver

-- The node as deployed: the extension layer stacked on the base spec.  Its
-- adversary channel is the base functionality's next to `LinearLeios`'s own,
-- the split `IsExtension` asks for.
Leios1 : Machine DD.M ((IO ⊗₀ Clock) ⊗₀ (BaseAdv ⊗₀ Adv))
Leios1 = ext-spec ∘ᴷ spec

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗₀ AdvF p)) honestNodes
  (honest-Node : {p : Participant} → p ∈ honestNodes → nodesF p ≡ᴹ Leios1)
  -- The honest nodes' channel, component by component; see `Deployment`.
  -- For a uniform deployment (`IOF = const IO`, `AdvF = const _`) both are
  -- `λ _ → refl`.
  (honest-IOF  : {p : Participant} → p ∈ honestNodes → IOF p ≡ IO ⊗₀ Clock)
  (honest-AdvF : {p : Participant} → p ∈ honestNodes → AdvF p ≡ BaseAdv ⊗₀ Adv)
  (isConstrained-Leios : IsConstrained Leios1 (IsBC.bciQueryType Participant {Block = LeiosBlock}))
  (isPure-Leios        : IsPure isConstrained-Leios)
  (IsBlockchain-base : IsBC.IsBlockchain Participant RankingBlock spec)
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
    ; honest-IOF          = honest-IOF
    ; honest-AdvF         = honest-AdvF
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

  extension : IsExtension base-spec (Deployment.spec safetyS)
  extension = record
    { AdvL             = Adv
    ; ext-Adv≡base-Adv⊗AdvL = refl
    ; ext-layer        = ext-spec
    ; is-extension     = ≅ᴹ-refl
    ; getBaseBlock     = LeiosBlock.rb
    ; getBaseBlock-inj = LeiosBlock-Injective
    }

  private
    module Tr = Transfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec extension
    module TrM = Tr.Main

  leiosSafety : (∀ {A} (E : Deployment.Environment safetyS A) → TrM.ChainLemma-ty E)
              → Deployment.safety Tr.base k → S.safety k
  leiosSafety = TrM.transfer k

  private
    module LTr = LTransfer {BlockExt = LeiosBlock} {BlockBase = RankingBlock}
      safetyS base-spec extension (λ _ → refl) (λ _ → refl)
    module LTrM = LTr.Main

  leiosHCG : (∀ {A} (E : S.Environment A) → LTrM.TrM.ChainLemma-ty E)
           → (∀ {A} (E : S.Environment A) → LTrM.SlotLemma-ty E)
           → ∀ τ → LTr.BL.hcg τ → LTr.EL.hcg τ
  leiosHCG CL SL τ = LTrM.hcg-transfer τ CL SL

  leios∃CQ : (∀ {A} (E : S.Environment A) → LTrM.TrM.ChainLemma-ty E)
           → (∀ {A} (E : S.Environment A) → LTrM.SlotLemma-ty E)
           → ∀ T → LTr.BL.∃cq T → LTr.EL.∃cq T
  leios∃CQ CL SL T = LTrM.∃cq-transfer T CL SL
