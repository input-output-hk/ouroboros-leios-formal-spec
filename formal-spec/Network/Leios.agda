{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Iso
  using (_≅ᴹ_; ≅ᴹ-refl; ≅ᴹ-sym; ≅ᴹ-trans; ∘-resp-≅ᴹ; ⊗₁-resp-≅ᴹ;
         ∘-identityˡ-≅ᴹ; ∘-identityʳ-≅ᴹ; ∘-assoc-≅ᴹ)
open import CategoricalCrypto.Machine.Monoidal using (⊗₁-id; ⊗₁-interchange; ⊗-assoc⃖-natural)

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

-- The adversary channel is the base functionality's, `BaseAdv`, next to
-- `LinearLeios`'s own, `Adv`; that split is what `IsExtension` asks for.
-- `Shim` and `NetTranslate` have no adversary channel, so they are composed
-- plainly rather than lifted into the Kleisli combinators, which would pad the
-- adversary channel with units.  The one reshuffle, `⊗-assoc⃖`, moves the
-- base functionality's adversary channel out to the Kleisli slot.
Leios1 : Machine DD.M (IO ⊗₀ BaseAdv ⊗₀ Adv)
Leios1 = LinearLeios ∘ᴷ (⊗-assoc⃖ CC.∘ (Shim ⊗₁ B.m) CC.∘ NetTranslate)

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

-- The base functionality as seen through the multiplexed network.
spec : Machine DD.M ((Network ⊗₀ BaseIO) ⊗₀ BaseAdv)
spec = ⊗-assoc⃖ CC.∘ (CC.id ⊗₁ B.m) CC.∘ NetTranslate

-- The extension layer, with `Adv` as its adversary channel.
ext-spec : Machine (Network ⊗₀ BaseIO) (IO ⊗₀ Adv)
ext-spec = LinearLeios CC.∘ (Shim ⊗₁ CC.id)

-- `Leios1` is the extension layer stacked on the base spec.  `_∘ᴷ_` unfolds
-- to `∘ᴷ-fwd ∘ ((M₂ ⊗₁ id) ∘ M₁)`, so once `⊗₁-interchange` has split
-- `ext-spec ⊗₁ id` into `LinearLeios ⊗₁ id` over `(Shim ⊗₁ id) ⊗₁ id`, the
-- shim is moved through the associator (`⊗-assoc⃖-natural`) and merged with
-- `id ⊗₁ B.m` (interchange again, then the unit laws).
is-extension-eq : Leios1 ≅ᴹ ext-spec ∘ᴷ spec
is-extension-eq = ∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym outer)
  where
    S₁ : Machine (Network ⊗₀ BaseIO) (FFD ⊗₀ BaseIO)
    S₁ = Shim ⊗₁ CC.id

    -- The shim on the three-fold channel, on either side of the associator.
    S₃ˡ : Machine ((Network ⊗₀ BaseIO) ⊗₀ BaseAdv) ((FFD ⊗₀ BaseIO) ⊗₀ BaseAdv)
    S₃ˡ = S₁ ⊗₁ CC.id

    S₃ʳ : Machine (Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) (FFD ⊗₀ (BaseIO ⊗₀ BaseAdv))
    S₃ʳ = Shim ⊗₁ (CC.id ⊗₁ CC.id)

    Bm : Machine (Network ⊗₀ BaseNetwork) (Network ⊗₀ (BaseIO ⊗₀ BaseAdv))
    Bm = CC.id ⊗₁ B.m

    X : Machine DD.M ((FFD ⊗₀ BaseIO) ⊗₀ BaseAdv)
    X = ⊗-assoc⃖ CC.∘ ((Shim ⊗₁ B.m) CC.∘ NetTranslate)

    split-ext : ((LinearLeios CC.∘ S₁) ⊗₁ CC.id {BaseAdv})
              ≅ᴹ ((LinearLeios ⊗₁ CC.id) CC.∘ S₃ˡ)
    split-ext = ≅ᴹ-trans (⊗₁-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-identityˡ-≅ᴹ))
                         (⊗₁-interchange S₁ LinearLeios CC.id CC.id)

    shim-nat : (S₃ˡ CC.∘ ⊗-assoc⃖) ≅ᴹ (⊗-assoc⃖ CC.∘ S₃ʳ)
    shim-nat = ⊗-assoc⃖-natural Shim CC.id CC.id

    merge-base : (S₃ʳ CC.∘ Bm) ≅ᴹ (Shim ⊗₁ B.m)
    merge-base = ≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange CC.id Shim B.m (CC.id ⊗₁ CC.id)))
                          (⊗₁-resp-≅ᴹ ∘-identityʳ-≅ᴹ
                             (≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl) ∘-identityˡ-≅ᴹ))

    inner : (S₃ˡ CC.∘ (⊗-assoc⃖ CC.∘ (Bm CC.∘ NetTranslate))) ≅ᴹ X
    inner =
      ≅ᴹ-trans (≅ᴹ-sym (∘-assoc-≅ᴹ {f = Bm CC.∘ NetTranslate} {g = ⊗-assoc⃖} {h = S₃ˡ}))
      (≅ᴹ-trans (∘-resp-≅ᴹ shim-nat ≅ᴹ-refl)
      (≅ᴹ-trans (∘-assoc-≅ᴹ {f = Bm CC.∘ NetTranslate} {g = S₃ʳ} {h = ⊗-assoc⃖})
      (∘-resp-≅ᴹ ≅ᴹ-refl
        (≅ᴹ-trans (≅ᴹ-sym (∘-assoc-≅ᴹ {f = NetTranslate} {g = Bm} {h = S₃ʳ}))
                  (∘-resp-≅ᴹ merge-base ≅ᴹ-refl)))))

    outer : (((LinearLeios CC.∘ S₁) ⊗₁ CC.id) CC.∘ (⊗-assoc⃖ CC.∘ (Bm CC.∘ NetTranslate)))
          ≅ᴹ ((LinearLeios ⊗₁ CC.id) CC.∘ X)
    outer =
      ≅ᴹ-trans (∘-resp-≅ᴹ split-ext ≅ᴹ-refl)
      (≅ᴹ-trans (∘-assoc-≅ᴹ {f = ⊗-assoc⃖ CC.∘ (Bm CC.∘ NetTranslate)} {g = S₃ˡ}
                            {h = LinearLeios ⊗₁ CC.id})
                (∘-resp-≅ᴹ ≅ᴹ-refl inner))

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine DD.M (IOF p ⊗₀ AdvF p)) honestNodes
  (honest-Node : {p : Participant} → p ∈ honestNodes → nodesF p ≡ᴹ Leios1)
  -- The honest nodes' channel, component by component; see `Deployment`.
  -- For a uniform deployment (`IOF = const IO`, `AdvF = const _`) both are
  -- `λ _ → refl`.
  (honest-IOF  : {p : Participant} → p ∈ honestNodes → IOF p ≡ IO)
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
    ; is-extension     = is-extension-eq
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
