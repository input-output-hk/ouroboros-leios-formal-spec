{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC

open import Blockchain.Safety
import Blockchain.IsBlockchain as IsBC
import Blockchain.Safety.Transfer as Transfer
import Blockchain.Liveness.Transfer as LTransfer

module Network.Leios
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂)
  (forEB     : Vote → EBRef)
  (mkCert    : EBRef → EBCert)
  -- a certificate names the reference it was made for, so that a positive
  -- answer to a query can match the query (`AnswerMatches`)
  (mkCert-hash : ∀ r → getEBHash (mkCert r) ≡ r)
  (threshold : ℕ)
  (voter     : Vote → Fin numberOfParties)
  (Valid     : Vote → Type) ⦃ _ : Valid ⁇¹ ⦄
    where

open import Leios.Linear ⋯ params
open Types params hiding (Network)

open import Leios.NetworkShim ⋯ params
open BaseAbstract B'

LeiosMsg = FFDA.Header ⊎ FFDA.Body
Message  = LeiosMsg ⊎ BaseMsg

import Network.DelayedDiffuse numberOfParties Message k as DD
import Leios.Voting.Certifier numberOfParties Vote EBRef EBCert forEB mkCert threshold as Certifier
import Leios.Voting.Voter Participant EBRef threshold Vote voter forEB Valid EBCert mkCert as Voter

-- multiplexing the network for the base & leios functionality
-- this is somewhat awkward because we require a strict order on
-- the messages going through it
module NetTranslate where
  record State : Type where
    field inBuffer  : Maybe (List LeiosMsg)
          outBuffer : Maybe (List BaseMsg)

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

-- Votes travel over the same network in the FFD wire format: a vote batch
-- is a `vtHeader` message, like any other FFD header.
splitVotes : List LeiosMsg → List Vote × List LeiosMsg
splitVotes ms = map₁ L.concat (partitionSumsWith isVote ms)
  where
    isVote : LeiosMsg → List Vote ⊎ LeiosMsg
    isVote (inj₁ (GenFFD.vtHeader vs)) = inj₁ vs
    isVote m                           = inj₂ m

voteMsgs : List Vote → List Message
voteMsgs [] = []
voteMsgs cs = [ inj₁ (inj₁ (GenFFD.vtHeader cs)) ]

-- `NetTranslate` with a vote hop: the round's votes go to the voter, never
-- to the node, and the voter's pending casts join the round's outgoing
-- diffuse as a `vtHeader` message.
module NetTranslateV where
  record State : Type where
    field inLeios  : Maybe (List LeiosMsg)
          inBase   : Maybe (List BaseMsg)
          outBase  : Maybe (List BaseMsg)
          outVotes : Maybe (List Vote)

  data WithState_receive_return_newState_ :
    MachineType DD.M ((Network ⊗₀ BaseNetwork) ⊗₀ Voter.VoteNet) State where

    Receive : ∀ {l} → let (msgs , base)  = partitionSumsWith proj₂ l
                          (votes , leios) = splitVotes msgs in
      WithState record { inLeios = nothing ; inBase = nothing ; outBase = nothing ; outVotes = nothing }
      receive ϵ ⊗R ↑ᵢ DD.Deliver l
      return just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ Voter.Deliver votes)
      newState record { inLeios = just leios ; inBase = just base ; outBase = nothing ; outVotes = nothing }

    SendV : ∀ {leios base cs} →
      WithState record { inLeios = just leios ; inBase = just base ; outBase = nothing ; outVotes = nothing }
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ Voter.Diffuse cs
      return just (L⊗ ((L⊗ ϵ) ⊗R) ᵗ¹ ↑ᵢ base)
      newState record { inLeios = just leios ; inBase = nothing ; outBase = nothing ; outVotes = just cs }

    SendB : ∀ {leios cs m} →
      WithState record { inLeios = just leios ; inBase = nothing ; outBase = nothing ; outVotes = just cs }
      receive L⊗ ((L⊗ ϵ) ⊗R) ᵗ¹ ↑ₒ m
      return just (L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ᵢ Activate leios)
      newState record { inLeios = nothing ; inBase = nothing ; outBase = just m ; outVotes = just cs }

    SendL : ∀ {m cs m'} →
      WithState record { inLeios = nothing ; inBase = nothing ; outBase = just m ; outVotes = just cs }
      receive L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ₒ Done m'
      return just (ϵ ⊗R ↑ₒ DD.Diffuse (map inj₂ m ++ map inj₁ m' ++ voteMsgs cs))
      newState record { inLeios = nothing ; inBase = nothing ; outBase = nothing ; outVotes = nothing }

NetTranslateV : Machine DD.M ((Network ⊗₀ BaseNetwork) ⊗₀ Voter.VoteNet)
NetTranslateV .Machine.State   = _
NetTranslateV .Machine.stepRel = NetTranslateV.WithState_receive_return_newState_

spec-rewire : Machine ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC)
                      (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
spec-rewire = ⊗-assoc⃖ ∘ (CC.id ⊗₁ ⊗-symₘ) ∘ ⊗-assoc ∘ ⊗-assoc⃖ ⊗₁ CC.id

-- The base functionality as seen through the multiplexed network.  Voting is
-- passed through untouched: the base protocol is voting-oblivious.
spec : Machine (DD.M ⊗₀ VotingC) (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
spec = spec-rewire ∘ ((CC.id ⊗₁ B.m) ⊗₁ CC.id) ∘ NetTranslate ⊗₁ CC.id

ext-spec : Machine ((Network ⊗₀ BaseIO) ⊗₀ VotingC) (IO ⊗₀ Adv)
ext-spec = LinearLeios ∘ (Shim ⊗₁ CC.id) ⊗₁ CC.id

-- The node as deployed, over the shared functionalities:
--
--              IO                                  Adv (= I)
--               ▲                                     ▲
--      ┌────────┴─────────────────────────────────────┴──┐
--      │                   LinearLeios                   │
--      └────▲───────────────────▲────────────────▲───────┘
--          FFD                BaseIO           VotingC
--       ┌───┴───┐               │                │              ext-spec
--       │ Shim  │               │                │
--       └───▲───┘               │                │
--  ─ ─ ─ ─ ─┼─ ─ ─ ─ ─ ─ ─ ─ ─ ─┼─ ─ ─ ─ ─ ─ ─ ─ ┼ ─ ─ ─ ─ ─ ─ ─ ─ ─
--        Network             ┌──┴──┐             │              spec
--           │                │ B.m ├─────────────┼────────▶ BaseAdv
--           │                └──▲──┘             │
--           │             BaseNetwork            │
--      ┌────┴───────────────────┴───┐            │
--      │        NetTranslate        │            │
--      └─────────────▲──────────────┘            │
--                   DD.M                      VotingC
--                    │                           │
--        ────────────┴───────────────────────────┴────────────
--         shared: shuffle ∘ (DD.Network ⊗ Certifier.Functionality)
Leios1 : Machine (DD.M ⊗₀ VotingC) (IO ⊗₀ BaseAdv ⊗₀ Adv)
Leios1 = ext-spec ∘ᴷ spec

specʳ : Machine DD.M (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
specʳ = spec-rewire ∘ ((CC.id ⊗₁ B.m) ⊗₁ Voter.Voter) ∘ NetTranslateV

-- The real Leios node, with a local voter in place of the shared certifier.
-- The voter answers certificate queries from its own vote log, so it needs
-- no adversary port.  Relating a deployment of these nodes to `Leios1` over
-- the shared functionalities is open; it needs a synchrony premise relating
-- the diffusion delay `k` to `Ldiff`.
--
--              IO                                  Adv (= I)
--               ▲                                     ▲
--      ┌────────┴─────────────────────────────────────┴──┐
--      │                   LinearLeios                   │
--      └────▲───────────────────▲────────────────▲───────┘
--          FFD                BaseIO           VotingC
--       ┌───┴───┐               │                │              ext-spec
--       │ Shim  │               │                │
--       └───▲───┘               │                │
--  ─ ─ ─ ─ ─┼─ ─ ─ ─ ─ ─ ─ ─ ─ ─┼─ ─ ─ ─ ─ ─ ─ ─ ┼ ─ ─ ─ ─ ─ ─ ─ ─ ─
--        Network             ┌──┴──┐             │              specʳ
--           │                │ B.m ├─────────────┼────────▶ BaseAdv
--           │                └──▲──┘         ┌───┴───┐
--           │                   │            │ Voter │
--           │                   │            └───▲───┘
--           │             BaseNetwork         VoteNet
--      ┌────┴───────────────────┴────────────────┴───┐
--      │                NetTranslateV                │
--      └──────────────────────▲──────────────────────┘
--                            DD.M
--                             │
--        ─────────────────────┴───────────────────────────────
--                          DD.Network
Leios1ʳ : Machine DD.M (IO ⊗₀ BaseAdv ⊗₀ Adv)
Leios1ʳ = ext-spec ∘ᴷ specʳ

-- A positive answer from the certifier or the voter, `CERT (just (mkCert r))`
-- to `QUERY r`, is one `Cert₁` accepts
mkCert-matches : ∀ r → AnswerMatches (just (mkCert r)) r
mkCert-matches r = matches-just (mkCert-hash r)

-- the optional EB is the one determined by the RB, _not_ the one announced by it
record LeiosBlock : Type where
  field rb : RankingBlock
        eb : Maybe EndorserBlock
        correct : HashCorrectB rb eb

LeiosBlock-Injective : Injective _≡_ _≡_ LeiosBlock.rb
LeiosBlock-Injective {record { rb = rb ; eb = eb₁ ; correct = c₁ }} {record { eb = eb₂ ; correct = c₂ }} refl
  with refl ← hash-unique rb eb₁ eb₂ c₁ c₂
  with refl ← HashCorrect-irrel rb eb₁ c₁ c₂ = refl

-- `shuffle` regroups the n-fold diffusion network and the n-fold certifier
-- into one `DD.M ⊗₀ VotingC` channel per node, as the deployment's `network`
-- needs.

⊗-interchange : ∀ {m} {A B C D : Channel}
              → (A ⊗₀ B) ⊗₀ (C ⊗₀ D) [ m ]⇒[ m ] (A ⊗₀ C) ⊗₀ (B ⊗₀ D)
⊗-interchange =
  ⊗-right-assoc
    ⇒ₜ ⊗-left-double-intro (⊗-left-assoc ⇒ₜ ⊗-right-double-intro ⊗-sym ⇒ₜ ⊗-right-assoc)
    ⇒ₜ ⊗-left-assoc

zip⇒ : ∀ {m} n (A B : Channel) → (n ⨂ⁿ A) ⊗₀ (n ⨂ⁿ B) [ m ]⇒[ m ] n ⨂ⁿ (A ⊗₀ B)
zip⇒ zero    A B = ⊗-right-neutral
zip⇒ (suc n) A B = ⊗-interchange ⇒ₜ ⊗-left-double-intro (zip⇒ n A B)

unzip⇒ : ∀ {m} n (A B : Channel) → n ⨂ⁿ (A ⊗₀ B) [ m ]⇒[ m ] (n ⨂ⁿ A) ⊗₀ (n ⨂ⁿ B)
unzip⇒ zero    A B = ⊗-right-intro
unzip⇒ (suc n) A B = ⊗-left-double-intro (unzip⇒ n A B) ⇒ₜ ⊗-interchange

shuffle : ∀ n (A B : Channel) → Machine ((n ⨂ⁿ A) ⊗₀ (n ⨂ⁿ B)) (n ⨂ⁿ (A ⊗₀ B))
shuffle n A B = TotalFunctionMachine' (zip⇒ n A B) (unzip⇒ n A B)

module _ (IOF AdvF : Participant → Channel)
  (nodesF : (p : Participant) → Machine (DD.M ⊗₀ VotingC) (IOF p ⊗₀ AdvF p)) honest-Nodes
  (honest-Node : {p : Participant} → p ∈ honest-Nodes → nodesF p ≡ᴹ Leios1)
  (honest-IOF  : {p : Participant} → p ∈ honest-Nodes → IOF p ≡ IO)
  (honest-AdvF : {p : Participant} → p ∈ honest-Nodes → AdvF p ≡ BaseAdv ⊗₀ Adv)
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
    ; honest-nodes        = honest-Nodes
    ; honest-nodes-≡-spec = honest-Node
    ; honest-IOF          = honest-IOF
    ; honest-AdvF         = honest-AdvF
    ; network             = liftᴷ {E = I} (shuffle numberOfParties DD.M VotingC)
                              ∘ᴷ (DD.Network ⊗ᴷ Certifier.Functionality) ∘ idᴷ
    }

  module S = Deployment safetyS

  base-spec : Spec RankingBlock S.n S.Network
  base-spec = record
    { IO                = _
    ; Adv               = _
    ; honest-node-spec  = spec
    ; spec-IsBlockchain = IsBlockchain-base
    }

  extension : IsExtension base-spec S.spec
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

  leiosSafety : (∀ {A} (E : S.Environment A) → TrM.ChainLemma-ty E)
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
