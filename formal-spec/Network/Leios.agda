{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Channel.Selection
import Data.Maybe.Relation.Unary.All as Maybe

open import Tactic.Defaults

module Network.Leios
  (⋯ : SpecStructure) (let open SpecStructure ⋯)
  (params : Params) (let open Params params)
  (k : ℕ)
  (HashCorrectB : RankingBlock → Maybe EndorserBlock → Type)
  (HashCorrect-irrel : ∀ rb eb → Irrelevant (HashCorrectB rb eb))
  (hash-unique : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
    → HashCorrectB rb eb₁ → HashCorrectB rb eb₂ → eb₁ ≡ eb₂)
  -- The EB a ranking block determines.  `hash-unique` already makes it a
  -- function of the block; naming it lets the deployed node answer a chain
  -- query with Leios blocks.
  (ebOf : RankingBlock → Maybe EndorserBlock)
  (ebOf-correct : ∀ rb → HashCorrectB rb (ebOf rb))
  (forEB     : Vote → EBRef)
  (mkCert    : EBRef → EBCert)
  -- a certificate names the reference it was made for, so that a positive
  -- answer to a query can match the query
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

-- The solver does not unfold names, so its goals spell the channels out.
spec-rewireᵢ : ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC) [ In ]⇒[ In ]
               (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
spec-rewireᵢ = ⇒-solver

spec-rewireₒ : (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv) [ Out ]⇒[ Out ]
               ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC)
spec-rewireₒ = ⇒-solver

spec-rewire : Machine ((Network ⊗₀ (BaseIO ⊗₀ BaseAdv)) ⊗₀ VotingC)
                      (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
spec-rewire = TotalFunctionMachine' spec-rewireᵢ spec-rewireₒ

-- The base functionality as seen through the multiplexed network.  Voting is
-- passed through untouched: the base protocol is voting-oblivious.
spec : Machine (DD.M ⊗₀ VotingC) (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
spec = spec-rewire ∘ ((CC.id ⊗₁ B.m) ⊗₁ CC.id) ∘ NetTranslate ⊗₁ CC.id

-- The node's query port.  The base layer's queries are asked of the deployed
-- node here and answered here; its own channel type keeps the port a distinct
-- atom for the wiring solver, although its messages are the base layer's.
data QryT : Mode → Type where
  ask : BaseIOF Out → QryT Out
  ans : BaseIOF In  → QryT In

QIO : Channel
QIO = simpleChannel QryT

-- The base layer has one IO port and two users, the Leios node and whoever
-- queries the deployed node.  `Mux` shares it: every request is forwarded
-- down, and for the ones the base layer answers it remembers whom to hand the
-- answer to.  The memory is a stack, pushed by a request and popped by its
-- answer, so that a query finds the multiplexer in any state and leaves it as
-- it found it; a request and its answer never straddle a step of the composite.
module Mux where

  data Requester : Type where
    node query : Requester

  State = List Requester

  -- The requests the base layer answers.  `SUBMIT` is fire-and-forget.
  pend : BaseIOF Out → State → State
  pend FTCH-LDG  rs = node ∷ rs
  pend FTCH-SLOT rs = node ∷ rs
  pend _         rs = rs

  private variable
    rs : State
    x  : BaseIOF Out
    y  : BaseIOF In

  data WithState_receive_return_newState_ : MachineType BaseIO (BaseIO ⊗₀ QIO) State where

    Req :                                                -- the node asks the base layer
      WithState rs
      receive L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ x
      return just (ϵ ⊗R ↑ₒ x)
      newState (pend x rs)

    Ans :                                                -- and is answered
      WithState (node ∷ rs)
      receive ϵ ⊗R ↑ᵢ y
      return just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ y)
      newState rs

    Ask :                                                -- a query for the base layer
      WithState rs
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ ask x
      return just (ϵ ⊗R ↑ₒ x)
      newState (query ∷ rs)

    Tell :                                               -- and its answer
      WithState (query ∷ rs)
      receive ϵ ⊗R ↑ᵢ y
      return just (L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ ans y)
      newState rs

Mux : Machine BaseIO (BaseIO ⊗₀ QIO)
Mux .Machine.State   = _
Mux .Machine.stepRel = Mux.WithState_receive_return_newState_

-- The extension layer, with `Adv` as its adversary channel.  From the base
-- spec's IO up: the network shim next to the multiplexer, which splits the
-- base layer's port into the node's and the query port; a reassociation that
-- puts the node's three channels together; the node; and a regrouping that
-- gathers the layer's IO, `ExtIO`, next to its adversary channel.  The query
-- port passes through the node untouched, and so does voting through the
-- multiplexer.
ExtIO : Channel
ExtIO = IO ⊗₀ QIO

mux-layer : Machine ((Network ⊗₀ BaseIO) ⊗₀ VotingC) ((FFD ⊗₀ (BaseIO ⊗₀ QIO)) ⊗₀ VotingC)
mux-layer = (Shim ⊗₁ Mux) ⊗₁ CC.id

mux-shuffleᵢ : ((FFD ⊗₀ (BaseIO ⊗₀ QIO)) ⊗₀ VotingC) [ In ]⇒[ In ] (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ QIO)
mux-shuffleᵢ = ⇒-solver

mux-shuffleₒ : (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ QIO) [ Out ]⇒[ Out ] ((FFD ⊗₀ (BaseIO ⊗₀ QIO)) ⊗₀ VotingC)
mux-shuffleₒ = ⇒-solver

mux-shuffle : Machine ((FFD ⊗₀ (BaseIO ⊗₀ QIO)) ⊗₀ VotingC) (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ QIO)
mux-shuffle = TotalFunctionMachine' mux-shuffleᵢ mux-shuffleₒ

node-layer : Machine (((FFD ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ QIO) ((IO ⊗₀ Adv) ⊗₀ QIO)
node-layer = LinearLeios ⊗₁ CC.id

regroup-extᵢ : ((IO ⊗₀ Adv) ⊗₀ QIO) [ In ]⇒[ In ] ((IO ⊗₀ QIO) ⊗₀ Adv)
regroup-extᵢ = ⇒-solver

regroup-extₒ : ((IO ⊗₀ QIO) ⊗₀ Adv) [ Out ]⇒[ Out ] ((IO ⊗₀ Adv) ⊗₀ QIO)
regroup-extₒ = ⇒-solver

regroup-ext : Machine ((IO ⊗₀ Adv) ⊗₀ QIO) (ExtIO ⊗₀ Adv)
regroup-ext = TotalFunctionMachine' regroup-extᵢ regroup-extₒ

ext-spec : Machine ((Network ⊗₀ BaseIO) ⊗₀ VotingC) (ExtIO ⊗₀ Adv)
ext-spec = regroup-ext ∘ (node-layer ∘ (mux-shuffle ∘ mux-layer))

-- The node as deployed, over the shared functionalities.  Every wire is a
-- channel, so each carries messages in both directions: uniformly, `inType`
-- travels up the diagram and `outType` down.  Elided are the three
-- forwarders, which carry no state and only reroute messages: `spec-rewire`
-- inside `spec`, `mux-shuffle`, and `regroup-ext`, which gathers `IO` and
-- `QIO` into `ExtIO` next to `Adv`.
--
--                 ExtIO = IO ⊗₀ QIO
--          ┌────────────┴───────────────┐
--          IO                          QIO                 Adv (= I)
--          ↕                            ↕                     ↕
--   ┌──────┴────────────────────────┐   │                     │
--   │          LinearLeios          ├───┼─────────────────────┘
--   └──↕──────────↕────────────↕────┘   │
--     FFD       BaseIO       VotingC    │
--   ┌──┴───┐   ┌──┴───────────┼─────────┴──┐
--   │ Shim │   │          Mux │            │                  ext-spec
--   └──↕───┘   └──────↕───────┼────────────┘
--  ─ ─ ┼ ─ ─ ─ ─ ─ ─ ─┼─ ─ ─ ─┼─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
--   Network        ┌──┴──┐    │                                   spec
--      │           │ B.m ├────┼──────────────────────────↔ BaseAdv
--      │           └──↕──┘    │
--      │       BaseNetwork    │
--   ┌──┴──────────────┴──┐    │
--   │    NetTranslate    │    │
--   └─────────↕──────────┘    │
--            DD.M          VotingC
--             │               │
--   ──────────┴───────────────┴──────────────────────────────────
--    shared: shuffle ∘ (DD.Network ⊗ Certifier.Functionality)
--
-- `VotingC` passes `Mux` by on the identity side.  A query runs down the
-- right-hand side and back inside a SINGLE composite step, since `_∘_`'s step
-- relation is a trace:
--
--   QIO ── ask (FTCH-LDG) ──▶ Mux ──▶ B.m ──▶ Mux ── ans (BASE-LDG rbs) ──▶ QIO
--
-- `LinearLeios` never sees it: in `node-layer = LinearLeios ⊗₁ id` the `QIO`
-- wire passes the node on the identity side.  So the answer is the base
-- layer's current chain and not the node's cached `RBs`, which is why the
-- chain and slot lemmas hold at every state rather than only at quiescent
-- ones.  `Mux`'s stack is pushed by the request and popped by the answer, so
-- a query leaves the multiplexer as it found it, which is what
-- `Leios1-isPure` needs.
Leios1 : Machine (DD.M ⊗₀ VotingC) (ExtIO ⊗₀ BaseAdv ⊗₀ Adv)
Leios1 = ext-spec ∘ᴷ spec

specʳ : Machine DD.M (((Network ⊗₀ BaseIO) ⊗₀ VotingC) ⊗₀ BaseAdv)
specʳ = spec-rewire ∘ ((CC.id ⊗₁ B.m) ⊗₁ Voter.Voter) ∘ NetTranslateV

-- The real Leios node, with a local voter in place of the shared certifier.
-- The voter answers certificate queries from its own vote log, so it needs
-- no adversary port.  Relating a deployment of these nodes to `Leios1` over
-- the shared functionalities is open; it needs a synchrony premise relating
-- the diffusion delay `k` to `Ldiff`.  The diagram leaves out `ext-spec`'s
-- query port and multiplexer, which are as in `Leios1`.
--
--              IO                               Adv (= I)
--               ↕                                     ↕
--      ┌────────┴─────────────────────────────────────┴──┐
--      │                   LinearLeios                   │
--      └────↕───────────────────↕────────────────↕───────┘
--          FFD                BaseIO           VotingC
--       ┌───┴───┐               │                │              ext-spec
--       │ Shim  │               │                │
--       └───↕───┘               │                │
--  ─ ─ ─ ─ ─┼─ ─ ─ ─ ─ ─ ─ ─ ─ ─┼─ ─ ─ ─ ─ ─ ─ ─ ┼ ─ ─ ─ ─ ─ ─ ─ ─ ─
--        Network             ┌──┴──┐             │              specʳ
--           │                │ B.m ├─────────────┼────────↔ BaseAdv
--           │                └──↕──┘         ┌───┴───┐
--           │                   │            │ Voter │
--           │                   │            └───↕───┘
--           │             BaseNetwork         VoteNet
--      ┌────┴───────────────────┴────────────────┴───┐
--      │                NetTranslateV                │
--      └──────────────────────↕──────────────────────┘
--                            DD.M
--                             │
--        ─────────────────────┴───────────────────────────────
--                          DD.Network
Leios1ʳ : Machine DD.M (ExtIO ⊗₀ BaseAdv ⊗₀ Adv)
Leios1ʳ = ext-spec ∘ᴷ specʳ

-- A positive answer from the certifier or the voter, `CERT (just (mkCert r))`
-- to `QUERY r`, satisfies `Cert₁`'s premise on the answer.
mkCert-matches : ∀ r → Maybe.All (λ c → getEBHash c ≡ r) (just (mkCert r))
mkCert-matches r = Maybe.just (mkCert-hash r)

-- the optional EB is the one determined by the RB, _not_ the one announced by it
record LeiosBlock : Type where
  field rb : RankingBlock
        eb : Maybe EndorserBlock
        correct : HashCorrectB rb eb

-- A ranking block as a Leios block.
toLeiosBlock : RankingBlock → LeiosBlock
toLeiosBlock rb = record { rb = rb ; eb = ebOf rb ; correct = ebOf-correct rb }

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
