{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_; _∘_; All)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import CategoricalCrypto hiding (id)
import CategoricalCrypto as CC
open import CategoricalCrypto.Channel.Selection

open import Tactic.Defaults

open import Data.Product.Properties

-- | The Leios node as deployed: the extension layer stacked on the base
-- functionality, `Leios1 = ext-spec ∘ᴷ spec`.
--
--               ExtIO = IO ⊗₀ QIO
--          ┌──────────┴──────────┐
--          IO                   QIO            Adv           BaseAdv
--          ↕                     ↕              ↕               ↕
--          │                     │              │               │
--    ┌─────┴─────────────────┐   │              │               │
--    │      LinearLeios      ├───┼──────────────┘               │
--    └──↕─────────────────↕──┘   │                              │
--      FFD             BaseIO    │                              │
--       │                 │      │                              │
--    ┌──┴───┐          ┌──┴──────┴──┐                           │
--    │ Shim │          │    Mux     │                           │
--    └──↕───┘          └──────↕─────┘                           │
--       │                  BaseIO                               │
--       │                     │                                 │
--       │              ┌──────┴──────┐                          │
--       │              │  B.m (base) ├──────────────────────────┘
--       │              └──────↕──────┘
--       │                 BaseNetwork
--       │                     │
--    ┌──┴─────────────────────┴──┐
--    │        NetTranslate       │
--    └─────────────↕─────────────┘
--                  │
--                DD.M
--
-- Every wire is a channel, so each carries messages in BOTH directions; the
-- vertical arrangement says only which machine's domain a wire leaves and
-- which machine's codomain it enters.  Uniformly, `inType` travels UP the
-- diagram and `outType` DOWN — note that `_ᵀ` on `IO` and `FFD` flips which
-- is which relative to their `Mode`:
--
--   ExtIO        IO ⊗₀ QIO
--   IO       ↑   FetchLdgO (List Tx)
--            ↓   SubmitTxs (List Tx) | FetchLdgI
--   QIO      ↑   ans (y : BaseIOF In)
--            ↓   ask (x : BaseIOF Out)
--   Adv          I — empty, the layer has no adversary messages yet
--   BaseAdv      abstract, a field of `BaseAbstract`
--   FFD      ↑   FFD-OUT (List (Header ⊎ Body)) | SLOT | FTCH
--            ↓   FFD-IN FFDA.Input
--   BaseIO   ↑   BASE-LDG (List RankingBlock) | SLOT ℕ | STAKE StakeDistr | EMPTY
--            ↓   FTCH-LDG | FTCH-SLOT | SUBMIT RankingBlock | INIT …
--   Network  ↑   Activate (List (Header ⊎ Body))
--            ↓   Done (List (Header ⊎ Body))
--   BaseNetwork  List BaseMsg, both ways
--   DD.M     ↑   Deliver (List Message')
--            ↓   Diffuse (List Message)
--
-- `ext-spec` is everything above the `Network`/`BaseIO` cut; `spec` is
-- `NetTranslate` and the base functionality below it, with `BaseAdv` routed
-- past the layer.  The `∘ᴷ` joining them is what collects the two adversary
-- channels side by side at the top.
--
-- Elided: three forwarders that carry no state and change no messages, only
-- their routing — `⊗-assoc⃖` inside `spec`, `mux-shuffle` (also `⊗-assoc⃖`),
-- and `regroup-ext`, which gathers `IO` and `QIO` into `ExtIO` next to `Adv`.
--
-- A query runs down the right-hand side and back inside a SINGLE composite
-- step, since `_∘_`'s step relation is a trace:
--
--   QIO ── ask (FTCH-LDG) ──▶ Mux ──▶ B.m ──▶ Mux ── ans (BASE-LDG rbs) ──▶ QIO
--
-- `LinearLeios` never sees it: in `node-layer = LinearLeios ⊗₁ id` the `QIO`
-- wire passes the node on the identity side.  So the answer is the base
-- layer's current chain and not the node's cached `RBs`, which is why the
-- chain and slot lemmas hold at every state rather than only at quiescent
-- ones.  `Mux`'s stack is pushed by the request and popped by the answer, so
-- a query leaves the multiplexer as it found it — what `Leios1-isPure` needs.
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

-- The base functionality as seen through the multiplexed network
spec : Machine DD.M ((Network ⊗₀ BaseIO) ⊗₀ BaseAdv)
spec = ⊗-assoc⃖ CC.∘ (CC.id ⊗₁ B.m) CC.∘ NetTranslate

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
-- puts the node's two channels together; the node; and a regrouping that
-- gathers the layer's IO, `ExtIO`, next to its adversary channel.  The query
-- port passes through the node untouched.
ExtIO : Channel
ExtIO = IO ⊗₀ QIO

mux-layer : Machine (Network ⊗₀ BaseIO) (FFD ⊗₀ (BaseIO ⊗₀ QIO))
mux-layer = Shim ⊗₁ Mux

mux-shuffle : Machine (FFD ⊗₀ (BaseIO ⊗₀ QIO)) ((FFD ⊗₀ BaseIO) ⊗₀ QIO)
mux-shuffle = ⊗-assoc⃖

node-layer : Machine ((FFD ⊗₀ BaseIO) ⊗₀ QIO) ((IO ⊗₀ Adv) ⊗₀ QIO)
node-layer = LinearLeios ⊗₁ CC.id

-- The solver does not unfold names, so its goals spell `ExtIO` out.
regroup-extᵢ : ((IO ⊗₀ Adv) ⊗₀ QIO) [ In ]⇒[ In ] ((IO ⊗₀ QIO) ⊗₀ Adv)
regroup-extᵢ = ⇒-solver

regroup-extₒ : ((IO ⊗₀ QIO) ⊗₀ Adv) [ Out ]⇒[ Out ] ((IO ⊗₀ Adv) ⊗₀ QIO)
regroup-extₒ = ⇒-solver

regroup-ext : Machine ((IO ⊗₀ Adv) ⊗₀ QIO) (ExtIO ⊗₀ Adv)
regroup-ext = TotalFunctionMachine' regroup-extᵢ regroup-extₒ

ext-spec : Machine (Network ⊗₀ BaseIO) (ExtIO ⊗₀ Adv)
ext-spec = regroup-ext CC.∘ (node-layer CC.∘ (mux-shuffle CC.∘ mux-layer))

-- The node as deployed: the extension layer stacked on the base spec. Its
-- adversary channel is the base functionality's, `BaseAdv`, next to
-- `LinearLeios`'s own, `Adv`
Leios1 : Machine DD.M (ExtIO ⊗₀ BaseAdv ⊗₀ Adv)
Leios1 = ext-spec ∘ᴷ spec

-- the optional EB is the one determined by the RB, _not_ the one announced by it
record LeiosBlock : Type where
  field rb : RankingBlock
        eb : Maybe EndorserBlock
        correct : HashCorrectB rb eb

hash-unique' : (rb : RankingBlock) → (eb₁ eb₂ : Maybe EndorserBlock)
  → (hc₁ : HashCorrectB rb eb₁) → (hc₂ : HashCorrectB rb eb₂) → (eb₁ , hc₁) ≡ (eb₂ , hc₂)
hash-unique' rb eb₁ eb₂ hc₁ hc₂ =
  Σ-≡,≡→≡ (hash-unique rb eb₁ eb₂ hc₁ hc₂ , HashCorrect-irrel _ _ _ _)

-- A ranking block as a Leios block.
toLeiosBlock : RankingBlock → LeiosBlock
toLeiosBlock rb = record { rb = rb ; eb = ebOf rb ; correct = ebOf-correct rb }

LeiosBlock-Injective : Injective _≡_ _≡_ LeiosBlock.rb
LeiosBlock-Injective
  {record { rb = rb ; eb = eb₁ ; correct = correct₁ }}
  {record { rb = rb ; eb = eb₂ ; correct = correct₂ }} refl =
  subst (λ (eb , correct) → _ ≡ record { rb = rb ; eb = eb ; correct = correct })
    (hash-unique' rb eb₁ eb₂ correct₁ correct₂) refl
