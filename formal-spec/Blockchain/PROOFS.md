# Safety & Liveness proofs — structure and open obligations

This note describes how the safety and liveness results for Linear Leios are
organised in the Agda spec, the individual steps each proof takes, and — most
importantly — **what is still unproven** (taken as a hypothesis / module
parameter rather than discharged).

Both results have the same shape: they are **conditional reduction (transfer)
theorems**. They do *not* prove Linear Leios secure from scratch. They prove:

> *If the underlying Praos protocol is safe/live, and the Linear Leios honest
> node is a faithful "extension" of a Praos node whose chain projects onto a
> Praos chain, then Linear Leios inherits safety/liveness.*

Everything is stated over the Ranking-Block (RB) **backbone**: the block
projection `getBaseBlock = LeiosBlock.rb` throws the Endorser Block (EB) away,
so the properties below talk about the RB sequence only, not EB/ledger content.

Relevant files:

| File | Role |
|------|------|
| `Blockchain/Safety.agda` | `Spec`, `Deployment`, `IsExtension`, `safeState`/`safety` |
| `Blockchain/Safety/Transfer.agda` | safety transfer (base ⇒ ext) |
| `Blockchain/Liveness.agda` | `hcg` (chain growth), `∃cq` (chain quality) |
| `Blockchain/Liveness/Transfer.agda` | liveness transfer (base ⇒ ext) |
| `Blockchain/IsBlockchain.agda` | `BlockChainInfo` / `Chain`,`Slot` queries |
| `Network/Leios.agda` | instantiation for the concrete Linear Leios node |

---

## Shared setup (`Blockchain/Safety.agda`)

- **`Spec` / `Deployment`** (`Safety.agda:12`, `:21`) — a protocol deployed
  across `n` nodes. Honest nodes behave as `honest-node-spec`; the rest are
  arbitrary (`honest-nodes-≡-spec`, `:33`). `protocol E` is the closed machine
  obtained by composing the environment, the nodes, and the network (`:46`).
- **Queries** (`:49`) — `getChain` and `getSlot` read an honest node's local
  state through the deployment's `IsBlockchain` instance
  (`BlockChainInfo`/`queryCompute`, `IsBlockchain.agda:13`).
- **Safety property** (`:63`) —
  `safeState k`: for all honest `p`, `p'`,
  `prune k (getChain p) ≼ getChain p'` (common prefix).
  `safety k`: `safeState k` is an `Invariant` of `protocol E` for every `E`.
- **`IsExtension`** (`:73`) — the structural bridge from an *ext* spec (Leios)
  to a *base* spec (Praos):
  - `getBaseBlock : BlockExt → BlockBase`, required injective
    (`getBaseBlock-inj`);
  - `ext-layer` and `is-extension`: the honest ext node factors as
    `ext-layer ∘ base-honest-node`.

---

## Safety proof (`Blockchain/Safety/Transfer.agda`)

Input: an ext `Deployment`, a `base-spec`, a `ChannelCat`, and an `IsExtension`
witness. Output: `Base.safety k → Ext.safety k`.

**Step 1 — Build the base deployment from the ext one.**
`base-all-nodes` (`:44`) replaces each honest node with the Praos node;
`extPart` (`:60`) is the per-node extension layer (`idᴷ` for adversarial
nodes). `base` (`:65`) assembles these into a `Deployment BlockBase` sharing
the *same* network and honest set.

**Step 2 — The protocols are isomorphic.**
`single-protocol-≡` (`:81`) rewrites each honest node `idᴷ ∘ nodeₚ` into
`extPart ∘ base-nodeₚ` using `is-extension`. Lifting this over the network
gives `transProtocol : Ext.protocol E ≡ᴹ Base.protocol transEnv` (`:105`), a
machine isomorphism. `transEnv`/`transState`/`transTrace` (`:102`, `:118`,
`:121`) transport environments, states, and traces across it.

**Step 3 — Chain projection (the key hypothesis).**
`ChainLemma-ty` (`:125`):
`Base.getChain (transEnv E) (transState E s) ≡ map getBaseBlock (Ext.getChain E s)`.
The Praos chain equals the RB-projection of the Leios chain on the same state.

**Step 4 — Push safety through the projection.**
`safeState-ext⇒base` / `safeState-base⇒ext` (`:140`, `:148`) move the
common-prefix relation across `map getBaseBlock`, using `prune-map`, `map-≼`,
and (for the `base⇒ext` direction) injectivity of `getBaseBlock` (`inj-≼`).

**Step 5 — Assemble.**
`transfer k CL baseSafety` (`:156`): for any `E`, transport the ext trace to
base, apply `baseSafety`, transport the conclusion back.

---

## Liveness proof (`Blockchain/Liveness.agda` + `.../Transfer.agda`)

Two block-level properties (`Liveness.agda`):

- **HCG — honest chain growth** (`:40`): for every honest block `b` in an
  honest chain, `τ · (currentSlot − slotOf b) ≤ length (suffix after b)`.
- **∃CQ — existential chain quality** (`:57`): the suffix of blocks produced in
  the last `T` slots (`recent T`, `:49`) contains at least one honest block.

Transfer (`Liveness/Transfer.agda`) reuses the safety machinery
(`transEnv`/`transState`/`transTrace`, `ChainLemma`) and adds:

- **`SlotLemma-ty`** (`:86`):
  `Base.getSlot (transEnv E) (transState E s) ≡ Ext.getSlot E s` — slot reports
  agree. (For Leios this is definitional: `slotOf`/`producer` of a `LeiosBlock`
  are those of its RB.)
- **`producer-compat` / `slotOf-compat`** (module params, `:32`): a block's
  producer/slot factor through `getBaseBlock`. Instantiated with `refl` for
  Leios.

**Steps.**
- `recent-map` (`:91`): `map getBaseBlock` commutes with the `recent T` filter
  (slots are preserved by `slotOf-compat`).
- `map-split` (`:56`): split a `map f` chain at a block, recovering the
  pre-image split — lets HCG move between ext and base chains.
- `hcgState-ext⇒base` / `base⇒ext` (`:108`, `:158`): transport the growth
  inequality, rewriting slots via `SlotLemma`, lengths via `length-map`, and
  honesty via `producer-compat`.
- `∃cqState-ext⇒base` / `base⇒ext` (`:209`, `:238`): transport the `Any` honest
  witness through `recent-map` and `Any.map`.
- `hcg-transfer` / `∃cq-transfer` (`:268`, `:278`): given `ChainLemma` +
  `SlotLemma` for all `E` and Praos HCG/∃CQ, conclude ext HCG/∃CQ.

---

## Instantiation for Linear Leios (`Network/Leios.agda`)

- `LeiosBlock` (`:79`) bundles `rb : RankingBlock`, `eb : Maybe EndorserBlock`,
  and `correct : HashCorrectB rb eb`; `getBaseBlock = LeiosBlock.rb` (`:162`),
  injective via `LeiosBlock-Injective` (`:89`).
- `safetyS : Deployment LeiosBlock` (`:128`), `base-spec` (`:149`), and
  `extension : IsExtension …` (`:157`) wire the concrete node into the generic
  transfer lemmas.
- Exposed entry points — **still conditional**:
  - `leiosSafety` (`:171`) `: (∀ E → ChainLemma) → Base.safety k → S.safety k`
  - `leiosHCG` (`:180`) `: (∀ E → ChainLemma) → (∀ E → SlotLemma) → ∀ τ → BL.hcg τ → EL.hcg τ`
  - `leios∃CQ` (`:185`) `: (∀ E → ChainLemma) → (∀ E → SlotLemma) → ∀ T → BL.∃cq T → EL.∃cq T`

---

## What still needs to be finished

The transfer theorems typecheck, but **no unconditional safety/liveness theorem
exists yet** — every premise below is an open hypothesis or an un-instantiated
module parameter. To turn these into real guarantees:

1. **Discharge `ChainLemma-ty`** for the concrete Leios deployment
   (`Safety/Transfer.agda:125`, consumed at `Network/Leios.agda:171,180,185`).
   This is where the real work is: prove that the RB-projection of an honest
   Leios node's chain equals the Praos chain it would hold. Tractable *because*
   RB adoption is decoupled from EB delivery (`Leios/Linear.lagda.md:163`
   `Slot₂` takes `RBs = rbs` wholesale), but it is currently assumed, not proven.

2. **Discharge `SlotLemma-ty`** (`Liveness/Transfer.agda:86`). Expected to be
   near-definitional (`slotOf`/`getSlot` inherited from the RB), but still
   needs to be written.

3. **Supply the Praos premises** `Base.safety k`, `BL.hcg τ`, `BL.∃cq T`. These
   are *assumed*; the Praos security proof lives outside this repo and is not
   imported. Without it the reductions conclude nothing.

4. **Instantiate the `Network.Leios` module parameters** (`:107`–`:114`):
   `IsBlockchain-base`, `isConstrained-Leios`, `isPure-Leios`, the
   `HashCorrectB` predicate (+ its irrelevance/uniqueness laws, `:23`–`:26`),
   and the structural equation `is-extension-eq`. Nothing in the repo provides
   concrete values for these, so `leiosSafety`/`leiosHCG`/`leios∃CQ` are never
   actually applied.

5. **Apply the entry points** to obtain a closed theorem `S.safety k` /
   `EL.hcg τ` / `EL.∃cq T` once (1)–(4) are available.

### Scope limitation worth recording

All of the above concern the **RB backbone only** (`getBaseBlock` discards the
EB). The "Linear Leios Security Analysis" assumptions — *Assumption 1* (certified
EBs delivered within `L_diff`) and *Assumption 2* (reapply cheaper than apply) —
are **not** needed for these proofs, because they govern EB delivery/cost, which
the chosen abstraction projects away. They would only re-enter if the properties
were strengthened to talk about EB/ledger content, e.g.:

- chain growth/quality that **counts EBs** instead of projecting them away;
- an "honest nodes can always extend with a full ledger state" property (the
  empty-block problem from the doc's *Robustness to extreme conditions*);
- relating the EB-inclusive `currentChain` (`Leios/Protocol.lagda.md:90`) across
  honest parties rather than just the RB sequence.

At that point "the EB referenced by an adopted RB is present in the node's
`EBs'`" becomes a non-trivial invariant whose justification is exactly
Assumption 1.
