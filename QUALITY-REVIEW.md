# Quality review — yveshauser/voting (2026-09-29)

Scope: the branch diff against `git merge-base origin/main yveshauser/voting` (ec5bc25) up to the source tip 2bdb8b2, as follows:
`Leios/Linear.lagda.md`, `Leios/Linear/Progress.agda`, `Leios/Linear/Trace/Verifier.lagda.md`, `Leios/Linear/Trace/Verifier/Test.lagda.md`, `Leios/Protocol.lagda.md`, `Leios/SpecStructure.lagda.md`, `Leios/Voting/{Channel,Certifier,Ideal,Real,Voter}`, `Network/Leios.agda`, `Test/Defaults.agda` and `formal-spec.lagda.md` (all under `formal-spec/`).
The sibling `leios-trace-verifier` in `ouroboros-leios` was read to decide what is downstream-facing.

Verification: whole-project `agda formal-spec.lagda.md` green (rc 0, no `-W[no]` warnings) after every cherry-picked batch and at the tip.  Soundness baseline unchanged: 0 `postulate`, `TERMINATING`, `NON_TERMINATING`, `trustMe`, `primTrustMe`, `believe_me`, `unsafe` and `--no-` pragmas in scope, and every scope file is `--safe`, before and after.  The added lines contain none of them.  `nix build .#leiosSpec` (GHC/MAlonzo, tracked files) succeeded at a761f11.

Sweep tally: the repo has no `.claude/sweeps` toolkit, so no tally JSON exists.  The classes were run by hand as typechecked spikes; the manual counts are as follows:
- `using-drop`: 17 candidates, 16 kept; 1 red (`Test.Defaults … using (d-SpecStructure; hpe)`, which the test's TODO explains).  A further `using` narrowing in `Test.Defaults` (`CategoricalCrypto`) is red either way (`id`, then `_∘_` ambiguous).
- Dead imports and `hiding` clauses: 25 candidates, 25 kept (one, `open FFD hiding …` in `Leios.Linear`, is red and stays).
- Dead generalisable variables: 13 kept (Linear 8, Verifier 3, Network.Leios 2).
- `binder-drop` / `implicit-drop`: about 20 sites across Certifier, Voter, Ideal, Real, Dec-↝ and the verifier, all kept green.
- `enum-with` → `case_of_` or a library combinator: 11 sites; 8 kept (`Certifier.covers` via `decidable-stable`, `Dec-AnswerMatches` via `map′`, `Base₃`/`Cert₁`/`Cert₂`/`Cert₃` in `verifyStep'` via the generated premises, `mkRB` via `maybe`, `upd` fall-through); `α-WF`/`covers` in `Real` stay as `with` because `∈-map⁻` has to be matched on `refl`, and `base-step`'s `certRequest s in eqc` and `subst'` need the equation.
- `enum-where`/`let` inlining: 6 sites; 4 kept (`eq₃'`, `voted-votes`, `sub'`, the `Real.α-WF` let); `s₁` in `base-step` is red (unsolved meta) and `splitVotes.isVote` stays as a named helper.
- Comment blocks: every block in the 14 files was listed and dispositioned by two enumeration passes (about 170 blocks); cuts and rewrites landed in the five prose commits below; the kept TODO markers are listed under Suggestions.

The house standard `CLAUDE.md` does not exist in this repository; the review used the maintainer's global house style, the surrounding code's idiom and the review contract.

## Committed (you can skim these)
- 85891b4 Shorten the voting correctness proofs — match `∈-map⁻` on `refl`, `decidable-stable`, `≤⇒≯`; statements untouched.
- fcbb4a4 Refute impossible `Dec-↝` cases by absurd patterns — removes four `≢` lemmas with no other use.
- 9984f7f Prune imports and unused private variables — each removal typechecked individually.
- 60439be Simplify small proofs in Linear, Progress and Protocol — `maybe`, `map′`, `(_ , VT-Role p , refl)`, `upd _ = s`, `Vote₁` layout.
- fc31413 Cut and correct prose in Linear, Progress, Protocol and SpecStructure — fixes, among others, "exactly three steps", the `CertCheck` gloss and the `Cert₂`/`Cert₃` rationale.
- e9b82d9 Use two spaces after sentence-ending periods in Linear prose — mechanical.
- 166ba91 Rewrap the `Base₃` paragraph — mechanical.
- 813473a Decide the verifier's certificate steps by their generated premises — every `errorMsg` string byte-identical, constructor types untouched.
- 25e516a Test that the verifier rejects broken certificate steps — six negative tests through `verifyTrace`/`errorMsg`, one per new premise.
- db422e4 Share the test's initial state and drop its redundant `PubKeys` override — a field `initLeiosState` already sets.
- dd82ce6 Simplify `hrb` and the `Dec-SimpleFFD` refutations — test fixture only.
- f6c972a Trim and correct the verifier and test prose — includes the stale `toRcvType (inj₂ (inj₂ FetchLdgI))`.
- 4162678 Use two spaces after sentence-ending periods in the verifier prose — mechanical.
- 6c9232a Tidy the ideal and real voting proofs — `length-++-sucʳ`, Prelude `filter`, inlined helpers.
- 87625ea Tidy the certifier — `Dec-honest` replaced by instance search; binders shortened.
- ed46246 Open `Real` in the voter — also makes `Recv*`'s list argument implicit (internal, no other user).
- 002facc Trim and correct the voting modules' prose — removes the "forward simulation" and "exactly" overclaims and the ill-typed `Real ≤'UC Ideal` TODO.
- 7d3eac2 Tidy notation in `Network.Leios` — bare `∘`, parentheses, `Participant`, `S.` aliases, `map₁`; terms unchanged.
- 8878d0b Prove `LeiosBlock-Injective` by rewriting with the hash lemmas — deletes the single-use `hash-unique'` (no importer uses it).
- 10c1ce9 Draw the voter inside `specʳ` in the `Leios1ʳ` diagram — moves `Voter`, a component of `specʳ`, out of `ext-spec`.
- a761f11 Trim the comments in `Network.Leios` and the index — with `Leios1ʳ` as the single site of the open realization note.
- f9598c1 Key certificate queries by the announcing RB's hash — maintainer-approved (was a Statement-audit suggestion): `VT-Role` signs `hash currentRB`, so `Base₃`/`Cert₁`/`Cert₃` now query and correlate on it; merged into `yveshauser/voting`, whole project green.
- e935198 Assume that a certificate names its reference — maintainer-approved (was a Statement-audit suggestion): module parameter `mkCert-hash : ∀ r → getEBHash (mkCert r) ≡ r`, plus `mkCert-matches` showing a positive answer satisfies `AnswerMatches`.
- 29f4cd2 State the voter's certificate correctness over its log — maintainer-approved (was a Statement-audit suggestion): `vih`/`cc` now range over `log s'`; body is `real-cert-correct` directly.
- 5ca614c Say why a certificate step was refused — maintainer-approved (was a Public API suggestion): the `Err-Cert*` messages list the premises that can fail, as `Base₂`/`Base₃` do; the pinned tests are updated.

## Suggestions (need your call)

### Statement audit
- formal-spec/Leios/Voting/Certifier.lagda.md :: cert-correct — pigeonhole only: `Validated := HasVoteFor` makes `WF` and `covers` trivial, and `corrupt` is not tied to the deployment's `honest-Nodes`.  The prose now says so.  The intended property needs a trace lemma in `Network.Leios` linking logged votes on honest slots to `VT-Role` steps.
- formal-spec/Leios/Voting/Certifier.lagda.md :: Certified — the quorum is a count of distinct slots, ignoring stake, committee membership and signer validity; `length corrupt < threshold` is count-based while CIP-0164 is stake-based.  Document `threshold` as a stand-in, or parameterize by a weight.
- formal-spec/Leios/Linear.lagda.md :: Slot₂ — certificates adopted from other parties' RBs are never checked, and `mkCert : EBRef → EBCert` carries no evidence, so the certifier theorems say nothing about on-chain certificates.  Record as an open obligation.
- formal-spec/Leios/Voting/Voter.lagda.md :: machine⇒steps — `Real.Step` relates every list to every extension, so `Star Real.Step` is only a suffix relation, and nothing consumes the lemma.  Drop `Recv*`/`machine⇒steps`, or replace them with a lemma with content (every logged vote came from a `CAST` or a `Deliver`).
- formal-spec/Leios/Voting/Ideal.lagda.md :: Step — `Ideal.Step`, `wf-init`, `wf-step` and `Real.Step` have no consumer and no step simulation links them.  Either add `Real.Step rs rs' → … → α rs ≡ α rs' ⊎ I.Step (α rs) (α rs')` plus `Reachable ⇒ WF`, or drop them.
- formal-spec/Leios/Voting/Ideal.lagda.md :: cert-correct — the conclusion drops `Voted p x st`, which the proof has; `∃[ p ] (Voted p x st × honest p × Validated p x)` is strictly more informative.
- formal-spec/Leios/Voting/Voter.lagda.md :: AnswersCert — correctness is keyed on a classifier defined in the same file; a future rule emitting `CERT (just _)` without updating `AnswersCert` escapes the theorem.  An output-based premise is sturdier.
- formal-spec/Leios/Linear.lagda.md :: Cert₁ — `needsUpkeep Base` and `CertCheck ∈ˡ Upkeep` are implied by `PendingQuery ≡ just _` on reachable states; they matter only for arbitrary start states (`enough-traces`).  Keep or drop.

### Public API / module layout
- formal-spec/Leios/Linear/Trace/Verifier.lagda.md :: Err-EB-Role-premises — restate `Err-EB-Role-premises`/`Err-VT-Role-premises` as `¬ (EB-Role-premises … .proj₁)` like the certificate ones; definitionally equal, but it changes public constructor text.
- formal-spec/Leios/Linear/Trace/Verifier.lagda.md :: Ok' — `Ok'`, `Mismatch`, the nine `inj…≢…` lemmas and `verifyStep'` are unused downstream; candidates for `private`.
- formal-spec/Leios/Linear.lagda.md :: π-unique — `P`, `P?`, `not-found`, `subst'`, `π-unique` are `Dec-↝` helpers only; candidates for `private`.
- formal-spec/Leios/Linear.lagda.md :: Slot₂-premises — `Slot₂-premises` and `Base₁-premises` have zero uses.
- formal-spec/Leios/Linear.lagda.md :: AnswerMatches — it is stdlib `Data.Maybe.Relation.Unary.All ((_≡ r) ∘ getEBHash)`; the swap renames its constructors (`matches-nothing` is used in Progress).
- formal-spec/Leios/Linear/Progress.agda :: base-step — state the result as `Upkeep s' ≡ Base ∷ CertCheck ∷ Upkeep s` (both tails become `refl`); `upkeep-step`/`base-step`/`slot-step` could be `private`.
- formal-spec/Leios/Voting/Certifier.lagda.md :: castMsg — `castMsg`/`queryMsg`/`certMsg` could be `private`; `init` has zero uses.
- formal-spec/Leios/Voting/Real.lagda.md :: α-init — zero uses.
- formal-spec/Leios/Voting/Ideal.lagda.md :: unique-⊆⇒length≤ — general list lemmas (`∈-remove` too); move to `Leios.Prelude` or upstream to abstract-set-theory.
- formal-spec/Network/Leios.agda :: splitVotes — `splitVotes`, `voteMsgs`, `spec-rewire`, `⊗-interchange`, `zip⇒`, `unzip⇒` are used only in this file; candidates for `private`.
- formal-spec/Test/Defaults.agda :: d-Abstract — seven `open … public` re-exports are unused (the one importer takes `using (d-SpecStructure; hpe)`); the `Vote`/`vote` change only feeds the inert `VT₁` and diverges from the downstream fork.
- formal-spec/Leios/Protocol.lagda.md :: LeiosInput — `LeiosInput`, `LeiosOutput`, `Block`, `hasRB`, `hasTx`, `BaseT`, `BaseC`, the `Upkeep-Stage` helpers and the `↑-preserves-Upkeep` chain have zero uses (all older than the branch).
- formal-spec/Leios/Protocol.lagda.md :: High level structure — the diagram shows no voting functionality; the TODOs in `ebValid`/`vsValid`, `Test.lagda.md` (`Hashable-EndorserBlock`) and `Test/Defaults.agda` (`Dec-SimpleFFD` performance) were kept as open-work markers.
- formal-spec/formal-spec.lagda.md :: Network.Node — `Network.Basic`, `Network.MessageInterface`, `Network.Node` are imported nowhere and never checked (`Network.Node` has holes); delete or list.  The README's safety/liveness line omits the chain/slot-lemma and `IsConstrained`/`IsPure` hypotheses.
- Downstream (`leios-trace-verifier`, pinned at 73d61e9) will break on the next bump: `va`/`getEBCert` are gone from `SpecStructure`, `TestInput` has a fourth summand, and `Base₂` now refuses slots that call for a certificate.

### Tests
- formal-spec/Leios/Linear/Trace/Verifier/Test.lagda.md :: test₂ — under "Test error handling" it only re-checks that `test₁`'s trace is `Ok`; the new `test₅`–`test₁₀` cover the error path, so `test₂` can go or be retitled.
- formal-spec/Leios/Linear/Trace/Verifier/Test.lagda.md :: verify-EB₁-hash — pins the `Test.Defaults` fixture (`hash = txs`), not the verifier.  Delete.
- formal-spec/Leios/Linear/Trace/Verifier/Test.lagda.md :: VT₁ — the slot-105 vote delivery is inert (`upd` ignores vote headers); drop it with the `Vote` default change above.
- formal-spec/Leios/Linear/Trace/Verifier/Test.lagda.md :: Ftch-Action — the `Ftch` rule is exercised by no trace.

### Simplifications / perf not committed (judgment needed)
- formal-spec/Network/Leios.agda :: leiosSafety — state it through `LTr.Tr`/`LTrM.TrM` (which `Blockchain.Liveness.Transfer` already instantiates) and drop the private `Tr`/`TrM` and the `Blockchain.Safety.Transfer` import; spiked green, `Network.Leios` 21.7/20.4 s against 24.4–28.0 s (about 15% faster); same type, different statement text.
- formal-spec/Network/Leios.agda :: shuffle — `⨂-zip {n} {const A} {const B}` from `CategoricalCrypto.Machine.NAry` replaces `⊗-interchange`/`zip⇒`/`unzip⇒`; spiked green, time neutral; it changes the `network` machine term.
- formal-spec/Network/Leios.agda :: spec-rewire — `TotalFunctionMachine' ⇒-solver ⇒-solver` (plus `Tactic.Defaults`); spiked green, neutral, `is-extension = ≅ᴹ-refl` survives; changes `spec`'s state shape, which `IsBlockchain-base` mentions.
- formal-spec/Network/Leios.agda :: network — `shuffle … ⊗ʳ _ ∘ (DD.Network ⊗ᴷ Certifier.Functionality) ∘ ρ⇐` drops the `I` pad from `NAdv`; changes `S.Environment`.  Not spiked.
- formal-spec/Leios/Voting/Certifier.lagda.md :: toIdealCert — route the certifier through `Real.Refines` (`Vote := Party × Vote`, `Valid := λ _ → ⊤`), deleting about 30 lines of `voteRef`/`α`/`wf`/`covers`/`toIdealCert`; also unify `quorum` on `length votes` vs `length (map voter votes)`.  Not spiked.
- formal-spec/Leios/Voting/Real.lagda.md :: α-WF — one `α-sound` helper would serve both `α-WF` and `covers` (adds a public name).
- formal-spec/Leios/Linear.lagda.md :: certRequest — the hash lookup over `EBs`/`EBs'` exists four times (`lookupEB`, `voteDeadline`, `VT-Role`, `P?`); a shared lookup would need a first-match vs first-old-enough decision.
- formal-spec/Leios/Linear/Trace/Verifier.lagda.md :: verifyStep' — `Prelude.Result`'s `¿_¿ᴿ:_` with `>>=` would make each three-line decision one line.

## Tried, not worth it
- formal-spec/Leios/Voting/Certifier.lagda.md :: sel — replacing `sel`/`castMsg`/`queryMsg`/`certMsg` by the `app (⨂⇒ p)` idiom leaves unsolved metas even with `{f = const VotingC}` pinned.
- formal-spec/Leios/Linear/Progress.agda :: Base∉ — a decision procedure (`from-no`) for the four `∉` lemmas is red (`_≟_` ambiguous, unsolved instance metas); spelling the goal inside `¿ ¿` restates the signature.
- formal-spec/Leios/Linear/Progress.agda :: base-step — inlining the `s₁` let leaves an unsolved meta.
- formal-spec/Test/Defaults.agda :: CategoricalCrypto — opening the module bare or with `hiding (id)` is red (`id`, then `_∘_` ambiguous).
- formal-spec/Leios/Linear.lagda.md :: FFD — `open FFD hiding (_-⟦_/_⟧⇀_)` is needed (`Send`).
- formal-spec/Network/Leios.agda :: ⊗-interchange — `⇒-solver` instead of the hand-built permutation is green but time-neutral and needs an extra import; subsumed by the `⨂-zip` suggestion.
- formal-spec/Leios/Linear/Trace/Verifier.lagda.md :: Error handling — moving the heading down to `Err-verifyStep` would split a code fence for no gain.
- Typecheck perf: cold profile of the scope is 8.1 s `Leios.Linear`, 7.9 s the verifier, 4.4 s `Network.Leios`, everything else under 2.2 s (whole project 50.8 s); no hotspot warranted a structural spike beyond the `leiosSafety` dedup above.
