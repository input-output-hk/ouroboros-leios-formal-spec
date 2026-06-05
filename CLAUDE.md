# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Agda formal specification of the Ouroboros Leios protocol. All Agda sources live under `formal-spec/`. Files use either `.agda` or literate `.lagda.md`; the top-level entry point is `formal-spec/formal-spec.lagda.md`, which transitively imports every module that is expected to typecheck.

## Common commands

Typecheck the whole specification (preferred, uses pinned dependencies):

```console
nix build --no-link --accept-flake-config .#leiosSpec
```

Interactive development inside a shell with the right Agda + libraries:

```console
nix develop
cd formal-spec
agda formal-spec.lagda.md          # typecheck the entry point
agda Leios/Linear.lagda.md         # typecheck a single module
```

Generate HTML docs (also runs as a CI step on `main`):

```console
nix build .#leiosDocs
```

The `formal-spec/Makefile` drives Agda → Haskell extraction via MAlonzo and is invoked by the `leiosSpec` Nix derivation; you usually don't call it directly.

## Dependencies

`leios-spec.agda-lib` depends on: `standard-library`, `standard-library-classes`, `standard-library-meta`, `abstract-set-theory`, `iog-prelude`, `agda-categories`, `categorical-crypto`. These are pinned through `flake.nix` (via the `agda-nix` overlay) — bumping a library means updating `flake.lock`.

## Architecture

The specification is layered. New code generally lands in `formal-spec/Leios/`; the other top-level directories provide the substrate it builds on.

- `Leios/Abstract` defines the abstract interface (core types and functions) the protocol is parameterised over. `Leios/SpecStructure` bundles `Abstract` together with `FFD` (freshest-first delivery), `VRF`, `Base`, `KeyRegistration`, `Voting`, and `Blocks` into a single `SpecStructure` record. **Most concrete protocol modules take a `SpecStructure` as a module parameter** — this is the main extension point.
- `Leios/Protocol`, `Leios/Blocks`, `Leios/Voting`, `Leios/VRF`, `Leios/Base`, `Leios/KeyRegistration`, `Leios/FFD` are the core protocol pieces. `Leios/Config` holds protocol parameters; `Test/Defaults` provides default instantiations.
- `Leios/Linear` is the Linear Leios variant. `Leios/Linear/Trace/Verifier` defines trace verification used to state and check protocol properties; its `Test.lagda.md` is the executable test harness.
- `Leios/Prelude` is the project prelude (re-exported almost everywhere); `Prelude/Result` and `Prelude/Errors` are TODO-marked for migration into `iog-prelude`.
- `CategoricalCrypto` + `Leios/ChannelCat` + `Leios/NetworkShim` express cryptographic / network abstractions in the `categorical-crypto` library's category-theoretic framework (objects = `Channel`, morphisms = `Machine`). When working on `ChannelCat` proofs, look at how `⊗`, `⨂`, and `⊗ᴷ` interact — many lemmas are structure isomorphisms over these combinators.
- `Network/` (`Basic`, `BasicBroadcast`, `DelayedDiffuse`, `Leios`, `MessageInterface`, `Node`) models the network layer; `Blockchain/` (`IsBlockchain`, `Liveness/Transfer`, `Safety/Transfer`) holds the blockchain abstractions and the liveness/safety transfer lemmas.

When adding a new module, also import it from `formal-spec.lagda.md` (otherwise CI won't typecheck it). Use `{-# OPTIONS --safe #-}` — the build expects the whole spec to be `--safe`.

## CI

`.github/workflows/formal-spec.yaml` runs `nix build .#leiosSpec` on every PR touching `formal-spec/**`, `flake.nix`, or `flake.lock`. On merge to `main` it also builds `leiosDocs` and pings the downstream `input-output-hk/ouroboros-leios` repo via a `repository_dispatch` so the implementation repo can pull in the updated spec.
