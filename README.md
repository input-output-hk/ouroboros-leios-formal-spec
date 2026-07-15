# Ouroboros Leios formal specification

Formal specification of the [Linear Leios](https://cips.cardano.org/cip/CIP-0164) protocol in Agda, covering:

- **Linear Leios protocol** — specification ([`Leios/Linear.lagda.md`](formal-spec/Leios/Linear.lagda.md))
- **Certified trace verifier** — for verifying real run-time traces ([`Leios/Linear/Trace/Verifier.lagda.md`](formal-spec/Leios/Linear/Trace/Verifier.lagda.md)), see also [here](https://github.com/input-output-hk/ouroboros-leios/blob/main/leios-trace-verifier/ReadMe.md)
- **Safety & liveness** — proofs of CP, HCG and ∃CQ (as defined in Section 2 of the [Ouroboros paper](https://eprint.iacr.org/2016/889.pdf)) assuming corresponding properties about the base chain (Praos) ([`Network/Leios.agda`](formal-spec/Network/Leios.agda))

Built on the [`categorical-crypto`](https://github.com/input-output-hk/categorical-crypto) library, providing a notion of composable processes and reasoning techniques.

For rendered interactive and explorable documentation, see [here](https://leios.cardano-scaling.org/formal-spec/Leios.Linear.html).

## Build

```console
$ nix build --no-link --accept-flake-config .#leiosSpec
```

or

```console
$ nix develop
$ cd formal-spec
$ agda formal-spec.lagda.md
```
