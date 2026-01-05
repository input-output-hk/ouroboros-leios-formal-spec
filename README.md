# Ouroboros Leios formal specification

This repository is to define a formal specification of the Ouroboros Leios protocol.

## Specification

Build the Agda specification for Leios using either

```console
$ nix build --no-link --accept-flake-config .#leiosSpec
```

or

```console
$ nix develop
$ cd formal-spec
$ agda formal-spec.lagda.md
```
