# Ouroboros Leios formal specification

This repository is to define a formal specification of the Ouroboros Leios protocol.

> [!CAUTION]
> This project is in its very early stage and is mostly
> experimental and exploratory. All contributions and feedbacks are
> welcome. No warranties of any kind about the current or future
> features of Cardano are to be expected, implicitly and explicitly.

## Specification

Build the Agda specification for Leios using either

```console
$ nix build --no-link --accept-flake-config .#leiosSpec
```

or

```console
$ nix develop
$ cd formal-spec
$ agda Everything.agda
```
