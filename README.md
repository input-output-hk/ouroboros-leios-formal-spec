> [!CAUTION]
> 
> **Important Disclaimer & Acceptance of Risk**
> 
> This is a proof-of-concept implementation in its very early stage and is mostly experimental and exploratory. This code is provided "as is" for research and educational purposes only.  All contributions and feedbacks are welcome. **By using this code, you acknowledge and accept all associated risks, and our company disclaims any liability for damages or losses.**

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
$ agda Everything.agda
```
