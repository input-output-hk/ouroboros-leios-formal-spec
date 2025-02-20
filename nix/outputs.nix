{ repoRoot, inputs, pkgs, lib, system }:

let
  agda = import ./agda.nix {inherit pkgs lib inputs;};
in
[{
    devShells.default = repoRoot.nix.shell;
    packages = agda;
}]
