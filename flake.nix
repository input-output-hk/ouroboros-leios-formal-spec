{
  description = "Ouroboros Leios specification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-utils.url = "github:numtide/flake-utils";

    agda-nix = {
      url = "github:input-output-hk/agda.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-utils,
      ...
    }:
    let
      inherit (nixpkgs) lib;
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            inputs.agda-nix.overlays.default
          ];
        };

        deps = with pkgs.agdaPackages; [
          standard-library
          standard-library-classes
          standard-library-meta
          abstract-set-theory
          agda-categories
          iog-prelude
        ];

        leiosSpec = pkgs.agdaPackages.mkDerivation {
          pname = "leios-spec";
          version = "0.1";
          src = ./formal-spec;
          meta = { };
          libraryFile = "leios-spec.agda-lib";
          everythingFile = "formal-spec.agda";
          buildPhase = ''
            OUT_DIR=$out make
          '';
          buildInputs = deps;
        };

        agdaWithPkgs = pkgs.agda.withPackages { pkgs = deps; ghc = pkgs.ghc; };

        leiosDocs = pkgs.stdenv.mkDerivation {
          pname = "leios-docs";
          version = "0.1";
          src = ./formal-spec;
          meta = { };
          buildInputs = [ agdaWithPkgs pkgs.pandoc ];
          buildPhase = ''
            agda --html --html-highlight=auto formal-spec.agda
            pandoc -s -c Agda.css html/Leios.Linear.md -o html/Leios.Linear.html
          '';
          installPhase = ''
            mkdir "$out"
            cp -r html "$out"
          '';
        };

      in
      {
        packages = {
          leiosSpec = leiosSpec;
          leiosDocs = leiosDocs;
          agdaWithPkgs = agdaWithPkgs;
          default = leiosSpec;
        };
        devShells.default = pkgs.mkShell {
          packages = [
            (pkgs.agdaPackages.agda.withPackages (
              builtins.filter (p: p ? isAgdaDerivation) leiosSpec.buildInputs
            ))
          ];
        };
      }
    );
}
