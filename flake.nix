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

        locales = {
          LANG = "en_US.UTF-8";
          LC_ALL = "en_US.UTF-8";
          LOCALE_ARCHIVE = if pkgs.system == "x86_64-linux"
                   then "${pkgs.glibcLocales}/lib/locale/locale-archive"
                   else "";
        };

        leiosSpec = pkgs.agdaPackages.mkDerivation {
          inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
          pname = "leios-spec";
          version = "0.1";
          src = ./formal-spec;
          meta = { };
          libraryFile = "leios-spec.agda-lib";
          everythingFile = "formal-spec.lagda.md";
          buildPhase = ''
            OUT_DIR=$out make
          '';
          buildInputs = deps;
        };

        agdaWithPkgs = pkgs.agda.withPackages { pkgs = deps; ghc = pkgs.ghc; };

        leiosDocs = pkgs.stdenv.mkDerivation {
          inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
          pname = "leios-docs";
          version = "0.1";
          src = ./formal-spec;
          meta = { };
          buildInputs = [ agdaWithPkgs pkgs.pandoc ];
          buildPhase = ''
            agda --html --html-highlight=auto formal-spec.lagda.md
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
