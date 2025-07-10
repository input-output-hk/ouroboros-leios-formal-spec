{ pkgs, lib, inputs, ... }:

with pkgs;
let

  locales = {
    LANG = "en_US.UTF-8";
    LC_ALL = "en_US.UTF-8";
    LOCALE_ARCHIVE = if pkgs.system == "x86_64-linux"
                     then "${pkgs.glibcLocales}/lib/locale/locale-archive"
                     else "";
  };

  customAgda = inputs.agda-nixpkgs.legacyPackages;

  agdaStdlib = customAgda.agdaPackages.standard-library;

  agdaStdlibClasses = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-classes";
    version = "2.2";
    src = fetchFromGitHub {
      repo = "agda-stdlib-classes";
      owner = "agda";
      rev = "v2.2";
      sha256 = "iaxCETpDKVhiprhRf+3jWJYFZU7D6D4/teYdHZ5Qw24=";
    };
    meta = { };
    libraryFile = "agda-stdlib-classes.agda-lib";
    everythingFile = "standard-library-classes.agda";
    buildInputs = [ agdaStdlib ];
  };

  agdaStdlibMeta = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-meta";
    version = "2.2";
    src = fetchFromGitHub {
      repo = "agda-stdlib-meta";
      owner = "agda";
      rev = "d459f65812b7eb73f8ebec771c2f6c17c9d79dc3";
      sha256 = "oSGZAgaaA8etxJJ+0b31OBIC08k9izQEaI9OEssjV6o=";
    };
    meta = { };
    libraryFile = "agda-stdlib-meta.agda-lib";
    everythingFile = "standard-library-meta.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  agdaSets = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-sets";
    version = "2.2";
    src = pkgs.fetchFromGitHub {
      repo = "agda-sets";
      owner = "input-output-hk";
      rev = "751b3ee39122fe33022af41e6c94dc820afde19a";
      sha256 = "sha256-0vjmNN8wuZXT4NM3aEv4z1Y+/6LpNfb7vzeajwZ3eFY=";
    };
    meta = { };
    libraryFile = "abstract-set-theory.agda-lib";
    everythingFile = "src/abstract-set-theory.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  };

  agdaIOGPrelude = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-prelude";
    version = "2.2";
    src = pkgs.fetchFromGitHub {
      repo = "iog-agda-prelude";
      owner = "input-output-hk";
      rev = "3329f250f2cbb9e3a5a0ef2c3c01e923f2bdf83a";
      sha256 = "sha256-PvfxcoK5MweXfdtbfDUTY23xsaAG093MbeX9fRac4sQ=";
    };
    meta = { };
    libraryFile = "iog-prelude.agda-lib";
    everythingFile = "src/Everything.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  deps = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta agdaSets agdaIOGPrelude ];

  leiosSpec = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "leios-spec";
    name = "leios-spec";  # FIXME: Why is this entry needed?
    src = ../formal-spec;
    meta = { };
    libraryFile = "leios-spec.agda-lib";
    everythingFile = "Everything.agda";
    buildPhase = ''
      OUT_DIR=$out make
    '';
    buildInputs = deps;
  };

  agdaWithPkgs = p: customAgda.agda.withPackages { pkgs = p; ghc = pkgs.ghc; };

  leiosDocs = stdenv.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "leios-docs";
    version = "0.1";
    src = ../formal-spec;
    meta = { };
    buildInputs = [ (agdaWithPkgs deps) pandoc ];
    buildPhase = ''
      agda --html --html-highlight=auto Everything.agda
      pandoc -s -c Agda.css html/Leios.Short.md -o html/Leios.Short.html
    '';
    installPhase = ''
      mkdir "$out"
      cp -r html "$out"
    '';
  };

in
{
  inherit agdaStdlib agdaStdlibClasses agdaStdlibMeta agdaSets agdaIOGPrelude ;
  agdaWithDeps = agdaWithPkgs deps;
  leiosSpec = leiosSpec;
  leiosDocs = leiosDocs;
}
