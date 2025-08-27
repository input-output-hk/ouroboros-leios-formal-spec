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
    version = "2.0";
    src = fetchFromGitHub {
      repo = "agda-stdlib-classes";
      owner = "omelkonian";
      rev = "2b42a6043296b4601134b8ab9371b37bda5d4424";
      sha256 = "sha256-kTqS9p+jjv34d4JIWV9eWAI8cw9frX/K9DHuwv56AHo=";
    };
    meta = { };
    libraryFile = "agda-stdlib-classes.agda-lib";
    everythingFile = "standard-library-classes.agda";
    buildInputs = [ agdaStdlib ];
  };

  agdaStdlibMeta = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-meta";
    version = "2.1.1";
    src = fetchFromGitHub {
      repo = "stdlib-meta";
      owner = "omelkonian";
      rev = "480242a38feb948cafc8bcf673d057c04b0ed347";
      sha256 = "pa6Zd9O3M1d/JMSvnfgteAbDMgHyelQrR5xyibU0EeM=";
    };
    meta = { };
    libraryFile = "agda-stdlib-meta.agda-lib";
    everythingFile = "standard-library-meta.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  agdaSets = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-sets";
    version = "2.1.1";
    src = pkgs.fetchFromGitHub {
      repo = "agda-sets";
      owner = "input-output-hk";
      rev = "f517d0d0c1ff1fd6dbac8b34309dea0e1aea6fc6";
      sha256 = "sha256-OsdDNNJp9NWDgDM0pDOGv98Z+vAS1U8mORWF7/B1D7k=";
    };
    meta = { };
    libraryFile = "abstract-set-theory.agda-lib";
    everythingFile = "src/abstract-set-theory.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  };

  agdaIOGPrelude = customAgda.agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-prelude";
    version = "2.0";
    src = pkgs.fetchFromGitHub {
      repo = "iog-agda-prelude";
      owner = "input-output-hk";
      rev = "e1a54e1d317e4acd3dc66162a31204557976201c";
      sha256 = "sha256-Hn4+vLDOsaVS4rq5XBvAJ0q4loelO+W18fO+6SIXHQc=";
    };
    meta = { };
    libraryFile = "iog-prelude.agda-lib";
    everythingFile = "src/Everything.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
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
      pandoc -s -c Agda.css html/Leios.Linear.md -o html/Leios.Linear.html
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
