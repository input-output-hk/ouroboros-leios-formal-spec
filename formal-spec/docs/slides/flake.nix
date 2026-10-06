{
  description = "Slides: Linear Leios in Agda";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs =
    { self, nixpkgs, ... }:
    let
      inherit (nixpkgs) lib;
      forAllSystems = lib.genAttrs [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      perSystem =
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          tex = import ./tex-env.nix { inherit pkgs; };

          # Metropolis sets Fira Sans.  The deck sets DejaVu Sans Mono, with
          # Noto Sans Math and DejaVu Sans as fallbacks for Agda symbols.
          # nixpkgs only ships Noto as the whole family, so fetch the one
          # font.
          notoSansMath = pkgs.fetchurl {
            url = "https://raw.githubusercontent.com/notofonts/notofonts.github.io/noto-monthly-release-2026.09.01/fonts/NotoSansMath/unhinted/otf/NotoSansMath-Regular.otf";
            hash = "sha256-o6OQTt42A51LqBd+wKqc+QZT58eSfXTXZr8x6ibip8E=";
          };
          fonts = pkgs.runCommand "slide-fonts" { } ''
            mkdir -p $out/share/fonts
            ln -s ${pkgs.dejavu_fonts}/share/fonts/truetype $out/share/fonts/dejavu
            ln -s ${pkgs.fira-sans}/share/fonts/truetype $out/share/fonts/fira-sans
            ln -s ${pkgs.fira-mono}/share/fonts/opentype $out/share/fonts/fira-mono
            install -Dm444 ${notoSansMath} $out/share/fonts/noto/NotoSansMath-Regular.otf
          '';
          # luaotfload finds system fonts through OSFONTDIR.
          OSFONTDIR = "${fonts}/share/fonts";
        in
        {
          inherit pkgs tex OSFONTDIR;
        };
    in
    {
      packages = forAllSystems (
        system:
        let
          inherit (perSystem system) pkgs tex OSFONTDIR;
        in
        {
          default = pkgs.stdenvNoCC.mkDerivation {
            name = "leios-cc-intro";
            # The rules diagram is rendered from its Graphviz source one
            # directory up, so the slide cannot drift from it.
            src = lib.fileset.toSource {
              root = ./..;
              fileset = lib.fileset.unions [
                ./leios-cc-intro.tex
                ../linear-rules.dot
              ];
            };
            sourceRoot = "source/slides";
            nativeBuildInputs = [
              tex
              pkgs.graphviz
            ];
            # \today on the title page: date the deck by its source, not by
            # the 1980 epoch that the build sandbox would give it.
            env = {
              inherit OSFONTDIR;
              FONTCONFIG_FILE = pkgs.makeFontsConf { fontDirectories = [ pkgs.dejavu_fonts ]; };
              SOURCE_DATE_EPOCH = toString self.lastModified;
            };
            # Two passes: the outline and frame numbers come from the
            # auxiliary files of the first.  -shell-escape lets minted run
            # Pygments.
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR TEXMFVAR=$TMPDIR/texmf-var
              # The frame title replaces the graph's own, and the slide background
              # shows through.
              dot -Tpdf -Glabel= -Gbgcolor=transparent ../linear-rules.dot -o linear-rules.pdf
              for pass in 1 2; do
                lualatex -shell-escape -interaction=nonstopmode -halt-on-error leios-cc-intro.tex
              done
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm444 leios-cc-intro.pdf $out/leios-cc-intro.pdf
              runHook postInstall
            '';
          };
        }
      );

      devShells = forAllSystems (
        system:
        let
          inherit (perSystem system) pkgs tex OSFONTDIR;
        in
        {
          default = pkgs.mkShell {
            packages = [
              tex
              pkgs.graphviz
            ];
            inherit OSFONTDIR;
          };
        }
      );
    };
}
