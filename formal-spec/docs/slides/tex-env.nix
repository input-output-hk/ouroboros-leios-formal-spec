# TeX Live environment for the slides: scheme-medium plus minted.
#
# minted 3.7 bundles latexminted 0.6.0, which crashes under Python 3.14
# (`ArgParser.__init__() got an unexpected keyword argument 'color'`), so
# texlive is built against Python 3.13.  The packages must come from the
# overridden set: the `ps` argument of `withPackages` is the original one.
{ pkgs }:
let
  tl = pkgs.texlive.override { python3 = pkgs.python313; };
in
tl.withPackages (
  _: with tl.pkgs; [
    scheme-medium
    beamertheme-metropolis
    minted
    # minted's dependencies, which scheme-medium lacks
    upquote
    lineno
    catchfile
    xstring
    fvextra
    latex2pydata
    pgfopts
  ]
)
