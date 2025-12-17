# Constants
AGDA?=agda
AGDA_RUN=$(AGDA) --transliterate --no-main
OUT_DIR?=dist
HS_DIR=$(OUT_DIR)/haskell
MALONZO_DIR=MAlonzo/Code
CABAL_TEST=cabal run test

# Agda -> Haskell
define agdaToHs
    @echo "Generating $@"
    $(eval CABAL_FILE=leios-spec.cabal)
    $(eval HS_DIST=$(HS_DIR)/src)
    mkdir -p $(HS_DIST)
    $(AGDA_RUN) -c --ghc-dont-call-ghc --compile-dir $(HS_DIST) $<
    find $(HS_DIST)/MAlonzo -name "*.hs" -print\
      | sed "s#^$(HS_DIST)/#        #;s#\.hs##;s#/#.#g"\
      >> $(HS_DIR)/$(CABAL_FILE)
endef
HS_LEIOS=$(HS_DIST)/$(MALONZO_DIR)/formal-spec.hs
$(HS_LEIOS): formal-spec.lagda.md
	$(call agdaToHs,leios-spec)
