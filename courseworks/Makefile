AGDA_EXEC ?= agda

.PHONY: all build clean run image

all: hello cellular tiling

hello: 00-Install.agda
	${AGDA_EXEC} -c 00-Install.agda

cellular: 01-Cellular.agda
	${AGDA_EXEC} -c 01-Cellular.agda

tiling: 02-Tiling.agda
	$(AGDA_EXEC) -c 02-Tiling.agda --ghc-dont-call-ghc
	cabal build Tiling.cabal

clean:
	rm -rf dist-newstyle
	rm -rf MAlonzo
	find . -name "*.agdai" | xargs rm -f
