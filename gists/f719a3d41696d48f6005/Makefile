all: literate

literate: literate.hs
	ghc --make -fllvm -O3 literate.hs
	strip literate
	cp literate ~/bin
