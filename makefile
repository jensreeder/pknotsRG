
OPTIONS=  -fvia-C  -O2 -fglasgow-exts -funbox-strict-fields

all: pknotsRG-mfe pknotsRG-enf pknotsRG-loc ADPfold

pknotsRG-mfe: pknotsRG-mfe.lhs 
	ghc $(OPTIONS) --make $< -o $@

pknotsRG-enf: pknotsRG-enf.lhs 
	ghc $(OPTIONS) --make $< -o $@

pknotsRG-loc: pknotsRG-loc.lhs 
	ghc $(OPTIONS) --make $< -o $@

ADPfold: ADPfold.lhs 
	ghc $(OPTIONS) --make $< -o $@

pknotsRG-mfe-nd: pknotsRG-mfe_nodangle.lhs 
	ghc $(OPTIONS) --make $< -o $@

clean:
	rm *.hi
	rm *.o
