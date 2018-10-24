intepreter_sources = InterpretGrammar.hs Types.hs Monad.hs InterpretDecl.hs TypeCheck.hs

.PHONY: all sources docs

all: interpreter test
	

	
interpreter: sources main.hs $(intepreter_sources)
	ghc --make main.hs -o interpreter

test: sources Testgrammar.hs
	ghc --make Testgrammar.hs -o test

## Rules for producing bnfc files

Pargrammar.y Lexgrammar.x Docgrammar.tex Testgrammar.hs: grammar.cf
	bnfc grammar.cf

Pargrammar.hs: Pargrammar.y
	happy -gca Pargrammar.y

Lexgrammar.hs: Lexgrammar.x
	alex -g Lexgrammar.x

sources: Pargrammar.hs Lexgrammar.hs

docs: Docgrammar.hs
	latex Docgrammar.tex; dvips Docgrammar.dvi -o Docgrammar.ps


clean:
	-rm -f Docgrammar.* Lexgrammar.* Pargrammar.* Layoutgrammar.* Skelgrammar.* Printgrammar.* Testgrammar.* Absgrammar.* ErrM.* SharedString.* grammar.dtd XMLgrammar.* 
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f Docgrammar.ps
	-rm -f test interpreter

