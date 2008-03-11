#! /bin/sh

if [ -d publish/ver$1 ]; then
	echo "ver $1 already exists"
else
	if [ ! -d publish ]; then
		mkdir publish
	fi
	mkdir publish/ver$1
	mkdir publish/ver$1/celf

	cp AbstractRecursion.sml publish/ver$1/celf/
	cp ApproxTypes.sig publish/ver$1/celf/
	cp ApproxTypes.sml publish/ver$1/celf/
	cp BackTrack.sig publish/ver$1/celf/
	cp BackTrack.sml publish/ver$1/celf/
	cp Context.sig publish/ver$1/celf/
	cp Context.sml publish/ver$1/celf/
	cp Conv.sig publish/ver$1/celf/
	cp Conv.sml publish/ver$1/celf/
	cp Eta.sig publish/ver$1/celf/
	cp Eta.sml publish/ver$1/celf/
	cp ExactTypes.sig publish/ver$1/celf/
	cp ExactTypes.sml publish/ver$1/celf/
	cp ImplicitVars.sig publish/ver$1/celf/
	cp ImplicitVars.sml publish/ver$1/celf/
	cp OpSem.sig publish/ver$1/celf/
	cp OpSem.sml publish/ver$1/celf/
	cp PatternBind.sig publish/ver$1/celf/
	cp PatternBind.sml publish/ver$1/celf/
	cp PermuteList.sig publish/ver$1/celf/
	cp PermuteList.sml publish/ver$1/celf/
	cp PrettyPrint.sig publish/ver$1/celf/
	cp PrettyPrint.sml publish/ver$1/celf/
	cp README publish/ver$1/celf/
	cp Rnd-smlnj-mlton.sml publish/ver$1/celf/
	cp Rnd.sig publish/ver$1/celf/
	cp Signatur.sml publish/ver$1/celf/
	cp SignaturTable.sig publish/ver$1/celf/
	cp SignaturTable.sml publish/ver$1/celf/
	cp Subst.sml publish/ver$1/celf/
	cp SymbTable.sig publish/ver$1/celf/
	cp SymbTable.sml publish/ver$1/celf/
	cp Syntax.sig publish/ver$1/celf/
	cp Syntax.sml publish/ver$1/celf/
	cp TopLevelUtil.sml publish/ver$1/celf/
	cp TypeCheck.sig publish/ver$1/celf/
	cp TypeCheck.sml publish/ver$1/celf/
	cp TypeRecon.sig publish/ver$1/celf/
	cp TypeRecon.sml publish/ver$1/celf/
	cp Unify.sig publish/ver$1/celf/
	cp Unify.sml publish/ver$1/celf/
	cp Util.sig publish/ver$1/celf/
	cp Util.sml publish/ver$1/celf/
	cp VRef.sig publish/ver$1/celf/
	cp VRef.sml publish/ver$1/celf/
	cp Whnf.sig publish/ver$1/celf/
	cp Whnf.sml publish/ver$1/celf/
	cp celf.grm publish/ver$1/celf/
	cp celf.lex publish/ver$1/celf/
	cp celf.mlb publish/ver$1/celf/
	cp license-gpl3.txt publish/ver$1/celf/
	cp main-export.sml publish/ver$1/celf/
	cp main-run.sml publish/ver$1/celf/
	cp main.sml publish/ver$1/celf/
	cp sources.cm publish/ver$1/celf/
	cp .mkexec publish/ver$1/celf/

	echo "ignore cvs comments about celf.lex.sml, celf.grm.sig, and celf.grm.sml"
	cvs stat README celf.lex celf.grm celf.mlb *.cm .mkexec *.sml *.sig | grep Reposit > publish/ver$1/ver$1.txt

	grep "Celf ver" main.sml

	cd publish/ver$1
	tar -c celf | gzip > celf-v$1.tgz
	cd ../..
fi

