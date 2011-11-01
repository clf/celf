
all:
	echo "Run 'make mlton' or 'make smlnj' or 'make test'"

mlton: *.sml *.sig */*.sml */*.sig *.mlb
	mllex celf.lex
	mlyacc celf.grm
	mlton celf.mlb

smlnj: *.sml *.sig */*.sml */*.sig *.cm
	sml < main-export.sml
	./.mkexec `which sml` `pwd` celf

install: 
	cp celf $(DESTDIR)/bin/celf.new
	mv $(DESTDIR)/bin/celf.new $(DESTDIR)/bin/twelf-server