all: EchoServer.native EchoTest.native

COQMAKEFILE	?= Makefile.coq

$(COQMAKEFILE): _CoqProject
	coq_makefile -f $^ -o $@

%.native: $(COQMAKEFILE)
	$(MAKE) -C ..
	$(MAKE) -f $^ $*.vo
	ocamlbuild -lib unix $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ $@
	$(RM) $^* *.ml*
	ocamlbuild -clean
