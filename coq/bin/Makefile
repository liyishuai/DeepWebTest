all:
	$(MAKE) EchoServer.native
	$(MAKE) EchoTest.native

COQMAKEFILE	?= Makefile.coq

$(COQMAKEFILE): _CoqProject
	coq_makefile -f $^ -o $@

%.native:
	$(RM) $@
	$(MAKE) -C ..
	$(MAKE) $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $*.vo
	ocamlbuild -lib unix $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ $@
	$(RM) $^* *.ml*
	ocamlbuild -clean
