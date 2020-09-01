all: clean
	$(MAKE) -C ..
	$(MAKE) EchoServer.native
	$(MAKE) EchoTest.native
	$(MAKE) Echo1.native
	$(MAKE) Client1.native

COQMAKEFILE	?= Makefile.coq

$(COQMAKEFILE): _CoqProject
	coq_makefile -f $^ -o $@

%.native:
	$(MAKE) $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $*.vo
	ocamlbuild -lib unix $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ $@
	$(RM) $^* *.ml*
	ocamlbuild -clean
