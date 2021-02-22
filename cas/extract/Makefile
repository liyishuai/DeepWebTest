COQMAKEFILE?=Makefile.coq

all:
	$(RM) TestCAS.native CasServer.native
	$(MAKE) CasServer.native
	$(MAKE) TestCAS.native 

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $^ cleanall
	@rm -f $^ $^.conf *~ *.ml* *.log
	@ocamlbuild -clean

%.native:
	$(MAKE) $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $*.vo
	ocamlbuild -use-ocamlfind $@
