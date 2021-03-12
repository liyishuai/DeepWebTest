COQMAKEFILE?=Makefile.coq

all: $(COQMAKEFILE)
	$(MAKE) -C ../shrink
	@+$(MAKE) -f $(COQMAKEFILE) all
	$(MAKE) -C extract

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $(COQMAKEFILE) cleanall
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
	$(MAKE) -C extract $@

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

force _CoqProject Makefile: ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f $(COQMAKEFILE) $@

.PHONY: all clean force
