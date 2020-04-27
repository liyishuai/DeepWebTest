all: Makefile.coq
	$(MAKE) -f $^ $@

clean: Makefile.coq
	$(MAKE) -f $^ $@
	$(RM) $^ $^.conf

Makefile.coq: _CoqProject
	coq_makefile -f $^ -o $@
