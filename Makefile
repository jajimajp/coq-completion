ifeq "$(COQBIN)" ""
	COQBIN=$(dir $(shell which coqtop))/
endif

%: Makefile.coq

Makefile.coq: _CoqProject.plugin
	$(COQBIN)coq_makefile -f _CoqProject.plugin -o Makefile.coq

-include Makefile.coq
