PARTS =						\
    Demo

all ::

TARGETS = all clean

$(foreach p,$(PARTS),																\
	$(eval $(TARGETS) :: $p/Makefile.coq ; $(MAKE) -C $p -w -f Makefile.coq $$@)								\
	$(eval $p/Makefile.coq : $p/Makefile.coq.input ; cd $p && ../../UniMath/sub/coq/bin/coq_makefile -f Makefile.coq.input -o Makefile.coq)	\
	)
