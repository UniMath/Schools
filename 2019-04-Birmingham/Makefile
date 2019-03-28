PARTS =						\
    Part1_Spartan_Type_Theory			\
    Part2_Fundamentals_Coq			\
    Part3_Univalent_Foundations			\
    Part4_Tactics_UniMath			\
    Part5_Set_Level_Mathematics			\
    Part6_Category_Theory			\
    Part8_UniMath_future

all ::

TARGETS = all clean

$(foreach p,$(PARTS),																\
	$(eval $(TARGETS) :: $p/Makefile.coq ; $(MAKE) -C $p -w -f Makefile.coq $$@)								\
	$(eval $p/Makefile.coq : $p/Makefile.coq.input ; cd $p && ../../UniMath/sub/coq/bin/coq_makefile -f Makefile.coq.input -o Makefile.coq)	\
	)
