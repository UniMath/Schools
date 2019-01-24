PARTS =						\
    Part1_Spartan_Type_Theory			\
    Part2_Fundamentals_Coq			\
    Part3_Univalent_Foundations			\
    Part4_Tactics_UniMath			\
    Part5_Set_Level_Mathematics			\
    Part6_Category_Theory			\
    Part7_UniMath_future

clean all :; for p in $(PARTS) ; do $(MAKE) -C $$p -w -f Makefile.coq $@ || exit 1 ; done
