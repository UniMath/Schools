COQVOFILES = fundamentals_lecture.vo coq_exercises.vo coq_solutions.vo
COQPATH = /Applications/Coq-Platform~8.15~2022.04.app/Contents/Resources
COQC = $(COQPATH)/bin/coqc
COQOPTS = -noinit -indices-matter -type-in-type -w -notation-overridden -Q $(COQPATH)/lib/coq/user-contrib/UniMath UniMath

all : $(COQVOFILES)

clean :
	-rm -f *.vo *.vo[sk] *.glob .*.aux

$(COQVOFILES) : %.vo : %.v
	$(COQC) $(COQOPTS) $^


.PHONY : all clean
