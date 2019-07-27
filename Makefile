all:

UniMath/README.md:
	git submodule update --init UniMath

build_UniMath: UniMath/README.md
	$(MAKE) -C UniMath TAGS all

WORKSHOPS = 			\
	2017-12-Birmingham 	\
	2019-04-Birmingham	\
	2019-07-Columbus

all clean: build_UniMath
	for w in $(WORKSHOPS) ; do $(MAKE) -C $$w $@ || exit 1 ; done

