all:

build_UniMath:
	$(MAKE) -C UniMath TAGS all

WORKSHOPS = 2017-12-Birmingham

all clean: build_UniMath
	for w in $(WORKSHOPS) ; do $(MAKE) -C $$w $@ || exit 1 ; done

