create a makefile like so:

coq_makefile -f _CoqProject -o Makefile

This creates Makefile.conf and Makefile

compile with the makefile:

make clean
make

Here, we assume that the UniMath library is accessible. For this, we could
either sit within the UniMath library or have already "installed" UniMath inside
Coq (using make install of the UniMath sources).

Notice that the system issues a lot of warnings about notation conflicts of the UniMath library.
