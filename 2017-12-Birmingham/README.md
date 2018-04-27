create a makefile like so:

```bash
$ coq_makefile -f _CoqProject -o Makefile
```

This creates ```Makefile.conf``` and ```Makefile```.

compile with the makefile:

```bash
$ make clean
$ make
```

Here, we assume that the UniMath library is accessible. For this, we could
either sit within the UniMath library or have already "installed" UniMath inside
Coq (using ```make install``` of the UniMath sources).

Notice that the system issues a lot of warnings about notation conflicts of the UniMath library.

The underlying Coq version is supposed to be at least 8.8.0.

You can also create HTML documentation:
```bash
$ make html
```
places the files into a sister directory ```html```, with entry point ```toc.html```

In particular, the course on tactics (part 4) is supposed to be viewed in the HTML form.