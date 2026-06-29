WHY3-PY
====

Why3-py is a modified version of the Why3 verification platform developed for StatWhy.
It supports the execution and verification of statistical Python programs.

The original Why3 project is available at:
https://www.why3.org/

Author
------

Akira Tanaka and Yusuke Kawamoto at National Institute of Advanced Industrial Science and Technology (AIST)

Installation
------------

Why3-py installs its dependencies (Python, mypy, etc.) into a dedicated directory. It also creates a dedicated opam switch.
In the last command, `./statwhy-install.sh $HOME/statwhy statwhy`, `$HOME/statwhy` specifies the installation directory and `statwhy` specifies the name of the opam switch.

This software is tested with Debian GNU/Linux 13 (trixie).

```
% sudo apt-get install \
  opam \
  wget \
  git \
  rsync \
  ca-certificates \
  build-essential \
  libsqlite3-dev \
  libssl-dev \
  pkgconf \
  autoconf \
  cvc5 \
  libgmp-dev \
  libcairo2-dev \
  libgtk-3-dev \
  libgtksourceview-3.0-dev
% git clone https://github.com/fm4stats/why3-py.git
% cd why3-py
% ./statwhy-install.sh $HOME/statwhy statwhy
% eval $(opam env)
```

Example
-------

After installation, examples can be run as follows.
(`env-why3` and `statwhy-py` must be executed from the Why3-py source directory.)

```
% ./env-why3 python3 examples/statwhy-python/example0_meta_pv.py
eg_meta_pvs_fisher p-value : 0.115216
```

Verification can be started with the `./statwhy-py` command.
This starts the IDE of Why3.

```
% ./statwhy-py examples/statwhy-python/example0_meta_pv.py
```

![](./doc-statwhy/figures/why3-py-start.png?raw=true "The Why3 IDE screen at start.")

Verification in Why3-py (and StatWhy) is performed by selecting the `StatWhy` item from the context menu of the root node in the left pane.
The context menu is shown by Right-Click at the root node (shown as question mark and "example0\_meta\_pv.py").

All descendants are folded, and the question mark changes to a green check mark.
This indicates that the verification has succeeded.

![](./doc-statwhy/figures/why3-py-verified.png?raw=true "The Why3 IDE screen: verification succeed.")

More examples can be found in the `examples/statwhy-python/` directory.

Copyright
---------

The modifications and additions specific to Why3-py are licensed under the GNU LGPL 2.1, the same license as Why3.

See the accompanying LICENSE file for details.

The original README.md of Why3 is follows:
====

WHY3
====

Why3 is a platform for deductive program verification. It provides
a rich language for specification and programming, called WhyML, and
relies on external theorem provers, both automated and interactive,
to discharge verification conditions. Why3 comes with a standard
library of logical theories (integer and real arithmetic, Boolean
operations, sets and maps, etc.) and basic programming data structures
(arrays, queues, hash tables, etc.). A user can write WhyML programs
directly and get correct-by-construction OCaml programs through an
automated extraction mechanism. WhyML is also used as an intermediate
language for the verification of C, Java, or Ada programs.

PROJECT HOME
------------

https://www.why3.org/

https://gitlab.inria.fr/why3/why3

DOCUMENTATION
-------------

The documentation (a tutorial and a reference manual) is
available [online](https://www.why3.org/doc/).

Various examples can be found in the subdirectories [stdlib/](stdlib)
and [examples/](examples).

COPYRIGHT
---------

This program is distributed under the GNU LGPL 2.1. See the enclosed
file [LICENSE](LICENSE).

The files [src/util/extmap.ml{i}](src/util/extmap.mli) are derived from the
sources of OCaml 3.12 standard library, and are distributed under the GNU
LGPL version 2 (see file [OCAML-LICENSE](OCAML-LICENSE)).

Icon sets for the graphical interface of Why3 are subject to specific
licenses, some of them may forbid commercial usage. These specific
licenses are detailed in files [share/images/\*/\*.txt](share/images).

INSTALLATION
------------

See the file [INSTALL.md](INSTALL.md).
