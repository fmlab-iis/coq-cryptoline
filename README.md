CoqCryptoLine
=============

*CoqCryptoLine* is a certified tool for the verification of low-level
implementations of mathematical constructs.


Installation
============

To compile the Coq proofs of CoqCryptoLine, the following packages
are required.

* [Coq](https://coq.inria.fr) (>= 8.11.0)
* [MathComp](https://github.com/math-comp/math-comp) (>= 1.10.0)

To compile the extracted certified OCaml code, the following packages
are required.

* [OCaml](https://ocaml.org) (>= 4.08.1)
* [Dune](https://dune.build) (>= 2.1.3)
* [Zarith](https://github.com/ocaml/Zarith) (>= 1.9.1)
* [Lwt](https://ocsigen.org/lwt/latest/manual/manual)

To run CoqCryptoLine, the following tool is required.

* [Singular](https://www.singular.uni-kl.de/)
* [kissat](http://fmv.jku.at/kissat/)
* [gratgen](https://www21.in.tum.de/~lammich/grat/) and
  [gratchk](https://www21.in.tum.de/~lammich/grat/)

Make sure that the tool is installed and can be found in the PATH
environment variable.


On Ubuntu
---------

On Ubuntu 20.04 LTS, the packages for compilation can be installed by the
following command.

    $ sudo apt install ocaml ocaml-dune libzarith-ocaml-dev
                       coq libssreflect-coq liblwt-ocaml-dev

The script *setup-ubuntu* can be used to install all required packages
and external tools on Ubuntu 20.04.


With OPAM
---------

The packages for compilation can also be installed via
[opam](http://opam.ocaml.org).

    $ opam switch create ocaml-base-compiler.4.08.1
    $ eval $(opam env)
    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam install dune zarith lwt lwt_ppx
    $ opam pin coq 8.11.0
    $ opam pin coq-mathcomp-ssreflect 1.10.0
    $ opam install coq-mathcomp-algebra

Some system dependencies such as libgmp-dev on Ubuntu 20.04 may need to be
installed before installing opam packages.


Compilation
-----------

Run the following commands in the root directory of the CoqCryptoLine
project to compile the Coq proofs

    $ git submodule update --init --recursive
    $ make all

Run the following command in the directory src/ocaml to compile the
extracted certified OCaml code.

    $ dune build

The binary coqcryptoline.exe of CoqCryptoLine can be found in
src/ocaml/_build/default.



USAGE
=====

$ _build/default/coqcryptoline.exe [ ARGS ] FILE


ARGUMENTS
---------

    -algebra_args ARGS     Specify additional arguments passed to the
                           algebra solver
    -cadical PATH          Use Cadical at the specified path
    -cryptominisat PATH    Use Cryptominisat at the specified path
    -debug                 Log debug messages
    -disable_rewriting     Disable rewriting of equalities
    -disable_vars_cache_in_rewriting
                           Disable variables cache in rewriting
    -drat-trim             Set the path to drat-trim (default: drat-trim)
    -fork                  Use fork instead of lwt if the number of jobs is
                           greater than 1
    -glucose PATH          Use Glucose at the specified path
    -gratchk PATH          Set the path to gratchk (default: gratchk)
    -gratgen PATH          Set the path to gratgen (default: gratgen)
    -jobs N                Set number of jobs (default = 4)
    -keep                  Keep temporary files
    -kissat PATH           Use Kissat at the specified path
    -lrat PATH             Set the path to lrat-checker
                           (default: Interface.native)
    -no_carry_constraint   Do not add carry constraints
    -o FILE                Save log messages to the specified file (default
                           is cryptoline.log)
    -p                     Print the parsed specification
    -sat_args ARGS         Specify additional arguments passed to the SAT
                           solver
    -sat_cert {drat|grat|lrat}
                           Specify the UNSAT proof certifier (the default is
                           grat)
    -sat_solver {cryptominisat|cadical|glucose|kissat}
                           Specify the SAT solver (the default is kissat)
    -singular PATH         Use Singular at the specified path
    -tmpdir PATH           Specify a directory for temporary files
    -v                     Display verbose messages
    -vo {lex|appearing|rev_lex|rev_appearing}
                           Set variable ordering in algebra solver (default
                           is rev_appearing)
    -help                  Display this list of options
    --help                 Display this list of options


OCAMLRUNPARAM
-------------

It is important to allocate enough space of the minor heap
to achieve better performance. To specify the size of the minor
heap, run _build/default/coqcryptoline.exe with the following
prefix:

    OCAMLRUNPARAM=s=X

where X is the size. For example, using the command

    $ OCAMLRUNPARAM=s=2G _build/default/coqcryptoline.exe fe25519_mul.cl

to verify fe25519_mul.cl is much faster than using the command

    $ _build/default/coqcryptoline.exe fe25519_mul.cl


EXAMPLE
-------

    $ OCAMLRUNPARAM=s=2G \
        ./_build/default/coqcryptoline.exe -v -jobs 16 \
        -sat_solver kissat -sat_cert grat \
        -no_carry_constraint -tmpdir .

