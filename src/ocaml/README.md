COMPILE
=======

$ dune build


RUN
====

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


EXTERNAL TOOLS
--------------

* SAT solvers
  * kissat: http://fmv.jku.at/kissat/
  * cadical: http://fmv.jku.at/cadical/
  * cryptominisat: https://github.com/msoos/cryptominisat
  * glucose: https://www.labri.fr/perso/lsimon/glucose/
* SAT solver certifiers
  * drat: http://www.cs.utexas.edu/~marijn/drat-trim/
  * grat: https://www21.in.tum.de/~lammich/grat/
  * lrat: https://github.com/acl2/acl2/tree/master/books/projects/sat/lrat/
* Computer algebra systems
  * singular: https://www.singular.uni-kl.de
