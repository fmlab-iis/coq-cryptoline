
open Arg
open Options.Std

(* Do not use -c or -instr below. *)
let args =
  [
    ("-algebra_args", String (fun str -> algebra_args := str),
     "ARGS\n\t     Specify additional arguments passed to the algebra solver\n");
    ("-sat_cert", Symbol ([Options.Std.string_of_unsat_certifier Options.Std.Drat;
                           Options.Std.string_of_unsat_certifier Options.Std.Grat;
                           Options.Std.string_of_unsat_certifier Options.Std.Lrat],
                          (fun str -> if str = Options.Std.string_of_unsat_certifier Options.Std.Drat then unsat_certifier := Options.Std.Drat
                                      else if str = Options.Std.string_of_unsat_certifier Options.Std.Grat then unsat_certifier := Options.Std.Grat
                                      else if str = Options.Std.string_of_unsat_certifier Options.Std.Lrat then unsat_certifier := Options.Std.Lrat
                                      else failwith ("Unknown format of SAT certification: " ^ str))),
     "\n\t     Specify the UNSAT proof certifier (the default is " ^ Options.Std.string_of_unsat_certifier Options.Std.default_unsat_certifier ^ ").\n");
    ("-cadical", String (fun str -> cadical_path := str; sat_solver := Cadical), "PATH\n\t     Use Cadical at the specified path\n");
    ("-cryptominisat", String (fun str -> cryptominisat_path := str; sat_solver := Cryptominisat), "PATH\n\t     Use Cryptominisat at the specified path\n");
    ("-debug", Set debug, "    Log debug messages\n");
    ("-disable_rewriting", Unit (fun () -> apply_rewriting_arep := false; apply_rewriting_imp := false), "\n\t     Disable rewriting of equalities\n");
    ("-enable_rewriting_arep", Set apply_rewriting_arep, "\n\t     Enable rewriting of equalities in root entailment problems\n");
    ("-disable_rewriting_imp", Clear apply_rewriting_imp, "\n\t     Disable rewriting of equalities in ideal membership problems\n");
    ("-drat-trim", String (fun str -> Options.Std.drat_trim_path := str),
     "Set the path to drat-trim (default: " ^
       !Options.Std.drat_trim_path ^ ")\n");
    ("-fork", Unit (fun () -> Extraction.External.use_fork := true), "     Use fork instead of lwt if the number of jobs is greater than 1\n");
    ("-glucose", String (fun str -> glucose_path := str; sat_solver := Glucose), "PATH\n\t     Use Glucose at the specified path\n");
    ("-gratchk", String (fun str -> Options.Std.gratchk_path := str),
     "  Set the path to gratchk (default: " ^
       !Options.Std.gratchk_path ^ ")\n");
    ("-gratgen", String (fun str -> Options.Std.gratgen_path := str),
     "  Set the path to gratgen (default: " ^
       !Options.Std.gratgen_path ^ ")\n");
    ("-keep", Set Extraction.External.keep_temp_files, "     Keep temporary files\n");
    ("-kissat", String (fun str -> kissat_path := str; sat_solver := Kissat), "PATH\n\t     Use Kissat at the specified path\n");
    ("-lrat", String (fun str -> Options.Std.lrat_checker_path := str),
     "     Set the path to lrat-checker (default: " ^ !Options.Std.lrat_checker_path ^ ")\n");
    ("-no_carry_constraint", Clear carry_constraint, "\n\t     Do not add carry constraints\n");
    ("-o", String (fun str -> logfile := str),
     "FILE    Save log messages to the specified file (default is " ^ !logfile ^ ")\n");
    ("-sat_args", String (fun str -> sat_args := str),
     "ARGS\n\t     Specify additional arguments passed to the SAT solver\n");
    ("-sat_solver", Symbol ([Options.Std.string_of_sat_solver Options.Std.Cryptominisat;
							 Options.Std.string_of_sat_solver Options.Std.Cadical;
							 Options.Std.string_of_sat_solver Options.Std.Glucose;
                             Options.Std.string_of_sat_solver Options.Std.Kissat],
                            (fun str ->
                              if str = Options.Std.string_of_sat_solver Options.Std.Cryptominisat then sat_solver := Cryptominisat
                              else if str = Options.Std.string_of_sat_solver Options.Std.Cadical then sat_solver := Cadical
                              else if str = Options.Std.string_of_sat_solver Options.Std.Glucose then sat_solver := Glucose
                              else if str = Options.Std.string_of_sat_solver Options.Std.Kissat then sat_solver := Kissat
                              else failwith ("Unknown SAT solver: " ^ str))),
     "\n\t     Specify the SAT solver (the default is " ^ Options.Std.string_of_sat_solver Options.Std.default_solver ^ ")\n");
    ("-singular", String (fun str -> singular_path := str; algebra_system := Singular),
     "PATH\n\t     Use Singular at the specified path\n");
    ("-tmpdir", String (fun str -> tmpdir := Some str),
     "PATH\n\t     Specify a directory for temporary files\n");
    ("-vo", Symbol (["lex"; "appearing"; "rev_lex"; "rev_appearing"],
                    (fun str ->
                      try
                        variable_ordering := parse_variable_ordering str
                      with Not_found ->
                        failwith ("Unknown variable ordering: " ^ str))),
     "\n\t     Set variable ordering in algebra solver (default is " ^ string_of_variable_ordering !variable_ordering ^ ")\n")
  ]
