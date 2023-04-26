
open Arg
open Options.Std
open Typecheck.Std
open Parsers.Std
open Ast.Cryptoline
open Utils.Std

let mk_arg_desc lines = (String.concat "\n\t     " lines) ^ "\n"

let args_parsing =
  [
    ("-rename_local", Set rename_local, mk_arg_desc([""; "Rename local variables when inlining a call to a procedure."]))
  ]

let args_io =
  [
    ("-debug", Set Options.Std.debug, mk_arg_desc(["    Log debug messages"]));
    ("-keep", Set keep_temp_files, mk_arg_desc(["     Keep temporary files."]));
    ("-o", String (fun str -> logfile := str), mk_arg_desc(["FILE    Save log messages to the specified file (default is"; !logfile ^ ")."]));
    ("-tmpdir", String (fun str -> tmpdir := Some str), mk_arg_desc(["PATH"; "Specify a directory for temporary files."]));
    ("-v", Set verbose, mk_arg_desc(["\t     Display verbose messages."]))
  ]

(* Do not use -c or -instr below. *)
let args_verifier =
  [
    ("-algebra_args", String (fun str -> algebra_solver_args := str),
     mk_arg_desc(["ARGS"; "Specify additional arguments passed to the algebra solver."]));
    ("-no_carry_constraint", Clear carry_constraint, mk_arg_desc([""; "Do not add carry constraints."]));
    ("-singular", String (fun str -> singular_path := str; algebra_solver := Singular),
     mk_arg_desc(["PATH"; "Use Singular at the specified path."]));
    ("-singular_path", String (fun str -> singular_path := str),
     mk_arg_desc(["PATH"; "Set the path to Singular."]));
    ("-slicing", Set apply_slicing, mk_arg_desc(["  Enable slicing."]));
    ("-vo", Symbol (["lex"; "appearing"; "rev_lex"; "rev_appearing"],
                    (fun str ->
                      try
                        variable_ordering := parse_variable_ordering str
                      with Not_found ->
                        failwith ("Unknown variable ordering: " ^ str))),
     mk_arg_desc([""; "Set variable ordering in algebra solver (default is " ^ string_of_variable_ordering !variable_ordering ^ ")."]))
  ]

(* REDEFINED FOR COQCRYPTOLINE *)
(*
let parse_and_check file =
  let parse_spec file =
    let t1 = Unix.gettimeofday() in
    let _ = vprint ("Parsing CryptoLine file:\t\t") in
    try
      let spec = spec_from_file file in
      let t2 = Unix.gettimeofday() in
      let _ = vprintln ("[OK]\t\t" ^ string_of_running_time t1 t2) in
      spec
    with ex ->
      let t2 = Unix.gettimeofday() in
      let _ = vprintln ("[FAILED]\t" ^ string_of_running_time t1 t2) in
      raise ex in
  let check_well_formedness vs s =
    let t1 = Unix.gettimeofday() in
    let _ = vprint ("Checking well-formedness:\t\t") in
    let ropt = illformed_spec_reason vs s in
    let wf = ropt = None in
    let t2 = Unix.gettimeofday() in
    let _ = vprintln ((if wf then "[OK]\t" else "[FAILED]") ^ "\t" ^ string_of_running_time t1 t2) in
    let _ =
      match ropt with
      | Some (IllPrecondition e, r) -> vprintln("Ill-formed precondition: " ^ string_of_bexp e ^ ".\nReason: " ^ r)
      | Some (IllInstruction i, r) -> vprintln("Ill-formed instruction: " ^ string_of_instr i ^ ".\nReason: " ^ r)
      | Some (IllPostcondition e, r) -> vprintln("Ill-formed postcondition: " ^ string_of_bexp_prove_with e ^ ".\nReason: " ^ r)
      | _ -> () in
    wf in
  let (vs, s) = parse_spec file in
  if check_well_formedness (VS.of_list vs) s then (vs, from_typecheck_spec s)
  else if not !verbose then failwith ("The program is not well-formed. Run again with \"-v\" to see the detailed error.")
  else exit 1
 *)

let find_output_vars p vnames =
  let p = List.rev p in
  let rec find_output_var p vname =
    match p with
    | [] -> failwith("Output variable '" ^ vname ^ "' is not found.")
    | hd::tl -> let vs = lvs_instr hd in
                (try
                   VS.filter (fun v -> v.vname = vname) vs |> VS.min_elt
                 with Not_found ->
                   find_output_var tl vname) in
  tmap (find_output_var p) vnames




(* ADDED FOR COQCRYPTOLINE *)

let args_coqcryptoline =
  [
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
    ("-disable_rewriting", Unit (fun () -> apply_rewriting_arep := false; apply_rewriting_imp := false), "\n\t     Disable rewriting of equalities\n");
    ("-enable_rewriting_arep", Set apply_rewriting_arep, "\n\t     Enable rewriting of equalities in root entailment problems\n");
    ("-disable_rewriting_arep", Clear apply_rewriting_arep, "\n\t     Enable rewriting of equalities in root entailment problems\n");
    ("-enable_rewriting_imp", Set apply_rewriting_imp, "\n\t     Disable rewriting of equalities in ideal membership problems\n");
    ("-disable_rewriting_imp", Clear apply_rewriting_imp, "\n\t     Disable rewriting of equalities in ideal membership problems\n");
    ("-enable_slicing_espec", Set apply_slicing_espec, "\n\t     Enable slicing in the verification of algebraic specifications\n");
    ("-enable_slicing_rspec", Set apply_slicing_rspec, "\n\t     Enable slicing in the verification of range specifications\n");
    ("-enable_slicing_assume", Set apply_slicing_assume, "\n\t     Enable slicing predicates in assume statements. Use with\n\t     -enable_slicing_espec or -enable_slicing_rspec.\n");
    ("-disable_slicing_espec", Clear apply_slicing_espec, "\n\t     Disable slicing in the verification of algebraic specifications\n");
    ("-disable_slicing_rspec", Clear apply_slicing_rspec, "\n\t     Disable slicing in the verification of range specifications\n");
    ("-disable_slicing_assume", Clear apply_slicing_assume, "\n\t     Disable slicing predicates in assume statements\n");
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
    ("-kissat", String (fun str -> kissat_path := str; sat_solver := Kissat), "PATH\n\t     Use Kissat at the specified path\n");
    ("-lrat", String (fun str -> Options.Std.lrat_checker_path := str),
     "     Set the path to lrat-checker (default: " ^ !Options.Std.lrat_checker_path ^ ")\n");
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
     "\n\t     Specify the SAT solver (the default is " ^ Options.Std.string_of_sat_solver Options.Std.default_sat_solver ^ ")\n")
  ]


(* Redefine parse_and_check. Check well-formedness using the extracted CoqCryptoLine code. *)
let parse_and_check file =
  let parse_spec file =
    let t1 = Unix.gettimeofday() in
    let _ = vprint ("Parsing CryptoLine file:\t\t") in
    try
      let spec = spec_from_file file in
      let t2 = Unix.gettimeofday() in
      let _ = vprintln ("[OK]\t\t" ^ string_of_running_time t1 t2) in
      spec
    with ex ->
      let t2 = Unix.gettimeofday() in
      let _ = vprintln ("[FAILED]\t" ^ string_of_running_time t1 t2) in
      raise ex in
  let (vs, s) = parse_spec file in
  (vs, from_typecheck_spec s)
