
open Utils

exception UnknownAlgebraSolver of string

let debug = ref false

type algebra_solver =
  | Singular
  | Sage
  | Magma
  | Mathematica
  | Macaulay2
  | Maple
  | SMTSolver of string

type variable_order =
  | LexOrder
  | AppearingOrder
  | RevLexOrder
  | RevAppearingOrder

let default_range_solver = "boolector"

let default_algebra_solver = Singular

let range_solver = ref default_range_solver

let range_solver_args = ref ""

let use_btor = ref false

let singular_path = ref "Singular"
let sage_path = ref "sage"
let magma_path = ref "magma"
let mathematica_path = ref "wolframscript"
let macaulay2_path = ref "M2"
let maple_path = ref "maple"

let algebra_solver = ref default_algebra_solver
let algebra_solver_args = ref ""
let string_of_algebra_solver s =
  match s with
  | Singular -> "singular"
  | Magma -> "magma"
  | Sage -> "sage"
  | Mathematica -> "mathematica"
  | Macaulay2 -> "macaulay2"
  | Maple -> "maple"
  | SMTSolver solver -> "smt:\"" ^ solver ^ "\""
let parse_algebra_solver str =
  if str = string_of_algebra_solver Singular then Singular
  else if str = string_of_algebra_solver Sage then Sage
  else if str = string_of_algebra_solver Magma then Magma
  else if str = string_of_algebra_solver Mathematica then Mathematica
  else if str = string_of_algebra_solver Macaulay2 then Macaulay2
  else if str = string_of_algebra_solver Maple then Maple
  else if Str.string_match (Str.regexp "^smt:\\(.*\\)") str 0 then SMTSolver (Str.matched_group 1 str)
  else raise (UnknownAlgebraSolver ("Unknown algebra solver: " ^ str))

let apply_rewriting = ref true
(* let polys_rewrite_replace_eexp = ref false *)  (* REMOVED FOR COQCRYPTOLINE *)
let apply_slicing = ref false

let variable_ordering = ref RevAppearingOrder
let string_of_variable_ordering o =
  match o with
  | LexOrder -> "lex"
  | AppearingOrder -> "appearing"
  | RevLexOrder -> "rev_lex"
  | RevAppearingOrder -> "rev_appearing"
let parse_variable_ordering str =
  if str = "lex" then LexOrder
  else if str = "appearing" then AppearingOrder
  else if str = "rev_lex" then RevLexOrder
  else if str = "rev_appearing" then RevAppearingOrder
  else raise Not_found

let verify_program_safety = ref true
let verify_epost = ref true
let verify_rpost = ref true
let verify_eassertion = ref true
let verify_rassertion = ref true
let verify_ecuts = ref None
let verify_rcuts = ref None
let verify_eacuts = ref None
let verify_racuts = ref None
let verify_scuts = ref None
let verify_eassert_ids = ref None
let verify_rassert_ids = ref None
let verify_safety_ids = ref None
let mem_hashset_opt so e =
  match so with
  | None -> true
  | Some s -> Hashset.mem s e
let incremental_safety = ref false
let incremental_safety_timeout = ref 300

let carry_constraint = ref true

let verbose = ref false

(* MODIFIED FOR COQCRYPTOLINE *)
let unix cmd =
  let r = Unix.system cmd in
  if r = r then r
  else r

let logfile = ref "cryptoline.log"

let trace ?log:(lf=(!logfile)) msg =
  if !debug then
    let ch = open_out_gen [Open_append; Open_creat; Open_text] 0o640 lf in
    let _ = output_string ch msg in
    let _ = output_string ch "\n" in
    let _ = close_out ch in
    ()

let trace_file ?log:(lf=(!logfile)) file =
  if !debug then
    ignore(unix ("cat " ^ file ^ " >>  " ^ lf))

let fail s = trace s; failwith s

let string_of_running_time st ed = (Printf.sprintf "%f" (ed -. st)) ^ " seconds"

let vprint msg = if !verbose then print_string msg; flush stdout

let vprintln msg = if !verbose then print_endline msg; flush stdout

let jobs = ref 4

let use_cli = ref false

let cli_path = ref "cv_cli"

let rename_local = ref false

let auto_cast = ref false
let auto_cast_preserve_value = ref false
let use_binary_repr = ref false

let keep_temp_files = ref false
let tmpdir = ref None
let tmpfile prefix suffix =
  match !tmpdir with
  | None -> Filename.temp_file prefix suffix
  | Some dir -> Filename.temp_file ~temp_dir:dir prefix suffix
let cleanup files =
  if not !keep_temp_files then List.iter Unix.unlink files

let cryptoline_filename_extension = ".cl"

let native_smtlib_expn_operator = ref None

let two_phase_rewriting = ref false

let abc_path = ref "abc"
let boolector_path = ref "boolector"

let track_split = ref false

let expand_poly = ref false



(* ADDED FOR COQCRYPTOLINE *)

type sat_solver = Cryptominisat | Cadical | Glucose | Kissat

let default_sat_solver = Kissat

let apply_rewriting_arep = ref true
let apply_rewriting_imp = ref true
let polys_rewrite_replace_eexp = ref false
let apply_slicing_espec = ref true
let apply_slicing_rspec = ref true
let apply_slicing_assume = ref true

let minisat_path = ref "minisat"
let cryptominisat_path = ref "cryptominisat5_simple"
let cadical_path = ref "cadical"
let glucose_path = ref "glucose"
let kissat_path = ref "kissat"

let sat_solver = ref default_sat_solver
let sat_args = ref ""
let string_of_sat_solver s =
  match s with
  | Cryptominisat -> "cryptominisat"
  | Cadical -> "cadical"
  | Glucose -> "glucose"
  | Kissat -> "kissat"

type unsat_certifier = Drat | Lrat | Grat
let string_of_unsat_certifier c =
  match c with
  | Drat -> "drat"
  | Lrat -> "lrat"
  | Grat -> "grat"
let default_unsat_certifier = Grat
let unsat_certifier = ref default_unsat_certifier
let drat_trim_path = ref "drat-trim"
let gratgen_path = ref "gratgen"
let gratchk_path = ref "gratchk"
(*let lrat_checker_path = ref "PracticalInterface"*)
let lrat_checker_path = ref "Interface.native"

let disable_range = ref false
