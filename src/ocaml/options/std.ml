
type sat_solver = Cryptominisat | Cadical | Glucose | Kissat

type algebra_system =
  | Singular
  | Sage
  | Magma
  | Mathematica
  | Macaulay2

type variable_order =
  | LexOrder
  | AppearingOrder
  | RevLexOrder
  | RevAppearingOrder

let default_solver = Kissat

let default_algebra = Singular

let wordsize = ref 64

let z3_path = ref "z3"
let boolector_path = ref "boolector"
let mathsat_path = ref "mathsat"
let stp_path = ref "stp"

let minisat_path = ref "minisat"
let cryptominisat_path = ref "cryptominisat5_simple"
let cadical_path = ref "cadical"
let glucose_path = ref "glucose"
let kissat_path = ref "kissat"

let sat_solver = ref default_solver
let sat_args = ref ""
let string_of_sat_solver s =
  match s with
  | Cryptominisat -> "cryptominisat"
  | Cadical -> "cadical"
  | Glucose -> "glucose"
  | Kissat -> "kissat"

let use_btor = ref false

let singular_path = ref "Singular"
let sage_path = ref "sage"
let magma_path = ref "magma"
let mathematica_path = ref "wolframscript"
let macaulay2_path = ref "M2"

let algebra_system = ref default_algebra
let algebra_args = ref ""
let string_of_algebra_system s =
  match s with
  | Singular -> "singular"
  | Magma -> "magma"
  | Sage -> "sage"
  | Mathematica -> "mathematica"
  | Macaulay2 -> "macaulay2"

let apply_rewriting_arep = ref false
let apply_rewriting_imp = ref true
let polys_rewrite_replace_eexp = ref false
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
let incremental_safety = ref false
let incremental_safety_timeout = ref 300

let carry_constraint = ref true

let verbose = ref false

let unix cmd =
  let r = Unix.system cmd in
  if r = r then r
  else r

let logfile = ref "cryptoline.log"

let debug = ref false

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

let use_vector_parser = ref false

let auto_cast = ref false
let auto_cast_preserve_value = ref false
let typing_file = ref None
let use_binary_repr = ref false


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

let tmpdir = ref None
let tmpfile prefix suffix =
  match !tmpdir with
  | None -> Filename.temp_file prefix suffix
  | Some dir -> Filename.temp_file ~temp_dir:dir prefix suffix

let disable_range = ref false
