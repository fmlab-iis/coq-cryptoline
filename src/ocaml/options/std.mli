
type sat_solver = Cryptominisat | Cadical | Glucose

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

val default_solver : sat_solver
val default_algebra : algebra_system

val wordsize : int ref

val boolector_path : string ref
val z3_path : string ref
val mathsat_path : string ref
val stp_path : string ref

val minisat_path : string ref
val cryptominisat_path : string ref
val cadical_path : string ref
val glucose_path : string ref

val sat_solver : sat_solver ref
val sat_args : string ref
val string_of_sat_solver : sat_solver -> string

val use_btor : bool ref

val singular_path : string ref
val sage_path : string ref
val magma_path : string ref
val mathematica_path : string ref
val macaulay2_path : string ref

val algebra_system : algebra_system ref
val algebra_args : string ref
val string_of_algebra_system : algebra_system -> string

val apply_rewriting : bool ref
val polys_rewrite_replace_eexp : bool ref
val apply_slicing : bool ref

val variable_ordering : variable_order ref
val string_of_variable_ordering : variable_order -> string
val parse_variable_ordering : string -> variable_order

val verify_program_safety : bool ref
val verify_epost : bool ref
val verify_rpost : bool ref
val verify_eassertion : bool ref
val verify_rassertion : bool ref
val verify_ecuts : (int list) option ref
val verify_rcuts : (int list) option ref
val incremental_safety : bool ref
val incremental_safety_timeout : int ref

val carry_constraint : bool ref

val verbose : bool ref

val unix : string -> Unix.process_status

val logfile : string ref

val trace : string -> unit
val trace_file : string -> unit

val fail : string -> 'a

val string_of_running_time : float -> float -> string

val vprint : string -> unit
val vprintln : string -> unit

val jobs : int ref

val use_cli : bool ref
val cli_path : string ref

(* Rename local variables when inlining a call to a procedure. *)
val rename_local : bool ref

val use_legacy_parser : bool ref
val use_untyped_parser : bool ref
val use_vector_parser : bool ref

val auto_cast : bool ref
val auto_cast_preserve_value : bool ref
val typing_file : (string option) ref
val use_binary_repr : bool ref

type sat_certificate = Drat | Lrat | Grat
val string_of_sat_certificate : sat_certificate -> string
val default_sat_certificate : sat_certificate
val sat_certificate : sat_certificate ref
val drat_trim_path : string ref
val gratgen_path : string ref
val gratchk_path : string ref
val lrat_checker_path : string ref
