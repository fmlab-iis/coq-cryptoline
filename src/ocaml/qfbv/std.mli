
(** QFBV *)

type result = Common.result

type exp = Common.exp

type bexp = Common.bexp

val string_of_exp : exp -> string
val string_of_bexp : bexp -> string

(** Solver *)

val run_minisat : ?timeout:int -> string -> string -> string -> unit
val run_cryptominisat : ?timeout:int -> string -> string -> string -> unit
val read_minisat_output : string -> result
val read_cryptominisat_output : string -> result

val solve_simp : ?timeout:int -> bexp list -> result
