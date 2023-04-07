open BinNums
open CNF
open IMP
open Options0
open QFBV2CNF
open QFBVHash
open REP
open Ring_polynom
open SSA2REP
open Seqs
open Eqtype
open Seq
open Ssrnat

val ext_all_unsat : cnf list -> bool

val ext_solve_imp :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr list -> coq_Z
  coq_PExpr list * coq_Z coq_PExpr list

val ext_solve_imp_list :
  ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr list) list ->
  (coq_Z coq_PExpr list * coq_Z coq_PExpr list) list

val verify_qfbv_bexps : TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> bool

val verify_rspec_algsnd : options -> SSALite.SSALite.spec -> bool

val polys_of_arep :
  options -> arep -> (coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z
  coq_PExpr list

val verify_arep : options -> arep -> bool

val verify_areps : options -> arep list -> bool

val polys_of_areps :
  options -> arep list -> ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z
  coq_PExpr list) list

val validate_imp_answer_list :
  ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr list) list ->
  (coq_Z coq_PExpr list * coq_Z coq_PExpr list) list -> bool

val verify_areps_list : options -> arep list -> bool

val verify_rep : options -> rep -> bool

val verify_reps_seq : options -> rep list -> bool

val verify_reps_paral : options -> rep list -> bool

val verify_reps : options -> rep list -> bool

val verify_rep1 : options -> rep -> bool

val verify_espec : options -> SSALite.SSALite.spec -> bool

val verify_ssalite : options -> SSALite.SSALite.spec -> bool

val verify_dsllite : options -> DSLLite.DSLLite.spec -> bool
