open BinNums
open CNF
open Options0
open Poly
open QFBV2CNF
open QFBVHash
open Ring_polynom
open SSA2ZSSA
open Eqtype
open Seq
open Ssrnat

val ext_all_unsat : cnf list -> bool

val verify_rspec_safety : SSA.SSA.spec -> bool

val ext_find_coefficients :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z
  coq_PExpr list * coq_Z coq_PExpr

val verify_pspec : pspec -> bool

val verify_pspecs : pspec list -> bool

val verify_zspec : options -> ZSSA.ZSSA.zspec -> bool

val ext_find_coefficients_list :
  ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr) list -> (coq_Z
  coq_PExpr list * coq_Z coq_PExpr) list

val polys_of_pspecs :
  pspec list -> ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr)
  list

val coefficients_checker_tr_list :
  ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr) list -> (coq_Z
  coq_PExpr list * coq_Z coq_PExpr) list -> bool

val verify_pspecs_list : pspec list -> bool

val verify_zspec_list : options -> ZSSA.ZSSA.zspec -> bool

val verify_ssa : options -> SSA.SSA.spec -> bool

val verify_dsl : options -> DSL.DSL.spec -> bool
