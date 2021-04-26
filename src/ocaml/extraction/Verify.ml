open BinNums
open CNF
open Options0
open Poly
open QFBV2CNF
open QFBVHash
open Ring_polynom
open SSA2ZSSA
open Seq

(** val ext_all_unsat : cnf list -> bool **)

let ext_all_unsat = External.ext_all_unsat_impl

(** val verify_rspec_safety : SSA.SSA.spec -> bool **)

let verify_rspec_safety s =
  let fE = SSA.SSA.program_succ_typenv (SSA.SSA.sprog s) (SSA.SSA.sinputs s)
  in
  let es = bb_range_safety_la_simplified_filtered s in
  let (_, cnfs) = bb_hbexps_cache fE (map (Obj.magic hash_bexp) es) in
  ext_all_unsat cnfs

(** val ext_find_coefficients :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z
    coq_PExpr list * coq_Z coq_PExpr **)

let ext_find_coefficients = External.ext_find_coefficients_impl

(** val verify_pspecs : pspec list -> bool **)

let rec verify_pspecs = function
| [] -> true
| ps :: pss0 ->
  let (p, q) = zpexprs_of_pspec ps in
  let (p0, m) = p in
  let (_, ps0) = p0 in
  let (cs, c) = ext_find_coefficients ps0 q m in
  if coefficients_checker_tr ps0 m q cs c then verify_pspecs pss0 else false

(** val verify_zspec : options -> ZSSA.ZSSA.zspec -> bool **)

let verify_zspec o zs =
  if o.rewrite_assignments
  then verify_pspecs (pspecs_of_zspec_simplified o zs)
  else verify_pspecs (pspecs_of_zspec zs)

(** val verify_ssa : options -> SSA.SSA.spec -> bool **)

let verify_ssa o s =
  (&&) (verify_rspec_safety s)
    (verify_zspec o
      (bv2z_espec o (new_svar_spec s) (SSA.SSA.espec_of_spec s)))

(** val verify_dsl : options -> DSL.DSL.spec -> bool **)

let verify_dsl o s =
  verify_ssa o (SSA.ssa_spec s)
