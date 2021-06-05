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

(** val verify_pspec : pspec -> bool **)

let verify_pspec ps =
  let (p, q) = zpexprs_of_pspec ps in
  let (p0, m) = p in
  let (_, ps0) = p0 in
  let (cs, c) = ext_find_coefficients ps0 q m in
  coefficients_checker_tr ps0 m q cs c

(** val verify_pspecs : pspec list -> bool **)

let verify_pspecs pss =
  all verify_pspec pss

(** val verify_zspec : options -> ZSSA.ZSSA.zspec -> bool **)

let verify_zspec o zs =
  if o.rewrite_assignments
  then verify_pspecs (pspecs_of_zspec_simplified o zs)
  else verify_pspecs (pspecs_of_zspec zs)

(** val ext_find_coefficients_list :
    ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr) list ->
    (coq_Z coq_PExpr list * coq_Z coq_PExpr) list **)

let ext_find_coefficients_list = External.ext_find_coefficients_list_impl

(** val polys_of_pspecs :
    pspec list -> ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z
    coq_PExpr) list **)

let polys_of_pspecs pss =
  let f = fun ps ->
    let (p, q) = zpexprs_of_pspec ps in
    let (p0, m) = p in let (_, ps0) = p0 in ((ps0, q), m)
  in
  map f pss

(** val coefficients_checker_tr_list :
    ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr) list ->
    (coq_Z coq_PExpr list * coq_Z coq_PExpr) list -> bool **)

let rec coefficients_checker_tr_list polys coefs =
  match polys with
  | [] -> (match coefs with
           | [] -> true
           | _ :: _ -> false)
  | y :: tlp ->
    let (y0, m) = y in
    let (ps, q) = y0 in
    (match coefs with
     | [] -> false
     | y1 :: tlc ->
       let (cs, c) = y1 in
       if coefficients_checker_tr ps m q cs c
       then coefficients_checker_tr_list tlp tlc
       else false)

(** val verify_pspecs_list : pspec list -> bool **)

let verify_pspecs_list pss =
  let poly_list = polys_of_pspecs pss in
  let coef_list = ext_find_coefficients_list poly_list in
  if eq_op nat_eqType (Obj.magic size poly_list) (Obj.magic size coef_list)
  then coefficients_checker_tr_list poly_list coef_list
  else false

(** val verify_zspec_list : options -> ZSSA.ZSSA.zspec -> bool **)

let verify_zspec_list o zs =
  if o.rewrite_assignments
  then verify_pspecs_list (pspecs_of_zspec_simplified o zs)
  else verify_pspecs_list (pspecs_of_zspec zs)

(** val verify_ssa : options -> SSA.SSA.spec -> bool **)

let verify_ssa o s =
  (&&) (verify_rspec_safety s)
    (if o.compute_coefficients_one_by_one
     then verify_zspec o
            (bv2z_espec o (new_svar_spec s) (SSA.SSA.espec_of_spec s))
     else verify_zspec_list o
            (bv2z_espec o (new_svar_spec s) (SSA.SSA.espec_of_spec s)))

(** val verify_dsl : options -> DSL.DSL.spec -> bool **)

let verify_dsl o s =
  verify_ssa o (SSA.ssa_spec s)
