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

(** val verify_rspec_algsnd : SSA.SSA.spec -> bool **)

let verify_rspec_algsnd s =
  let fE = SSA.SSA.program_succ_typenv (SSA.SSA.sprog s) (SSA.SSA.sinputs s)
  in
  let es = bb_range_algsnd_la_simplified_filtered s in
  let (_, cnfs) = bb_hbexps_cache fE (map (Obj.magic hash_bexp) es) in
  ext_all_unsat cnfs

(** val ext_solve_imp :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr list -> coq_Z
    coq_PExpr list * coq_Z coq_PExpr list **)

let ext_solve_imp = External.ext_solve_imp_impl

(** val verify_arep : arep -> bool **)

let verify_arep ps =
  let (p, q) = imp_of_arep ps in
  let (p0, ms) = p in
  let (_, ps0) = p0 in
  let (cps, cms) = ext_solve_imp ps0 q ms in
  validate_imp_answer ps0 ms q cps cms

(** val verify_areps : arep list -> bool **)

let verify_areps pss =
  all verify_arep pss

(** val verify_rep : options -> ZSSA.ZSSA.rep -> bool **)

let verify_rep o zs =
  if o.rewrite_assignments
  then verify_areps (areps_of_rep_simplified o zs)
  else verify_areps (areps_of_rep zs)

(** val ext_solve_imp_list :
    ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr list) list ->
    (coq_Z coq_PExpr list * coq_Z coq_PExpr list) list **)

let ext_solve_imp_list = External.ext_solve_imp_list_impl

(** val polys_of_areps :
    arep list -> ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr
    list) list **)

let polys_of_areps pss =
  let f = fun ps ->
    let (p, q) = imp_of_arep ps in
    let (p0, ms) = p in let (_, ps0) = p0 in ((ps0, q), ms)
  in
  map f pss

(** val validate_imp_answer_list :
    ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr list) list ->
    (coq_Z coq_PExpr list * coq_Z coq_PExpr list) list -> bool **)

let rec validate_imp_answer_list polys coefs =
  match polys with
  | [] -> (match coefs with
           | [] -> true
           | _ :: _ -> false)
  | y :: tlp ->
    let (y0, ms) = y in
    let (ps, q) = y0 in
    (match coefs with
     | [] -> false
     | y1 :: tlc ->
       let (cps, cms) = y1 in
       if validate_imp_answer ps ms q cps cms
       then validate_imp_answer_list tlp tlc
       else false)

(** val verify_areps_list : arep list -> bool **)

let verify_areps_list pss =
  let poly_list = polys_of_areps pss in
  let coef_list = ext_solve_imp_list poly_list in
  if eq_op nat_eqType (Obj.magic size poly_list) (Obj.magic size coef_list)
  then validate_imp_answer_list poly_list coef_list
  else false

(** val verify_rep_list : options -> ZSSA.ZSSA.rep -> bool **)

let verify_rep_list o zs =
  if o.rewrite_assignments
  then verify_areps_list (areps_of_rep_simplified o zs)
  else verify_areps_list (areps_of_rep zs)

(** val verify_espec : options -> SSA.SSA.spec -> bool **)

let verify_espec o s =
  if o.compute_coefficients_one_by_one
  then verify_rep o
         (algred_espec o (new_svar_spec s) (SSA.SSA.espec_of_spec s))
  else verify_rep_list o
         (algred_espec o (new_svar_spec s) (SSA.SSA.espec_of_spec s))

(** val verify_ssa : options -> SSA.SSA.spec -> bool **)

let verify_ssa o s =
  (&&) (verify_rspec_algsnd s) (verify_espec o s)

(** val verify_dsl : options -> DSL.DSL.spec -> bool **)

let verify_dsl o s =
  verify_ssa o (SSA.ssa_spec s)
