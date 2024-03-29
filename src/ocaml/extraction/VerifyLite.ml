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

(** val ext_all_unsat : cnf list -> bool **)

let ext_all_unsat = External.ext_all_unsat_impl

(** val ext_solve_imp :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr list -> coq_Z
    coq_PExpr list * coq_Z coq_PExpr list **)

let ext_solve_imp = External.ext_solve_imp_impl

(** val ext_solve_imp_list :
    ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z coq_PExpr list) list ->
    (coq_Z coq_PExpr list * coq_Z coq_PExpr list) list **)

let ext_solve_imp_list = External.ext_solve_imp_list_impl

(** val verify_qfbv_bexps :
    TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> bool **)

let verify_qfbv_bexps fE es =
  let (_, cnfs) = bb_hbexps_cache fE (tmap hash_bexp es) in ext_all_unsat cnfs

(** val verify_rspec_algsnd : options -> SSALite.SSALite.spec -> bool **)

let verify_rspec_algsnd o s =
  let rs = SSALite.SSALite.rspec_of_spec s in
  let fE =
    SSALite.SSALite.program_succ_typenv (SSALite.SSALite.rsprog rs)
      (SSALite.SSALite.rsinputs rs)
  in
  let es = bb_rngred_algsnd o rs in verify_qfbv_bexps fE es

(** val polys_of_arep :
    options -> arep -> (coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z
    coq_PExpr list **)

let polys_of_arep o ps =
  let (p, q) = imp_of_arep ps in
  let (p0, ms) = p in
  let (_, ps0) = p0 in
  ((if o.rewrite_assignments_imp
    then if o.vars_cache_in_rewrite_assignments
         then simplify_generator_vars_cache ps0 q
         else simplify_generator ps0 q
    else (ps0, q)), ms)

(** val verify_arep : options -> arep -> bool **)

let verify_arep o ps =
  let (p, ms) = polys_of_arep o ps in
  let (ps', q') = p in
  let (cps, cms) = ext_solve_imp ps' q' ms in
  validate_imp_answer ps' ms q' cps cms

(** val verify_areps : options -> arep list -> bool **)

let verify_areps o pss =
  all (verify_arep o) pss

(** val polys_of_areps :
    options -> arep list -> ((coq_Z coq_PExpr list * coq_Z coq_PExpr) * coq_Z
    coq_PExpr list) list **)

let polys_of_areps o pss =
  tmap (polys_of_arep o) pss

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

(** val verify_areps_list : options -> arep list -> bool **)

let verify_areps_list o pss =
  let poly_list = polys_of_areps o pss in
  let coef_list = ext_solve_imp_list poly_list in
  if eq_op nat_eqType (Obj.magic size poly_list) (Obj.magic size coef_list)
  then validate_imp_answer_list poly_list coef_list
  else false

(** val verify_rep : options -> rep -> bool **)

let verify_rep o zs =
  if o.rewrite_assignments_arep
  then verify_areps o (areps_of_rep_simplified o zs)
  else verify_areps o (areps_of_rep zs)

(** val verify_reps_seq : options -> rep list -> bool **)

let verify_reps_seq o zss =
  all (verify_rep o) zss

(** val verify_reps_paral : options -> rep list -> bool **)

let verify_reps_paral o zss =
  if o.rewrite_assignments_arep
  then verify_areps_list o (tflatten (tmap (areps_of_rep_simplified o) zss))
  else verify_areps_list o (tflatten (tmap areps_of_rep zss))

(** val verify_reps : options -> rep list -> bool **)

let verify_reps o reps =
  if o.compute_coefficients_one_by_one
  then verify_reps_seq o reps
  else verify_reps_paral o reps

(** val verify_rep1 : options -> rep -> bool **)

let verify_rep1 o rep0 =
  if o.compute_coefficients_one_by_one
  then verify_rep o rep0
  else verify_reps_paral o (rep0 :: [])

(** val verify_espec : options -> SSALite.SSALite.spec -> bool **)

let verify_espec o s =
  let avn = new_svar_spec s in
  let apply_algred = fun s0 -> algred_espec o avn s0 in
  if o.apply_slicing_espec
  then let reps =
         tmap apply_algred
           (tmap (SSALite.SSALite.slice_espec o)
             (SSALite.SSALite.split_espec (SSALite.SSALite.espec_of_spec s)))
       in
       verify_reps o reps
  else let rep0 = apply_algred (SSALite.SSALite.espec_of_spec s) in
       verify_rep1 o rep0

(** val verify_ssalite : options -> SSALite.SSALite.spec -> bool **)

let verify_ssalite o s =
  (&&) (verify_rspec_algsnd o s) (verify_espec o s)

(** val verify_dsllite : options -> DSLLite.DSLLite.spec -> bool **)

let verify_dsllite o s =
  verify_ssalite o (SSALite.ssa_spec s)
