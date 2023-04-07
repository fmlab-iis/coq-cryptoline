open Options0
open QFBV2CNF
open REP
open SSA2QFBV
open SSA2REP
open SSA2SSALite
open Seqs
open VerifyLite
open Seq

(** val rngred_spec :
    options -> SSALite.SSALite.spec -> QFBV.QFBV.bexp list **)

let rngred_spec o s =
  let rs = SSALite.SSALite.rspec_of_spec s in
  Obj.magic filter_not_true
    (simplify_bexps
      (if o.apply_slicing_rspec
       then rngred_rspec_slice_split_la o rs
       else rngred_rspec_split_la rs))

(** val algsnd_spec :
    options -> SSALite.SSALite.spec -> QFBV.QFBV.bexp list **)

let algsnd_spec o s =
  let rs = SSALite.SSALite.rspec_of_spec s in
  Obj.magic filter_not_true
    (simplify_bexps
      (if o.apply_slicing_rspec
       then algsnd_slice_la o rs
       else qfbv_spec_algsnd_la rs))

(** val algred_spec : options -> SSALite.SSALite.spec -> rep list **)

let algred_spec o s =
  let avn = new_svar_spec s in
  let apply_algred = fun s0 -> algred_espec o avn s0 in
  if o.apply_slicing_espec
  then tmap apply_algred
         (tmap (SSALite.SSALite.slice_espec o)
           (SSALite.SSALite.split_espec (SSALite.SSALite.espec_of_spec s)))
  else (apply_algred (SSALite.SSALite.espec_of_spec s)) :: []

(** val verify_ssa : options -> SSA.SSA.spec -> bool **)

let verify_ssa o s =
  let fE = SSA.SSA.program_succ_typenv (SSA.SSA.sprog s) (SSA.SSA.sinputs s)
  in
  let s0 = rewrite_mov s in
  let cuts = SSA.SSA.cut_spec s0 in
  let asserts = tflatten (tmap SSA.SSA.extract_asserts cuts) in
  let asserts_ssa = tmap ssa2lite_spec asserts in
  let nacuts = tmap SSA.SSA.remove_asserts cuts in
  let nacuts_ssa = tmap ssa2lite_spec nacuts in
  let rngconds =
    let sndconds = tflatten (tmap (algsnd_spec o) nacuts_ssa) in
    let rngasserts = tflatten (tmap (rngred_spec o) asserts_ssa) in
    let rngpost = tflatten (tmap (rngred_spec o) nacuts_ssa) in
    catrev (rev sndconds) (catrev (rev rngasserts) rngpost)
  in
  let reps =
    let algasserts = tflatten (tmap (algred_spec o) asserts_ssa) in
    let algpost = tflatten (tmap (algred_spec o) nacuts_ssa) in
    catrev (rev algasserts) algpost
  in
  (&&) (verify_qfbv_bexps fE rngconds) (verify_reps o reps)

(** val verify_dsl : options -> DSL.DSL.spec -> bool **)

let verify_dsl o s =
  verify_ssa o (SSA.ssa_spec s)
