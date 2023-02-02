open Options0
open QFBV2CNF
open QFBVHash
open SSA2QFBV
open SSA2ZSSA
open SSAFull2SSA
open Seqs
open Verify
open Seq

(** val verify_qfbv_bexps :
    TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> bool **)

let verify_qfbv_bexps fE es =
  let (_, cnfs) = bb_hbexps_cache fE (tmap hash_bexp es) in ext_all_unsat cnfs

(** val verify_reps : options -> ZSSA.ZSSA.rep list -> bool **)

let verify_reps o reps =
  if o.compute_coefficients_one_by_one
  then verify_reps_seq o reps
  else verify_reps_paral o reps

(** val rngred_spec : options -> SSA.SSA.spec -> QFBV.QFBV.bexp list **)

let rngred_spec o s =
  let rs = SSA.SSA.rspec_of_spec s in
  Obj.magic filter_not_true
    (simplify_bexps
      (if o.apply_slicing_rspec
       then rngred_rspec_slice_split_la o rs
       else rngred_rspec_split_la rs))

(** val algsnd_spec : options -> SSA.SSA.spec -> QFBV.QFBV.bexp list **)

let algsnd_spec o s =
  let rs = SSA.SSA.rspec_of_spec s in
  Obj.magic filter_not_true
    (simplify_bexps
      (if o.apply_slicing_rspec
       then algsnd_slice_la o rs
       else qfbv_spec_algsnd_la rs))

(** val algred_spec : options -> SSA.SSA.spec -> ZSSA.ZSSA.rep list **)

let algred_spec o s =
  let avn = new_svar_spec s in
  let apply_algred = fun s0 -> algred_espec o avn s0 in
  if o.apply_slicing_espec
  then tmap apply_algred
         (tmap (SSA.SSA.slice_espec o)
           (SSA.SSA.split_espec (SSA.SSA.espec_of_spec s)))
  else (apply_algred (SSA.SSA.espec_of_spec s)) :: []

(** val verify_fullssa : options -> SSAFull.SSAFull.spec -> bool **)

let verify_fullssa o s =
  let fE =
    SSAFull.SSAFull.program_succ_typenv (SSAFull.SSAFull.sprog s)
      (SSAFull.SSAFull.sinputs s)
  in
  let s0 = rewrite_mov s in
  let cuts = SSAFull.SSAFull.cut_spec s0 in
  let asserts = tflatten (tmap SSAFull.SSAFull.extract_asserts cuts) in
  let asserts_ssa = tmap ssa2lite_spec asserts in
  let nacuts = tmap SSAFull.SSAFull.remove_asserts cuts in
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

(** val verify_fulldsl : options -> DSLFull.DSLFull.spec -> bool **)

let verify_fulldsl o s =
  verify_fullssa o (SSAFull.ssa_spec s)
