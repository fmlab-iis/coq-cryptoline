
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder Seqs Tactics.
From Cryptoline Require Import DSL SSA ZSSA SSA2QFBV SSA2ZSSA QFBV2CNF Poly.
From Coq Require Import Ring_polynom.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Verification.


  (* This is the external SAT solver.
     The correctness is guaranteed by external checker. *)
  Parameter ext_all_unsat : seq CNF.cnf -> bool.

  Axiom all_unsat_sound :
    forall css : seq CNF.cnf,
      ext_all_unsat css ->
      forall cs, List.In cs css -> ~ CNF.sat cs.

  Definition verify_rspec_safety (s : SSA.spec) : bool :=
    let fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s) in
    let es := bb_range_safety s in
    let '(_, _, _, cnfs) := bb_bexps_cache fE es in
    ext_all_unsat cnfs.

  Lemma verify_rspec_safety_sound (s : SSA.spec) :
    well_formed_ssa_spec s ->
    verify_rspec_safety s ->
    SSA.valid_rspec (SSA.rspec_of_spec s) /\ ssa_spec_safe s.
  Proof.
    move=> Hwf Hv. apply: (bb_range_safety_sound Hwf).
    move=> m c g cnfs cnf Hbb Hin. rewrite /verify_rspec_safety in Hv.
    rewrite Hbb in Hv. exact: (all_unsat_sound Hv Hin).
  Qed.


  (* This is the external coefficients finder.
     The correctness is guaranteed by coefficients_checker.
     ps -> q -> m -> (cs, c) *)
  Parameter ext_find_coefficients :
    seq (PExpr Z) -> PExpr Z -> PExpr Z -> seq (PExpr Z) * (PExpr Z).

  Fixpoint verify_pspecs (pss : seq pspec) : bool :=
    match pss with
    | [::] => true
    | ps::pss =>
      let '(g, t, ps, m, q) := zpexprs_of_pspec ps in
      let (cs, c) := ext_find_coefficients ps q m in
      if coefficients_checker ps m q cs c then verify_pspecs pss
      else false
    end.

  Definition verify_zspec (zs : ZSSA.zspec) : bool :=
    verify_pspecs (pspecs_of_zspec zs).

  Lemma verify_zspec_sound (zs : ZSSA.zspec) : verify_zspec zs -> ZSSA.valid_zspec zs.
  Proof.
    rewrite /verify_zspec=> Hv. apply: pspecs_of_zspec_sound => ps Hin.
    move: (pspecs_of_zspec zs) Hv Hin => {zs} pss. elim: pss => [| hd tl IH] //=.
    dcase (zpexprs_of_pspec hd) => [[[[[g t] zps] zm] zq] Hzp].
    dcase (ext_find_coefficients zps zq zm) => [[cs c] Hco].
    case Hch: (coefficients_checker zps zm zq cs c) => //=.
    move=> Htl Hin. rewrite in_cons in Hin. case/orP: Hin=> Hin.
    - rewrite (eqP Hin). exact: (checker_valid_pspec Hzp Hch).
    - exact: (IH Htl Hin).
  Qed.


  (* Verify specifications *)

  Definition verify_ssa (o : options) (s : SSA.spec) :=
    (verify_rspec_safety s) &&
    (verify_zspec (bv2z_espec o (new_svar_spec s) (SSA.espec_of_spec s))).

  Definition verify_dsl (o : options) (s : DSL.spec) :=
    verify_ssa o (ssa_spec s).

  Theorem verify_ssa_sound (o : options) (s : SSA.spec) :
    well_formed_ssa_spec s ->
    verify_ssa o s ->
    SSA.valid_spec s.
  Proof.
    move=> Hwf /andP [Hvrs Hvz].
    move: (verify_rspec_safety_sound Hwf Hvrs) => [Hvr Hvs].
    apply: (bv2z_spec_sound (o:=o) Hwf Hvs Hvr).
    exact: (verify_zspec_sound Hvz).
  Qed.

  Theorem verify_dsl_sound (o : options) (s : DSL.spec) :
    DSL.well_formed_spec s ->
    verify_dsl o s ->
    DSL.valid_spec s.
  Proof.
    rewrite /verify_dsl => Hwf Hv. apply: ssa_spec_sound.
    apply: (verify_ssa_sound _ Hv).
    exact: (ssa_spec_well_formed Hwf).
  Qed.

End Verification.