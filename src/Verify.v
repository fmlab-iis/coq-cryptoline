
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder Seqs Tactics.
From Cryptoline Require Import Options DSL SSA ZSSA SSA2QFBV SSA2ZSSA QFBV2CNF Poly.
From Coq Require Import Ring_polynom.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Verification.

  Import CNF.

  (* This is the external SAT solver.
     The correctness is guaranteed by external checker. *)
  Parameter ext_all_unsat : seq cnf -> bool.

  Axiom all_unsat_sound :
    forall css : seq cnf,
      ext_all_unsat css ->
      forall cs, cs \in css -> ~ sat cs.

  Axiom all_unsat_complete :
    forall css : seq cnf,
      (forall cs, cs \in css -> ~ sat cs) ->
      ext_all_unsat css.

  Definition verify_rspec_safety (s : SSA.spec) : bool :=
    let fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s) in
    let es := bb_range_safety_la_simplified_filtered s in
    let '(_, _, _, cnfs) := bb_hbexps_cache fE (map QFBVHash.hash_bexp es) in
    ext_all_unsat cnfs.

  Lemma verify_rspec_safety_sound (s : SSA.spec) :
    well_formed_ssa_spec s ->
    verify_rspec_safety s ->
    SSA.valid_rspec (SSA.rspec_of_spec s) /\ ssa_spec_safe s.
  Proof.
    move=> Hwf Hv. apply: (bb_range_safety_la_simplified_filtered_sound Hwf).
    move=> m c g cnfs cnf Hbb Hin. rewrite /verify_rspec_safety in Hv.
    rewrite Hbb in Hv. move: (all_unsat_sound Hv) => Hsat.
    move: (Hsat cnf Hin) => {Hsat} Hsat.
    move=> Hsat'; apply: Hsat. exact: Hsat'.
  Qed.

  Lemma verify_rspec_safety_complete (s : SSA.spec) :
    well_formed_ssa_spec s ->
    SSA.valid_rspec (SSA.rspec_of_spec s) -> ssa_spec_safe s ->
    verify_rspec_safety s.
  Proof.
    move=> Hwf Hrange Hsafe. rewrite /verify_rspec_safety.
    dcase (bb_hbexps_cache (SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s))
                           (map QFBVHash.hash_bexp
                                (bb_range_safety_la_simplified_filtered s))) =>
    [[[[m c] g] cnfs] Hbb].
    apply: all_unsat_complete.
    move: (bb_range_safety_la_simplified_filtered_complete Hwf Hrange Hsafe) => Hv.
    move=> cs Hin. apply: (Hv _ _ _ _ _ Hbb). assumption.
  Qed.


  (* This is the external coefficients finder.
     The correctness is guaranteed by coefficients_checker.
     ps -> q -> m -> (cs, c) *)
  Parameter ext_find_coefficients :
    seq (PExpr Z) -> PExpr Z -> PExpr Z -> seq (PExpr Z) * (PExpr Z).

  Definition verify_pspec (ps : pspec) : bool :=
    let '(_, _, ps, m, q) := zpexprs_of_pspec ps in
    let (cs, c) := ext_find_coefficients ps q m in
    coefficients_checker_tr ps m q cs c.

  Definition verify_pspecs (pss : seq pspec) : bool := all verify_pspec pss.

  Definition verify_zspec (o : options) (zs : ZSSA.zspec) : bool :=
    if rewrite_assignments o
    then verify_pspecs (pspecs_of_zspec_simplified o zs)
    else verify_pspecs (pspecs_of_zspec zs).

  Lemma verify_pspec_sound ps : verify_pspec ps -> valid_pspec ps.
  Proof.
    rewrite /verify_pspec. dcase (zpexprs_of_pspec ps) => [[[[[g t] zps] zm] zq] Hzp].
    dcase (ext_find_coefficients zps zq zm) => [[cs c] Hco]. move=> Hch.
    exact: (checker_tr_valid_pspec Hzp Hch).
  Qed.

  Lemma verify_pspecs_in ps pss :
    verify_pspecs pss -> ps \in pss -> valid_pspec ps.
  Proof.
    elim: pss => [| hd tl IH] //=. move/andP=> [Hhd Htl] Hin.
    rewrite in_cons in Hin. case/orP: Hin => Hin.
    - rewrite (eqP Hin). exact: (verify_pspec_sound Hhd).
    - exact: (IH Htl Hin).
  Qed.

  Lemma verify_zspec_sound o (zs : ZSSA.zspec) :
    verify_zspec o zs -> ZSSA.valid_zspec zs.
  Proof.
    rewrite /verify_zspec. case: (rewrite_assignments o) => Hv.
    - apply: (@pspecs_of_zspec_simplified_sound o) => ps Hin.
      exact: (verify_pspecs_in Hv Hin).
    - apply: pspecs_of_zspec_sound => ps Hin.
      exact: (verify_pspecs_in Hv Hin).
  Qed.


  (* The external coefficients finder for a list of algebraic specifications.
     (ps * q * m) list -> (cs, c) list *)
  Parameter ext_find_coefficients_list :
    seq (seq (PExpr Z) * PExpr Z * PExpr Z) -> seq (seq (PExpr Z) * (PExpr Z)).

  Axiom ext_find_coefficients_list_cons :
    forall ps m q tl,
      ext_find_coefficients_list ((ps, m, q)::tl) =
      (ext_find_coefficients ps m q)::(ext_find_coefficients_list tl).

  Definition polys_of_pspecs (pss : seq pspec) :
    seq (seq (PExpr Z) * PExpr Z * PExpr Z) :=
    let f ps :=
        let '(_, _, ps, m, q) := zpexprs_of_pspec ps in
        (ps, q, m) in
    map f pss.

  Fixpoint coefficients_checker_tr_list polys coefs : bool :=
    match polys, coefs with
    | [::], [::] => true
    | ((ps, q, m)::tlp), ((cs, c)::tlc) => if coefficients_checker_tr ps m q cs c
                                           then coefficients_checker_tr_list tlp tlc
                                           else false
    | _, _ => false
    end.

  Definition verify_pspecs_list (pss : seq pspec) : bool :=
    let poly_list := polys_of_pspecs pss in
    let coef_list := ext_find_coefficients_list poly_list in
    if size poly_list == size coef_list
    then coefficients_checker_tr_list poly_list coef_list
    else false.

  Definition verify_zspec_list (o : options) (zs : ZSSA.zspec) : bool :=
    if rewrite_assignments o
    then verify_pspecs_list (pspecs_of_zspec_simplified o zs)
    else verify_pspecs_list (pspecs_of_zspec zs).

  Lemma verify_pspecs_list_in psp psps :
    verify_pspecs_list psps -> psp \in psps -> valid_pspec psp.
  Proof.
    elim: psps => [| hd tl IH] //=. rewrite /verify_pspecs_list.
    case Hs: (size (polys_of_pspecs (hd :: tl)) ==
              size (ext_find_coefficients_list (polys_of_pspecs (hd :: tl)))) => //=.
    dcase (zpexprs_of_pspec hd) => [[[[[g t] ps] m] q] Hhd] /=.
    rewrite Hhd in Hs. rewrite ext_find_coefficients_list_cons /= in Hs.
    rewrite eqSS in Hs. rewrite ext_find_coefficients_list_cons.
    dcase (ext_find_coefficients ps q m) => [[cs c] Hcs].
    case Hchk_hd: (coefficients_checker_tr ps m q cs c) => //=.
    move=> Hchk_tl Hin. rewrite in_cons in Hin. case/orP: Hin => Hin.
    - rewrite (eqP Hin). exact: (checker_tr_valid_pspec Hhd Hchk_hd).
    - apply: (IH _ Hin). rewrite /verify_pspecs_list. rewrite Hs. exact: Hchk_tl.
  Qed.

  Lemma verify_zspec_list_sound o (zs : ZSSA.zspec) :
    verify_zspec_list o zs -> ZSSA.valid_zspec zs.
  Proof.
    rewrite /verify_zspec_list. case: (rewrite_assignments o) => Hv.
    - apply: (@pspecs_of_zspec_simplified_sound o) => ps Hin.
      exact: (verify_pspecs_list_in Hv Hin).
    - apply: pspecs_of_zspec_sound => ps Hin.
      exact: (verify_pspecs_list_in Hv Hin).
  Qed.


  (* Verify specifications *)

  Definition verify_ssa (o : options) (s : SSA.spec) :=
    (verify_rspec_safety s) &&
    if compute_coefficients_one_by_one o
    then (verify_zspec o (bv2z_espec o (new_svar_spec s) (SSA.espec_of_spec s)))
    else (verify_zspec_list o (bv2z_espec o (new_svar_spec s) (SSA.espec_of_spec s))).

  Definition verify_dsl (o : options) (s : DSL.spec) :=
    verify_ssa o (ssa_spec s).

  Theorem verify_ssa_sound (o : options) (s : SSA.spec) :
    well_formed_ssa_spec s ->
    verify_ssa o s ->
    SSA.valid_spec s.
  Proof.
    move=> Hwf /andP [Hvrs Hvz]. move: (verify_rspec_safety_sound Hwf Hvrs) => [Hvr Hvs].
    apply: (bv2z_spec_sound (o:=o) Hwf Hvs Hvr).
    case Hc: (compute_coefficients_one_by_one o) Hvz => Hvz.
    - exact: (verify_zspec_sound Hvz).
    - exact: (verify_zspec_list_sound Hvz).
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
