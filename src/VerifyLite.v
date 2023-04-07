
(** * Verification procedures for SSALite and DSLLite *)

From Coq Require Import List ZArith Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From ssrlib Require Import EqVar Types EqOrder Seqs Tactics.
From BitBlasting Require Import State QFBV Typ TypEnv.
From Cryptoline Require Import Options DSLLite SSALite REP SSA2QFBV SSA2REP QFBV2CNF IMP.
From Coq Require Import Ring_polynom.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** ** Verification procedures *)

Section Verification.

  Import CNF.

  (** Assumed external solvers *)

  (* External SAT solver *)
  Parameter ext_all_unsat : seq cnf -> bool.

  (* External computer algebra system.
     Solve an ideal membership problems by the external computer algebra system.
     An ideal membership problem is given as a tuple (ps, ms, q). The problem
     is to check if q is in the ideal of ms++ps, i.e., there are cps and cms such
     that q = cps * ps + cms * ms. ext_solve_imp returns such (cps, cms). *)
  Parameter ext_solve_imp :
    seq (PExpr Z) -> PExpr Z -> seq (PExpr Z) -> seq (PExpr Z) * seq (PExpr Z).

  (* External computer algebra system.
     Solve a sequence of ideal membership problems by the external computer
     algebra system. An ideal membership problem is given as a tuple
     (ps, ms, q). The problem is to check if q is in the ideal of ms++ps,
     i.e., there are cps and cms such that q = cps * ps + cms * ms.
     ext_solve_imp_list returns a sequence of (cps, cms). *)
  Parameter ext_solve_imp_list :
    seq (seq (PExpr Z) * PExpr Z * seq (PExpr Z)) -> seq (seq (PExpr Z) * seq (PExpr Z)).


  (** Verify QF_BV predicates *)

  Definition verify_qfbv_bexps fE (es : seq QFBV.bexp) : bool :=
    let '(_, _, _, cnfs) := bb_hbexps_cache fE (tmap QFBVHash.hash_bexp es) in
    ext_all_unsat cnfs.


  (** Range reduction and algebraic soundness conditions *)

  Definition verify_rspec_algsnd (o : options) (s : SSALite.spec) : bool :=
    let rs := SSALite.rspec_of_spec s in
    let fE := SSALite.program_succ_typenv (SSALite.rsprog rs) (SSALite.rsinputs rs) in
    let es := bb_rngred_algsnd o rs in
    verify_qfbv_bexps fE es.


  (** Verify an atomic root entailment problem - sequential version *)

  Definition polys_of_arep (o : options) (ps : arep) : seq (PExpr Z) * PExpr Z * seq (PExpr Z) :=
    let '(_, _, ps, ms, q) := imp_of_arep ps in
    let '(ps', q') :=
      if rewrite_assignments_imp o then
        if vars_cache_in_rewrite_assignments o then simplify_generator_vars_cache ps q
        else simplify_generator ps q
      else (ps, q) in
    (ps', q', ms).

  (* Verify an atomic root entailment problem by reducing the problem to an
     ideal membership problem, solving the ideal membership problem by an
     external computer algebra system, and validating the answer from the
     computer algebra system. *)
  Definition verify_arep (o : options) (ps : arep) : bool :=
    let '(ps', q', ms) := polys_of_arep o ps in
    let (cps, cms) := ext_solve_imp ps' q' ms in
    validate_imp_answer ps' ms q' cps cms.

  Definition verify_areps (o : options) (pss : seq arep) : bool := all (verify_arep o) pss.


  (** Verify atomic root entailment problems - concurrent solving, sequential validating *)

  Definition polys_of_areps (o : options) (pss : seq arep) :
    seq (seq (PExpr Z) * PExpr Z * seq (PExpr Z)) :=
    tmap (polys_of_arep o) pss.

  Fixpoint validate_imp_answer_list polys coefs : bool :=
    match polys, coefs with
    | [::], [::] => true
    | ((ps, q, ms)::tlp), ((cps, cms)::tlc) => if validate_imp_answer ps ms q cps cms
                                               then validate_imp_answer_list tlp tlc
                                               else false
    | _, _ => false
    end.

  Definition verify_areps_list (o : options) (pss : seq arep) : bool :=
    let poly_list := polys_of_areps o pss in
    let coef_list := ext_solve_imp_list poly_list in
    if size poly_list == size coef_list
    then validate_imp_answer_list poly_list coef_list
    else false.


  (** Verify root entailment problems - sequential version *)

  (* Verify a root entailment problem by reducing the problem to atomic
     root entailment problems and then verifying the atomic problems
     through verify_areps. *)
  Definition verify_rep (o : options) (zs : REP.rep) : bool :=
    if rewrite_assignments_arep o
    then verify_areps o (areps_of_rep_simplified o zs)
    else verify_areps o (areps_of_rep zs).

  Definition verify_reps_seq (o : options) (zss : seq REP.rep) : bool :=
    all (verify_rep o) zss.


  (** Verify root entailment problems - concurrent version *)

  Definition verify_reps_paral (o : options) (zss : seq REP.rep) : bool :=
    if rewrite_assignments_arep o
    then verify_areps_list o (tflatten (tmap (areps_of_rep_simplified o) zss))
    else verify_areps_list o (tflatten (tmap areps_of_rep zss)).


  (** Algebraic reduction *)

  Definition verify_reps o (reps : seq REP.rep) : bool :=
    if compute_coefficients_one_by_one o
    then verify_reps_seq o reps
    else verify_reps_paral o reps.

  Definition verify_rep1 o (rep : REP.rep) : bool :=
    if compute_coefficients_one_by_one o
    then verify_rep o rep
    else verify_reps_paral o [:: rep].

  Definition verify_espec (o : options) (s : SSALite.spec) :=
    let avn := new_svar_spec s in
    let apply_algred s := algred_espec o avn s in
    if apply_slicing_espec o
    then let reps := tmap apply_algred
                          (tmap (SSALite.slice_espec o) (SSALite.split_espec (SSALite.espec_of_spec s))) in
         verify_reps o reps
    else let rep := apply_algred (SSALite.espec_of_spec s) in
         verify_rep1 o rep.


  (** Verify specifications *)

  Definition verify_ssalite (o : options) (s : SSALite.spec) :=
    (verify_rspec_algsnd o s) && (verify_espec o s).

  Definition verify_dsllite (o : options) (s : DSLLite.spec) :=
    verify_ssalite o (ssa_spec s).

End Verification.


(** ** Properties of verification procedures *)

Section VerificationLemmas.

  Import CNF.

  (** Assumed properties of external solvers *)

  Axiom all_unsat_sound :
    forall css : seq cnf,
      ext_all_unsat css ->
      forall cs, cs \in css -> ~ sat cs.

  Axiom all_unsat_complete :
    forall css : seq cnf,
      (forall cs, cs \in css -> ~ sat cs) ->
      ext_all_unsat css.

  Axiom ext_solve_imp_list_nil :
    ext_solve_imp_list [::] = [::].

  Axiom ext_solve_imp_list_cons :
    forall ps q ms tl,
      ext_solve_imp_list ((ps, q, ms)::tl) =
      (ext_solve_imp ps q ms)::(ext_solve_imp_list tl).


  (** Properties of verification procedures *)

  Lemma verify_qfbv_bexps_empty fE :
    verify_qfbv_bexps fE [::].
  Proof.
    rewrite /verify_qfbv_bexps /=. apply: all_unsat_complete. done.
  Qed.

  Lemma verify_qfbv_bexps_sound fE es :
    QFBV.well_formed_bexps es fE ->
    verify_qfbv_bexps fE es ->
    QFBV.valid_bexps fE es.
  Proof.
    move=> Hwf Hv. apply: (bb_hbexps_cache_sound Hwf).
    move=> m c g cnfs cnf Hbb Hin. rewrite /verify_qfbv_bexps in Hv.
    rewrite tmap_map Hbb in Hv. move: (all_unsat_sound Hv) => Hsat.
    exact: (Hsat cnf Hin).
  Qed.

  Lemma verify_qfbv_bexps_complete fE es :
    QFBV.well_formed_bexps es fE ->
    QFBV.valid_bexps fE es ->
    verify_qfbv_bexps fE es.
  Proof.
    move=> Hwf Hv. rewrite /verify_qfbv_bexps tmap_map.
    dcase (bb_hbexps_cache fE (map QFBVHash.hash_bexp es)) => [[[[m c] g] cnfs] Hbb].
    apply: all_unsat_complete. move=> cs Hin.
    exact: (bb_hbexps_cache_complete Hwf Hv Hbb Hin).
  Qed.

  Lemma agree_verify_qfbv_bexps E1 E2 es :
    SSALite.MA.agree (QFBV.vars_bexps es) E1 E2 ->
    verify_qfbv_bexps E1 es = verify_qfbv_bexps E2 es.
  Proof.
    move=> Hag. rewrite /verify_qfbv_bexps.
    rewrite (agree_bb_hbexps_cache Hag). reflexivity.
  Qed.


  (* Range reduction and algebraic soundness conditions *)

  Lemma verify_rspec_algsnd_sound o (s : SSALite.spec) :
    well_formed_ssa_spec s ->
    verify_rspec_algsnd o s ->
    SSALite.valid_rspec (SSALite.rspec_of_spec s) /\ ssa_spec_algsnd (SSALite.rspec_of_spec s).
  Proof.
    move=> Hwf Hv.
    apply: (bb_rngred_algsnd_sound (o:=o)
              (SSALite.rspec_of_spec_is_rng_rspec s) (well_formed_ssa_rng_spec Hwf)).
    move=> m c g cnfs cnf Hbb Hin. rewrite /verify_rspec_algsnd in Hv.
    rewrite /verify_qfbv_bexps tmap_map Hbb in Hv.
    move: (all_unsat_sound Hv) => Hsat. move: (Hsat cnf Hin) => {} Hsat.
    move=> Hsat'; apply: Hsat. exact: Hsat'.
  Qed.

  Lemma verify_rspec_algsnd_complete o (s : SSALite.spec) :
    apply_slicing_rspec o = false ->
    well_formed_ssa_spec s ->
    SSALite.valid_rspec (SSALite.rspec_of_spec s) -> ssa_spec_algsnd (SSALite.rspec_of_spec s) ->
    verify_rspec_algsnd o s.
  Proof.
    move=> Ho Hwf Hrange Hsafe. rewrite /verify_rspec_algsnd /verify_qfbv_bexps.
    rewrite tmap_map.
    dcase (bb_hbexps_cache (SSALite.program_succ_typenv (SSALite.rsprog (SSALite.rspec_of_spec s)) (SSALite.rsinputs (SSALite.rspec_of_spec s)))
                           (map QFBVHash.hash_bexp
                                (bb_rngred_algsnd o (SSALite.rspec_of_spec s)))) =>
    [[[[m c] g] cnfs] Hbb].
    apply: all_unsat_complete.
    move: (bb_rngred_algsnd_complete Ho
             (SSALite.rspec_of_spec_is_rng_rspec s) (well_formed_ssa_rng_spec Hwf) Hrange Hsafe) => Hv.
    move=> cs Hin. apply: (Hv _ _ _ _ _ Hbb). assumption.
  Qed.


  (* Verify an atomic root entailment problem - sequential version *)

  Lemma verify_areps_rev o pss :
    verify_areps o (rev pss) = verify_areps o pss.
  Proof.
    rewrite /verify_areps. rewrite all_rev. reflexivity.
  Qed.

  Lemma verify_arep_sound o ps : verify_arep o ps -> valid_arep ps.
  Proof.
    rewrite /verify_arep. rewrite /polys_of_arep.
    dcase (imp_of_arep ps) => [[[[[g t] zps] zms] zq] Hzp].
    case: (rewrite_assignments_imp o).
    - case: (vars_cache_in_rewrite_assignments o).
      + dcase (simplify_generator_vars_cache zps zq) => [[zps' zq'] Hsimp].
        dcase (ext_solve_imp zps' zq' zms) => [[cs c] Hco]. move=> Hch.
        exact: (validated_simplified_imp_vars_cache_valid_arep Hzp Hsimp Hch).
      + dcase (simplify_generator zps zq) => [[zps' zq'] Hsimp].
        dcase (ext_solve_imp zps' zq' zms) => [[cs c] Hco]. move=> Hch.
        exact: (validated_simplified_imp_valid_arep Hzp Hsimp Hch).
    - dcase (ext_solve_imp zps zq zms) => [[cs c] Hco]. move=> Hch.
      exact: (validated_imp_valid_arep Hzp Hch).
  Qed.

  Lemma verify_areps_in o ps pss :
    verify_areps o pss -> ps \in pss -> valid_arep ps.
  Proof.
    elim: pss => [| hd tl IH] //=. move/andP=> [Hhd Htl] Hin.
    rewrite in_cons in Hin. case/orP: Hin => Hin.
    - rewrite (eqP Hin). exact: (verify_arep_sound Hhd).
    - exact: (IH Htl Hin).
  Qed.


  (* Verify atomic root entailment problems - concurrent solving, sequential validating *)

  Lemma polys_of_areps_nil o : polys_of_areps o [::] = [::].
  Proof. reflexivity. Qed.

  Lemma polys_of_areps_cons o p ps :
    polys_of_areps o (p::ps) = (polys_of_arep o p)::(polys_of_areps o ps).
  Proof.
    rewrite /polys_of_areps. rewrite !tmap_map /=. reflexivity.
  Qed.

  Lemma size_ext_solve_imp_list ins :
    size (ext_solve_imp_list ins) = size ins.
  Proof.
    elim: ins => [| i ins IH] /=.
    - rewrite ext_solve_imp_list_nil. reflexivity.
    - case: i => [[ps q] ms]. rewrite ext_solve_imp_list_cons /=.
      rewrite IH. reflexivity.
  Qed.

  Lemma verify_areps_list_nil o : verify_areps_list o [::].
  Proof.
    rewrite /verify_areps_list /=. rewrite polys_of_areps_nil.
    rewrite ext_solve_imp_list_nil. by rewrite eqxx.
  Qed.

  Lemma verify_areps_list_cons o p ps :
    verify_areps_list o (p::ps) = verify_arep o p && verify_areps_list o ps.
  Proof.
    rewrite /verify_areps_list /verify_arep. rewrite !size_ext_solve_imp_list.
    rewrite !eqxx. rewrite polys_of_areps_cons.
    dcase (polys_of_arep o p) => [[[ps' q'] ms] Hpp].
    rewrite ext_solve_imp_list_cons /=.
    dcase (ext_solve_imp ps' q' ms) => [[cps cms] Hs].
    by case: (validate_imp_answer ps' ms q' cps cms).
  Qed.

  Lemma verify_areps_list_singleton o p :
    verify_areps_list o [:: p] = verify_arep o p.
  Proof.
    rewrite verify_areps_list_cons verify_areps_list_nil andbT. reflexivity.
  Qed.

  Lemma verify_areps_list_rcons o ps p :
    verify_areps_list o (rcons ps p) = verify_areps_list o ps && verify_arep o p.
  Proof.
    elim: ps => [| q ps IH] /=.
    - rewrite verify_areps_list_cons verify_areps_list_nil andbT /=. reflexivity.
    - rewrite !verify_areps_list_cons IH. by btauto.
  Qed.

  Lemma verify_areps_list_rev o ps :
    verify_areps_list o (rev ps) = verify_areps_list o ps.
  Proof.
    elim: ps => [| p ps IH] //=. rewrite verify_areps_list_cons.
    rewrite rev_cons. rewrite verify_areps_list_rcons IH.
    by rewrite andbC.
  Qed.

  Lemma verify_areps_list_cat o ps1 ps2 :
    verify_areps_list o (ps1 ++ ps2) = verify_areps_list o ps1 && verify_areps_list o ps2.
  Proof.
    elim: ps1 ps2 => [| p1 ps1 IH1] ps2 /=.
    - rewrite verify_areps_list_nil. reflexivity.
    - rewrite !verify_areps_list_cons. rewrite IH1. rewrite andbA. reflexivity.
  Qed.

  Lemma verify_areps_list_verify_areps o ps :
    verify_areps_list o ps = verify_areps o ps.
  Proof.
    elim: ps => [| p ps IH] /=.
    - rewrite verify_areps_list_nil. reflexivity.
    - rewrite verify_areps_list_cons IH. reflexivity.
  Qed.

  Lemma verify_areps_list_in o psp psps :
    verify_areps_list o psps -> psp \in psps -> valid_arep psp.
  Proof.
    elim: psps => [| hd tl IH] //=. rewrite /verify_areps_list.
    case Hs: (size (polys_of_areps o (hd :: tl)) ==
                size (ext_solve_imp_list (polys_of_areps o (hd :: tl)))) => //=.
    move: Hs. rewrite /polys_of_areps /polys_of_arep !tmap_map /= -!tmap_map -/(polys_of_areps o tl).
    case: (rewrite_assignments_imp o).
    - dcase (imp_of_arep hd) => [[[[[g t] ps] m] q] Hhd] /=.
      case: (vars_cache_in_rewrite_assignments o).
      + dcase (simplify_generator_vars_cache ps q) => [[ps' q'] Hsimp] Hs.
        rewrite ext_solve_imp_list_cons /= in Hs. rewrite eqSS in Hs.
        rewrite ext_solve_imp_list_cons. dcase (ext_solve_imp ps' q' m) => [[cs c] Hcs].
        case Hchk_hd: (validate_imp_answer ps' m q' cs c) => //=.
        move=> Hchk_tl Hin. rewrite in_cons in Hin. case/orP: Hin => Hin.
        * rewrite (eqP Hin).
          exact: (validated_simplified_imp_vars_cache_valid_arep Hhd Hsimp Hchk_hd).
        * apply: (IH _ Hin). rewrite /verify_areps_list. rewrite Hs. exact: Hchk_tl.
      + dcase (simplify_generator ps q) => [[ps' q'] Hsimp] Hs.
        rewrite ext_solve_imp_list_cons /= in Hs. rewrite eqSS in Hs.
        rewrite ext_solve_imp_list_cons. dcase (ext_solve_imp ps' q' m) => [[cs c] Hcs].
        case Hchk_hd: (validate_imp_answer ps' m q' cs c) => //=.
        move=> Hchk_tl Hin. rewrite in_cons in Hin. case/orP: Hin => Hin.
        * rewrite (eqP Hin). exact: (validated_simplified_imp_valid_arep Hhd Hsimp Hchk_hd).
        * apply: (IH _ Hin). rewrite /verify_areps_list. rewrite Hs. exact: Hchk_tl.
    - dcase (imp_of_arep hd) => [[[[[g t] ps] m] q] Hhd] /=.
      rewrite !ext_solve_imp_list_cons /= => Hs.
      rewrite eqSS in Hs. dcase (ext_solve_imp ps q m) => [[cs c] Hcs].
      case Hchk_hd: (validate_imp_answer ps m q cs c) => //=.
      move=> Hchk_tl Hin. rewrite in_cons in Hin. case/orP: Hin => Hin.
      + rewrite (eqP Hin). exact: (validated_imp_valid_arep Hhd Hchk_hd).
      + apply: (IH _ Hin). rewrite /verify_areps_list. rewrite Hs. exact: Hchk_tl.
  Qed.


  (* Verify root entailment problems - sequential version *)

  Lemma verify_reps_seq_in o zs zss :
    In zs zss -> verify_reps_seq o zss -> verify_rep o zs.
  Proof.
    elim: zss => [| z zss IH] //= Hin Hv. move/andP: Hv => [Hvz Hvzss].
    case: Hin.
    - move=> ?; subst. exact: Hvz.
    - move=> Hin. exact: (IH Hin Hvzss).
  Qed.

  Lemma verify_rep_sound o (zs : REP.rep) :
    verify_rep o zs -> REP.valid_rep zs.
  Proof.
    rewrite /verify_rep. case: (rewrite_assignments_arep o) => Hv.
    - apply: (@areps_of_rep_simplified_sound o) => ps Hin.
      exact: (verify_areps_in Hv Hin).
    - apply: areps_of_rep_sound => ps Hin.
      exact: (verify_areps_in Hv Hin).
  Qed.

  Lemma verify_reps_seq_sound o (zss : seq REP.rep) :
    verify_reps_seq o zss -> REP.valid_reps zss.
  Proof.
    elim: zss => [| zs zss IH] //=. move/andP=> [Hzs Hzss].
    rewrite REP.valid_reps_cons. split.
    - exact: (verify_rep_sound Hzs).
    - exact: (IH Hzss).
  Qed.


  (* Verify root entailment problems - concurrent version *)

  Lemma verify_reps_paral_nil o : verify_reps_paral o [::].
  Proof.
    rewrite /verify_reps_paral. rewrite verify_areps_list_nil.
    by case_if.
  Qed.

  Lemma verify_reps_paral_cons o z zs :
    verify_reps_paral o (z::zs) = verify_rep o z && verify_reps_paral o zs.
  Proof.
    rewrite /verify_reps_paral. case Hrw: (rewrite_assignments_arep o).
    - rewrite tflatten_flatten tmap_map /=. rewrite rev_cat.
      rewrite verify_areps_list_cat. rewrite -tflatten_flatten -tmap_map.
      rewrite (andbC (verify_rep _ _)).
      case: (verify_areps_list o (tflatten (tmap (areps_of_rep_simplified o) zs))) => //=.
      rewrite /verify_rep. rewrite Hrw. rewrite verify_areps_list_rev.
      exact: verify_areps_list_verify_areps.
    - rewrite tflatten_flatten tmap_map /=. rewrite rev_cat.
      rewrite verify_areps_list_cat. rewrite -tflatten_flatten -tmap_map.
      rewrite (andbC (verify_rep _ _)).
      case: (verify_areps_list o (tflatten (tmap areps_of_rep zs))) => //=.
      rewrite /verify_rep. rewrite Hrw. rewrite verify_areps_list_rev.
      exact: verify_areps_list_verify_areps.
  Qed.

  Lemma verify_reps_paral_seqs o zss :
    verify_reps_paral o zss = verify_reps_seq o zss.
  Proof.
    elim: zss => [| zs zss IH] //=.
    - rewrite verify_reps_paral_nil. reflexivity.
    - rewrite verify_reps_paral_cons IH. reflexivity.
  Qed.

  Lemma verify_reps_paral_sound o (zss : seq REP.rep) :
    verify_reps_paral o zss -> REP.valid_reps zss.
  Proof.
    rewrite /verify_reps_paral. case: (rewrite_assignments_arep o) => /= Hv.
    - move=> s Hs. apply: (@areps_of_rep_simplified_sound o) => ps Hin.
      apply: (verify_areps_list_in Hv). rewrite !tflatten_flatten !tmap_map /=.
      rewrite mem_rev. apply/flattenP. exists (areps_of_rep_simplified o s).
      + exact: (map_f _ Hs).
      + assumption.
    - move=> s Hs. apply: areps_of_rep_sound => ps Hin.
      apply: (verify_areps_list_in Hv). rewrite !tflatten_flatten !tmap_map /=.
      rewrite mem_rev. apply/flattenP. exists (areps_of_rep s).
      + exact: (map_f _ Hs).
      + assumption.
  Qed.


  (* Algebraic reduction *)

  Lemma verify_reps_nil o : verify_reps o [::].
  Proof.
    rewrite /verify_reps. rewrite verify_reps_paral_nil /=.
    by case_if.
  Qed.

  Lemma verify_reps_cons o r rs :
    verify_reps o (r::rs) = verify_rep o r && verify_reps o rs.
  Proof.
    rewrite /verify_reps. case_if.
    - rewrite /=. reflexivity.
    - rewrite verify_reps_paral_cons. reflexivity.
  Qed.

  Lemma verify_reps_rcons o rs r :
    verify_reps o (rcons rs r) = verify_reps o rs && verify_rep o r.
  Proof.
    elim: rs => [| s rs IH] /=.
    - rewrite verify_reps_cons verify_reps_nil andbT /=. reflexivity.
    - rewrite !verify_reps_cons IH. rewrite andbA. reflexivity.
  Qed.

  Lemma verify_reps_rev o rs :
    verify_reps o (rev rs) = verify_reps o rs.
  Proof.
    elim: rs => [| r rs IH] //=.
    rewrite rev_cons verify_reps_rcons verify_reps_cons IH.
    rewrite andbC. reflexivity.
  Qed.

  Lemma verify_reps_cat o rs1 rs2 :
    verify_reps o (rs1 ++ rs2) = verify_reps o rs1 && verify_reps o rs2.
  Proof.
    elim: rs1 => [| r1 rs1 IH] /=.
    - rewrite verify_reps_nil. reflexivity.
    - rewrite !verify_reps_cons IH. rewrite andbA. reflexivity.
  Qed.

  Lemma verify_reps_tflatten o rss :
    verify_reps o (tflatten rss) = all (verify_reps o) rss.
  Proof.
    elim: rss => [| rs rss IH] /=.
    - rewrite verify_reps_nil. reflexivity.
    - rewrite tflatten_cons verify_reps_cat IH.
      rewrite verify_reps_rev andbC. reflexivity.
  Qed.

  Lemma verify_reps_sound o reps :
    verify_reps o reps ->
    REP.valid_reps reps.
  Proof.
    rewrite /verify_reps. case_if; eauto using verify_reps_seq_sound, verify_reps_paral_sound.
  Qed.

  Lemma verify_rep1_sound o rep :
    verify_rep1 o rep ->
    REP.valid_rep rep.
  Proof.
    rewrite /verify_rep1. case_if.
    - exact: (verify_rep_sound H0).
    - exact: (REP.valid_reps_hd (verify_reps_paral_sound H0)).
  Qed.


  (* Verify specifications *)

  Theorem verify_ssalite_sound (o : options) (s : SSALite.spec) :
    well_formed_ssa_spec s -> verify_ssalite o s ->
    SSALite.valid_spec s.
  Proof.
    rewrite /verify_ssalite /verify_espec=> Hwf /andP [Hvrs Hvz].
    move: (verify_rspec_algsnd_sound Hwf Hvrs) => [Hvr Hvs].
    case: (apply_slicing_espec o) Hvz.
    - case: (compute_coefficients_one_by_one o) => Hrep.
      + apply: (algred_spec_slice_sound
                  (o:=o) Hwf Hvs (fresh_var_spec_espec (new_svar_spec_fresh s)) Hvr).
        move=> ss Hin. exact: (verify_reps_sound (o:=o) Hrep Hin).
      + apply: (algred_spec_slice_sound
                  (o:=o) Hwf Hvs (fresh_var_spec_espec (new_svar_spec_fresh s)) Hvr).
        move=> ss Hin. exact: (verify_reps_sound Hrep Hin).
    - case: (compute_coefficients_one_by_one o) => Hrep.
      + apply: (algred_spec_sound
                  (o:=o) Hwf Hvs Hvr (fresh_var_spec_espec (new_svar_spec_fresh s))).
        exact: (verify_rep1_sound Hrep).
      + apply: (algred_spec_sound
                  (o:=o) Hwf Hvs Hvr (fresh_var_spec_espec (new_svar_spec_fresh s))).
        exact: (verify_rep1_sound Hrep).
  Qed.

  Theorem verify_dsllite_sound (o : options) (s : DSLLite.spec) :
    DSLLite.well_formed_spec s -> verify_dsllite o s ->
    DSLLite.valid_spec s.
  Proof.
    rewrite /verify_dsllite => Hwf Hv. apply: ssa_spec_sound.
    apply: (verify_ssalite_sound _ Hv).
    exact: (ssa_spec_well_formed Hwf).
  Qed.

End VerificationLemmas.
