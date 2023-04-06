
(** Verification procedures *)

From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From ssrlib Require Import EqVar Types EqOrder Lists Seqs Tactics.
From BitBlasting Require Import State QFBV Typ TypEnv.
From Cryptoline Require Import Options DSLLite SSALite DSL SSA SSA2SSALite ZSSA SSA2QFBV SSA2ZSSA QFBV2CNF Poly VerifyLite.
From Coq Require Import Ring_polynom.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* Verify full specifications *)

Section Verification.

  (* Reductions *)

  Definition rngred_spec (o : options) (s : SSALite.spec) : seq QFBV.bexp :=
    let rs := SSALite.rspec_of_spec s in
    let fE := SSALite.program_succ_typenv (SSALite.rsprog rs) (SSALite.rsinputs rs) in
    filter_not_true
      (simplify_bexps
         (if apply_slicing_rspec o then rngred_rspec_slice_split_la o rs
          else rngred_rspec_split_la rs)).

  Definition algsnd_spec (o : options) (s : SSALite.spec) : seq QFBV.bexp :=
    let rs := SSALite.rspec_of_spec s in
    let fE := SSALite.program_succ_typenv (SSALite.rsprog rs) (SSALite.rsinputs rs) in
    filter_not_true
      (simplify_bexps
         (if apply_slicing_rspec o then algsnd_slice_la o rs
          else qfbv_spec_algsnd_la rs)).

  Definition algred_spec (o : options) (s : SSALite.spec) : seq ZSSA.rep :=
    let avn := new_svar_spec s in
    let apply_algred s := algred_espec o avn s in
    if apply_slicing_espec o
    then tmap apply_algred
              (tmap (SSALite.slice_espec o) (SSALite.split_espec (SSALite.espec_of_spec s)))
    else [:: apply_algred (SSALite.espec_of_spec s)].

  Lemma algsnd_spec_vars_subset o s :
    SSAVS.subset (QFBV.vars_bexps (algsnd_spec o s)) (SSALite.vars_spec s).
  Proof.
    rewrite /algsnd_spec. rewrite vars_filter_not_true.
    apply: (SSAVS.Lemmas.subset_trans (vars_simplify_bexps _)). case_if.
    - rewrite /SSALite.vars_spec.
      apply: (SSAVS.Lemmas.subset_trans (vars_algsnd_slice_la o (SSALite.rspec_of_spec s))).
      simpl. case: s => E [e r] p g /=.
      rewrite /SSALite.vars_bexp /=. move: (SSALite.vars_rng_program p) => Hsub.
      by SSAVS.Lemmas.dp_subset.
    - rewrite /SSALite.vars_spec.
      apply: (SSAVS.Lemmas.subset_trans (vars_qfbv_spec_algsnd_la _)).
      case: s => E [e r] p g /=. rewrite /SSALite.vars_bexp /=.
      move: (SSALite.vars_rng_program p) => Hsub.
      by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma rngred_spec_vars_subset o s :
    SSAVS.subset (QFBV.vars_bexps (rngred_spec o s)) (SSALite.vars_spec s).
  Proof.
    rewrite /rngred_spec. rewrite vars_filter_not_true.
    apply: (SSAVS.Lemmas.subset_trans (vars_simplify_bexps _)). case_if.
    - apply: (SSAVS.Lemmas.subset_trans (vars_rngred_rspec_slice_split_la _ _)).
      exact: SSALite.vars_rspec_of_spec.
    - apply: (SSAVS.Lemmas.subset_trans (vars_rngred_rspec_split_la _)).
      exact: SSALite.vars_rspec_of_spec.
  Qed.

  Lemma rngred_spec_sound o s :
    let rs := SSALite.rspec_of_spec s in
    let fE := SSALite.program_succ_typenv (SSALite.rsprog rs) (SSALite.rsinputs rs) in
    SSALite.well_formed_ssa_spec s ->
    verify_qfbv_bexps fE (rngred_spec o s) ->
    SSALite.valid_rspec (SSALite.rspec_of_spec s).
  Proof.
    move=> rs fE Hwf. move: (well_formed_ssa_rng_spec Hwf) => {}Hwf.
    rewrite /rngred_spec. case_if.
    - apply: (rngred_rspec_slice_split_la_sound (SSALite.rspec_of_spec_is_rng_rspec s) Hwf (o:=o)).
      rewrite /valid_rngred_rspec_slice_split_la /=.
      apply/simplify_bexps_valid. apply/filter_not_true_valid.
      apply: (verify_qfbv_bexps_sound _ H0).
      apply/filter_not_true_well_formed. apply/simplify_bexps_well_formed.
      exact: (rngred_rspec_slice_split_la_well_formed _ Hwf).
    - apply: (rngred_rspec_split_la_sound Hwf).
      rewrite /valid_rngred_rspec_split_la /=.
      apply/simplify_bexps_valid. apply/filter_not_true_valid.
      apply: (verify_qfbv_bexps_sound _ H0).
      apply/filter_not_true_well_formed. apply/simplify_bexps_well_formed.
      exact: (well_formed_qfbv_rngred_rspec_split_la Hwf).
  Qed.

  Lemma algsnd_spec_sound o s :
    let rs := SSALite.rspec_of_spec s in
    let fE := SSALite.program_succ_typenv (SSALite.rsprog rs) (SSALite.rsinputs rs) in
    SSALite.well_formed_ssa_spec s ->
    verify_qfbv_bexps fE (algsnd_spec o s) ->
    ssa_spec_algsnd (SSALite.rspec_of_spec s).
  Proof.
    move=> rs fE Hwf. move: (well_formed_ssa_rng_spec Hwf) => {}Hwf.
    rewrite /algsnd_spec. case_if.
    - apply: (algsnd_slice_la_sound Hwf (o:=o)).
      apply/simplify_bexps_valid. apply/filter_not_true_valid.
      apply: (verify_qfbv_bexps_sound _ H0).
      apply/filter_not_true_well_formed. apply/simplify_bexps_well_formed.
      exact: (algsnd_slice_la_well_formed _ Hwf).
    - apply: (qfbv_spec_algsnd_la_sound Hwf).
      apply/simplify_bexps_valid. apply/filter_not_true_valid.
      apply: (verify_qfbv_bexps_sound _ H0).
      apply/filter_not_true_well_formed. apply/simplify_bexps_well_formed.
      exact: (qfbv_spec_algsnd_la_well_formed Hwf).
  Qed.

  Lemma algred_spec_sound o s :
    SSALite.well_formed_ssa_spec s ->
    ssa_spec_algsnd (SSALite.rspec_of_spec s) ->
    SSALite.valid_rspec (SSALite.rspec_of_spec s) ->
    ZSSA.valid_reps (algred_spec o s) ->
    SSALite.valid_spec s.
  Proof.
    move=> Hwf Hsnd Hvr. move: (fresh_var_spec_espec (new_svar_spec_fresh s)) => Havn.
    rewrite /algred_spec. case_if.
    - exact: (algred_spec_slice_sound Hwf Hsnd Havn Hvr H0).
    - exact: (algred_spec_sound Hwf Hsnd Hvr Havn (ZSSA.valid_reps_hd H0)).
  Qed.


  (* Verification procedure *)

  Definition verify_ssa (o : options) (s : SSA.spec) : bool :=
    let fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s) in
    (* Rewrite mov statements before cutting the specification *)
    let s := rewrite_mov s in
    (* Split cuts *)
    let cuts := SSA.cut_spec s in
    (* Extract all assertions *)
    let asserts := tflatten (tmap SSA.extract_asserts cuts) in
    let asserts_ssa := tmap SSA2SSALite.ssa2lite_spec asserts in
    (* Cuts without any assertions *)
    let nacuts := tmap SSA.remove_asserts cuts in
    let nacuts_ssa := tmap SSA2SSALite.ssa2lite_spec nacuts in
    (* range reduction and algebraic soundness *)
    let rngconds :=
      (* QF_BV predicates for soundness conditions *)
      let sndconds := tflatten (tmap (algsnd_spec o) nacuts_ssa) in
      (* QF_BV predicates for range assertions *)
      let rngasserts := tflatten (tmap (rngred_spec o) asserts_ssa) in
      (* QF_BV predicates for range postcondition *)
      let rngpost := tflatten (tmap (rngred_spec o) nacuts_ssa) in
      catrev (rev sndconds) (catrev (rev rngasserts) rngpost) in
    (* algebraic reduction *)
    let reps :=
      let algasserts := tflatten (tmap (algred_spec o) asserts_ssa) in
      let algpost := tflatten (tmap (algred_spec o) nacuts_ssa) in
      catrev (rev algasserts) algpost in
    (verify_qfbv_bexps fE rngconds) && (verify_reps o reps).

  Definition verify_dsl (o : options) (s : DSL.spec) :=
    verify_ssa o (SSA.ssa_spec s).


  (* Soundness *)

  Lemma algsnd_spec_remove_asserts_well_formed_bexps o s cut :
    let fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s) : SSATE.env in
    let rms := rewrite_mov s : SSA.spec in
    let cuts := SSA.cut_spec rms : seq SSA.spec in
    well_formed_ssa_spec s ->
    In cut cuts ->
    QFBV.well_formed_bexps (algsnd_spec o (ssa2lite_spec (SSA.remove_asserts cut))) fE.
  Proof.
    move=> fE rms cuts Hwf Hin. rewrite /algsnd_spec.
    apply/filter_not_true_well_formed. apply: simplify_bexps_well_formed.
    (* well_formed SSA *)
    have Hwfssa: SSALite.well_formed_ssa_spec (ssa2lite_spec (SSA.remove_asserts cut)).
    { rewrite (ssa2lite_spec_well_formed_ssa (cut_remove_asserts_is_lite_in Hin)).
      apply: remove_asserts_well_formed_ssa. apply: (cut_spec_well_formed_ssa_in _ Hin).
      exact: (rewrite_mov_well_formed_ssa Hwf). }
    (* from fE to (program_succ_typenv (sprog cut) (sinputs cut)) *)
    rewrite -(@agree_well_formed_bexps
                (SSA.program_succ_typenv (SSA.sprog cut) (SSA.sinputs cut)) fE).
    - (* well_formed *)
      rewrite -SSA.remove_asserts_succ_typenv. rewrite -ssa2lite_spec_succ_typenv.
      rewrite -SSALite.rspec_of_spec_succ_typenv. case_if.
      + apply: algsnd_slice_la_well_formed. apply: well_formed_ssa_rng_spec.
        exact: Hwfssa.
      + apply: qfbv_spec_algsnd_la_well_formed. apply: well_formed_ssa_rng_spec.
        exact: Hwfssa.
    - (* agree *)
      move: (cut_spec_agree_in (rewrite_mov_well_formed_ssa Hwf) Hin) => Hag.
      rewrite (rewrite_mov_succ_typenv Hwf) in Hag.
      apply: (SSALite.MA.subset_set_agree _ Hag).
      apply: (SSAVS.Lemmas.subset_trans _ (SSA.remove_asserts_vars_subset _)).
      apply: (SSAVS.Lemmas.subset_trans _ (ssa2lite_spec_vars_subset _)).
      apply: (SSAVS.Lemmas.subset_trans _ (SSALite.vars_rspec_of_spec _)).
      case_if.
      + apply: (SSAVS.Lemmas.subset_trans (vars_algsnd_slice_la _ _)).
        rewrite /SSALite.vars_rspec. by SSAVS.Lemmas.dp_subset.
      + apply: (SSAVS.Lemmas.subset_trans (vars_qfbv_spec_algsnd_la _)).
        rewrite /SSALite.vars_rspec. by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma rngred_spec_remove_asserts_well_formed_bexps o s cut :
    let fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s) : SSATE.env in
    let rms := rewrite_mov s : SSA.spec in
    let cuts := SSA.cut_spec rms : seq SSA.spec in
    well_formed_ssa_spec s ->
    In cut cuts ->
    QFBV.well_formed_bexps (rngred_spec o (ssa2lite_spec (SSA.remove_asserts cut))) fE.
  Proof.
    move=> fE rms cuts Hwf Hin. rewrite /rngred_spec.
    apply/filter_not_true_well_formed. apply: simplify_bexps_well_formed.
    (* well_formed SSA *)
    have Hwfssa: SSALite.well_formed_ssa_spec (ssa2lite_spec (SSA.remove_asserts cut)).
    { rewrite (ssa2lite_spec_well_formed_ssa (cut_remove_asserts_is_lite_in Hin)).
      apply: remove_asserts_well_formed_ssa.
      exact: (cut_spec_well_formed_ssa_in (rewrite_mov_well_formed_ssa Hwf) Hin). }
    (* from fE to (program_succ_typenv (sprog cut) (sinputs cut)) *)
    rewrite -(@agree_well_formed_bexps
                (SSA.program_succ_typenv (SSA.sprog cut) (SSA.sinputs cut)) fE).
    - (* well_formed *)
      rewrite -SSA.remove_asserts_succ_typenv. rewrite -ssa2lite_spec_succ_typenv.
      rewrite -SSALite.rspec_of_spec_succ_typenv. case_if.
      + apply: rngred_rspec_slice_split_la_well_formed. apply: well_formed_ssa_rng_spec.
        exact: Hwfssa.
      + apply: well_formed_qfbv_rngred_rspec_split_la. apply: well_formed_ssa_rng_spec.
        exact: Hwfssa.
    - (* agree *)
      move: (cut_spec_agree_in (rewrite_mov_well_formed_ssa Hwf) Hin) => Hag.
      rewrite (rewrite_mov_succ_typenv Hwf) in Hag.
      apply: (SSALite.MA.subset_set_agree _ Hag).
      apply: (SSAVS.Lemmas.subset_trans _ (SSA.remove_asserts_vars_subset _)).
      apply: (SSAVS.Lemmas.subset_trans _ (ssa2lite_spec_vars_subset _)).
      apply: (SSAVS.Lemmas.subset_trans _ (SSALite.vars_rspec_of_spec _)).
      case_if.
      + apply: (SSAVS.Lemmas.subset_trans (vars_rngred_rspec_slice_split_la _ _)).
        rewrite /SSALite.vars_rspec. by SSAVS.Lemmas.dp_subset.
      + apply: (SSAVS.Lemmas.subset_trans (vars_rngred_rspec_split_la _)).
        rewrite /SSALite.vars_rspec. by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma rngred_spec_extract_asserts_well_formed_bexps o s cut a :
    let fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s) : SSATE.env in
    let rms := rewrite_mov s : SSA.spec in
    let cuts := SSA.cut_spec rms : seq SSA.spec in
    well_formed_ssa_spec s ->
    In cut cuts ->
    In a (SSA.extract_asserts cut) ->
    QFBV.well_formed_bexps (rngred_spec o (ssa2lite_spec a)) fE.
  Proof.
    move=> fE rms cuts Hwf Hinc Hina. rewrite /rngred_spec.
    apply/filter_not_true_well_formed. apply: simplify_bexps_well_formed.
    (* well_formed SSA *)
    move: (cut_spec_well_formed_ssa_in (rewrite_mov_well_formed_ssa Hwf) Hinc) => Hwfc.
    move: (extract_asserts_well_formed_ssa_in Hwfc Hina) => Hwfa.
    have Hwfssa: SSALite.well_formed_ssa_spec (ssa2lite_spec a).
    { rewrite (ssa2lite_spec_well_formed_ssa (cut_extract_asserts_ls_lite_in Hinc Hina)).
      exact: Hwfa. }
    (* from fE to (program_succ_typenv (sprog a) (sinputs a)) *)
    rewrite -(@agree_well_formed_bexps
                (SSA.program_succ_typenv (SSA.sprog a) (SSA.sinputs a)) fE).
    - (* well_formed *)
      rewrite -ssa2lite_spec_succ_typenv. rewrite -SSALite.rspec_of_spec_succ_typenv. case_if.
      + apply: rngred_rspec_slice_split_la_well_formed. apply: well_formed_ssa_rng_spec.
        exact: Hwfssa.
      + apply: well_formed_qfbv_rngred_rspec_split_la. apply: well_formed_ssa_rng_spec.
        exact: Hwfssa.
    - (* agree *)
      move: (cut_spec_agree_in (rewrite_mov_well_formed_ssa Hwf) Hinc) => Hagc.
      move: (extract_asserts_agree_in Hwfc Hina) => Haga.
      move: (SSA.MA.subset_set_agree (SSA.extract_asserts_vars_subset Hina) Hagc) => {}Hagc.
      move: (SSA.MA.agree_trans Haga Hagc) => {Haga Hagc} Hag.
      rewrite (rewrite_mov_succ_typenv Hwf) in Hag.
      apply: (SSALite.MA.subset_set_agree _ Hag).
      apply: (SSAVS.Lemmas.subset_trans _ (ssa2lite_spec_vars_subset _)).
      apply: (SSAVS.Lemmas.subset_trans _ (SSALite.vars_rspec_of_spec _)).
      case_if.
      + apply: (SSAVS.Lemmas.subset_trans (vars_rngred_rspec_slice_split_la _ _)).
        rewrite /SSALite.vars_rspec. by SSAVS.Lemmas.dp_subset.
      + apply: (SSAVS.Lemmas.subset_trans (vars_rngred_rspec_split_la _)).
        rewrite /SSALite.vars_rspec. by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma rngred_algsnd_well_formed_bexps o s :
    let fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s) : SSATE.env in
    let rms := rewrite_mov s : SSA.spec in
    let cuts := SSA.cut_spec rms : seq SSA.spec in
    let asserts := tflatten (tmap SSA.extract_asserts cuts) : seq SSA.spec in
    let asserts_ssa := tmap ssa2lite_spec asserts : seq SSALite.spec in
    let nacuts := tmap SSA.remove_asserts cuts : seq SSA.spec in
    let nacuts_ssa := tmap ssa2lite_spec nacuts : seq SSALite.spec in
    let sndconds := tflatten (tmap (algsnd_spec o) nacuts_ssa) : seq QFBV.bexp in
    let rngasserts := tflatten (tmap (rngred_spec o) asserts_ssa) : seq QFBV.bexp in
    let rngpost := tflatten (tmap (rngred_spec o) nacuts_ssa) : seq QFBV.bexp in
    well_formed_ssa_spec s ->
    QFBV.well_formed_bexps (catrev (rev sndconds) (catrev (rev rngasserts) rngpost)) fE.
  Proof.
    move=> fE rms cuts asserts asserts_ssa nacuts nacuts_ssa sndconds rngasserts rngpost Hwf.
    rewrite !catrev_rev. rewrite 2!QFBV.well_formed_bexps_cat.
    apply/andP; split; last (apply/andP; split).
    - rewrite /sndconds. rewrite QFBV.well_formed_bexps_tflatten tmap_map.
      apply/all_forall=> c Hinc. move: (in_map_exists Hinc) => {Hinc} [d [Hind ?]]; subst.
      rewrite /nacuts_ssa tmap_map in Hind. move: (in_map_exists Hind) => {Hind} [c [Hinc ?]]; subst.
      rewrite /nacuts tmap_map in Hinc. move: (in_map_exists Hinc) => {Hinc} [d [Hind ?]]; subst.
      exact: (algsnd_spec_remove_asserts_well_formed_bexps _ Hwf Hind).
    - rewrite /rngasserts. rewrite QFBV.well_formed_bexps_tflatten tmap_map.
      apply/all_forall=> c Hinc. move: (in_map_exists Hinc) => {Hinc} [d [Hind ?]]; subst.
      rewrite /asserts_ssa tmap_map in Hind. move: (in_map_exists Hind) => {Hind} [c [Hinc ?]]; subst.
      rewrite /asserts tmap_map in Hinc. move/in_tflatten: Hinc => [asts [Hinasts Hinc]].
      move: (in_map_exists Hinasts) => {Hinasts} [cut [Hincut ?]]; subst.
      exact: (rngred_spec_extract_asserts_well_formed_bexps _ Hwf Hincut Hinc).
    - rewrite /rngpost. rewrite QFBV.well_formed_bexps_tflatten tmap_map.
      apply/all_forall=> c Hinc. move: (in_map_exists Hinc) => {Hinc} [d [Hind ?]]; subst.
      rewrite /nacuts_ssa tmap_map in Hind. move: (in_map_exists Hind) => {Hind} [c [Hinc ?]]; subst.
      rewrite /nacuts tmap_map in Hinc. move: (in_map_exists Hinc) => {Hinc} [d [Hind ?]]; subst.
      exact: (rngred_spec_remove_asserts_well_formed_bexps _ Hwf Hind).
  Qed.

  Lemma algsnd_extract_asserts s a :
    well_formed_ssa_spec s ->
    SSA.spec_has_no_cut s ->
    ssa_spec_algsnd (SSALite.rspec_of_spec (ssa2lite_spec (SSA.remove_asserts s))) ->
    In a (SSA.extract_asserts s) ->
    ssa_spec_algsnd (SSALite.rspec_of_spec (ssa2lite_spec a)).
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /SSA.well_formed_spec /=.
    move=> H. caseb H. move=> Hwff Hwfp Hwfg HunEp Hssap.
    rewrite /SSA.spec_has_no_cut /=. move=> Hnocp.
    rewrite /ssa_spec_algsnd /=. move=> Has.
    rewrite /SSA.extract_asserts /=. move=> Hina.
    move=> s Hco Hevf.
    rewrite (SSA.extract_asserts_rec_inputs Hina) in Hco.
    rewrite (SSA.extract_asserts_rec_pre Hina) in Hevf.
    move: (Has s Hco Hevf) => {Has}. clear Hwff Hwfg Hwfp HunEp Hssap Hevf Hco g.
    move: Hina Hnocp.
    have: ssa_program_algsnd_at E (SSALite.rng_program (ssa2lite_program [::])) s
      by exact: ssa_program_algsnd_at_nil.
    have: SSA.program_has_no_assert [::] by done.
    rewrite -{2 3}(cat0s p).
    have {3}->: [::] = rev [::] by reflexivity.
    move: [::].
    elim: p a E f s => [| i p IH] a E f s visited //=. rewrite revK.
    move=> Hnav Hsndv.
    case: i; intros;
      try by (rewrite -rev_rcons in Hina; rewrite -cat_rcons in Hnocp Has;
              apply: (IH _ _ _ _ _ _ _ Hina Hnocp Has);
                [ by rewrite SSA.program_has_no_assert_rcons /= Hnav
                | rewrite SSA.remove_asserts_program_cat in Has;
                  rewrite ssa2lite_program_cat in Has;
                  rewrite SSALite.rng_program_cat in Has;
                  (rewrite SSA.no_asserts_remove_asserts in Has; last by
                     (rewrite SSA.program_has_no_assert_rcons Hnav /=));
                  (move/ssa_program_algsnd_at_cat: Has => [Has1 Has2]);
                  exact: Has1 ]).
    (* Iassert *)
    case: (in_inv Hina) => {}Hina.
    - subst; simpl. exact: Hsndv.
    - apply: (IH _ E f s visited Hnav Hsndv Hina).
      + rewrite 2!SSA.program_has_no_cut_cat in Hnocp *. move/andP: Hnocp => [-> Hnocp].
        rewrite SSA.program_has_no_cut_cons in Hnocp. move/andP: Hnocp => [_ ->]. reflexivity.
      + rewrite SSA.remove_asserts_program_cat /= in Has.
        rewrite -SSA.remove_asserts_program_cat in Has. exact: Has.
  Qed.

  Lemma verify_ssa_sound o s :
    SSA.well_formed_ssa_spec s ->
    verify_ssa o s ->
    SSA.valid_spec s.
  Proof.
    move=> Hwf. rewrite /verify_ssa.
    set fE := SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s).
    set rms := rewrite_mov s.
    set cuts := SSA.cut_spec rms.
    set asserts := tflatten (tmap SSA.extract_asserts cuts).
    set asserts_ssa := tmap SSA2SSALite.ssa2lite_spec asserts.
    set nacuts := tmap SSA.remove_asserts cuts.
    set nacuts_ssa := tmap SSA2SSALite.ssa2lite_spec nacuts.
    set sndconds := tflatten (tmap (algsnd_spec o) nacuts_ssa).
    set rngasserts := tflatten (tmap (rngred_spec o) asserts_ssa).
    set rngpost := tflatten (tmap (rngred_spec o) nacuts_ssa).
    set algasserts := tflatten (tmap (algred_spec o) asserts_ssa).
    set algpost := tflatten (tmap (algred_spec o) nacuts_ssa).
    move/andP => [Hrngred Halgred].
    (* rewrite mov statements *)
    apply: (rewrite_mov_sound Hwf).
    move: (rewrite_mov_well_formed_ssa Hwf) => Hwfrw.
    (* cut specification *)
    apply: (SSA.cut_spec_sound
              (SSA.well_formed_spec_prog
                 (SSA.well_formed_ssa_spec_well_formed Hwfrw))).
    rewrite -/cuts.
    (* Each cut is valid *)
    apply/Forall_forall. move=> cut Hincut.
    (* cut is well-formed *)
    move: (cut_spec_well_formed_ssa_in Hwfrw Hincut) => Hwfcut.
    (* well-formed after removing assertions *)
    have Hwfra: SSALite.well_formed_ssa_spec (ssa2lite_spec (SSA.remove_asserts cut)).
    { rewrite (ssa2lite_spec_well_formed_ssa (cut_remove_asserts_is_lite_in Hincut)).
      apply: remove_asserts_well_formed_ssa. assumption. }
    (* QF_BV predicates are well-formed *)
    have Hwfrngred_algsnd:
      QFBV.well_formed_bexps (catrev (rev sndconds) (catrev (rev rngasserts) rngpost)) fE.
    { exact: (rngred_algsnd_well_formed_bexps _ Hwf). }
    (* cut is algebraic sound *)
    have Halgsnd_cut: ssa_spec_algsnd (SSALite.rspec_of_spec (ssa2lite_spec (SSA.remove_asserts cut))).
    { apply: (algsnd_spec_sound Hwfra (o:=o)). simpl.
      rewrite SSALite.rng_program_succ_typenv. rewrite ssa2lite_program_succ_typenv.
      rewrite SSA.remove_asserts_program_succ_typenv.
      rewrite (agree_verify_qfbv_bexps (E2:=fE)).
      - apply: (verify_qfbv_bexps_complete (algsnd_spec_remove_asserts_well_formed_bexps _ Hwf Hincut)).
        move: (verify_qfbv_bexps_sound Hwfrngred_algsnd Hrngred).
        rewrite !catrev_rev. move/QFBV.valid_bexps_cat=> [H _].
        rewrite /sndconds in H. move/QFBV.valid_bexps_tflatten: H => H.
        apply: H. apply/in_In. apply: in_tmap. apply: in_tmap.
        apply: in_tmap. exact: Hincut.
      - move: (cut_spec_agree_in Hwfrw Hincut) => Hag.
        rewrite (rewrite_mov_succ_typenv Hwf) in Hag.
        apply: (SSA.MA.subset_set_agree _ Hag).
        apply: (SSAVS.Lemmas.subset_trans (algsnd_spec_vars_subset _ _)).
        apply: (SSAVS.Lemmas.subset_trans (ssa2lite_spec_vars_subset _)).
        exact: SSA.remove_asserts_vars_subset. }
    apply: SSA.extract_asserts_sound.
    - (* The postcondition of a cut is valid *)
      apply: ssa2lite_spec_sound.
      + (* The specification is lite after cutting and removing asserts *)
        move: (cut_remove_asserts_is_lite rms). move/all_forall. apply.
        rewrite tmap_map. apply: in_map. exact: Hincut.
      + apply: (algred_spec_sound Hwfra Halgsnd_cut (o:=o)).
        * (* Range postcondition *)
          apply: (rngred_spec_sound Hwfra (o:=o)).
          rewrite SSALite.rng_program_succ_typenv. rewrite ssa2lite_program_succ_typenv.
          rewrite SSA.remove_asserts_program_succ_typenv.
          rewrite (agree_verify_qfbv_bexps (E2:=fE)).
          -- apply: (verify_qfbv_bexps_complete (rngred_spec_remove_asserts_well_formed_bexps _ Hwf Hincut)).
             move: (verify_qfbv_bexps_sound Hwfrngred_algsnd Hrngred).
             rewrite !catrev_rev. move/QFBV.valid_bexps_cat=> [_ /QFBV.valid_bexps_cat [_ H]].
             rewrite /rngpost in H. move/QFBV.valid_bexps_tflatten: H => H.
             apply: H. apply/in_In. apply: in_tmap. apply: in_tmap.
             apply: in_tmap. exact: Hincut.
          -- move: (cut_spec_agree_in Hwfrw Hincut) => Hag.
             rewrite (rewrite_mov_succ_typenv Hwf) in Hag.
             apply: (SSA.MA.subset_set_agree _ Hag).
             apply: (SSAVS.Lemmas.subset_trans (rngred_spec_vars_subset _ _)).
             apply: (SSAVS.Lemmas.subset_trans (ssa2lite_spec_vars_subset _)).
             exact: SSA.remove_asserts_vars_subset.
        * (* Algebraic postcondition *)
          apply: (verify_reps_sound (o:=o)).
          rewrite catrev_rev in Halgred. rewrite verify_reps_cat in Halgred.
          move/andP: Halgred => [Halgassert Halgpost].
          rewrite /algpost in Halgpost.
          rewrite verify_reps_tflatten in Halgpost.
          move/all_forall: Halgpost => Halgpost. apply: Halgpost.
          apply: in_tmap. apply: in_tmap. apply: in_tmap. assumption.
    - (* The assertions of a cut are all valid *)
      apply/Forall_forall => noca Hinoca. apply: ssa2lite_spec_sound.
      + (* The extracted specification for assertions is lite *)
        move/all_forall: (cut_extract_asserts_ls_lite rms). apply.
        exact: (in_tflatten_tmap Hincut Hinoca).
      + (* The extracted specification for assertions is valid *)
        have Hwfnoca: SSALite.well_formed_ssa_spec (ssa2lite_spec noca).
        { rewrite (ssa2lite_spec_well_formed_ssa (cut_extract_asserts_ls_lite_in Hincut Hinoca)).
          apply: (extract_asserts_well_formed_ssa_in _ Hinoca).
          exact: Hwfcut. }
        apply: (algred_spec_sound Hwfnoca (o:=o)).
        * (* Algebraic soundness of assertion specifications *)
          exact: (algsnd_extract_asserts
                    Hwfcut (SSA.cut_spec_has_no_cut_in Hincut) Halgsnd_cut Hinoca).
        * (* Range reduction of assertion specifications *)
          apply: (rngred_spec_sound Hwfnoca (o:=o)).
          rewrite SSALite.rng_program_succ_typenv. rewrite ssa2lite_program_succ_typenv.
          rewrite (agree_verify_qfbv_bexps (E2:=fE)).
          -- apply: (verify_qfbv_bexps_complete (rngred_spec_extract_asserts_well_formed_bexps _ Hwf Hincut Hinoca)).
             move: (verify_qfbv_bexps_sound Hwfrngred_algsnd Hrngred).
             rewrite !catrev_rev. move/QFBV.valid_bexps_cat=> [_ /QFBV.valid_bexps_cat [H _]].
             rewrite /rngasserts in H. move/QFBV.valid_bexps_tflatten: H => H.
             apply: H. apply/in_In. apply: in_tmap. apply: in_tmap.
             exact: (in_tflatten_tmap Hincut Hinoca).
          -- move: (extract_asserts_agree_in Hwfcut Hinoca). simpl => Hag1.
             move: (cut_spec_agree_in Hwfrw Hincut) => Hag2.
             move: (SSA.MA.subset_set_agree (SSA.extract_asserts_vars_subset Hinoca) Hag2) => {}Hag2.
             move: (SSA.MA.agree_trans Hag1 Hag2) =>{Hag1 Hag2}.
             rewrite (rewrite_mov_succ_typenv Hwf).
             apply: SSA.MA.subset_set_agree.
             apply: (SSAVS.Lemmas.subset_trans (rngred_spec_vars_subset _ _)).
             apply: (SSAVS.Lemmas.subset_trans (ssa2lite_spec_vars_subset _)).
             exact: SSAVS.Lemmas.subset_refl.
        * (* Algebraic reduction of assertion specifications *)
          apply: (verify_reps_sound (o:=o)).
          rewrite catrev_rev in Halgred. rewrite verify_reps_cat in Halgred.
          move/andP: Halgred => [Halgassert Halgpost].
          rewrite /algasserts in Halgassert.
          rewrite verify_reps_tflatten in Halgassert.
          move/all_forall: Halgassert => Halgassert. apply: Halgassert.
          apply: in_tmap. apply: in_tmap.
          exact: (in_tflatten_tmap Hincut Hinoca).
  Qed.

  Lemma verify_dsl_sound o s :
    DSL.well_formed_spec s ->
    verify_dsl o s ->
    DSL.valid_spec s.
  Proof.
    move=> Hwf Hv. apply: SSA.ssa_spec_sound.
    exact: (verify_ssa_sound (ssa_spec_well_formed Hwf) Hv).
  Qed.

End Verification.
