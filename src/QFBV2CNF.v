
(** Bit blast SMT QF_BV queries to CNF. *)

From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import EqVar Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv CNF.
From BBCache Require Import Cache BitBlastingInit BitBlastingCacheDef BitBlastingCache.
From BBCache Require Import CacheHash BitBlastingCacheHash.
From Cryptoline Require Import Options SSALite SSA2ZSSA SSA2QFBV.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section QFBV2CNF.

  Import SSALite.
  Import QFBV.

  Lemma wf_conform_exp E e s :
    QFBV.well_formed_exp e E ->
    SSAStore.conform s E ->
    AdhereConform.conform_exp e s E
  with wf_conform_bexp E e s :
    QFBV.well_formed_bexp e E ->
    SSAStore.conform s E ->
    AdhereConform.conform_bexp e s E.
  Proof.
    (* wf_conform_exp *)
    case: e => //=.
    - move=> v Hmem Hco. apply/eqP. exact: (Hco v Hmem).
    - move=> op e Hwf Hco. exact: (wf_conform_exp _ _ _ Hwf Hco).
    - move=> op e1 e2 /andP [/andP [/andP [Hwf1 Hwf2] Hw] Hs] Hco.
      by rewrite (wf_conform_exp _ _ _ Hwf1 Hco) (wf_conform_exp _ _ _ Hwf2 Hco).
    - move=> c e1 e2 /andP [/andP [/andP [Hwfb Hwf1] Hwf2] Hs] Hco.
        by rewrite (wf_conform_bexp _ _ _ Hwfb Hco)
                   (wf_conform_exp _ _ _ Hwf1 Hco) (wf_conform_exp _ _ _ Hwf2 Hco).
    (* wf_conform_bexp *)
    case: e => //=.
    - move=> op e1 e2 /andP [/andP [Hwf1 Hwf2] _] Hco.
      by rewrite (wf_conform_exp _ _ _ Hwf1 Hco) (wf_conform_exp _ _ _ Hwf2 Hco).
    - move=> e Hwf Hco. exact: (wf_conform_bexp _ _ _ Hwf Hco).
    - move=> e1 e2 /andP [Hwf1 Hwf2] Hco.
        by rewrite (wf_conform_bexp _ _ _ Hwf1 Hco) (wf_conform_bexp _ _ _ Hwf2 Hco).
    - move=> e1 e2 /andP [Hwf1 Hwf2] Hco.
        by rewrite (wf_conform_bexp _ _ _ Hwf1 Hco) (wf_conform_bexp _ _ _ Hwf2 Hco).
  Qed.

  Lemma wf_conform_bexps E es s :
    QFBV.well_formed_bexps es E ->
    SSAStore.conform s E ->
    AdhereConform.conform_bexps es s E.
  Proof.
    elim: es => [| e es IH] //=. move/andP=> [Hwf_e Hwf_es] Hco.
    rewrite (wf_conform_bexp Hwf_e Hco) (IH Hwf_es Hco). exact: is_true_true.
  Qed.

  Lemma force_conform_eval_exp E vs s e :
    SSAVS.Lemmas.disjoint vs (vars_exp e) ->
    QFBV.eval_exp e s =
    QFBV.eval_exp e (force_conform_vars E (SSAVS.elements vs) s)
  with force_conform_eval_bexp E vs s e :
         SSAVS.Lemmas.disjoint vs (vars_bexp e) ->
         QFBV.eval_bexp e s =
         QFBV.eval_bexp e (force_conform_vars E (SSAVS.elements vs) s).
  Proof.
    (* force_conform_eval_exp *)
    case: e => //=.
    - move=> v. rewrite SSAVS.Lemmas.disjoint_singleton.
      move=> Hnotin. rewrite force_conform_vars_notin; first reflexivity.
      apply/negP => H. move/negP: Hnotin. apply.
      exact: (SSAVS.Lemmas.in_elements_mem H).
    - move=> op e Hdisj. rewrite (force_conform_eval_exp E _ _ _ Hdisj).
      reflexivity.
    - move=> op e1 e2. rewrite SSAVS.Lemmas.disjoint_union.
      move/andP=> [Hdisj1 Hdisj2]. rewrite (force_conform_eval_exp E _ _ _ Hdisj1)
                                           (force_conform_eval_exp E _ _ _ Hdisj2).
      reflexivity.
    - move=> b e1 e2. rewrite !SSAVS.Lemmas.disjoint_union.
      move/andP=> [Hdisj /andP [Hdisj1 Hdisj2]].
      rewrite (force_conform_eval_bexp E _ _ _ Hdisj)
              (force_conform_eval_exp E _ _ _ Hdisj1)
              (force_conform_eval_exp E _ _ _ Hdisj2). reflexivity.
    (* force_conform_eval_bexp *)
    case: e => //=.
    - move=> op e1 e2. rewrite SSAVS.Lemmas.disjoint_union.
      move/andP=> [Hdisj1 Hdisj2]. rewrite (force_conform_eval_exp E _ _ _ Hdisj1)
                                           (force_conform_eval_exp E _ _ _ Hdisj2).
      reflexivity.
    - move=> e Hdisj. rewrite (force_conform_eval_bexp E _ _ _ Hdisj). reflexivity.
    - move=> e1 e2. rewrite SSAVS.Lemmas.disjoint_union.
      move/andP=> [Hdisj1 Hdisj2]. rewrite (force_conform_eval_bexp E _ _ _ Hdisj1)
                                           (force_conform_eval_bexp E _ _ _ Hdisj2).
      reflexivity.
    - move=> e1 e2. rewrite SSAVS.Lemmas.disjoint_union.
      move/andP=> [Hdisj1 Hdisj2]. rewrite (force_conform_eval_bexp E _ _ _ Hdisj1)
                                           (force_conform_eval_bexp E _ _ _ Hdisj2).
      reflexivity.
  Qed.

  Lemma conform_exp_force_conform E s e :
    AdhereConform.conform_exp e s E ->
    SSAStore.conform
      (force_conform_vars E (SSAVS.elements (SSAVS.diff (vars_env E) (vars_exp e))) s)
      E.
  Proof.
    move=> Hco. apply: SSAStore.conform_def. move=> v Hmem.
    case H: (v \in (SSAVS.elements (SSAVS.diff (vars_env E) (vars_exp e)))).
    - rewrite (force_conform_vars_in E s H). rewrite size_zeros. reflexivity.
    - move/idP/negP: H => H. rewrite (force_conform_vars_notin E s H).
      rewrite -VSLemmas.mem_in in H. rewrite SSALite.VSLemmas.diff_b in H.
      rewrite negb_and Bool.negb_involutive in H. move/memenvP: Hmem => Hmem.
      rewrite Hmem /= in H. rewrite (AdhereConform.conform_exp_mem Hco H).
      reflexivity.
  Qed.

  Lemma conform_bexp_force_conform E s e :
    AdhereConform.conform_bexp e s E ->
    SSAStore.conform
      (force_conform_vars E (SSAVS.elements (SSAVS.diff (vars_env E) (vars_bexp e))) s)
      E.
  Proof.
    move=> Hco. apply: SSAStore.conform_def. move=> v Hmem.
    case H: (v \in (SSAVS.elements (SSAVS.diff (vars_env E) (vars_bexp e)))).
    - rewrite (force_conform_vars_in E s H). rewrite size_zeros. reflexivity.
    - move/idP/negP: H => H. rewrite (force_conform_vars_notin E s H).
      rewrite -VSLemmas.mem_in in H. rewrite SSALite.VSLemmas.diff_b in H.
      rewrite negb_and Bool.negb_involutive in H. move/memenvP: Hmem => Hmem.
      rewrite Hmem /= in H. rewrite (AdhereConform.conform_bexp_mem Hco H).
      reflexivity.
  Qed.


  (* Bit-blast range spec and safety conditions *)

  Fixpoint bb_hbexps_cache E (es : seq QFBVHash.hbexp) :=
    match es with
    | [::] => (init_vm, init_hcache, init_gen, [::])
    | e :: es' =>
      let '(m, c, g, cnfs) := bb_hbexps_cache E es' in
      let '(m', c', g', cs, lr) := bit_blast_bexp_hcache_tflatten
                                     E m (CacheHash.reset_ct c) g e in
      (m', c', g', (CNF.add_prelude ([::CNF.neg_lit lr]::cs))::cnfs)
    end.

  Definition valid_bb_bexps_cache E (es : seq QFBV.bexp) :=
    forall m c g cnfs cnf,
      bb_hbexps_cache E (map QFBVHash.hash_bexp es) = (m, c, g, cnfs) ->
      (cnf \in cnfs) ->
      ~ (CNF.sat cnf).

  Lemma agree_bb_hbexps_cache E1 E2 es :
    SSALite.MA.agree (QFBV.vars_bexps es) E1 E2 ->
    bb_hbexps_cache E1 (tmap QFBVHash.hash_bexp es) = bb_hbexps_cache E2 (tmap QFBVHash.hash_bexp es).
  Proof.
    elim: es => [| e es IH] //=. move=> Hag.
    rewrite tmap_map /=. rewrite -tmap_map.
    rewrite (IH (SSALite.MA.agree_union_set_r Hag)).
    dcase (bb_hbexps_cache E2 (tmap QFBVHash.hash_bexp es)) => [[[[mes ces] ges] cnfses] Hes].
    move: (SSALite.MA.agree_union_set_l Hag).
    rewrite -{1}(QFBVHash.unhash_hash_bexp e) => Hage.
    rewrite (agree_bit_blast_bexp_hcache_tflatten _ _ _ Hage).
    reflexivity.
  Qed.

  Lemma bb_hbexps_cache_bit_blast_bexps_hcache_eq E es m1 c1 g1 cnfs m2 c2 g2 cs lr :
    bb_hbexps_cache E es = (m1, c1, g1, cnfs) ->
    bit_blast_hbexps_hcache E es = (m2, c2, g2, cs, lr) ->
    m1 = m2 /\ c1 = c2 /\ g1 = g2.
  Proof.
    elim: es m1 c1 g1 cnfs m2 c2 g2 cs lr =>
    [| e es IH] m1 c1 g1 cnfs m2 c2 g2 cs lr /=.
    - case=> ? ? ? ?; subst. case=> ? ? ? ? ?; subst. done.
    - dcase (bb_hbexps_cache E es) => [[[[m1' c1'] g1'] cnfs'] Hbb_es].
      dcase (bit_blast_hbexps_hcache E es) => [[[[[m2' c2'] g2'] cs'] lr'] Hhbb_es].
      dcase (bit_blast_bexp_hcache_tflatten E m1' (CacheHash.reset_ct c1') g1' e) =>
      [[[[[em ec] eg] ecs] elr] Hbb_e].
      case=> ? ? ? ?; subst. move=> Hhbb_e.
      move: (IH _ _ _ _ _ _ _ _ _ Hbb_es Hhbb_es) => [? [? ?]]; subst.
      rewrite Hhbb_e in Hbb_e. case: Hbb_e => ? ? ? ? ?; subst. done.
  Qed.

  Lemma bb_hbexps_cache_bit_blast_bexps_hcache_exists E es m c g cnfs :
    bb_hbexps_cache E es = (m, c, g, cnfs) ->
    exists cs, exists lr,
        bit_blast_hbexps_hcache E es = (m, c, g, cs, lr).
  Proof.
    elim: es m c g cnfs => [| e es IH] m c g cnfs /=.
    - case=> ? ? ? ?; subst. exists (add_prelude [::]). exists lit_tt. done.
    - dcase (bb_hbexps_cache E es) => [[[[m1 c1] g1] cnfs1] Hbb_es].
      rewrite /bit_blast_bexp_hcache_tflatten.
      dcase (bit_blast_bexp_hcache E m1 (CacheHash.reset_ct c1) g1 e)
      => [[[[[m2 c2] g2] cs] lr] Hbb_e]. case=> ? ? ? ?; subst.
      move: (IH _ _ _ _ Hbb_es) => [cs1 [lr1 Hhbb_es]]. rewrite Hhbb_es.
      rewrite Hbb_e. exists (tflatten cs). exists lr. done.
  Qed.

  Lemma bb_hbexps_cache_sound E es :
    QFBV.well_formed_bexps es E -> valid_bb_bexps_cache E es ->
    valid_bexps E es.
  Proof.
    rewrite /valid_bb_bexps_cache. rewrite /valid_bexps.
    elim: es => [| e es IH] Hwf //=.
    dcase (bb_hbexps_cache E (map QFBVHash.hash_bexp es)) =>
    [[[[m ec] g] cnfs] Hbbe_es].
    dcase (bit_blast_bexp_hcache_tflatten
             E m (CacheHash.reset_ct ec) g (QFBVHash.hash_bexp e)) =>
    [[[[[m' ec'] g'] cs] lr] Hbbe_e]. move=> H.
    move: (H m' ec' g' (add_prelude ([:: neg_lit lr] :: cs) :: cnfs)) =>
          {H} H. move=> s Hco. apply/andP; split.
    - apply: (@bit_blast_bexps_hcache_sound e es E m' ec' g' cs lr).
      + dcase (bit_blast_bexps_hcache E es) => [[[[[m0 c0] g0] cs0] lr0] Hb_es].
        rewrite /bit_blast_bexps_hcache in Hb_es.
        move: (bb_hbexps_cache_bit_blast_bexps_hcache_eq Hbbe_es Hb_es) =>
        [? [? ?]]; subst.
        rewrite /bit_blast_bexps_hcache /=. rewrite Hb_es. rewrite Hbbe_e.
        reflexivity.
      + exact: Hwf.
      + apply: (H _ (Logic.eq_refl _)). exact: mem_head.
      + exact: (wf_conform_bexps Hwf Hco).
    - rewrite well_formed_bexps_cons in Hwf. move/andP: Hwf=> [Hwf_e Hwf_es].
      apply: (IH Hwf_es _ _ Hco). move=> m0 c0 g0 cnfs0 cnf0 Hbb_es0 Hin0.
      apply: (H cnf0 (Logic.eq_refl _)). rewrite Hbbe_es in Hbb_es0.
      case: Hbb_es0 => ? ? ? ?; subst. by rewrite in_cons Hin0 orbT.
  Qed.

  Lemma bb_hbexps_cache_complete E es :
    QFBV.well_formed_bexps es E -> valid_bexps E es ->
    valid_bb_bexps_cache E es.
  Proof.
    rewrite /valid_bb_bexps_cache. rewrite /valid_bexps.
    elim: es => [| e es IH] Hwf //=.
    - move=> He m c g cnfs cnf. case=> ? ? ? ?; subst. move=> H; by inversion H.
    - move=> He m c g cnfs cnf.
      dcase (bb_hbexps_cache E (map QFBVHash.hash_bexp es)) =>
             [[[[m1 c1] g1] cnfs1] Hbb_es].
      dcase (bit_blast_bexp_hcache_tflatten
               E m1 (CacheHash.reset_ct c1) g1 (QFBVHash.hash_bexp e))
      => [[[[[m2 c2] g2] cs2] lr2] Hbb_e].
      case=> ? ? ? ?; subst. move=> Hin. rewrite in_cons in Hin.
      case/orP: Hin => Hin.
      + rewrite (eqP Hin). apply: (bit_blast_bexps_hcache_complete _ Hwf).
        * rewrite /=. move: (bb_hbexps_cache_bit_blast_bexps_hcache_exists Hbb_es)
                      => [cs [lr Hb_es]].
          rewrite /bit_blast_bexps_hcache /=.
          rewrite Hb_es. exact: Hbb_e.
        * move=> s Hco. move/andP: Hco=> [Hco _].
          rewrite (force_conform_eval_bexp E _ (SSAVS.Lemmas.disjoint_diff
                                                  (vars_env E)
                                                  (vars_bexp e))).
          move: (He _ (conform_bexp_force_conform Hco)) => /andP [H _]. exact: H.
      + move/andP: Hwf=> [Hwf_e Hwf_es].
        apply: (IH Hwf_es _ _ _ _ _ _ Hbb_es Hin).
        move=> s Hco. move: (He _ Hco) => /andP [_ H]. exact: H.
  Qed.

  Lemma bb_hbexps_cache_eqvalid E es1 es2 :
    well_formed_bexps es1 E -> well_formed_bexps es2 E ->
    (valid_bexps E es1 <-> valid_bexps E es2) <->
    (valid_bb_bexps_cache E es1 <-> valid_bb_bexps_cache E es2).
  Proof.
    move=> Hwf1 Hwf2. split; move=> [H1 H2]; split; move=> H3.
    - apply: (bb_hbexps_cache_complete Hwf2). apply: H1.
      apply: (bb_hbexps_cache_sound Hwf1). assumption.
    - apply: (bb_hbexps_cache_complete Hwf1). apply: H2.
      apply: (bb_hbexps_cache_sound Hwf2). assumption.
    - apply: (bb_hbexps_cache_sound Hwf2). apply: H1.
      apply: (bb_hbexps_cache_complete Hwf1). assumption.
    - apply: (bb_hbexps_cache_sound Hwf1). apply: H2.
      apply: (bb_hbexps_cache_complete Hwf2). assumption.
  Qed.


  (* Simplify a sequence of QF_BV expressions *)

  Definition simplify_bexps (es : seq QFBV.bexp) :=
    tmap QFBV.simplify_bexp2 es.


  Lemma vars_simplify_bexps es :
    SSAVS.subset (QFBV.vars_bexps (simplify_bexps es)) (QFBV.vars_bexps es).
  Proof.
    elim: es => [| e es IH] //=. rewrite /simplify_bexps tmap_map /=.
    rewrite -tmap_map -/(simplify_bexps es). move: (QFBV.vars_simplify_bexp2 e) => H.
    by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma simplify_bexps_well_formed E es :
    well_formed_bexps es E -> well_formed_bexps (simplify_bexps es) E.
  Proof.
    rewrite /simplify_bexps tmap_map. elim: es => [| e es IH] //=.
    move/andP=> [He Hes]. rewrite (simplify_bexp2_well_formed He) /=. exact: (IH Hes).
  Qed.

  Lemma simplify_bexps_valid E es :
    valid_bexps E es <-> valid_bexps E (simplify_bexps es).
  Proof.
    rewrite /simplify_bexps tmap_map. elim: es => [| e es [IH1 IH2]] //=. split.
    - rewrite !valid_bexps_cons. move => [He Hes]. split.
      + apply/simplify_bexp2_eqvalid. assumption.
      + exact: (IH1 Hes).
    - rewrite !valid_bexps_cons. move=> [He Hes]. split.
      + apply/simplify_bexp2_eqvalid. assumption.
      + exact: (IH2 Hes).
  Qed.

  Lemma simplify_bexps_eqvalid E es1 es2 :
    valid_bexps E es1 <-> valid_bexps E es2 ->
    valid_bexps E (simplify_bexps es1) <-> valid_bexps E (simplify_bexps es2).
  Proof.
    move=> [H1 H2]. split=> H.
    - apply/(simplify_bexps_valid _ es2). apply: H1.
      apply/simplify_bexps_valid. assumption.
    - apply/(simplify_bexps_valid _ es1). apply: H2.
      apply/simplify_bexps_valid. assumption.
  Qed.


  (* Remove QFBV formulas that are trivially true *)

  Definition bexp_is_not_true e :=
    match e with
    | Btrue => false
    | _ => true
    end.

  Definition filter_not_true es := tfilter bexp_is_not_true es.

  Lemma vars_filter_not_true es :
    SSAVS.Equal (QFBV.vars_bexps (filter_not_true es)) (QFBV.vars_bexps es).
  Proof.
    elim: es => [| e es IH] //=.
    rewrite /filter_not_true /=. rewrite tfilter_cons. case_if.
    - rewrite -/(filter_not_true es). rewrite vars_bexps_rcons.
      rewrite IH. rewrite SSAVS.Lemmas.P.union_sym. reflexivity.
    - rewrite IH. by case: e H => //.
  Qed.

  Lemma bexp_is_true_valid E e : bexp_is_not_true e = false -> valid_bexp E e.
  Proof. by case: e => //=. Qed.

  Lemma bexp_is_true_well_formed E e : bexp_is_not_true e = false -> well_formed_bexp e E.
  Proof. by case: e => //=. Qed.

  Lemma filter_not_true_valid E es :
    valid_bexps E (filter_not_true es) <-> valid_bexps E es.
  Proof.
    rewrite /filter_not_true. elim: es => [| e es [IH1 IH2]] /=.
    - rewrite tfilter_nil. tauto.
    - rewrite tfilter_cons. case He: (bexp_is_not_true e).
      + rewrite valid_bexps_rcons valid_bexps_cons. tauto.
      + rewrite valid_bexps_cons. move: (@bexp_is_true_valid E e He). tauto.
  Qed.

  Lemma filter_not_true_well_formed E es :
    well_formed_bexps (filter_not_true es) E <-> well_formed_bexps es E.
  Proof.
    elim: es => [| e es [IH1 IH2]] //=. rewrite /filter_not_true. rewrite tfilter_cons.
    case He: (bexp_is_not_true e).
    - rewrite well_formed_bexps_rcons. split; move/andP => [H1 H2]; apply/andP; tauto.
    - move: (bexp_is_true_well_formed E He) => Hwfe.
      split; [ move=> H; apply/andP | move/andP => [H1 H2] ]; tauto.
  Qed.


  (* Apply range reduction, convert algebraic soundness conditions to QF_BV predicates, and
     bit-blast QF_BV predicates *)

  Definition bb_rngred_algsnd (o : options) (s : rspec) : seq QFBV.bexp :=
    filter_not_true
      (simplify_bexps
         (if apply_slicing_rspec o then rngred_algsnd_slice_split_la o s
          else rngred_algsnd_split_la s)).

  Lemma bb_rngred_algsnd_well_formed o s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    well_formed_bexps (bb_rngred_algsnd o s) fE.
  Proof.
    move=> fE Hwf. rewrite /bb_rngred_algsnd. rewrite filter_not_true_well_formed.
    apply: simplify_bexps_well_formed. case: (apply_slicing_rspec o).
    - exact: rngred_algsnd_slice_split_la_well_formed.
    - exact: rngred_algsnd_split_la_well_formed.
  Qed.

  Theorem bb_rngred_algsnd_sound o s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    is_rng_rspec s ->
    well_formed_ssa_rspec s ->
    valid_bb_bexps_cache fE (bb_rngred_algsnd o s) ->
    valid_rspec s /\ ssa_spec_algsnd s.
  Proof.
    move=> fE Hrng Hwf Hbb. case Hs: (apply_slicing_rspec o).
    - apply: (rngred_algsnd_slice_split_la_sound Hrng Hwf).
      move: (bb_hbexps_cache_sound (bb_rngred_algsnd_well_formed o Hwf) Hbb).
      rewrite /bb_rngred_algsnd. move/filter_not_true_valid.
      rewrite -simplify_bexps_valid. rewrite Hs. by apply.
    - apply: (rngred_algsnd_split_la_sound Hwf).
      move: (bb_hbexps_cache_sound (bb_rngred_algsnd_well_formed o Hwf) Hbb).
      rewrite /bb_rngred_algsnd. move/filter_not_true_valid.
      rewrite -simplify_bexps_valid. rewrite Hs. by apply.
  Qed.

  Theorem bb_rngred_algsnd_complete o s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    apply_slicing_rspec o = false ->
    is_rng_rspec s ->
    well_formed_ssa_rspec s ->
    valid_rspec s -> ssa_spec_algsnd s ->
    valid_bb_bexps_cache fE (bb_rngred_algsnd o s).
  Proof.
    move=> fE Ho Hrs Hwf Hrng Hsafe. move: (bb_rngred_algsnd_well_formed o Hwf).
    rewrite /bb_rngred_algsnd Ho => Hwfes. apply: (bb_hbexps_cache_complete Hwfes).
    rewrite /bb_rngred_algsnd. apply/filter_not_true_valid.
    rewrite -simplify_bexps_valid. exact: (rngred_algsnd_split_la_complete Hrs Hwf Hrng Hsafe).
  Qed.

End QFBV2CNF.
