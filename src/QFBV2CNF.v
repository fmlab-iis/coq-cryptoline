
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv CNF.
From BBCache Require Import Cache BitBlastingInit BitBlastingCacheDef BitBlastingCache.
From Cryptoline Require Import SSA SSA2ZSSA SSA2QFBV.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section QFBV2CNF.

  Import SSA.
  Import QFBV.


  (* The single QFBV expression for range spec is qfbv_bexp_spec *)

  Local Notation qfbv_spec_range := qfbv_bexp_spec.


  (* Construct QFBV expressions for safety conditions *)

  Fixpoint qfbv_spec_safety_rec f es :=
    match es with
    | [::] => [::]
    | (pre_es, safe)::tl =>
      (qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe)::(qfbv_spec_safety_rec f tl)
    end.

  Definition qfbv_spec_safety (s : spec) : seq QFBV.bexp :=
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    qfbv_spec_safety_rec (bexp_rbexp (rng_bexp (spre s)))
                         (bexp_program_safe_split_fixed_final fE (sprog s)).

  Definition valid_qfbv_spec_safety (s : spec) : Prop :=
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    forall e, (e \in qfbv_spec_safety s) ->
              QFBV.valid fE e.

  Lemma qfbv_spec_safety_rec_format E f p e :
    (e \in (qfbv_spec_safety_rec
              f
              (bexp_program_safe_split_fixed_final E p))) ->
    exists pre_es, exists safe,
        e = qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe.
  Proof.
    rewrite /bexp_program_safe_split_fixed_final. move: [::].
    elim: p e => [| i p IH] e //=. move=> pre_es'. rewrite in_cons. case/orP=> Hin.
    - exists pre_es'; exists (bexp_instr_safe E i). exact: (eqP Hin).
    - apply: IH. exact: Hin.
  Qed.

  Lemma qfbv_spec_safety_rec_in E f p pre_es safe:
    ((qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe) \in
        (qfbv_spec_safety_rec
           f
           (bexp_program_safe_split_fixed_final E p)))
    <->
    ((pre_es, safe) \in (bexp_program_safe_split_fixed_final E p)).
  Proof.
    rewrite /bexp_program_safe_split_fixed_final. move: [::].
    elim: p pre_es safe => [| i p IH] pre_es safe pre_es' //=. split.
    - rewrite in_cons. case/orP=> Hin.
      + rewrite in_cons. case: (eqP Hin). move=> H ->.
        rewrite (qfbv_conjs_inj H). rewrite eqxx /=. reflexivity.
      + apply/orP; right. apply/IH. assumption.
    - rewrite in_cons. case/orP=> Hin.
      + case: (eqP Hin)=> -> ->. exact: mem_head.
      + apply/orP; right. apply/IH. assumption.
  Qed.

  Lemma qfbv_spec_safety_sound s :
    well_formed_ssa_spec s ->
    valid_qfbv_spec_safety s -> ssa_spec_safe s.
  Proof.
    move=> Hwf Hq. apply: (ssa_spec_safe_final_init Hwf).
    apply: (ssa_spec_safe_qfbv_fixed_final_sound Hwf).
    move: Hwf Hq. rewrite /valid_qfbv_spec_safety /ssa_spec_safe_qfbv_fixed_final.
    rewrite /qfbv_spec_safety. case: s => [E f p g] /=.
    move=> Hwf Hq. move: (well_formed_ssa_spec_program Hwf) => /= Hwf_ssa_Ep.
    apply: (bexp_program_safe_split_fixed_final_sound Hwf_ssa_Ep).
    move=> pre_es safe Hin s Hco. apply: (Hq _ _ _ Hco).
    apply/qfbv_spec_safety_rec_in. assumption.
  Qed.

  Lemma qfbv_spec_safety_complete s :
    well_formed_ssa_spec s ->
    ssa_spec_safe s -> valid_qfbv_spec_safety s.
  Proof.
    move=> Hwf Hq. move: (ssa_spec_safe_init_final Hwf Hq) => {Hq} Hq.
    move: (ssa_spec_safe_qfbv_fixed_final_complete Hwf Hq) => {Hq} Hq.
    move: Hwf Hq. rewrite /valid_qfbv_spec_safety /ssa_spec_safe_qfbv_fixed_final.
    rewrite /qfbv_spec_safety. case: s => [E f p g] /=.
    move=> Hwf Hq. move: (well_formed_ssa_spec_program Hwf) => /= Hwf_ssa_Ep.
    move: (bexp_program_safe_split_fixed_final_complete Hwf_ssa_Ep Hq) => {Hq} Hq.
    move=> e Hin s Hco. move: (qfbv_spec_safety_rec_format Hin) => [pre_es [safe He]].
    rewrite He in Hin *. apply: (Hq _ _ _ _ Hco).
    apply/qfbv_spec_safety_rec_in. exact: Hin.
  Qed.

  Lemma qfbv_spec_safety_well_formed s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    well_formed_bexps (qfbv_spec_safety s) fE.
  Proof.
    move=> fE.
    have H1:
      (forall e, (e \in qfbv_spec_safety s) -> well_formed_bexp e fE) ->
      well_formed_bexps (qfbv_spec_safety s) fE.
    { move: fE. move: (qfbv_spec_safety s) => {s}. elim => [| e es IH] //=.
      move=> E H. rewrite (H e) /=.
      - rewrite IH; first exact: is_true_true.
        move=> e' Hin'. apply: H. by rewrite in_cons Hin' orbT.
      - exact: mem_head. }
    move=> Hwf_s. apply: H1.
    move=> e Hin. move: (qfbv_spec_safety_rec_format Hin) => [pre_es [safe He]].
    rewrite He in Hin * => {He}. move/qfbv_spec_safety_rec_in: Hin => Hin.
    move/andP: Hwf_s => [/andP [Hwf_s Hun] Hssa_p].
    move/andP: Hwf_s => [/andP [Hwf_f Hwf_p] Hwf_g].
    apply: (bexp_program_safe_split_fixed_final_cond_well_formed
              (well_formed_rng_bexp Hwf_f) _ Hin).
    rewrite /well_formed_ssa_program. by rewrite Hwf_p Hun Hssa_p.
  Qed.


  (* Bit-blast range spec and safety conditions *)

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
    - move=> op e1 e2 /andP [/andP [Hwf1 Hwf2] Hs] Hco.
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


  Fixpoint bb_bexps_cache E (es : seq QFBV.bexp) :=
    match es with
    | [::] => (init_vm, init_cache, init_gen, [::])
    | e :: es' =>
      let '(m, c, g, cnfs) := bb_bexps_cache E es' in
      let '(m', c', g', cs, lr) := bit_blast_bexp_cache E m (Cache.reset_ct c) g e in
      (m', c', g', (CNF.add_prelude ([::CNF.neg_lit lr]::cs))::cnfs)
    end.

  Definition valid_bb_bexps_cache E es :=
    forall m c g cnfs cnf,
      bb_bexps_cache E es = (m, c, g, cnfs) ->
      (cnf \in cnfs) ->
      ~ (CNF.sat cnf).

  Lemma bb_bexps_cache_bit_blast_bexps_cache_eq E es m1 c1 g1 cnfs m2 c2 g2 cs lr :
    bb_bexps_cache E es = (m1, c1, g1, cnfs) ->
    bit_blast_bexps_cache E es = (m2, c2, g2, cs, lr) ->
    m1 = m2 /\ c1 = c2 /\ g1 = g2.
  Proof.
    elim: es m1 c1 g1 cnfs m2 c2 g2 cs lr =>
    [| e es IH] m1 c1 g1 cnfs m2 c2 g2 cs lr /=.
    - case=> <- <- <- _. case=> <- <- <- _ _. done.
    - dcase (bb_bexps_cache E es) => [[[[m1' c1'] g1'] cnfs'] Hbb_es].
      dcase (bit_blast_bexps_cache E es) => [[[[[m2' c2'] g2'] cs'] lr'] Hb_es].
      move: (IH _ _ _ _ _ _ _ _ _ Hbb_es Hb_es) => [<- [<- <-]].
      dcase (bit_blast_bexp_cache E m1' (reset_ct c1') g1' e) =>
      [[[[[m'' c''] g''] cs''] lr''] Hbb_e].
      case=> -> -> -> _. case=> -> -> -> _ _. done.
  Qed.

  Lemma bb_bexps_cache_bit_blast_bexps_cache_exists E es m c g cnfs :
    bb_bexps_cache E es = (m, c, g, cnfs) ->
    exists cs, exists lr,
        bit_blast_bexps_cache E es = (m, c, g, cs, lr).
  Proof.
    elim: es m c g cnfs => [| e es IH] m c g cnfs /=.
    - case=> <- <- <- _. exists (add_prelude [::]). exists lit_tt. reflexivity.
    - dcase (bb_bexps_cache E es) => [[[[m1 c1] g1] cnfs1] Hbb_es].
      dcase (bit_blast_bexp_cache E m1 (reset_ct c1) g1 e)
      => [[[[[m2 c2] g2] cs] lr] Hbb_e].
      case=> <- <- <- _. move: (IH _ _ _ _ Hbb_es) => [cs' [lr' Hb_es]].
      rewrite Hb_es. exists cs; exists lr. exact: Hbb_e.
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
      rewrite -VSLemmas.mem_in in H. rewrite SSA.VSLemmas.diff_b in H.
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
      rewrite -VSLemmas.mem_in in H. rewrite SSA.VSLemmas.diff_b in H.
      rewrite negb_and Bool.negb_involutive in H. move/memenvP: Hmem => Hmem.
      rewrite Hmem /= in H. rewrite (AdhereConform.conform_bexp_mem Hco H).
      reflexivity.
  Qed.

  Lemma bb_bexps_cache_sound E es :
    QFBV.well_formed_bexps es E ->
    valid_bb_bexps_cache E es ->
    valid_qfbv_bexps E es.
  Proof.
    rewrite /valid_bb_bexps_cache. rewrite /valid_qfbv_bexps.
    elim: es => [| e es IH] Hwf //=.
    dcase (bb_bexps_cache E es) => [[[[m c] g] cnfs] Hbb_es].
    dcase (bit_blast_bexp_cache E m (reset_ct c) g e) =>
    [[[[[m' c'] g'] cs] lr] Hbb_e]. move=> H.
    move: (H m' c' g' (add_prelude ([:: neg_lit lr] :: cs) :: cnfs)) => {H} H.
    move=> s Hco e' Hin. rewrite in_cons in Hin. case/orP: Hin=> Hin.
    - rewrite (eqP Hin) => {Hin e'}.
      apply: (@bit_blast_cache_sound_general e es E m' c' g' cs lr).
      + rewrite /bit_blast_bexps_cache -/bit_blast_bexps_cache.
        dcase (bit_blast_bexps_cache E es) => [[[[[m0 c0] g0] cs0] lr0] Hb_es].
        move: (bb_bexps_cache_bit_blast_bexps_cache_eq Hbb_es Hb_es).
        move=> [<- [<- <-]]. exact: Hbb_e.
      + exact: Hwf.
      + apply: (H _ (Logic.eq_refl _)). exact: mem_head.
      + exact: (wf_conform_bexps Hwf Hco).
    - move/andP: Hwf=> [Hwf_e Hwf_es]. apply: (IH Hwf_es _ _ Hco _ Hin).
      move=> m0 c0 g0 cnfs0 cnf0 Hbb_es0 Hin0.
      apply: (H cnf0 (Logic.eq_refl _)). rewrite Hbb_es in Hbb_es0.
      case: Hbb_es0 => ? ? ? ?; subst. by rewrite in_cons Hin0 orbT.
  Qed.

  Lemma bb_bexps_cache_complete E es :
    QFBV.well_formed_bexps es E ->
    valid_qfbv_bexps E es ->
    valid_bb_bexps_cache E es.
  Proof.
    rewrite /valid_bb_bexps_cache. rewrite /valid_qfbv_bexps.
    elim: es => [| e es IH] Hwf //=.
    - move=> He m c g cnfs cnf. case=> ? ? ? ?; subst. move=> H; by inversion H.
    - move=> He m c g cnfs cnf.
      dcase (bb_bexps_cache E es) => [[[[m1 c1] g1] cnfs1] Hbb_es].
      dcase (bit_blast_bexp_cache E m1 (reset_ct c1) g1 e)
            => [[[[[m2 c2] g2] cs2] lr2] Hbb_e].
      case=> ? ? ? ?; subst. move=> Hin. rewrite in_cons in Hin.
      case/orP: Hin => Hin.
      + rewrite (eqP Hin). apply: (bit_blast_cache_complete_general _ Hwf).
        * rewrite /=. move: (bb_bexps_cache_bit_blast_bexps_cache_exists Hbb_es)
                      => [cs [lr Hb_es]]. rewrite Hb_es. exact: Hbb_e.
        * move=> s Hco. move/andP: Hco=> [Hco _].
          rewrite (force_conform_eval_bexp E _ (SSAVS.Lemmas.disjoint_diff
                                                  (vars_env E)
                                                  (vars_bexp e))).
          apply: He.
          -- exact: (conform_bexp_force_conform Hco).
          -- exact: mem_head.
      + move/andP: Hwf=> [Hwf_e Hwf_es].
        apply: (IH Hwf_es _ _ _ _ _ _ Hbb_es Hin).
        move=> s Hco f Hin_f. apply: (He _ Hco). by rewrite in_cons Hin_f orbT.
  Qed.

  Lemma bb_bexps_cache_eqvalid E es1 es2 :
    well_formed_bexps es1 E -> well_formed_bexps es2 E ->
    (valid_qfbv_bexps E es1 <-> valid_qfbv_bexps E es2) <->
    (valid_bb_bexps_cache E es1 <-> valid_bb_bexps_cache E es2).
  Proof.
    move=> Hwf1 Hwf2. split; move=> [H1 H2]; split; move=> H3.
    - apply: (bb_bexps_cache_complete Hwf2). apply: H1.
      apply: (bb_bexps_cache_sound Hwf1). assumption.
    - apply: (bb_bexps_cache_complete Hwf1). apply: H2.
      apply: (bb_bexps_cache_sound Hwf2). assumption.
    - apply: (bb_bexps_cache_sound Hwf2). apply: H1.
      apply: (bb_bexps_cache_complete Hwf1). assumption.
    - apply: (bb_bexps_cache_sound Hwf1). apply: H2.
      apply: (bb_bexps_cache_complete Hwf2). assumption.
  Qed.


  (* Combine range spec and safety conditions for bit-blasting *)

  Definition bb_range_safety (s : spec) :=
    (qfbv_spec_range s)::(qfbv_spec_safety s).

  Theorem bb_range_safety_well_formed s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    QFBV.well_formed_bexps (bb_range_safety s) fE.
  Proof.
    move=> fE Hwf. rewrite well_formed_bexps_cons.
    rewrite (well_formed_qfbv_bexp_rspec Hwf) andTb.
    rewrite (qfbv_spec_safety_well_formed Hwf). exact: is_true_true.
  Qed.

  Lemma range_in_bb_range_safety s :
    (qfbv_spec_range s) \in (bb_range_safety s).
  Proof. rewrite /bb_range_safety. exact: mem_head. Qed.

  Lemma safety_in_bb_range_safety s pre_es safe :
    ((pre_es, safe) \in
       (bexp_program_safe_split_fixed_final
          (program_succ_typenv (sprog s) (sinputs s))
          (sprog s))) ->
    ((qfbv_imp (qfbv_conj (bexp_rbexp (rng_bexp (spre s))) (qfbv_conjs pre_es)) safe)
       \in (bb_range_safety s)).
  Proof.
    rewrite /bb_range_safety. move=> Hin.
    move/qfbv_spec_safety_rec_in: Hin => Hin. by rewrite in_cons Hin orbT.
  Qed.

  Theorem bb_range_safety_sound s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_bb_bexps_cache fE (bb_range_safety s) ->
    valid_rspec (rspec_of_spec s) /\ ssa_spec_safe s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hbb.
    move: (bb_bexps_cache_sound (bb_range_safety_well_formed Hwf) Hbb) => Hes.
    split.
    - apply: (qfbv_bexp_spec_sound Hwf). move=> st Hco.
      exact: (Hes st Hco (qfbv_spec_range s) (range_in_bb_range_safety s)).
    - apply: (ssa_spec_safe_final_init Hwf).
      apply: (ssa_spec_safe_qfbv_fixed_final_sound Hwf).
      move: (well_formed_ssa_spec_program Hwf) => Hwf_p.
      apply: (bexp_program_safe_split_fixed_final_sound Hwf_p).
      move=> pre_es safe Hin st Hco.
      exact: (Hes _ Hco
                  (qfbv_imp
                     (qfbv_conj (bexp_rbexp (rng_bexp (spre s))) (qfbv_conjs pre_es))
                     safe) (safety_in_bb_range_safety Hin)).
  Qed.

  Theorem bb_range_safety_complete s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_rspec (rspec_of_spec s) -> ssa_spec_safe s ->
    valid_bb_bexps_cache fE (bb_range_safety s).
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hrange Hsafety.
    apply: (bb_bexps_cache_complete (bb_range_safety_well_formed Hwf)).
    rewrite /bb_range_safety. move=> st Hco e Hin.
    rewrite in_cons in Hin. case/orP: Hin=> Hin.
    - rewrite (eqP Hin). exact: (qfbv_bexp_spec_complete Hwf Hrange Hco).
    - exact: (qfbv_spec_safety_complete Hwf Hsafety Hin Hco).
  Qed.


  (* Combine simplified range spec and safety conditions *)

  Definition bb_range_safety_simplified (s : spec) :=
    map QFBV.simplify_bexp (bb_range_safety s).

  Lemma bb_range_safety_simplified_well_formed E s :
    well_formed_bexps (bb_range_safety s) E ->
    well_formed_bexps (bb_range_safety_simplified s) E.
  Proof.
    rewrite /bb_range_safety_simplified. move: (bb_range_safety s) => {s}.
    elim => [| e es IH] //=. move/andP=> [Hwf_e Hwf_es].
    rewrite (simplify_bexp_well_formed Hwf_e) (IH Hwf_es). reflexivity.
  Qed.

  Lemma bb_range_safety_simplified_valid E s :
    valid_qfbv_bexps E (bb_range_safety s) <->
    valid_qfbv_bexps E (bb_range_safety_simplified s).
  Proof.
    rewrite /bb_range_safety_simplified. move: (bb_range_safety s) => {s}.
    move=> es; split=> H s Hco e Hin.
    - move: (H _ Hco) => {H Hco} H. elim: es e Hin H => [| e es IH] //= f Hin H.
      case/orP: Hin => Hin.
      + rewrite (eqP Hin). apply/simplify_bexp_eqsat. apply: H. exact: mem_head.
      + apply: (IH _ Hin). move=> g Hing. apply: H. by rewrite in_cons Hing orbT.
    - move: (H _ Hco) => {H Hco} H. elim: es e Hin H => [| e es IH] //= f Hin H.
      case/orP: Hin => Hin.
      + rewrite (eqP Hin). apply/simplify_bexp_eqsat. apply: H. exact: mem_head.
      + apply: (IH _ Hin). move=> g Hing. apply: H. by rewrite in_cons Hing orbT.
  Qed.

  Theorem bb_range_safety_simplified_sound s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_bb_bexps_cache fE (bb_range_safety_simplified s) ->
    valid_rspec (rspec_of_spec s) /\ ssa_spec_safe s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hbb.
    move: ((bb_range_safety_well_formed Hwf)) => Hwf_bb.
    move: (bb_range_safety_simplified_well_formed Hwf_bb) => Hwf_bbs.
    move: (bb_bexps_cache_sound Hwf_bbs Hbb) => Hess.
    move/bb_range_safety_simplified_valid: Hess => Hes.
    apply: (bb_range_safety_sound Hwf).
    exact: (bb_bexps_cache_complete Hwf_bb Hes).
  Qed.

  Theorem bb_range_safety_simplified_complete s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_rspec (rspec_of_spec s) -> ssa_spec_safe s ->
    valid_bb_bexps_cache fE (bb_range_safety_simplified s).
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hrange Hsafety.
    move: (bb_range_safety_well_formed Hwf) => Hwf_bb.
    move: (bb_range_safety_simplified_well_formed Hwf_bb) => Hwf_bbs.
    apply: (bb_bexps_cache_complete Hwf_bbs).
    apply/bb_range_safety_simplified_valid.
    apply: (bb_bexps_cache_sound Hwf_bb).
    exact: (bb_range_safety_complete Hwf Hrange Hsafety).
  Qed.


  (* Use qfbv_conjs_la to combine QFBV formulas and simplify QFBV formulas *)

  Local Notation qfbv_spec_range_split_la := qfbv_bexp_spec_split_la.

  Fixpoint qfbv_spec_safety_la_rec f es :=
    match es with
    | [::] => [::]
    | (pre_es, safe)::tl =>
      (qfbv_imp (qfbv_conj f (qfbv_conjs_la pre_es))
                safe)::(qfbv_spec_safety_la_rec f tl)
    end.

  Definition qfbv_spec_safety_la (s : spec) : seq QFBV.bexp :=
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    qfbv_spec_safety_la_rec (bexp_rbexp (rng_bexp (spre s)))
                            (bexp_program_safe_split_fixed_final fE (sprog s)).

  Definition bb_range_safety_la (s : spec) :=
    (qfbv_spec_range_split_la s) ++ (qfbv_spec_safety_la s).

  Definition bb_range_safety_la_simplified (s : spec) :=
    map QFBV.simplify_bexp (bb_range_safety_la s).

  Lemma map_simplify_bexp_eqvalid E es :
    valid_qfbv_bexps E es <-> valid_qfbv_bexps E (map simplify_bexp es).
  Proof.
    elim: es => [| e es [IH1 IH2]] //=. split=> H s Hco e' Hin.
    - rewrite in_cons in Hin. case/orP: Hin => Hin.
      + rewrite (eqP Hin). apply/simplify_bexp_eqsat.
        apply: (H s Hco). exact: mem_head.
      + apply: (IH1 _ _ Hco _ Hin). exact: (valid_qfbv_bexps_tl H).
    - apply/simplify_bexp_eqsat. apply: (H _ Hco). rewrite -map_cons.
      apply/mapP. exists e'; last by reflexivity. assumption.
  Qed.

  Lemma map_simplify_bexp_well_formed E es :
    well_formed_bexps es E -> well_formed_bexps (map simplify_bexp es) E.
  Proof.
    elim: es => [| e es IH] //=. move/andP=> [Hwf_e Hwf_es].
    rewrite (QFBV.simplify_bexp_well_formed Hwf_e) (IH Hwf_es).
    done.
  Qed.

  Lemma map_simplify_bexp_valid_qfbv_bexps E es1 es2 :
    valid_qfbv_bexps E es1 <-> valid_qfbv_bexps E es2 ->
    valid_qfbv_bexps E [seq simplify_bexp i | i <- es1] <->
    valid_qfbv_bexps E [seq simplify_bexp i | i <- es2].
  Proof.
    move=> [H1 H2]. split=> H.
    - apply/(map_simplify_bexp_eqvalid _ es2). apply: H1.
      apply/map_simplify_bexp_eqvalid. assumption.
    - apply/(map_simplify_bexp_eqvalid _ es1). apply: H2.
      apply/map_simplify_bexp_eqvalid. assumption.
  Qed.

  Lemma qfbv_spec_safety_well_formed_ra_la E s :
    QFBV.well_formed_bexps (qfbv_spec_safety s) E =
    QFBV.well_formed_bexps (qfbv_spec_safety_la s) E.
  Proof.
    rewrite /qfbv_spec_safety /qfbv_spec_safety_la /=.
    move: ((bexp_rbexp (rng_bexp (spre s)))).
    move: (bexp_program_safe_split_fixed_final
             (program_succ_typenv (sprog s) (sinputs s)) (sprog s)).
    clear s. elim => [| [pre_es e] es IH] f //=.
    rewrite -IH. rewrite -well_formed_bexp_ra_la. reflexivity.
  Qed.

  Lemma bb_range_safety_la_well_formed E s :
    well_formed_bexps (bb_range_safety s) E ->
    well_formed_bexps (bb_range_safety_la s) E.
  Proof.
    rewrite /bb_range_safety /bb_range_safety_la.
    rewrite well_formed_bexps_cons well_formed_bexps_cat.
    move/andP=> [H1 H2]. rewrite -well_formed_qfbv_bexp_spec_ra_split_la.
    rewrite -qfbv_spec_safety_well_formed_ra_la.
    by rewrite H1 H2.
  Qed.

  Lemma bb_range_safety_la_simplified_well_formed s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    well_formed_bexps (bb_range_safety_la_simplified s) fE.
  Proof.
    move=> fE Hwf. rewrite /bb_range_safety_la_simplified.
    rewrite /bb_range_safety_la. rewrite map_cat.
    rewrite well_formed_bexps_cat.
    move: (well_formed_qfbv_bexp_rspec Hwf) => Hwf_rng.
    rewrite well_formed_qfbv_bexp_spec_ra_split_la in Hwf_rng.
    rewrite (map_simplify_bexp_well_formed Hwf_rng) /=.
    move: (qfbv_spec_safety_well_formed Hwf) => Hwf_safe.
    rewrite qfbv_spec_safety_well_formed_ra_la in Hwf_safe.
    rewrite (map_simplify_bexp_well_formed Hwf_safe) /=.
    reflexivity.
  Qed.

  Lemma qfbv_spec_safety_la_valid s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    valid_qfbv_bexps fE (qfbv_spec_safety s) <->
    valid_qfbv_bexps fE (qfbv_spec_safety_la s).
  Proof.
    move=> fE. rewrite /qfbv_spec_safety /qfbv_spec_safety_la /=.
    move: fE.
    move: (bexp_rbexp (rng_bexp (spre s))).
    move: (bexp_program_safe_split_fixed_final
             (program_succ_typenv (sprog s) (sinputs s)) (sprog s)).
    clear s. elim => [| [pre_es safe] es IH] f E //=.
    move: (IH f E) => [H1 H2]. split=> H s Hco e Hin.
    - rewrite in_cons in Hin. case/orP: Hin => Hin.
      + rewrite (eqP Hin). move: (valid_qfbv_bexps_hd H Hco) => /=.
        case: (eval_bexp f s) => //=. case: (eval_bexp safe s) => //=.
        * rewrite !orbT. by apply.
        * rewrite !orbF. move/negP=> Hs. apply/negP=> Hs'; apply: Hs.
          rewrite eval_qfbv_conjs_ra_la. assumption.
      + move: (valid_qfbv_bexps_tl H) => {H} H. exact: (H1 H _ Hco _ Hin).
    - rewrite in_cons in Hin. case/orP: Hin => Hin.
      + rewrite (eqP Hin). move: (valid_qfbv_bexps_hd H Hco) => /=.
        case: (eval_bexp f s) => //=. case: (eval_bexp safe s) => //=.
        * rewrite !orbT. by apply.
        * rewrite !orbF. move/negP=> Hs. apply/negP=> Hs'; apply: Hs.
          rewrite -eval_qfbv_conjs_ra_la. assumption.
      + move: (valid_qfbv_bexps_tl H) => {H} H. exact: (H2 H _ Hco _ Hin).
  Qed.

  Lemma bb_range_safety_la_simplified_valid s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    valid_qfbv_bexps fE (bb_range_safety_simplified s) <->
    valid_qfbv_bexps fE (bb_range_safety_la_simplified s).
  Proof.
    rewrite /bb_range_safety_la_simplified /bb_range_safety_simplified.
    apply: map_simplify_bexp_valid_qfbv_bexps.
    rewrite /bb_range_safety /bb_range_safety_la.
    move: (valid_qfbv_bexp_spec_ra_split_la s) => [H1 H2].
    split=> H st Hco e Hin.
    - rewrite mem_cat in Hin. case/orP: Hin => Hin.
      + apply: (H1 _ _ Hco _ Hin). move=> st' Hco'.
        exact: (valid_qfbv_bexps_hd H Hco').
      + move: (valid_qfbv_bexps_tl H) => {H} H.
        move/qfbv_spec_safety_la_valid: H => H. exact: (H st Hco _ Hin).
    - move: (valid_qfbv_bexps_cat H) => {H} [Hrng Hsafe].
      rewrite in_cons in Hin. case/orP: Hin => Hin.
      + rewrite (eqP Hin). apply: (H2 _ _ Hco). exact: Hrng.
      + move/qfbv_spec_safety_la_valid: Hsafe => Hsafe.
        exact: (Hsafe _ Hco _ Hin).
  Qed.

  Theorem bb_range_safety_la_simplified_sound s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_bb_bexps_cache fE (bb_range_safety_la_simplified s) ->
    valid_rspec (rspec_of_spec s) /\ ssa_spec_safe s.
  Proof.
    move=> fE Hwf Hbb. apply: (bb_range_safety_simplified_sound Hwf).
    move: (bb_range_safety_well_formed Hwf) => Hwf_bb.
    move: (bb_range_safety_simplified_well_formed Hwf_bb) => Hwf_bbs.
    apply: (bb_bexps_cache_complete Hwf_bbs).
    move: (bb_range_safety_la_simplified_well_formed Hwf) => Hwf_la.
    apply/bb_range_safety_la_simplified_valid.
    apply: (bb_bexps_cache_sound Hwf_la). assumption.
  Qed.

  Theorem bb_range_safety_la_simplified_complete s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_rspec (rspec_of_spec s) -> ssa_spec_safe s ->
    valid_bb_bexps_cache fE (bb_range_safety_la_simplified s).
  Proof.
    move=> fE Hwf Hrng Hsafe.
    move: (bb_range_safety_simplified_complete Hwf Hrng Hsafe) => Hv.
    move: (bb_range_safety_well_formed Hwf) => Hwf_bb.
    move: (bb_range_safety_simplified_well_formed Hwf_bb) => Hwf_bbs.
    apply: (bb_bexps_cache_complete (bb_range_safety_la_simplified_well_formed Hwf)).
    apply/bb_range_safety_la_simplified_valid.
    apply: (bb_bexps_cache_sound Hwf_bbs). assumption.
  Qed.


  (* Use qfbv_conjs_la to combine QFBV formulas, simplify QFBV formulas, and
     remove QFBV formulas that are trivially true *)

  Definition bexp_is_not_true e :=
    match e with
    | Btrue => false
    | _ => true
    end.

  Definition filter_not_true es := tfilter bexp_is_not_true es.

  Lemma filter_not_true_eqvalid E es :
    valid_qfbv_bexps E (filter_not_true es) <-> valid_qfbv_bexps E es.
  Proof.
    rewrite /filter_not_true. elim: es => [| e es IH] /=.
    - rewrite tfilter_nil. tauto.
    - move: IH=> [IH1 IH2]. rewrite tfilter_cons. case He: (bexp_is_not_true e).
      + split=> Hv s Hco f Hinf.
        * rewrite in_cons in Hinf. case/orP: Hinf => Hinf.
          -- rewrite (eqP Hinf). apply: (Hv _ Hco). rewrite mem_rcons. exact: mem_head.
          -- apply: (IH1 _ _ Hco _ Hinf). exact: (valid_qfbv_bexps_prefix Hv).
        * rewrite mem_rcons in_cons in Hinf. case/orP: Hinf => Hinf.
          -- rewrite (eqP Hinf). apply: (Hv _ Hco). exact: mem_head.
          -- apply: (IH2 _ _ Hco _ Hinf). exact: (valid_qfbv_bexps_tl Hv).
      + split=> Hv s Hco f Hinf.
        * rewrite in_cons in Hinf. case/orP: Hinf=> Hinf.
          -- rewrite (eqP Hinf). clear IH1 IH2 Hv Hco f Hinf.
             move: He. by case: e.
          -- apply: (IH1 _ _ Hco _ Hinf). assumption.
        * apply: (IH2 _ _ Hco _ Hinf). exact: (valid_qfbv_bexps_tl Hv).
  Qed.

  Lemma filter_not_true_well_formed E es :
    well_formed_bexps (filter_not_true es) E <-> well_formed_bexps es E.
  Proof.
    elim: es => [| e es IH] //=. rewrite /filter_not_true. rewrite tfilter_cons.
    move: IH=> [IH1 IH2]. case He: (bexp_is_not_true e).
    - split.
      + move=> H. rewrite well_formed_bexps_rcons in H.
        move/andP: H => [Hwf_es Hwf_e]. rewrite (IH1 Hwf_es) Hwf_e. reflexivity.
      + move=> /andP [Hwf_e Hwf_es]. rewrite well_formed_bexps_rcons.
        rewrite (IH2 Hwf_es) Hwf_e. reflexivity.
    - split.
      + move=> H. rewrite (IH1 H) andbT. clear es IH1 IH2 H. move: He.
        by case: e.
      + move=> /andP [Hwf_e Hwf_es]. rewrite (IH2 Hwf_es). reflexivity.
  Qed.

  Definition bb_range_safety_la_simplified_filtered (s : spec) :=
    filter_not_true (bb_range_safety_la_simplified s).

  Lemma bb_range_safety_la_simplified_filtered_well_formed s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    well_formed_bexps (bb_range_safety_la_simplified_filtered s) fE.
  Proof.
    move=> fE Hwf. rewrite /bb_range_safety_la_simplified_filtered.
    apply/(@filter_not_true_well_formed _ (bb_range_safety_la_simplified s)).
    exact: (bb_range_safety_la_simplified_well_formed Hwf).
  Qed.

  Lemma bb_range_safety_la_simplified_filtered_eqvalid s :
    let fE := program_succ_typenv (sprog s) (sinputs s)  in
    well_formed_ssa_spec s ->
    (valid_bb_bexps_cache fE (bb_range_safety_la_simplified_filtered s)
     <-> valid_bb_bexps_cache fE (bb_range_safety_la_simplified s)).
  Proof.
    move=> fE Hwf.
    apply/(bb_bexps_cache_eqvalid
             (bb_range_safety_la_simplified_filtered_well_formed Hwf)
             (bb_range_safety_la_simplified_well_formed Hwf)).
    exact: filter_not_true_eqvalid.
  Qed.

  Theorem bb_range_safety_la_simplified_filtered_sound s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_bb_bexps_cache fE (bb_range_safety_la_simplified_filtered s) ->
    valid_rspec (rspec_of_spec s) /\ ssa_spec_safe s.
  Proof.
    move=> fE Hwf Hbb. apply: (bb_range_safety_la_simplified_sound Hwf).
    apply/(bb_range_safety_la_simplified_filtered_eqvalid Hwf).
    assumption.
  Qed.

  Theorem bb_range_safety_la_simplified_filtered_complete s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    valid_rspec (rspec_of_spec s) -> ssa_spec_safe s ->
    valid_bb_bexps_cache fE (bb_range_safety_la_simplified_filtered s).
  Proof.
    move=> fE Hwf Hrng Hsafe.
    apply/(bb_range_safety_la_simplified_filtered_eqvalid Hwf).
    exact: (bb_range_safety_la_simplified_complete Hwf Hrng Hsafe).
  Qed.

End QFBV2CNF.
