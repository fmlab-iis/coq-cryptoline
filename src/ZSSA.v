
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder ZAriths Store FSets FMaps Tactics.
From BitBlasting Require Import State.
From Cryptoline Require Import DSL SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ZSSA.

  Local Notation var := SSAVarOrder.t.



  (* Syntax *)

  Definition zexp := SSA.eexp.

  Definition zbexp := SSA.ebexp.

  Inductive zinstr : Type :=
  | Zassign : var -> zexp -> zinstr
  | Zsplit : var -> var -> zexp -> nat -> zinstr.

  Definition zprogram : Type := seq zinstr.

  Local Notation vars_zexp := SSA.vars_eexp.

  Local Notation vars_zbexp := SSA.vars_ebexp.

  Definition vars_zinstr (i : zinstr) : SSAVS.t :=
    match i with
    | Zassign v e => SSAVS.add v (vars_zexp e)
    | Zsplit vh vl e _ => SSAVS.add vh (SSAVS.add vl (vars_zexp e))
    end.

  Definition lvs_zinstr (i : zinstr) : SSAVS.t :=
    match i with
    | Zassign v e => SSAVS.singleton v
    | Zsplit vh vl e _ => SSAVS.add vh (SSAVS.singleton vl)
    end.

  Definition rvs_zinstr (i : zinstr) : SSAVS.t :=
    match i with
    | Zassign v e => vars_zexp e
    | Zsplit vh vl e _ => vars_zexp e
    end.

  Fixpoint vars_zprogram (p : zprogram) : SSAVS.t :=
    match p with
    | [::] => SSAVS.empty
    | hd::tl => SSAVS.union (vars_zinstr hd) (vars_zprogram tl)
    end.

  Fixpoint lvs_zprogram (p : zprogram) : SSAVS.t :=
    match p with
    | [::] => SSAVS.empty
    | hd::tl => SSAVS.union (lvs_zinstr hd) (lvs_zprogram tl)
    end.

  Fixpoint rvs_zprogram (p : zprogram) : SSAVS.t :=
    match p with
    | [::] => SSAVS.empty
    | hd::tl => SSAVS.union (rvs_zinstr hd) (rvs_zprogram tl)
    end.

  Lemma vars_zinstr_split i :
    SSAVS.Equal (vars_zinstr i) (SSAVS.union (lvs_zinstr i) (rvs_zinstr i)).
  Proof. elim : i => /=; move=> *; by SSAVS.Lemmas.dp_Equal. Qed.

  Lemma mem_vars_zinstr v i :
    SSAVS.mem v (vars_zinstr i) =
    (SSAVS.mem v (lvs_zinstr i) || SSAVS.mem v (rvs_zinstr i)).
  Proof.
    rewrite vars_zinstr_split. rewrite SSAVS.Lemmas.mem_union. reflexivity.
  Qed.

  Lemma mem_vars_zinstr1 v i :
    SSAVS.mem v (vars_zinstr i) ->
    SSAVS.mem v (lvs_zinstr i) \/ SSAVS.mem v (rvs_zinstr i).
  Proof. rewrite mem_vars_zinstr. by move/orP. Qed.

  Lemma mem_vars_zinstr2 v i :
    SSAVS.mem v (lvs_zinstr i) -> SSAVS.mem v (vars_zinstr i).
  Proof. move=> H. rewrite mem_vars_zinstr. by apply/orP; left. Qed.

  Lemma mem_vars_zinstr3 v i :
    SSAVS.mem v (rvs_zinstr i) -> SSAVS.mem v (vars_zinstr i).
  Proof. move=> H. rewrite mem_vars_zinstr. by apply/orP; right. Qed.

  Lemma lvs_zinstr_subset i : SSAVS.subset (lvs_zinstr i) (vars_zinstr i).
  Proof. rewrite vars_zinstr_split. exact: SSAVS.Lemmas.union_subset_1. Qed.

  Lemma rvs_zinstr_subset i : SSAVS.subset (rvs_zinstr i) (vars_zinstr i).
  Proof. rewrite vars_zinstr_split. exact: SSAVS.Lemmas.union_subset_2. Qed.

  Lemma vars_zprogram_split p :
    SSAVS.Equal (vars_zprogram p) (SSAVS.union (lvs_zprogram p) (rvs_zprogram p)).
  Proof.
    elim: p => /=.
    - rewrite SSAVS.Lemmas.union_emptyl. reflexivity.
    - move=> hd tl IH.
      have: SSAVS.Equal
              (SSAVS.union (SSAVS.union (lvs_zinstr hd) (lvs_zprogram tl))
                           (SSAVS.union (rvs_zinstr hd) (rvs_zprogram tl)))
              (SSAVS.union (SSAVS.union (lvs_zinstr hd) (rvs_zinstr hd))
                           (SSAVS.union (lvs_zprogram tl) (rvs_zprogram tl))) by
          SSAVS.Lemmas.dp_Equal.
      move=> ->. rewrite -IH. rewrite -vars_zinstr_split. reflexivity.
  Qed.

  Lemma mem_vars_zprogram v p :
    SSAVS.mem v (vars_zprogram p) =
    (SSAVS.mem v (lvs_zprogram p) || SSAVS.mem v (rvs_zprogram p)).
  Proof. rewrite vars_zprogram_split SSAVS.Lemmas.mem_union. reflexivity. Qed.

  Lemma mem_vars_zprogram1 v p :
    SSAVS.mem v (vars_zprogram p) ->
    SSAVS.mem v (lvs_zprogram p) \/ SSAVS.mem v (rvs_zprogram p).
  Proof. rewrite mem_vars_zprogram. by move/orP. Qed.

  Lemma mem_vars_zprogram2 v p :
    SSAVS.mem v (lvs_zprogram p) -> SSAVS.mem v (vars_zprogram p).
  Proof. rewrite mem_vars_zprogram. by move=> H; apply/orP; left. Qed.

  Lemma mem_vars_zprogram3 v p :
    SSAVS.mem v (rvs_zprogram p) -> SSAVS.mem v (vars_zprogram p).
  Proof. rewrite mem_vars_zprogram. by move=> H; apply/orP; right. Qed.

  Lemma lvs_zprogram_subset p : SSAVS.subset (lvs_zprogram p) (vars_zprogram p).
  Proof. rewrite vars_zprogram_split. exact: SSAVS.Lemmas.union_subset_1. Qed.

  Lemma rvs_zprogram_subset p : SSAVS.subset (rvs_zprogram p) (vars_zprogram p).
  Proof. rewrite vars_zprogram_split. exact: SSAVS.Lemmas.union_subset_2. Qed.

  Lemma vars_zprogram_cat p1 p2 :
    SSAVS.Equal (vars_zprogram (p1 ++ p2))
                (SSAVS.union (vars_zprogram p1) (vars_zprogram p2)).
  Proof.
    elim: p1 p2 => /=.
    - move=> p2. rewrite SSAVS.Lemmas.union_emptyl. reflexivity.
    - move=> hd tl IH p2. rewrite IH. rewrite SSAVS.Lemmas.OP.P.union_assoc.
      reflexivity.
  Qed.

  Lemma lvs_zprogram_cat p1 p2 :
    SSAVS.Equal (lvs_zprogram (p1 ++ p2))
                (SSAVS.union (lvs_zprogram p1) (lvs_zprogram p2)).
  Proof.
    elim: p1 p2 => /=.
    - move=> p2. rewrite SSAVS.Lemmas.union_emptyl. reflexivity.
    - move=> hd tl IH p2. rewrite IH. rewrite SSAVS.Lemmas.OP.P.union_assoc.
      reflexivity.
  Qed.

  Lemma vars_zprogram_rcons p i :
    SSAVS.Equal (vars_zprogram (rcons p i))
                (SSAVS.union (vars_zprogram p) (vars_zinstr i)).
  Proof.
    rewrite -cats1 vars_zprogram_cat /=. rewrite SSAVS.Lemmas.union_emptyr.
    reflexivity.
  Qed.

  Lemma lvs_zprogram_rcons p i :
    SSAVS.Equal (lvs_zprogram (rcons p i))
                (SSAVS.union (lvs_zprogram p) (lvs_zinstr i)).
  Proof.
    rewrite -cats1 lvs_zprogram_cat /=. rewrite SSAVS.Lemmas.union_emptyr.
    reflexivity.
  Qed.



  (* Semantics *)

  Fixpoint eval_zexp (e : zexp) (s : ZSSAStore.t) : Z :=
    match e with
    | Evar v => ZSSAStore.acc v s
    | Econst n => n
    | Eunop op e => SSA.eval_eunop op (eval_zexp e s)
    | Ebinop op e1 e2 => SSA.eval_ebinop op (eval_zexp e1 s) (eval_zexp e2 s)
    end.

  Fixpoint eval_zbexp (e : zbexp) (s : ZSSAStore.t) : Prop :=
    match e with
    | Etrue => True
    | Eeq e1 e2 => eval_zexp e1 s = eval_zexp e2 s
    | Eeqmod e1 e2 p => modulo (eval_zexp e1 s) (eval_zexp e2 s) (eval_zexp p s)
    | Eand e1 e2 => eval_zbexp e1 s /\ eval_zbexp e2 s
    end.

  Definition eval_zinstr (s : ZSSAStore.t) (i : zinstr) : ZSSAStore.t :=
    match i with
    | Zassign v e => ZSSAStore.upd v (eval_zexp e s) s
    | Zsplit vh vl e i =>
      let (q, r) := Z.div_eucl (eval_zexp e s) (2^(Z.of_nat i)) in
      ZSSAStore.upd2 vl r vh q s
    end.

  Definition eval_zprogram (s : ZSSAStore.t) (p : zprogram) : ZSSAStore.t :=
    foldl (fun s i => eval_zinstr s i) s p.

  Definition zentails (f g : zbexp) : Prop :=
    forall s, eval_zbexp f s -> eval_zbexp g s.

  (* Specification *)

  Record zspec : Type :=
    mkSpec { zsinputs : SSAVS.t;
             zspre : zbexp;
             zsprog : zprogram;
             zspost : zbexp }.

  Definition valid_zspec (s : zspec) : Prop :=
    forall s1 s2,
      eval_zbexp (zspre s) s1 ->
      eval_zprogram s1 (zsprog s) = s2 ->
      eval_zbexp (zspost s) s2.

  Lemma eval_zprogram_singleton i s1 s2 :
    eval_zprogram s1 ([:: i]) = s2 -> eval_zinstr s1 i = s2.
  Proof. done. Qed.

  Lemma eval_zprogram_cons hd tl s1 s2 :
    eval_zprogram s1 (hd::tl) = s2 ->
    exists s3, eval_zinstr s1 hd = s3 /\ eval_zprogram s3 tl = s2.
  Proof. move=> H. exists (eval_zinstr s1 hd). done. Qed.

  Lemma eval_zprogram_cat p1 p2 s1 s2 s3 :
    eval_zprogram s1 p1 = s2 -> eval_zprogram s2 p2 = s3 ->
    eval_zprogram s1 (p1 ++ p2) = s3.
  Proof.
    elim: p1 p2 s1 s2 s3 => /=.
    - move=> p2 s1 s2 s3 He1 He2. by rewrite He1.
    - move=> hd tl H p2 s1 s2 s3 He1 He2.
      move: (eval_zprogram_cons He1) => {He1} [s4 [He1 He4]].
      move: (H _ _ _ _ He4 He2) => Htlp2. rewrite He1; assumption.
  Qed.

  Lemma eval_zprogram_cat_step p1 p2 s :
    eval_zprogram s (p1 ++ p2) = eval_zprogram (eval_zprogram s p1) p2.
  Proof. by elim: p1 p2 s => //=. Qed.

  Lemma eval_zprogram_split p1 p2 s1 s2 :
    eval_zprogram s1 (p1 ++ p2) = s2 ->
    exists s3, eval_zprogram s1 p1 = s3 /\ eval_zprogram s3 p2 = s2.
  Proof.
    elim: p1 p2 s1 s2 => /=.
    - move=> p2 s1 s2 H1. by exists s1.
    - move=> hd tl H p2 s1 s2 He1.
      move: (eval_zprogram_cons He1) => {He1} [s3 [He13 He32]].
      move: (H _ _ _ He32) => {H} [s4 [He34 He42]]. exists s4; split.
      + rewrite He13. assumption.
      + exact: He42.
  Qed.

  Lemma zspec_empty vs f g :
    valid_zspec {| zsinputs := vs; zspre := f; zsprog := [::]; zspost := g |} ->
    zentails f g.
  Proof. move=> He s Hf. apply: (He s _ Hf). reflexivity. Qed.



  (* Well-formedness *)

  Definition well_formed_zinstr (vs : SSAVS.t) (i : zinstr) : bool :=
    match i with
    | Zassign v e => SSAVS.subset (vars_zexp e) vs
    | Zsplit vh vl e p => (vh != vl) && (SSAVS.subset (vars_zexp e) vs)
    end.

  Fixpoint well_formed_zprogram (vs : SSAVS.t) (p : zprogram) : bool :=
    match p with
    | [::] => true
    | hd::tl => well_formed_zinstr vs hd
                && well_formed_zprogram (SSAVS.union vs (lvs_zinstr hd)) tl
    end.

  Definition well_formed_zspec (s : zspec) : bool :=
    SSAVS.subset (vars_zbexp (zspre s)) (zsinputs s)
    && well_formed_zprogram (zsinputs s) (zsprog s)
    && SSAVS.subset (vars_zbexp (zspost s))
                 (SSAVS.union (zsinputs s) (vars_zprogram (zsprog s))).

  Lemma well_formed_zinstr_subset_rvs vs i :
    well_formed_zinstr vs i -> SSAVS.subset (rvs_zinstr i) vs.
  Proof. case: i => /=; intros; SSAVS.Lemmas.dp_subset. Qed.

  Lemma well_formed_zinstr_subset vs1 vs2 i :
    well_formed_zinstr vs1 i -> SSAVS.subset vs1 vs2 -> well_formed_zinstr vs2 i.
  Proof.
    (case: i vs1 vs2 => /=);
      move=> *; hyps_splitb; repeat splitb;
               (match goal with
                | H: ?a |- ?a => assumption
                | |- is_true (SSAVS.subset _ _) => SSAVS.Lemmas.dp_subset
                | |- _ => idtac
                end).
  Qed.

  Lemma well_formed_zinstr_replace vs1 vs2 i :
    well_formed_zinstr vs1 i -> SSAVS.Equal vs1 vs2 -> well_formed_zinstr vs2 i.
  Proof.
    move=> Hwell Heq. apply: (well_formed_zinstr_subset Hwell). rewrite Heq.
    exact: SSAVS.Lemmas.subset_refl.
  Qed.

  Lemma well_formed_zprogram_subset vs1 vs2 p :
    well_formed_zprogram vs1 p -> SSAVS.subset vs1 vs2 -> well_formed_zprogram vs2 p.
  Proof.
    elim: p vs1 vs2 => //=. move=> hd tl IH vs1 vs2 /andP [Hhd Htl] Hsub.
    apply/andP; split.
    - exact: (well_formed_zinstr_subset Hhd Hsub).
    - apply: (IH _ _ Htl). apply: (SSAVS.Lemmas.union_subsets Hsub).
      exact: SSAVS.Lemmas.subset_refl.
  Qed.

  Lemma well_formed_zprogram_replace vs1 vs2 p :
    well_formed_zprogram vs1 p -> SSAVS.Equal vs1 vs2 -> well_formed_zprogram vs2 p.
  Proof.
    move=> Hwell Heq. apply: (well_formed_zprogram_subset Hwell). rewrite Heq.
    exact: SSAVS.Lemmas.subset_refl.
  Qed.

  Lemma well_formed_zinstr_vars vs i :
    well_formed_zinstr vs i ->
    SSAVS.Equal (SSAVS.union vs (vars_zinstr i)) (SSAVS.union vs (lvs_zinstr i)).
  Proof. case: i => /=; intros; hyps_splitb; SSAVS.Lemmas.dp_Equal. Qed.

  Lemma well_formed_zprogram_cat vs p1 p2 :
    well_formed_zprogram vs (p1 ++ p2) =
    (well_formed_zprogram vs p1)
      && (well_formed_zprogram (SSAVS.union vs (lvs_zprogram p1)) p2).
  Proof.
    case H: ((well_formed_zprogram vs p1)
               && (well_formed_zprogram (SSAVS.union vs (lvs_zprogram p1)) p2)).
    - move/andP: H => [Hp1 Hp2]. elim: p1 vs p2 Hp1 Hp2 => /=.
      + move=> vs p2 _ Hp2. apply: (well_formed_zprogram_replace Hp2).
        exact: SSAVS.Lemmas.union_emptyr.
      + move=> hd tl IH vs p2 /andP [Hhd Htl] Hp2. rewrite Hhd /=. apply: (IH _ _ Htl).
        apply: (well_formed_zprogram_replace Hp2).
        rewrite SSAVS.Lemmas.OP.P.union_assoc. reflexivity.
    - move/negP: H => Hneg. apply/negP => H; apply: Hneg; apply/andP.
      elim: p1 vs p2 H => /=.
      + move=> vs p2 Hp2; split; first by trivial.
        apply: (well_formed_zprogram_replace Hp2). rewrite SSAVS.Lemmas.union_emptyr.
        reflexivity.
      + move=> hd tl IH vs p2 /andP [Hhd Htlp2].
        move: (IH _ _ Htlp2) => {IH Htlp2} [Htl Hp2]. split.
        * by rewrite Hhd Htl.
        * apply: (well_formed_zprogram_replace Hp2).
          rewrite SSAVS.Lemmas.OP.P.union_assoc. reflexivity.
  Qed.

  Lemma well_formed_zprogram_cat1 vs p1 p2 :
    well_formed_zprogram vs (p1 ++ p2) -> well_formed_zprogram vs p1.
  Proof. rewrite well_formed_zprogram_cat. by move=> /andP [H _]. Qed.

  Lemma well_formed_zprogram_cat2 vs p1 p2 :
    well_formed_zprogram vs (p1 ++ p2) ->
    well_formed_zprogram (SSAVS.union vs (lvs_zprogram p1)) p2.
  Proof. rewrite well_formed_zprogram_cat. by move=> /andP [_ H]. Qed.

  Lemma well_formed_zprogram_cat3 vs p1 p2 :
    well_formed_zprogram vs p1 ->
    well_formed_zprogram (SSAVS.union vs (lvs_zprogram p1)) p2 ->
    well_formed_zprogram vs (p1 ++ p2).
  Proof. rewrite well_formed_zprogram_cat. by move=> H1 H2; rewrite H1 H2. Qed.

  Lemma well_formed_zprogram_cons1 vs p i :
    well_formed_zprogram vs (i::p) -> well_formed_zinstr vs i.
  Proof. by move=> /andP [H _]. Qed.

  Lemma well_formed_zprogram_cons2 vs p i :
    well_formed_zprogram vs (i::p) ->
    well_formed_zprogram (SSAVS.union vs (lvs_zinstr i)) p.
  Proof. by move=> /andP [_ H]. Qed.

  Lemma well_formed_zprogram_cons3 vs p i :
    well_formed_zinstr vs i ->
    well_formed_zprogram (SSAVS.union vs (lvs_zinstr i)) p ->
    well_formed_zprogram vs (i::p).
  Proof. move=> H1 H2. by rewrite /= H1 H2. Qed.

  Lemma well_formed_zprogram_rcons vs p i :
    well_formed_zprogram vs (rcons p i) =
    (well_formed_zprogram vs p)
      && (well_formed_zinstr (SSAVS.union vs (lvs_zprogram p)) i).
  Proof.
    rewrite -cats1 well_formed_zprogram_cat. case: (well_formed_zprogram vs p) => //=.
      by case: (well_formed_zinstr (SSAVS.union vs (lvs_zprogram p)) i).
  Qed.

  Lemma well_formed_zprogram_rcons1 vs p i :
    well_formed_zprogram vs (rcons p i) -> well_formed_zprogram vs p.
  Proof. rewrite well_formed_zprogram_rcons. by move=> /andP [H _]. Qed.

  Lemma well_formed_zprogram_rcons2 vs p i :
    well_formed_zprogram vs (rcons p i) ->
    well_formed_zinstr (SSAVS.union vs (lvs_zprogram p)) i.
  Proof. rewrite well_formed_zprogram_rcons. by move=> /andP [_ H]. Qed.

  Lemma well_formed_zprogram_rcons3 vs p i :
    well_formed_zprogram vs p ->
    well_formed_zinstr (SSAVS.union vs (lvs_zprogram p)) i ->
    well_formed_zprogram vs (rcons p i).
  Proof. rewrite well_formed_zprogram_rcons. by move=> H1 H2; rewrite H1 H2. Qed.

  Lemma well_formed_zprogram_vars vs p :
    well_formed_zprogram vs p ->
    SSAVS.Equal (SSAVS.union vs (vars_zprogram p)) (SSAVS.union vs (lvs_zprogram p)).
  Proof.
    elim: p vs => //=. move=> hd tl IH vs /andP [Hhd Htl].
    move: (IH _ Htl) => {IH Htl} => Heq.
    rewrite -(@SSAVS.Lemmas.OP.P.union_assoc _ (lvs_zinstr hd)). rewrite -{}Heq.
    rewrite -(well_formed_zinstr_vars Hhd). rewrite SSAVS.Lemmas.OP.P.union_assoc.
    reflexivity.
  Qed.



  (** Well-formed SSA *)

  Definition ssa_var_unchanged_zinstr (v : var) (i : zinstr) : bool :=
    ~~ (SSAVS.mem v (lvs_zinstr i)).

  Definition ssa_unchanged_zinstr_var (i : zinstr) (v : var) : bool :=
    ~~ (SSAVS.mem v (lvs_zinstr i)).

  Definition ssa_vars_unchanged_zinstr (vs : SSAVS.t) (i : zinstr) : bool :=
    SSAVS.for_all (ssa_unchanged_zinstr_var i) vs.

  Definition ssa_var_unchanged_zprogram (v : var) (p : zprogram) : bool :=
    all (ssa_var_unchanged_zinstr v) p.

  Definition ssa_unchanged_zprogram_var (p : zprogram) (v : var) : bool :=
    ssa_var_unchanged_zprogram v p.

  Definition ssa_vars_unchanged_zprogram (vs : SSAVS.t) (p : zprogram) : bool :=
    SSAVS.for_all (ssa_unchanged_zprogram_var p) vs.

  Fixpoint ssa_single_assignment (p : zprogram) : bool :=
    match p with
    | [::] => true
    | hd::tl =>
      (ssa_vars_unchanged_zprogram (lvs_zinstr hd) tl)
        && (ssa_single_assignment tl)
    end.

  Definition well_formed_ssa_zprogram (vs : SSAVS.t) (p : zprogram) : bool :=
    (well_formed_zprogram vs p)
      && (ssa_vars_unchanged_zprogram vs p)
      && (ssa_single_assignment p).

  Definition well_formed_ssa_zspec (s : zspec) : bool :=
    (well_formed_zspec s)
      && ssa_vars_unchanged_zprogram (zsinputs s) (zsprog s)
      && ssa_single_assignment (zsprog s).

  Lemma well_formed_ssa_zspec_zprogram s :
    well_formed_ssa_zspec s ->
    well_formed_ssa_zprogram (zsinputs s) (zsprog s).
  Proof.
    move=> /andP [/andP [/andP [/andP [Hpre Hwell] Hprog] Hvs] Hssa].
    by rewrite /well_formed_ssa_zprogram Hwell Hvs Hssa.
  Qed.

  Lemma ssa_var_unchanged_zassign x v e :
    ssa_var_unchanged_zinstr x (Zassign v e) -> x != v.
  Proof.
    rewrite /ssa_var_unchanged_zinstr => /= Hi. apply/negP.
    exact: (SSAVS.Lemmas.not_mem_singleton1 Hi).
  Qed.

  Lemma ssa_var_unchanged_zsplit x vh vl e i :
    ssa_var_unchanged_zinstr x (Zsplit vh vl e i) -> (x != vh) && (x != vl).
  Proof.
    rewrite /ssa_var_unchanged_zinstr => /= Hi.
    move: (SSAVS.Lemmas.not_mem_add1 Hi) => [Hm1 Hm2]. apply/andP; split.
    - apply/negP; assumption.
    - apply/negP; exact: (SSAVS.Lemmas.not_mem_singleton1 Hm2).
  Qed.

  Lemma acc_unchanged_zinstr v i s1 s2 :
    ssa_var_unchanged_zinstr v i -> eval_zinstr s1 i = s2 ->
    ZSSAStore.acc v s1 = ZSSAStore.acc v s2.
  Proof.
    case: i.
    - move=> v' e /= Hun Hei. move: (ssa_var_unchanged_zassign Hun) => {Hun} Hne.
      rewrite -Hei (ZSSAStore.acc_upd_neq Hne). reflexivity.
    - move=> vh vl e p Hun Hei.
      move: (ssa_var_unchanged_zsplit Hun) => {Hun} /andP [Hneh Hnel].
      rewrite -Hei /= => {Hei}.
      set tmp := Z.div_eucl (eval_zexp e s1) (2 ^ Z.of_nat p); destruct tmp as [q r].
      rewrite (ZSSAStore.acc_upd_neq Hneh) (ZSSAStore.acc_upd_neq Hnel). reflexivity.
  Qed.

  Lemma acc_unchanged_zprogram v p s1 s2 :
    ssa_var_unchanged_zprogram v p -> eval_zprogram s1 p = s2 ->
    ZSSAStore.acc v s1 = ZSSAStore.acc v s2.
  Proof.
    elim: p s1 s2 => /=.
    - move=> s1 s2 _ ->. reflexivity.
    - move=> hd tl IH s1 s2 /andP [Huchd Huctl] Hep.
      move: (eval_zprogram_cons Hep) => {Hep} [s3 [Hehd Hetl]].
      rewrite (acc_unchanged_zinstr Huchd Hehd). exact: (IH _ _ Huctl Hetl).
  Qed.

  Lemma ssa_var_unchanged_zprogram_empty v : ssa_var_unchanged_zprogram v [::].
  Proof. done. Qed.

  Lemma ssa_var_unchanged_zprogram_cons1 v hd tl :
    ssa_var_unchanged_zprogram v (hd::tl) ->
    ssa_var_unchanged_zinstr v hd /\ ssa_var_unchanged_zprogram v tl.
  Proof. move => /andP H. exact: H. Qed.

  Lemma ssa_var_unchanged_zprogram_cons2 v hd tl :
    ssa_var_unchanged_zinstr v hd -> ssa_var_unchanged_zprogram v tl ->
    ssa_var_unchanged_zprogram v (hd::tl).
  Proof.
    move=> Hhd Htl.
    rewrite /ssa_var_unchanged_zprogram /= -/(ssa_var_unchanged_zprogram v tl).
      by rewrite Hhd Htl.
  Qed.

  Lemma ssa_var_unchanged_zprogram_cat1 v p1 p2 :
    ssa_var_unchanged_zprogram v (p1 ++ p2) ->
    ssa_var_unchanged_zprogram v p1 /\ ssa_var_unchanged_zprogram v p2.
  Proof.
    elim: p1 p2.
    - move=> /= p2 H. by rewrite H.
    - move=> hd tl IH p2 /andP [Hhd Htlp2]. move: (IH _ Htlp2) => {IH Htlp2} [Htl Hp2].
        by rewrite /= Hhd Htl Hp2.
  Qed.

  Lemma ssa_var_unchanged_zprogram_cat2 v p1 p2 :
    ssa_var_unchanged_zprogram v p1 -> ssa_var_unchanged_zprogram v p2 ->
    ssa_var_unchanged_zprogram v (p1 ++ p2).
  Proof.
    elim: p1 p2.
    - move=> /= p2 _ Hp2. exact: Hp2.
    - move=> hd tl IH p2 [Hhdtl Hp2].
      move: (ssa_var_unchanged_zprogram_cons1 Hhdtl) => {Hhdtl} [Hhd Htl].
      apply/andP; split.
      + exact: Hhd.
      + exact: (IH _ Htl Hp2).
  Qed.

  Lemma acc_unchanged_zprogram_cons v hd tl s1 s2 s3 :
    ssa_var_unchanged_zprogram v (hd::tl) -> eval_zinstr s1 hd = s2 ->
    eval_zprogram s2 tl = s3 ->
    ZSSAStore.acc v s2 = ZSSAStore.acc v s1 /\ ZSSAStore.acc v s3 = ZSSAStore.acc v s1.
  Proof.
    move=> /andP [Hunhd Huntl] Hehd Hetl.
    move: (acc_unchanged_zinstr Hunhd Hehd) (acc_unchanged_zprogram Huntl Hetl) =>
    H21 H32. rewrite -H32 -H21. split; reflexivity.
  Qed.

  Lemma acc_unchanged_zprogram_cat v p1 p2 s1 s2 s3 :
    ssa_var_unchanged_zprogram v (p1 ++ p2) -> eval_zprogram s1 p1 = s2 ->
    eval_zprogram s2 p2 = s3 ->
    ZSSAStore.acc v s2 = ZSSAStore.acc v s1 /\ ZSSAStore.acc v s3 = ZSSAStore.acc v s1.
  Proof.
    move=> Hun12 Hep1 Hep2.
    move: (ssa_var_unchanged_zprogram_cat1 Hun12) => {Hun12} [Hun1 Hun2].
    rewrite -(acc_unchanged_zprogram Hun2 Hep2) -(acc_unchanged_zprogram Hun1 Hep1).
    split; reflexivity.
  Qed.

  Lemma ssa_unchanged_zinstr_var_compat i :
    SetoidList.compat_bool SSAVS.E.eq (ssa_unchanged_zinstr_var i).
  Proof. move=> x y Heq. rewrite (eqP Heq). reflexivity. Qed.

  Lemma ssa_unchanged_zprogram_var_compat p :
    SetoidList.compat_bool SSAVS.E.eq (ssa_unchanged_zprogram_var p).
  Proof. move=> x y Heq. rewrite (eqP Heq). reflexivity. Qed.

  Lemma ssa_unchanged_zinstr_mem v vs i :
    ssa_vars_unchanged_zinstr vs i -> SSAVS.mem v vs -> ssa_var_unchanged_zinstr v i.
  Proof.
    move=> Hun Hmem. apply: (SSAVS.for_all_2 (ssa_unchanged_zinstr_var_compat i) Hun).
    apply/SSAVS.Lemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_zprogram_mem v vs p :
    ssa_vars_unchanged_zprogram vs p -> SSAVS.mem v vs ->
    ssa_var_unchanged_zprogram v p.
  Proof.
    move=> Hun Hmem.
    apply: (SSAVS.for_all_2 (ssa_unchanged_zprogram_var_compat p) Hun).
    apply/SSAVS.Lemmas.memP; assumption.
  Qed.

  Lemma ssa_var_unchanged_zinstr_not_mem v i :
    ssa_var_unchanged_zinstr v i = ~~ SSAVS.mem v (lvs_zinstr i).
  Proof.
    case Hmem: (SSAVS.mem v (lvs_zinstr i)) => /=.
    - apply/negPn. exact: Hmem.
    - move/negP/idP: Hmem. by apply.
  Qed.

  Lemma ssa_var_unchanged_zprogram_not_mem v p :
    ssa_var_unchanged_zprogram v p = ~~ SSAVS.mem v (lvs_zprogram p).
  Proof.
    case Hmem: (SSAVS.mem v (lvs_zprogram p)) => /=.
    - elim: p Hmem => //=.
      move=> hd tl IH Hmem. case: (SSAVS.Lemmas.mem_union1 Hmem) => {Hmem} Hmem.
      + by rewrite /ssa_var_unchanged_zinstr Hmem.
      + rewrite (IH Hmem). by case: (ssa_var_unchanged_zinstr v hd).
    - move/negP/idP: Hmem => Hmem. elim: p Hmem => //=.
      move=> hd tl IH Hmem. move: (SSAVS.Lemmas.not_mem_union1 Hmem) =>
                            {Hmem} [Hmem1 Hmem2]. move: (IH Hmem2) => Hun.
        by rewrite ssa_var_unchanged_zinstr_not_mem Hmem1 Hun.
  Qed.

  Lemma ssa_unchanged_zinstr_global vs i :
    (forall v, SSAVS.mem v vs -> ssa_var_unchanged_zinstr v i) ->
    ssa_vars_unchanged_zinstr vs i.
  Proof.
    move=> H. apply: (SSAVS.for_all_1 (ssa_unchanged_zinstr_var_compat i)).
    move=> v Hin. apply: H; apply/SSAVS.Lemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_zprogram_global vs p :
    (forall v, SSAVS.mem v vs -> ssa_var_unchanged_zprogram v p) ->
    ssa_vars_unchanged_zprogram vs p.
  Proof.
    move=> H. apply: (SSAVS.for_all_1 (ssa_unchanged_zprogram_var_compat p)).
    move=> v Hin. apply: H; apply/SSAVS.Lemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_zinstr_local vs i :
    ssa_vars_unchanged_zinstr vs i ->
    (forall v, SSAVS.mem v vs -> ssa_var_unchanged_zinstr v i).
  Proof.
    move=> H v Hmem. apply: (SSAVS.for_all_2 (ssa_unchanged_zinstr_var_compat i) H).
    apply/SSAVS.Lemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_zprogram_local vs p :
    ssa_vars_unchanged_zprogram vs p ->
    (forall v, SSAVS.mem v vs -> ssa_var_unchanged_zprogram v p).
  Proof. move=> H v Hmem. exact: (ssa_unchanged_zprogram_mem H Hmem). Qed.

  Lemma ssa_unchanged_zprogram_cons1 vs hd tl :
    ssa_vars_unchanged_zprogram vs (hd::tl) ->
    ssa_vars_unchanged_zinstr vs hd /\ ssa_vars_unchanged_zprogram vs tl.
  Proof.
    move=> H. move: (ssa_unchanged_zprogram_local H) => {H} H. split.
    - apply: ssa_unchanged_zinstr_global => v Hmem. move: (H v Hmem) => {H} H.
      exact: (proj1 (ssa_var_unchanged_zprogram_cons1 H)).
    - apply: ssa_unchanged_zprogram_global => v Hmem. move: (H v Hmem) => {H} H.
      exact: (proj2 (ssa_var_unchanged_zprogram_cons1 H)).
  Qed.

  Lemma ssa_unchanged_zprogram_cons2 vs hd tl :
    ssa_vars_unchanged_zinstr vs hd -> ssa_vars_unchanged_zprogram vs tl ->
    ssa_vars_unchanged_zprogram vs (hd::tl).
  Proof.
    move=> [Hhd Htl]. apply: ssa_unchanged_zprogram_global => v Hmem.
    apply/andP; split.
    - exact: (ssa_unchanged_zinstr_local Hhd Hmem).
    - exact: (ssa_unchanged_zprogram_local Htl Hmem).
  Qed.

  Lemma ssa_unchanged_zprogram_cat1 vs p1 p2 :
    ssa_vars_unchanged_zprogram vs (p1 ++ p2) ->
    ssa_vars_unchanged_zprogram vs p1 /\ ssa_vars_unchanged_zprogram vs p2.
  Proof.
    move=> H; split; apply: ssa_unchanged_zprogram_global => v Hmem.
    - exact: (proj1 (ssa_var_unchanged_zprogram_cat1
                       (ssa_unchanged_zprogram_local H Hmem))).
    - exact: (proj2 (ssa_var_unchanged_zprogram_cat1
                       (ssa_unchanged_zprogram_local H Hmem))).
  Qed.

  Lemma ssa_unchanged_zprogram_cat2 vs p1 p2 :
    ssa_vars_unchanged_zprogram vs p1 -> ssa_vars_unchanged_zprogram vs p2 ->
    ssa_vars_unchanged_zprogram vs (p1 ++ p2).
  Proof.
    move=> Hp1 Hp2. apply: ssa_unchanged_zprogram_global => v Hmem.
    apply: ssa_var_unchanged_zprogram_cat2.
    - exact: (ssa_unchanged_zprogram_local Hp1 Hmem).
    - exact: (ssa_unchanged_zprogram_local Hp2 Hmem).
  Qed.

  Lemma ssa_unchanged_zprogram_hd vs hd tl :
    ssa_vars_unchanged_zprogram vs (hd::tl) -> ssa_vars_unchanged_zinstr vs hd.
  Proof.
    move=> Hun; move: (ssa_unchanged_zprogram_cons1 Hun) => [Hhd Htl]; assumption.
  Qed.

  Lemma ssa_unchanged_zprogram_tl vs hd tl :
    ssa_vars_unchanged_zprogram vs (hd::tl) -> ssa_vars_unchanged_zprogram vs tl.
  Proof.
    move=> Hun; move: (ssa_unchanged_zprogram_cons1 Hun) => [Hhd Htl]; assumption.
  Qed.

  Lemma ssa_unchanged_zinstr_singleton1 v i :
    ssa_vars_unchanged_zinstr (SSAVS.singleton v) i -> ssa_var_unchanged_zinstr v i.
  Proof.
    move=> Hun. apply: (ssa_unchanged_zinstr_mem Hun).
    apply: SSAVS.Lemmas.mem_singleton2. exact: eqxx.
  Qed.

  Lemma ssa_unchanged_zprogram_singleton1 v p :
    ssa_vars_unchanged_zprogram (SSAVS.singleton v) p ->
    ssa_var_unchanged_zprogram v p.
  Proof.
    move=> Hun. apply: (ssa_unchanged_zprogram_mem Hun).
    apply: SSAVS.Lemmas.mem_singleton2. exact: eqxx.
  Qed.

  Lemma ssa_unchanged_zinstr_singleton2 v i :
    ssa_var_unchanged_zinstr v i -> ssa_vars_unchanged_zinstr (SSAVS.singleton v) i.
  Proof.
    move=> Hun. apply: ssa_unchanged_zinstr_global => x Hmem.
    move: (SSAVS.Lemmas.mem_singleton1 Hmem) => Heq. rewrite (eqP Heq); assumption.
  Qed.

  Lemma ssa_unchanged_zprogram_singleton2 v p :
    ssa_var_unchanged_zprogram v p ->
    ssa_vars_unchanged_zprogram (SSAVS.singleton v) p.
  Proof.
    move=> Hun. apply: ssa_unchanged_zprogram_global => x Hmem.
    move: (SSAVS.Lemmas.mem_singleton1 Hmem) => Heq. rewrite (eqP Heq); assumption.
  Qed.

  Lemma ssa_unchanged_zinstr_union1 s1 s2 i :
    ssa_vars_unchanged_zinstr (SSAVS.union s1 s2) i ->
    ssa_vars_unchanged_zinstr s1 i /\ ssa_vars_unchanged_zinstr s2 i.
  Proof.
    move=> Hun. move: (ssa_unchanged_zinstr_local Hun) => {Hun} Hun.
    split; apply: ssa_unchanged_zinstr_global => v Hmem.
    - apply: Hun. exact: SSAVS.Lemmas.mem_union2.
    - apply: Hun. exact: SSAVS.Lemmas.mem_union3.
  Qed.

  Lemma ssa_unchanged_zprogram_union1 s1 s2 p :
    ssa_vars_unchanged_zprogram (SSAVS.union s1 s2) p ->
    ssa_vars_unchanged_zprogram s1 p /\ ssa_vars_unchanged_zprogram s2 p.
  Proof.
    move=> Hun. move: (ssa_unchanged_zprogram_local Hun) => {Hun} Hun.
    split; apply: ssa_unchanged_zprogram_global => v Hmem.
    - apply: Hun. exact: SSAVS.Lemmas.mem_union2.
    - apply: Hun. exact: SSAVS.Lemmas.mem_union3.
  Qed.

  Lemma ssa_unchanged_zinstr_union2 s1 s2 i :
    ssa_vars_unchanged_zinstr s1 i -> ssa_vars_unchanged_zinstr s2 i ->
    ssa_vars_unchanged_zinstr (SSAVS.union s1 s2) i.
  Proof.
    move=> Hun1 Hun2. apply: ssa_unchanged_zinstr_global => x Hmem.
    move: (SSAVS.Lemmas.mem_union1 Hmem); case => {Hmem} Hmem.
    - exact: (ssa_unchanged_zinstr_mem Hun1 Hmem).
    - exact: (ssa_unchanged_zinstr_mem Hun2 Hmem).
  Qed.

  Lemma ssa_unchanged_zprogram_union2 s1 s2 p :
    ssa_vars_unchanged_zprogram s1 p -> ssa_vars_unchanged_zprogram s2 p ->
    ssa_vars_unchanged_zprogram (SSAVS.union s1 s2) p.
  Proof.
    move=> Hun1 Hun2. apply: ssa_unchanged_zprogram_global => x Hmem.
    move: (SSAVS.Lemmas.mem_union1 Hmem); case => {Hmem} Hmem.
    - exact: (ssa_unchanged_zprogram_mem Hun1 Hmem).
    - exact: (ssa_unchanged_zprogram_mem Hun2 Hmem).
  Qed.

  Lemma ssa_unchanged_zinstr_subset vs1 vs2 i :
    ssa_vars_unchanged_zinstr vs2 i -> SSAVS.subset vs1 vs2 ->
    ssa_vars_unchanged_zinstr vs1 i.
  Proof.
    move=> Hun Hsub. move: (ssa_unchanged_zinstr_local Hun) => {Hun} Hun.
    apply: ssa_unchanged_zinstr_global. move=> v Hmem; apply: Hun.
    exact: (SSAVS.Lemmas.mem_subset Hmem Hsub).
  Qed.

  Lemma ssa_unchanged_zprogram_subset vs1 vs2 p :
    ssa_vars_unchanged_zprogram vs2 p -> SSAVS.subset vs1 vs2 ->
    ssa_vars_unchanged_zprogram vs1 p.
  Proof.
    move=> Hun Hsub. move: (ssa_unchanged_zprogram_local Hun) => {Hun} Hun.
    apply: ssa_unchanged_zprogram_global. move=> v Hmem; apply: Hun.
    exact: (SSAVS.Lemmas.mem_subset Hmem Hsub).
  Qed.

  Lemma ssa_unchanged_zinstr_add1 v s p :
    ssa_vars_unchanged_zinstr (SSAVS.add v s) p ->
    ssa_var_unchanged_zinstr v p /\ ssa_vars_unchanged_zinstr s p.
  Proof.
    move=> H; split.
    - apply: (ssa_unchanged_zinstr_mem H). apply: SSAVS.Lemmas.mem_add2.
      exact: SSAVS.E.eq_refl.
    - apply: (ssa_unchanged_zinstr_subset H).
      exact: (SSAVS.Lemmas.subset_add _ (SSAVS.Lemmas.subset_refl s)).
  Qed.

  Lemma ssa_unchanged_zinstr_add2 v s p :
    ssa_var_unchanged_zinstr v p /\ ssa_vars_unchanged_zinstr s p ->
    ssa_vars_unchanged_zinstr (SSAVS.add v s) p.
  Proof.
    move=> [H1 H2]. apply: ssa_unchanged_zinstr_global => x Hmem.
    case: (SSAVS.Lemmas.mem_add1 Hmem) => {Hmem}.
    - move=> Heq. by rewrite (eqP Heq).
    - move=> Hmem. exact: (ssa_unchanged_zinstr_mem H2 Hmem).
  Qed.

  Lemma ssa_unchanged_zprogram_add1 v s p :
    ssa_vars_unchanged_zprogram (SSAVS.add v s) p ->
    ssa_var_unchanged_zprogram v p /\ ssa_vars_unchanged_zprogram s p.
  Proof.
    move=> H; split.
    - apply: (ssa_unchanged_zprogram_mem H). apply: SSAVS.Lemmas.mem_add2.
      exact: SSAVS.E.eq_refl.
    - apply: (ssa_unchanged_zprogram_subset H).
      exact: (SSAVS.Lemmas.subset_add _ (SSAVS.Lemmas.subset_refl s)).
  Qed.

  Lemma ssa_unchanged_zprogram_add2 v s p :
    ssa_var_unchanged_zprogram v p /\ ssa_vars_unchanged_zprogram s p ->
    ssa_vars_unchanged_zprogram (SSAVS.add v s) p.
  Proof.
    move=> [H1 H2]. apply: ssa_unchanged_zprogram_global => x Hmem.
    case: (SSAVS.Lemmas.mem_add1 Hmem) => {Hmem}.
    - move=> Heq. by rewrite (eqP Heq).
    - move=> Hmem. exact: (ssa_unchanged_zprogram_mem H2 Hmem).
  Qed.

  Lemma ssa_unchanged_zprogram_empty vs :
    ssa_vars_unchanged_zprogram vs [::].
  Proof. by apply: ssa_unchanged_zprogram_global. Qed.

  Lemma ssa_unchanged_zinstr_disjoint_lvs vs i :
    ssa_vars_unchanged_zinstr vs i = SSAVS.Lemmas.disjoint vs (lvs_zinstr i).
  Proof.
    case Hdisj: (SSAVS.Lemmas.disjoint vs (lvs_zinstr i)).
    - apply: ssa_unchanged_zinstr_global => v Hmem.
      exact: (SSAVS.Lemmas.mem_disjoint1 Hdisj Hmem).
    - apply/negP => Hunch. move/negP: Hdisj; apply.
      move: (ssa_unchanged_zinstr_local Hunch) => {Hunch} Hunch.
      exact: (SSAVS.Lemmas.mem_disjoint3 Hunch).
  Qed.

  Lemma ssa_unchanged_zprogram_disjoint_lvs vs p :
    ssa_vars_unchanged_zprogram vs p = SSAVS.Lemmas.disjoint vs (lvs_zprogram p).
  Proof.
    case Hdisj: (SSAVS.Lemmas.disjoint vs (lvs_zprogram p)).
    - elim: p vs Hdisj => /=.
      + move=> vs _. exact: ssa_unchanged_zprogram_empty.
      + move=> hd tl IH vs Hdisj. rewrite SSAVS.Lemmas.disjoint_union in Hdisj.
        move/andP: Hdisj => [Hdisjhd Hdisjtl]. apply: ssa_unchanged_zprogram_cons2.
        * rewrite ssa_unchanged_zinstr_disjoint_lvs. exact: Hdisjhd.
        * exact: (IH _ Hdisjtl).
    - apply/negP => Hunch. move/negP: Hdisj; apply.
      move: (ssa_unchanged_zprogram_local Hunch) => {Hunch} Hunch.
      apply: SSAVS.Lemmas.mem_disjoint3. move=> x Hmem.
      move: (Hunch x Hmem). rewrite ssa_var_unchanged_zprogram_not_mem. done.
  Qed.

  Lemma ssa_unchanged_zprogram_replace vs1 vs2 p :
    SSAVS.Equal vs1 vs2 -> ssa_vars_unchanged_zprogram vs1 p ->
    ssa_vars_unchanged_zprogram vs2 p.
  Proof.
    move=> Heq H. move: (ssa_unchanged_zprogram_local H) => {H} H.
    apply: ssa_unchanged_zprogram_global => v Hv. apply: H.
    rewrite Heq. assumption.
  Qed.

  Lemma ssa_single_assignment_cons1 i p :
    ssa_single_assignment (i::p) ->
    (ssa_vars_unchanged_zprogram (lvs_zinstr i) p) /\ (ssa_single_assignment p).
  Proof. move=> H; apply/andP; exact: H. Qed.

  Lemma ssa_single_assignment_cons2 i p :
    (ssa_vars_unchanged_zprogram (lvs_zinstr i) p) -> (ssa_single_assignment p) ->
    ssa_single_assignment (i::p).
  Proof.
    move=> Hi Hp; by rewrite /ssa_single_assignment -/ssa_single_assignment Hi Hp.
  Qed.

  Lemma ssa_single_assignment_cat1 p1 p2 :
    ssa_single_assignment (p1 ++ p2) ->
    ssa_single_assignment p1 /\ ssa_single_assignment p2 /\
    (ssa_vars_unchanged_zprogram (lvs_zprogram p1) p2).
  Proof.
    elim: p1 => /=.
    - move=> Hp2; repeat split. exact: Hp2.
    - move=> i p1 IH /andP [Hun12 Hssa12].
      move: (IH Hssa12) => [Hssa1 [Hssa2 Hun2]] => {Hssa12 IH}. repeat split.
      + by rewrite (proj1 (ssa_unchanged_zprogram_cat1 Hun12)) Hssa1.
      + exact: Hssa2.
      + apply: ssa_unchanged_zprogram_union2.
        * exact: (proj2 (ssa_unchanged_zprogram_cat1 Hun12)).
        * exact: Hun2.
  Qed.

  Lemma ssa_single_assignment_cat2 p1 p2 :
    ssa_single_assignment p1 -> ssa_single_assignment p2 ->
    (ssa_vars_unchanged_zprogram (lvs_zprogram p1) p2) ->
    ssa_single_assignment (p1 ++ p2).
  Proof.
    elim: p1 => /=.
    - move=> _ Hssa2 _. exact: Hssa2.
    - move=> i p1 IH /andP [Hun1 Hssa1] Hssa2 Hun12.
      apply/andP; split.
      + apply: ssa_unchanged_zprogram_cat2.
        * exact: Hun1.
        * apply: (ssa_unchanged_zprogram_subset Hun12).
          apply: SSAVS.Lemmas.subset_union1. exact: SSAVS.Lemmas.subset_refl.
      + apply: (IH Hssa1 Hssa2). apply: (ssa_unchanged_zprogram_subset Hun12).
        apply: SSAVS.Lemmas.subset_union2. exact: SSAVS.Lemmas.subset_refl.
  Qed.

  Lemma well_formed_ssa_vars_unchanged_hd vs hd tl :
    well_formed_ssa_zprogram vs (hd::tl) ->
    ssa_vars_unchanged_zprogram (vars_zinstr hd) tl.
  Proof.
    move => /andP [/andP [Hwf Huc] Hssa].
    apply: (@ssa_unchanged_zprogram_replace
              (SSAVS.union (lvs_zinstr hd) (rvs_zinstr hd))).
    - rewrite -vars_zinstr_split.
      reflexivity.
    - apply: ssa_unchanged_zprogram_union2.
      + move/andP: Hssa => [Hssa1 Hssa2].
        exact: Hssa1.
      + apply: (@ssa_unchanged_zprogram_subset _ vs).
        * exact: (ssa_unchanged_zprogram_tl Huc).
        * apply: well_formed_zinstr_subset_rvs.
          exact: (well_formed_zprogram_cons1 Hwf).
  Qed.

  Lemma well_formed_ssa_tl vs hd tl :
    well_formed_ssa_zprogram vs (hd::tl) ->
    well_formed_ssa_zprogram (SSAVS.union vs (lvs_zinstr hd)) tl.
  Proof.
    move=> Hwfssa. move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
    apply/andP; split; first (apply/andP; split).
    - exact: (well_formed_zprogram_cons2 Hwf).
    - apply: ssa_unchanged_zprogram_union2.
      + exact: (ssa_unchanged_zprogram_tl Huc).
      + move/andP: Hssa => [H _]. exact: H.
    - move/andP: Hssa => [_ H]. exact: H.
  Qed.

  Lemma ssa_unchanged_zinstr_eval_exp e s1 s2 i :
    ssa_vars_unchanged_zinstr (vars_zexp e) i -> eval_zinstr s1 i = s2 ->
    eval_zexp e s1 = eval_zexp e s2.
  Proof.
    elim: e => /=.
    - move=> v Hun Hi. move: (ssa_unchanged_zinstr_singleton1 Hun) => {Hun} Hun.
      exact: (acc_unchanged_zinstr Hun Hi).
    - reflexivity.
    - move=> op e IH Hun Hi. rewrite (IH Hun Hi); reflexivity.
    - move=> op e1 IH1 e2 IH2 Hun Hi.
      move: (ssa_unchanged_zinstr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hi) (IH2 Hun2 Hi); reflexivity.
  Qed.

  Lemma ssa_unchanged_zprogram_eval_exp e s1 s2 p :
    ssa_vars_unchanged_zprogram (vars_zexp e) p -> eval_zprogram s1 p = s2 ->
    eval_zexp e s1 = eval_zexp e s2.
  Proof.
    elim: e => /=.
    - move=> v Hunch. move: (ssa_unchanged_zprogram_singleton1 Hunch) =>
                      {Hunch} Hunch Hp. exact: (acc_unchanged_zprogram Hunch Hp).
    - move=> c _ Hp. reflexivity.
    - move=> op e IH Hunch Hp. rewrite (IH Hunch Hp). reflexivity.
    - move=> op e1 IH1 e2 IH2 Hunch Hp.
      move: (ssa_unchanged_zprogram_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
      rewrite (IH1 Hunch1 Hp) (IH2 Hunch2 Hp). reflexivity.
  Qed.

  Lemma ssa_unchanged_zinstr_eval_bexp e s1 s2 i :
    ssa_vars_unchanged_zinstr (vars_zbexp e) i -> eval_zinstr s1 i = s2 ->
    eval_zbexp e s1 <-> eval_zbexp e s2.
  Proof.
    elim: e => /=.
    - done.
    - move=> e1 e2 Hun Hi.
      move: (ssa_unchanged_zinstr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (ssa_unchanged_zinstr_eval_exp Hun1 Hi)
              (ssa_unchanged_zinstr_eval_exp Hun2 Hi).
      done.
    - move=> e1 e2 p Hun Hi.
      move: (ssa_unchanged_zinstr_union1 Hun) => {Hun} [Hun1 Hun2].
      move: (ssa_unchanged_zinstr_union1 Hun2) => {Hun2} [Hun2 Hunp].
      rewrite (ssa_unchanged_zinstr_eval_exp Hun1 Hi)
              (ssa_unchanged_zinstr_eval_exp Hun2 Hi)
              (ssa_unchanged_zinstr_eval_exp Hunp Hi).
      done.
    - move=> e1 IH1 e2 IH2 Hun Hi.
      move: (ssa_unchanged_zinstr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hi) (IH2 Hun2 Hi).
      done.
  Qed.

  Lemma ssa_unchanged_zprogram_eval_bexp e s1 s2 p :
    ssa_vars_unchanged_zprogram (vars_zbexp e) p -> eval_zprogram s1 p = s2 ->
    eval_zbexp e s1 <-> eval_zbexp e s2.
  Proof.
    elim: e => /=.
    - done.
    - move=> e1 e2 Hunch Hp.
      move: (ssa_unchanged_zprogram_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
      rewrite (ssa_unchanged_zprogram_eval_exp Hunch1 Hp)
              (ssa_unchanged_zprogram_eval_exp Hunch2 Hp).
      done.
    - move=> e1 e2 i Hunch Hp.
      move: (ssa_unchanged_zprogram_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
      move: (ssa_unchanged_zprogram_union1 Hunch2) => {Hunch2} [Hunch2 Hunchp].
      rewrite (ssa_unchanged_zprogram_eval_exp Hunch1 Hp)
              (ssa_unchanged_zprogram_eval_exp Hunch2 Hp)
              (ssa_unchanged_zprogram_eval_exp Hunchp Hp).
      done.
    - move=> e1 IH1 e2 IH2 Hunch Hp.
      move: (ssa_unchanged_zprogram_union1 Hunch) => {Hunch} [Hunch1 Hunch2].
      rewrite (IH1 Hunch1 Hp) (IH2 Hunch2 Hp).
      done.
  Qed.

  Lemma ssa_unchanged_zprogram_eval_bexp1 e s1 s2 p :
    ssa_vars_unchanged_zprogram (vars_zbexp e) p -> eval_zprogram s1 p = s2 ->
    eval_zbexp e s1 -> eval_zbexp e s2.
  Proof.
    move=> Hunch Hp He. move: (ssa_unchanged_zprogram_eval_bexp Hunch Hp) => [H1 H2].
    exact: (H1 He).
  Qed.

  Lemma ssa_unchanged_zprogram_eval_bexp2 e s1 s2 p :
    ssa_vars_unchanged_zprogram (vars_zbexp e) p -> eval_zprogram s1 p = s2 ->
    eval_zbexp e s2 -> eval_zbexp e s1.
  Proof.
    move=> Hunch Hp He. move: (ssa_unchanged_zprogram_eval_bexp Hunch Hp) => [H1 H2].
    exact: (H2 He).
  Qed.

End ZSSA.
