
(** Root entailment problem. *)

From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder ZAriths Store FSets FMaps Tactics.
From BitBlasting Require Import State.
From Cryptoline Require Import DSL SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ZSEQM := TStateEqmod SSAVarOrder ZValueType ZSSAStore SSAVS.

Module ZSSA.

  Local Notation var := SSAVarOrder.t.



  (* Syntax *)

  Notation zexp := SSA.eexp.

  Notation zbexp := SSA.ebexp.

  Notation vars_zexp := SSA.vars_eexp.

  Notation vars_zexps := SSA.vars_eexps.

  Notation vars_zbexp := SSA.vars_ebexp.


  (* Semantics *)

  Fixpoint eval_zexp (e : zexp) (s : ZSSAStore.t) : Z :=
    match e with
    | Evar v => ZSSAStore.acc v s
    | Econst n => n
    | Eunop op e => SSA.eval_eunop op (eval_zexp e s)
    | Ebinop op e1 e2 => SSA.eval_ebinop op (eval_zexp e1 s) (eval_zexp e2 s)
    | Epow e n => Z.pow (eval_zexp e s) (Z.of_N n)
    end.

  Fixpoint eval_zexps (es : seq zexp) (s : ZSSAStore.t) : seq Z :=
    match es with
    | [::] => [::]
    | e::es => (eval_zexp e s)::(eval_zexps es s)
    end.

  Fixpoint eval_zbexp (e : zbexp) (s : ZSSAStore.t) : Prop :=
    match e with
    | Etrue => True
    | Eeq e1 e2 => eval_zexp e1 s = eval_zexp e2 s
    | Eeqmod e1 e2 ms => zeqms (eval_zexp e1 s) (eval_zexp e2 s) (eval_zexps ms s)
    | Eand e1 e2 => eval_zbexp e1 s /\ eval_zbexp e2 s
    end.

  Definition entails (f g : zbexp) : Prop :=
    forall s, eval_zbexp f s -> eval_zbexp g s.

  Lemma entails_eand f g1 g2 :
    entails f (Eand g1 g2) <-> entails f g1 /\ entails f g2.
  Proof.
    split.
    - move=> H; split; move=> s Hf; move: (H s Hf) => /=; tauto.
    - move=> [H1 H2] s Hf; split; move: (H1 s Hf) (H2 s Hf); tauto.
  Qed.

  Lemma size_eval_zexps es s : size (eval_zexps es s) = size es.
  Proof. elim: es => [| e es IH] //=. by rewrite IH. Qed.

  Lemma eval_zbexp_eands_cons e es s :
    eval_zbexp (SSA.eands (e::es)) s <-> eval_zbexp e s /\ eval_zbexp (SSA.eands es) s.
  Proof. done. Qed.

  Lemma eval_zbexp_eands_cat es1 es2 s :
    eval_zbexp (SSA.eands (es1 ++ es2)) s <->
    (eval_zbexp (SSA.eands es1) s) /\ (eval_zbexp (SSA.eands es2) s).
  Proof.
    elim: es1 es2 => [| e1 es1 IH] es2 /=.
    - by tauto.
    - split.
      + move=> [He1 H12]. move/IH: H12 => [Hes1 Hes2]. by tauto.
      + move=> [[He1 Hes1] Hes2]. split; first assumption.
        apply/IH. done.
  Qed.

  Lemma eval_zbexp_eands_split_eand e s :
    ZSSA.eval_zbexp (eands (split_eand e)) s <-> ZSSA.eval_zbexp e s.
  Proof.
    elim: e => //=.
    - move=> e1 e2; split.
      + move=> [H _]; assumption.
      + move=> H; tauto.
    - move=> e1 e2 ms; split.
      + move=> [H _]; assumption.
      + move=> H; tauto.
    - move=> e1 IH1 e2 IH2; split.
      + move/eval_zbexp_eands_cat=> [H1 H2]. move: ((proj1 IH1) H1) ((proj1 IH2) H2). tauto.
      + move=> [H1 H2]. move: ((proj2 IH1) H1) ((proj2 IH2) H2) => {}H1 {}H2.
        apply/eval_zbexp_eands_cat. tauto.
  Qed.


  (* String outputs *)

  Definition string_of_zexp := SSA.string_of_eexp.

  Definition string_of_zexps := SSA.string_of_eexps.

  Definition string_of_zbexp := SSA.string_of_ebexp.


  (* Specification *)

  (** A root entailment problem checks if the premise entails the consequence. *)
  Record rep : Type := { premise : zbexp; conseq : zbexp }.

  Definition rep_eqn (ps1 ps2 : rep) : bool :=
    (premise ps1 == premise ps2) && (conseq ps1 == conseq ps2).

  Lemma rep_eqn_eq ps1 ps2 : rep_eqn ps1 ps2 -> ps1 = ps2.
  Proof.
    case: ps1 => [pres1 post1]. case: ps2 => [pres2 post2]. rewrite /rep_eqn /=.
    move/andP=> [/eqP -> /eqP ->]. reflexivity.
  Qed.

  Lemma rep_eqn_refl ps : rep_eqn ps ps.
  Proof. by rewrite /rep_eqn 2!eqxx. Qed.

  Lemma rep_eqP (ps1 ps2 : rep) : reflect (ps1 = ps2) (rep_eqn ps1 ps2).
  Proof.
    case H: (rep_eqn ps1 ps2).
    - apply: ReflectT. exact: (rep_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: rep_eqn_refl.
  Qed.

  Definition rep_eqMixin := EqMixin rep_eqP.
  Canonical rep_eqType := Eval hnf in EqType rep rep_eqMixin.


  Definition valid_rep (s : rep) : Prop :=
    entails (premise s) (conseq s).

  Definition valid_reps (ss : seq rep) : Prop :=
    forall s, s \in ss -> valid_rep s.


  Lemma valid_reps_empty : valid_reps [::].
  Proof. move=> s Hin. discriminate. Qed.

  Lemma valid_reps_hd s ss :
    valid_reps (s::ss) -> valid_rep s.
  Proof. apply. exact: mem_head. Qed.

  Lemma valid_reps_tl s ss :
    valid_reps (s::ss) -> valid_reps ss.
  Proof.
    move=> H st Hin. apply: H. rewrite in_cons Hin orbT. reflexivity.
  Qed.

  Lemma valid_reps_cons s ss :
    valid_reps (s::ss) <-> valid_rep s /\ valid_reps ss.
  Proof.
    split.
    - move=> H; split.
      + exact: (valid_reps_hd H).
      + exact: (valid_reps_tl H).
    - move=> [H1 H2] st Hin. rewrite in_cons in Hin. case/orP: Hin=> Hin.
      + move/eqP: Hin => ?; subst. assumption.
      + exact: (H2 _ Hin).
  Qed.

  Lemma valid_reps_cat ss1 ss2 :
    valid_reps (ss1 ++ ss2) <-> valid_reps ss1 /\ valid_reps ss2.
  Proof.
    elim: ss1 ss2 => [| s1 ss1 IH] ss2 /=.
    - split.
      + move=> H; split; [exact: valid_reps_empty | exact: H].
      + move=> [_ H]; exact: H.
    - split.
      + move/valid_reps_cons=> [H1 H2]. move: (IH ss2) => {IH} [IH1 IH2].
        move: (IH1 H2) => {IH1} [IH11 IH12]. split.
        * apply/valid_reps_cons. tauto.
        * assumption.
      + move=> [/valid_reps_cons [Hs1 Hss1] Hss2]. apply/valid_reps_cons.
        move: (IH ss2) => {IH} [IH1 IH2]. split; first assumption.
        apply: IH2. tauto.
  Qed.

  Lemma valid_reps_cat1 ss1 ss2 :
    valid_reps (ss1 ++ ss2) -> valid_reps ss1.
  Proof. move/valid_reps_cat=> [H1 H2]; assumption. Qed.

  Lemma valid_reps_cat2 ss1 ss2 :
    valid_reps (ss1 ++ ss2) -> valid_reps ss2.
  Proof. move/valid_reps_cat=> [H1 H2]; assumption. Qed.



  Lemma steq_eval_zexp e {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zexp e s1 = eval_zexp e s2.
  Proof.
    elim: e => //=.
    - move=> op e IH Heq. rewrite (IH Heq). reflexivity.
    - move=> op e1 IH1 e2 IH2 Heq. rewrite (IH1 Heq) (IH2 Heq). reflexivity.
    - move=> e IH n Heq. rewrite (IH Heq). reflexivity.
  Qed.

  Lemma steq_eval_zexps es {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zexps es s1 = eval_zexps es s2.
  Proof.
    elim: es => [| e es IH] //= Heq. rewrite (steq_eval_zexp e Heq).
    rewrite (IH Heq). reflexivity.
  Qed.

  Lemma steq_eval_zbexp e {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zbexp e s1 <-> eval_zbexp e s2.
  Proof.
    elim: e => //=.
    - move=> e1 e2 Heq. rewrite (steq_eval_zexp e1 Heq) (steq_eval_zexp e2 Heq).
      tauto.
    - move=> e1 e2 ms Heq. rewrite (steq_eval_zexp e1 Heq) (steq_eval_zexp e2 Heq)
                                   (steq_eval_zexps ms Heq). tauto.
    - move=> e1 IH1 e2 IH2 Heq. move: (IH1 Heq) (IH2 Heq) => {IH1 IH2} IH1 IH2. tauto.
  Qed.


  Lemma eval_zexp_upd {x v s e} :
    ~~ SSAVS.mem x (vars_zexp e) ->
    eval_zexp e (ZSSAStore.upd x v s) = eval_zexp e s.
  Proof.
    elim: e x v s => //=.
    - move=> y x v s Hmem. move: (SSAVS.Lemmas.not_mem_singleton1 Hmem) =>
                           {Hmem} /negP Hne. rewrite eq_sym in Hne.
      rewrite (ZSSAStore.acc_upd_neq Hne). reflexivity.
    - move=> op e IH x v s Hmem. rewrite (IH _ _ _ Hmem). reflexivity.
    - move=> op e1 IH1 e2 IH2 x v s Hmem. move: (SSAVS.Lemmas.not_mem_union1 Hmem) =>
      {Hmem} [Hmem1 Hmem2]. rewrite (IH1 _ _ _ Hmem1) (IH2 _ _ _ Hmem2). reflexivity.
    - move=> e IH n x v s Hmem. rewrite (IH _ _ _ Hmem). reflexivity.
  Qed.

  Lemma eval_zexps_upd {x v s es} :
    ~~ SSAVS.mem x (vars_zexps es) ->
    eval_zexps es (ZSSAStore.upd x v s) = eval_zexps es s.
  Proof.
    elim: es => [| e es IH] //=. rewrite SSAVS.S.Lemmas.union_b negb_or.
    move/andP=> [Hmem1 Hmem2]. rewrite (eval_zexp_upd Hmem1). rewrite (IH Hmem2).
    reflexivity.
  Qed.

  Lemma eval_zbexp_upd {x v s e} :
    ~~ SSAVS.mem x (vars_zbexp e) ->
    eval_zbexp e (ZSSAStore.upd x v s) <-> eval_zbexp e s.
  Proof.
    elim: e x v s => //=.
    - move=> e1 e2 x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      rewrite (eval_zexp_upd Hmem1) (eval_zexp_upd Hmem2). done.
    - move=> e1 e2 ms x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem2 Hmemms].
      rewrite (eval_zexp_upd Hmem1) (eval_zexp_upd Hmem2) (eval_zexps_upd Hmemms). done.
    - move=> e1 IH1 e2 IH2 x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      move: (IH1 x v s Hmem1) (IH2 x v s Hmem2) => {IH1 IH2} IH1 IH2. split; tauto.
  Qed.

  Lemma eval_zexp_upd2 {x1 x2 v1 v2 s e} :
    ~~ SSAVS.mem x1 (vars_zexp e) ->
    ~~ SSAVS.mem x2 (vars_zexp e) ->
    eval_zexp e (ZSSAStore.upd2 x1 v1 x2 v2 s) = eval_zexp e s.
  Proof.
    elim: e x1 v1 x2 v2 s => //=.
    - move=> y x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_singleton1 Hmem1) => {Hmem1} Hmem1.
      move: (SSAVS.Lemmas.not_mem_singleton1 Hmem2) => {Hmem2} Hmem2.
      move/negP: Hmem1 => Hne1. move/negP: Hmem2 => Hne2. rewrite eq_sym in Hne1.
      rewrite eq_sym in Hne2. rewrite (ZSSAStore.acc_upd2_neq Hne1 Hne2). reflexivity.
    - move=> op e IH x1 v1 x2 v2 s Hmem1 Hmem2. rewrite (IH _ _ _ _ _ Hmem1 Hmem2).
      reflexivity.
    - move=> op e1 IH1 e2 IH2 x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      rewrite (IH1 _ _ _ _ _ Hmem11 Hmem21) (IH2 _ _ _ _ _ Hmem12 Hmem22). reflexivity.
    - move=> e IH n x1 v1 x2 v2 s Hmem1 Hmem2. rewrite (IH _ _ _ _ _ Hmem1 Hmem2).
      reflexivity.
  Qed.

  Lemma eval_zexps_upd2 {x1 x2 v1 v2 s es} :
    ~~ SSAVS.mem x1 (vars_zexps es) ->
    ~~ SSAVS.mem x2 (vars_zexps es) ->
    eval_zexps es (ZSSAStore.upd2 x1 v1 x2 v2 s) = eval_zexps es s.
  Proof.
    elim: es => [| e es IH] //=. rewrite 2!SSAVS.S.Lemmas.union_b 2!negb_or.
    move=> /andP [Hmem1e Hmem1es] /andP [Hmem2e Hmem2es].
    rewrite (eval_zexp_upd2 Hmem1e Hmem2e) (IH Hmem1es Hmem2es). reflexivity.
  Qed.

  Lemma eval_zbexp_upd2 {x1 v1 x2 v2 s e} :
    ~~ SSAVS.mem x1 (vars_zbexp e) ->
    ~~ SSAVS.mem x2 (vars_zbexp e) ->
    eval_zbexp e (ZSSAStore.upd2 x1 v1 x2 v2 s) <-> eval_zbexp e s.
  Proof.
    elim: e x1 v1 x2 v2 s => //=.
    - move=> e1 e2 x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      rewrite (eval_zexp_upd2 Hmem11 Hmem21) (eval_zexp_upd2 Hmem12 Hmem22). done.
    - move=> e1 e2 ms x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem12) => {Hmem12} [Hmem12 Hmem1ms].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem22) => {Hmem22} [Hmem22 Hmem2ms].
      rewrite (eval_zexp_upd2 Hmem11 Hmem21) (eval_zexp_upd2 Hmem12 Hmem22)
              (eval_zexps_upd2 Hmem1ms Hmem2ms). done.
    - move=> e1 IH1 e2 IH2 x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      move: (IH1 x1 v1 x2 v2 s Hmem11 Hmem21) (IH2 x1 v1 x2 v2 s Hmem12 Hmem22) =>
      {IH1 IH2} IH1 IH2. split; tauto.
  Qed.


  (* State equivalence *)

  Definition zs_eqi (E : SSAVS.t) (s1 s2 : ZSSAStore.t) :=
    forall x, SSAVS.mem x E -> ZSSAStore.acc x s1 = ZSSAStore.acc x s2.

  Lemma zs_eqi_refl E s : zs_eqi E s s.
  Proof. move=> *; reflexivity. Qed.

  Lemma zs_eqi_sym E s1 s2 : zs_eqi E s1 s2 -> zs_eqi E s2 s1.
  Proof. move=> Heqi x Hx. exact: (Logic.eq_sym (Heqi x Hx)). Qed.

  Lemma zs_eqi_trans E s1 s2 s3 :
    zs_eqi E s1 s2 -> zs_eqi E s2 s3 -> zs_eqi E s1 s3.
  Proof.
    move=> H12 H23 x Hx. rewrite (H12 x Hx) (H23 x Hx). reflexivity.
  Qed.

  Lemma zs_eqi_subset E1 E2 s1 s2 :
    SSAVS.subset E1 E2 -> zs_eqi E2 s1 s2 -> zs_eqi E1 s1 s2.
  Proof.
    move=> Hsub Heqi x Hx. exact: (Heqi x (SSAVS.Lemmas.mem_subset Hx Hsub)).
  Qed.

  Lemma zs_eqi_Upd E s1 s2 s3 x v :
    ~~ SSAVS.mem x E -> zs_eqi E s1 s2 ->
    ZSSAStore.Upd x v s2 s3 -> zs_eqi E s1 s3.
  Proof.
    move=> Hx Heqi HUpd y Hy. case Hyx: (y == x).
    - rewrite (eqP Hyx) in Hy. rewrite Hy in Hx. discriminate.
    - move/idP/negP: Hyx => Hyx. rewrite (ZSSAStore.acc_Upd_neq Hyx HUpd).
      exact: (Heqi _ Hy).
  Qed.

  Lemma zs_eqi_upd E s1 s2 x v :
    ~~ SSAVS.mem x E -> zs_eqi E s1 s2 ->
    zs_eqi E s1 (ZSSAStore.upd x v s2).
  Proof.
    move=> Hx Heqi. move: (ZSSAStore.Upd_upd x v s2) => HUpd.
    exact: (zs_eqi_Upd Hx Heqi HUpd).
  Qed.


  (* Slicing*)

  Lemma slice_zbexp_eval vs e s :
    eval_zbexp e s -> eval_zbexp (SSA.slice_ebexp vs e) s.
  Proof.
    elim: e => //=.
    - move=> e1 e2 H. by case_if.
    - move=> e1 e2 ms H. by case_if.
    - move=> e1 IH1 e2 IH2 [H1 H2].
      case Hs1: (SSA.slice_ebexp vs e1) => //=; rewrite Hs1 /= in IH1.
      + (case Hs2: (SSA.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
      + (case Hs2: (SSA.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
      + (case Hs2: (SSA.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
      + (case Hs2: (SSA.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
  Qed.

  Lemma state_eqmod_eval_zexp e s1 s2 :
    ZSEQM.state_eqmod (SSA.vars_eexp e) s1 s2 ->
    eval_zexp e s1 = eval_zexp e s2.
  Proof.
    elim: e => //=.
    - move=> v. apply. apply: SSA.VSLemmas.mem_singleton2. exact: eqxx.
    - move=> op e IH Heqm. rewrite (IH Heqm). reflexivity.
    - move=> op e1 IH1 e2 IH2 /ZSEQM.state_eqmod_union1 [Heqm1 Heqm2].
      rewrite (IH1 Heqm1) (IH2 Heqm2). reflexivity.
    - move=> e IH n Heqm. rewrite (IH Heqm). reflexivity.
  Qed.

  Lemma state_eqmod_eval_zexps es s1 s2 :
    ZSEQM.state_eqmod (SSA.vars_eexps es) s1 s2 ->
    eval_zexps es s1 = eval_zexps es s2.
  Proof.
    elim: es => [| e es IH] //=. move/ZSEQM.state_eqmod_union1 => [Heqm1 Heqm2].
    rewrite (state_eqmod_eval_zexp Heqm1) (IH Heqm2). reflexivity.
  Qed.

  Lemma state_eqmod_eval_zbexp e s1 s2 :
    ZSEQM.state_eqmod (SSA.vars_ebexp e) s1 s2 ->
    eval_zbexp e s1 -> eval_zbexp e s2.
  Proof.
    elim: e => //=.
    - move=> e1 e2 /ZSEQM.state_eqmod_union1 [Heqm1 Heqm2] H.
      rewrite -(state_eqmod_eval_zexp Heqm1) -(state_eqmod_eval_zexp Heqm2). exact: H.
    - move=> e1 e2 ms /ZSEQM.state_eqmod_union1
                [Heqm1 /ZSEQM.state_eqmod_union1 [Heqm2 Heqm3]] H.
      rewrite -(state_eqmod_eval_zexp Heqm1) -(state_eqmod_eval_zexp Heqm2)
              -(state_eqmod_eval_zexps Heqm3). exact: H.
    - move=> e1 IH1 e2 IH2 /ZSEQM.state_eqmod_union1 [Heqm1 Heqm2] [H1 H2].
      move: (IH1 Heqm1 H1) (IH2 Heqm2 H2). tauto.
  Qed.


End ZSSA.


Definition rep_eqMixin := ZSSA.rep_eqMixin.
Canonical rep_eqType := ZSSA.rep_eqType.
