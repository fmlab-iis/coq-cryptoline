
(** Root entailment problem. *)

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

  Notation zexp := SSA.eexp.

  Notation zbexp := SSA.ebexp.

  Notation vars_zexp := SSA.vars_eexp.

  Notation vars_zbexp := SSA.vars_ebexp.


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
    | Eeqmod e1 e2 p => zeqm (eval_zexp e1 s) (eval_zexp e2 s) (eval_zexp p s)
    | Eand e1 e2 => eval_zbexp e1 s /\ eval_zbexp e2 s
    end.

  Definition entails (f g : zbexp) : Prop :=
    forall s, eval_zbexp f s -> eval_zbexp g s.

  (* Specification *)

  (** A root entailment problem checks if the premise entails the consequence. *)
  Record rep : Type := { premise : zbexp; conseq : zbexp }.

  Definition valid_rep (s : rep) : Prop :=
    entails (premise s) (conseq s).

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


  Lemma steq_eval_zexp e {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zexp e s1 = eval_zexp e s2.
  Proof.
    elim: e => //=.
    - move=> op e IH Heq. rewrite (IH Heq). reflexivity.
    - move=> op e1 IH1 e2 IH2 Heq. rewrite (IH1 Heq) (IH2 Heq). reflexivity.
  Qed.

  Lemma steq_eval_zbexp e {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zbexp e s1 <-> eval_zbexp e s2.
  Proof.
    elim: e => //=.
    - move=> e1 e2 Heq. rewrite (steq_eval_zexp e1 Heq) (steq_eval_zexp e2 Heq).
      tauto.
    - move=> e1 e2 e3 Heq. rewrite (steq_eval_zexp e1 Heq) (steq_eval_zexp e2 Heq)
                                   (steq_eval_zexp e3 Heq). tauto.
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
  Qed.

  Lemma eval_zbexp_upd {x v s e} :
    ~~ SSAVS.mem x (vars_zbexp e) ->
    eval_zbexp e (ZSSAStore.upd x v s) <-> eval_zbexp e s.
  Proof.
    elim: e x v s => //=.
    - move=> e1 e2 x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      rewrite (eval_zexp_upd Hmem1) (eval_zexp_upd Hmem2). done.
    - move=> e1 e2 m x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem2 Hmem3].
      rewrite (eval_zexp_upd Hmem1) (eval_zexp_upd Hmem2) (eval_zexp_upd Hmem3). done.
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
    - move=> e1 e2 m x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem12) => {Hmem12} [Hmem12 Hmem13].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem22) => {Hmem22} [Hmem22 Hmem23].
      rewrite (eval_zexp_upd2 Hmem11 Hmem21) (eval_zexp_upd2 Hmem12 Hmem22)
              (eval_zexp_upd2 Hmem13 Hmem23). done.
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

End ZSSA.
