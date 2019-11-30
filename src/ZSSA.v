
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

  Definition vars_zinstr (i : zinstr) : SSAVS.t :=
    match i with
    | Zassign v e => SSAVS.add v (SSA.vars_eexp e)
    | Zsplit vh vl e _ => SSAVS.add vh (SSAVS.add vl (SSA.vars_eexp e))
    end.

  Definition lvs_zinstr (i : zinstr) : SSAVS.t :=
    match i with
    | Zassign v e => SSAVS.singleton v
    | Zsplit vh vl e _ => SSAVS.add vh (SSAVS.singleton vl)
    end.

  Definition rvs_zinstr (i : zinstr) : SSAVS.t :=
    match i with
    | Zassign v e => SSA.vars_eexp e
    | Zsplit vh vl e _ => SSA.vars_eexp e
    end.

  Definition vars_zprogram (p : zprogram) : SSAVS.t :=
    foldl (fun vs i => SSAVS.union vs (vars_zinstr i)) SSAVS.empty p.

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

  (* Well-formedness *)

  (* TODO: finish this *)
  Definition well_formed_zinstr (vs : SSAVS.t) (i : zinstr) : bool := true.

  Fixpoint well_formed_zprogram (vs : SSAVS.t) (p : zprogram) : bool :=
    match p with
    | [::] => true
    | hd::tl => well_formed_zinstr vs hd
                && well_formed_zprogram (SSAVS.union vs (lvs_zinstr hd)) tl
    end.

  Definition well_formed_zspec (s : zspec) : bool :=
    SSAVS.subset (SSA.vars_ebexp (zspre s)) (zsinputs s)
    && well_formed_zprogram (zsinputs s) (zsprog s)
    && SSAVS.subset (SSA.vars_ebexp (zspost s))
                 (SSAVS.union (zsinputs s) (vars_zprogram (zsprog s))).

End ZSSA.
