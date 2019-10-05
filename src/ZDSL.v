
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From BitBlasting Require Import Var.
From ssrlib Require Import Types SsrOrdered ZAriths Store Tactics.
From Cryptoline Require Import DSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ValueType <: HasDefaultTyp.
  Definition t := Z.
  Definition default : t := 0%Z.
End ValueType.

Module Store := RealizableTStoreAdapter VarOrder ValueType.

Section ZDSL.

  (* Syntax *)

  Definition zexp := eexp.

  Definition zbexp := ebexp.

  Inductive zinstr : Set :=
  | Zassign : var -> zexp -> zinstr
  | Zsplit : var -> var -> zexp -> nat -> zinstr.

  Definition zprogram : Set := seq zinstr.

  Definition vars_zinstr (i : zinstr) : VS.t :=
    match i with
    | Zassign v e => VS.add v (vars_eexp e)
    | Zsplit vh vl e _ => VS.add vh (VS.add vl (vars_eexp e))
    end.

  Definition lvs_zinstr (i : zinstr) : VS.t :=
    match i with
    | Zassign v e => VS.singleton v
    | Zsplit vh vl e _ => VS.add vh (VS.singleton vl)
    end.

  Definition rvs_zinstr (i : zinstr) : VS.t :=
    match i with
    | Zassign v e => vars_eexp e
    | Zsplit vh vl e _ => vars_eexp e
    end.

  Definition vars_zprogram (p : zprogram) : VS.t :=
    foldl (fun vs i => VS.union vs (vars_zinstr i)) VS.empty p.

  (* Semantics *)

  Fixpoint eval_zexp (e : zexp) (s : Store.t) : Z :=
    match e with
    | Evar v => Store.acc v s
    | Econst n => n
    | Eunop op e => eval_eunop op (eval_zexp e s)
    | Ebinop op e1 e2 => eval_ebinop op (eval_zexp e1 s) (eval_zexp e2 s)
    end.

  Fixpoint eval_zbexp (e : zbexp) (s : Store.t) : Prop :=
    match e with
    | Etrue => True
    | Eeq e1 e2 => eval_zexp e1 s = eval_zexp e2 s
    | Eeqmod e1 e2 p => modulo (eval_zexp e1 s) (eval_zexp e2 s) (eval_zexp p s)
    | Eand e1 e2 => eval_zbexp e1 s /\ eval_zbexp e2 s
    end.

  Definition eval_zinstr (s : Store.t) (i : zinstr) : Store.t :=
    match i with
    | Zassign v e => Store.upd v (eval_zexp e s) s
    | Zsplit vh vl e i =>
      let (q, r) := Z.div_eucl (eval_zexp e s) (2^(Z.of_nat i)) in
      Store.upd2 vl r vh q s
    end.

  Definition eval_zprogram (s : Store.t) (p : zprogram) : Store.t :=
    foldl (fun s i => eval_zinstr s i) s p.

  (* Specification *)

  Record zspec : Type :=
    mkSpec { zsinputs : VS.t;
             zspre : zbexp;
             zsprog : zprogram;
             zspost : zbexp }.

  Definition zspec_partial_correct (s : zspec) : Prop :=
    forall s1 s2,
      eval_zbexp (zspre s) s1 ->
      eval_zprogram s1 (zsprog s) = s2 ->
      eval_zbexp (zspost s) s2.

  (* Well-formedness *)

  (* TODO: finish this *)
  Definition well_formed_zinstr (vs : VS.t) (i : zinstr) : bool := true.

  Fixpoint well_formed_zprogram (vs : VS.t) (p : zprogram) : bool :=
    match p with
    | [::] => true
    | hd::tl => well_formed_zinstr vs hd
                && well_formed_zprogram (VS.union vs (lvs_zinstr hd)) tl
    end.

  Definition well_formed_zspec (s : zspec) : bool :=
    VS.subset (vars_ebexp (zspre s)) (zsinputs s)
    && well_formed_zprogram (zsinputs s) (zsprog s)
    && VS.subset (vars_ebexp (zspost s))
                 (VS.union (zsinputs s) (vars_zprogram (zsprog s))).

End ZDSL.
