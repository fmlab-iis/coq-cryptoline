
From Coq Require Import Arith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun prime.
From ssrlib Require Import Var Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv.
From Cryptoline Require Import DSL SSA SSA2ZSSA SSA2QFBV.
From nbits Require Import NBits.

(** Conversion from range specifications and safety conditions to QFBV expressions *)

Import SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*qfbv_bexp_spec*)

Fixpoint subst_eq_exp_exp (e : QFBV.exp) (e1 : QFBV.exp) (e2 : QFBV.exp) :=
  if QFBV.exp_eqn e1 e then e2 else
    match e with
    | QFBV.Eunop op o => QFBV.Eunop op (subst_eq_exp_exp o e1 e2)
    | QFBV.Ebinop op o1 o2 =>
      QFBV.Ebinop op (subst_eq_exp_exp o1 e1 e2) (subst_eq_exp_exp o2 e1 e2)
    | QFBV.Eite b1 b2 b3 => QFBV.Eite (subst_eq_bexp_exp b1 e1 e2) (subst_eq_exp_exp b2 e1 e2) (subst_eq_exp_exp b3 e1 e2)
    | _ => e
    end
with
subst_eq_bexp_exp (e : QFBV.bexp) (e1 : QFBV.exp) (e2 : QFBV.exp) :=
  match e with
  | QFBV.Bbinop op o1 o2 => QFBV.Bbinop op (subst_eq_exp_exp o1 e1 e2) (subst_eq_exp_exp o2 e1 e2)
  | QFBV.Blneg l => QFBV.Blneg (subst_eq_bexp_exp l e1 e2)
  | QFBV.Bconj c1 c2 => QFBV.Bconj (subst_eq_bexp_exp c1 e1 e2) (subst_eq_bexp_exp c2 e1 e2)
  | QFBV.Bdisj d1 d2 => QFBV.Bdisj (subst_eq_bexp_exp d1 e1 e2) (subst_eq_bexp_exp d2 e1 e2)
  | _ => e
  end.

Definition subst_eq_qfbv_spec (s : spec) (e1 : QFBV.exp) (e2 : QFBV.exp) := 
  (subst_eq_bexp_exp (qfbv_bexp_spec s) e1 e2).

Lemma subst_eq_ind e e' : subst_eq_exp_exp e e e' = e'.
Proof.
  case e; intros; rewrite/=; try rewrite eq_refl//; try rewrite !QFBV.exp_eqn_refl //.
  rewrite QFBV.bexp_eqn_refl//.
Qed.

(* subst evar *)
Lemma eval_subst_exp_evar :
  forall e v e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Evar v) e') s ->
    QFBV.eval_exp e s = QFBV.eval_exp (subst_eq_exp_exp e (QFBV.Evar v) e') s
with eval_subst_bexp_evar :
  forall be v e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Evar v) e') s ->
    QFBV.eval_bexp be s = QFBV.eval_bexp (subst_eq_bexp_exp be (QFBV.Evar v) e') s.
Proof.
  elim; intros; rewrite //.
  - rewrite /=. rewrite /= in H.
    case Heqn : (v == t); try done.
    + rewrite -(eqP H) (eqP Heqn)//.
  - rewrite /= in H0. rewrite /= -H//.
  - rewrite /= -H // -H0 //.
  - rewrite /= -H // -H0 //.
    rewrite -eval_subst_bexp_evar//.
  elim; intros; rewrite // /=.
  - rewrite -!eval_subst_exp_evar//.
  - rewrite -H //.
  - rewrite -H0 // -H //.
  - rewrite -H0 // -H //.
Qed.

Lemma eval_subst_spec_evar_eqn es v e2 s:
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Evar v) e2) s ->
  (QFBV.eval_bexp (qfbv_bexp_spec es) s
   = QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Evar v) e2) s).
Proof.
  intros; rewrite /=. 
  destruct es as [E (epre, rpre) pg (epst, rpst)]; rewrite/= . 
  case ((bexp_program E (rng_program pg))); rewrite /=.
  - rewrite /= in H. rewrite 2!andbT -!eval_subst_bexp_evar//.
  - intros. rewrite /= in H. rewrite -!eval_subst_bexp_evar//.
Qed.
    
Lemma eval_subst_spec_evar_iff es v e2 s :
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Evar v) e2) s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s <->
  QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Evar v) e2) s.
Proof.
  intros. split; rewrite -eval_subst_spec_evar_eqn//. Qed.

Lemma eval_subst_spec_evar_correct :
  forall es v e2, 
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Evar v) e2) s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s) <->
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Evar v) e2) s ->
              QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Evar v) e2) s).
Proof.
  split;
    (move => Hes s0 Heq; move : (Hes s0 Heq); rewrite -eval_subst_spec_evar_eqn//).
Qed.

(* subst econst *)
Lemma eval_subst_exp_econst :
  forall e b e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Econst b) e') s ->
    QFBV.eval_exp e s = QFBV.eval_exp (subst_eq_exp_exp e (QFBV.Econst b) e') s
with eval_subst_bexp_econst :
  forall be b e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Econst b) e') s ->
    QFBV.eval_bexp be s = QFBV.eval_bexp (subst_eq_bexp_exp be (QFBV.Econst b) e') s.
Proof.
  elim; intros; rewrite //.
  - rewrite /=. rewrite /= in H.
    case Heqn : (b0 == b); try done. rewrite -(eqP H) -(eqP Heqn)//. 
  - rewrite /= in H0. rewrite /= -H//.
  - rewrite /= -H // -H0 //.
  - rewrite /= -H // -H0 //.
    rewrite -eval_subst_bexp_econst//.
  elim; intros; rewrite // /=.
  - rewrite -!eval_subst_exp_econst//.
  - rewrite -H //.
  - rewrite -H0 // -H //.
  - rewrite -H0 // -H //.
Qed.

Lemma eval_subst_spec_econst_eqn es b e2 s:
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Econst b) e2) s ->
  (QFBV.eval_bexp (qfbv_bexp_spec es) s
   = QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Econst b) e2) s).
Proof.
  intros; rewrite /=. 
  destruct es as [E (epre, rpre) pg (epst, rpst)]; rewrite/= . 
  case ((bexp_program E (rng_program pg))); rewrite /=.
  - rewrite /= in H. rewrite 2!andbT -!eval_subst_bexp_econst//.
  - intros. rewrite /= in H. rewrite -!eval_subst_bexp_econst//.
Qed.
    
Lemma eval_subst_spec_econst_iff es b e2 s :
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Econst b) e2) s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s <->
  QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Econst b) e2) s.
Proof.
  intros. split; rewrite -eval_subst_spec_econst_eqn//. Qed.

Lemma eval_subst_spec_econst_correct :
  forall es b e2, 
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Econst b) e2) s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s) <->
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Econst b) e2) s ->
              QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Econst b) e2) s).
Proof.
  split;
    (move => Hes s0 Heq; move : (Hes s0 Heq); rewrite -eval_subst_spec_econst_eqn//).
Qed.

(* subst eunop *)
Lemma eval_subst_exp_eunop :
  forall e o e1 e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eunop o e1) e') s ->
    QFBV.eval_exp e s = QFBV.eval_exp (subst_eq_exp_exp e (QFBV.Eunop o e1) e') s
with eval_subst_bexp_eunop :
  forall be o e1 e' s, 
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eunop o e1) e') s ->
    QFBV.eval_bexp be s = QFBV.eval_bexp (subst_eq_bexp_exp be (QFBV.Eunop o e1) e') s.
Proof. 
  elim; intros; rewrite //.
  - rewrite /=; rewrite /= in H0.
    case Heqn : (o == e); case Heqn' : (QFBV.exp_eqn e1 e0); try rewrite /= -H//. 
    rewrite -(eqP Heqn) -(eqP Heqn') (eqP H0)//. 
  - rewrite /= -H // -H0 //.
  - rewrite /= -H // -H0 // -eval_subst_bexp_eunop//. 
  elim; intros; rewrite // /=.
  - rewrite -!eval_subst_exp_eunop//.
  - rewrite -H //.
  - rewrite -H0 // -H //.
  - rewrite -H0 // -H //.
Qed.

Lemma eval_subst_spec_eunop_eqn es o e1 e2 s:
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eunop o e1) e2) s ->
  (QFBV.eval_bexp (qfbv_bexp_spec es) s
   = QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Eunop o e1) e2) s).
Proof.
  intros; rewrite /=. 
  destruct es as [E (epre, rpre) pg (epst, rpst)]; rewrite/= . 
  case ((bexp_program E (rng_program pg))); rewrite /=.
  - rewrite /= in H. rewrite 2!andbT -!eval_subst_bexp_eunop//.
  - intros. rewrite /= in H. rewrite -!eval_subst_bexp_eunop//.
Qed.
    
Lemma eval_subst_spec_eunop_iff es o e1 e2 s :
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eunop o e1) e2) s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s <->
  QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Eunop o e1) e2) s.
Proof.
  intros. split; rewrite -eval_subst_spec_eunop_eqn//. Qed.

Lemma eval_subst_spec_eunop_correct :
  forall es o e1 e2, 
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eunop o e1) e2) s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s) <->
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eunop o e1) e2) s ->
              QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Eunop o e1) e2) s).
Proof.
  split;
    (move => Hes s0 Heq; move : (Hes s0 Heq); rewrite -eval_subst_spec_eunop_eqn//).
Qed.

(* subst ebinop *)
Lemma eval_subst_exp_ebinop :
  forall e o e1 e2 e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Ebinop o e1 e2) e') s ->
    QFBV.eval_exp e s = QFBV.eval_exp (subst_eq_exp_exp e (QFBV.Ebinop o e1 e2) e') s
with eval_subst_bexp_ebinop :
  forall be o e1 e2 e' s, 
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Ebinop o e1 e2) e') s ->
    QFBV.eval_bexp be s = QFBV.eval_bexp (subst_eq_bexp_exp be (QFBV.Ebinop o e1 e2) e') s.
Proof. 
  elim; intros; rewrite // /=.
  - rewrite -H//.
  - rewrite /= in H1.
    case Heqn : (o == e); case Heqn' : (QFBV.exp_eqn e2 e0); case Heqn'' : (QFBV.exp_eqn e3 e1);
      rewrite /=; try rewrite -H0// -H//.
    rewrite -(eqP Heqn) -(eqP Heqn') -(eqP Heqn'') -(eqP H1)//.
  - rewrite /= in H1. rewrite -H0// -H// -eval_subst_bexp_ebinop//.
  elim; intros; rewrite // /=.
  - rewrite -!eval_subst_exp_ebinop//.
  - rewrite -H //.
  - rewrite -H0 // -H //.
  - rewrite -H0 // -H //.
Qed.

Lemma eval_subst_spec_ebinop_eqn es o e1 e2 e' s:
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Ebinop o e1 e2) e') s ->
  (QFBV.eval_bexp (qfbv_bexp_spec es) s
   = QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Ebinop o e1 e2) e') s).
Proof.
  intros; rewrite /=. 
  destruct es as [E (epre, rpre) pg (epst, rpst)]; rewrite/= . 
  case ((bexp_program E (rng_program pg))); rewrite /=.
  - rewrite /= in H. rewrite 2!andbT -!eval_subst_bexp_ebinop//.
  - intros. rewrite /= in H. rewrite -!eval_subst_bexp_ebinop//.
Qed.
    
Lemma eval_subst_spec_ebinop_iff es o e1 e2 e' s :
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Ebinop o e1 e2) e') s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s <->
  QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Ebinop o e1 e2) e') s.
Proof.
  intros. split; rewrite -eval_subst_spec_ebinop_eqn//. Qed.

Lemma eval_subst_spec_ebinop_corrct :
  forall es o e1 e2 e', 
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Ebinop o e1 e2) e') s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s) <->
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Ebinop o e1 e2) e') s ->
              QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Ebinop o e1 e2) e') s).
Proof.
  split;
    (move => Hes s0 Heq; move : (Hes s0 Heq); rewrite -eval_subst_spec_ebinop_eqn//).
Qed.

(* subst eite *)
Lemma eval_subst_exp_eite :
  forall e b e1 e2 e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eite b e1 e2) e') s ->
    QFBV.eval_exp e s = QFBV.eval_exp (subst_eq_exp_exp e (QFBV.Eite b e1 e2) e') s
with eval_subst_bexp_eite :
  forall be b e1 e2 e' s, 
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eite b e1 e2) e') s ->
    QFBV.eval_bexp be s = QFBV.eval_bexp (subst_eq_bexp_exp be (QFBV.Eite b e1 e2) e') s.
Proof. 
  elim; intros; rewrite // /=.
  - rewrite -H//.
  - rewrite -H// -H0//.
  - rewrite /= in H1.
    case Heqn : (QFBV.bexp_eqn b0 b) ; case Heqn' : (QFBV.exp_eqn e1 e); case Heqn'' : (QFBV.exp_eqn e2 e0);
      rewrite /=; try rewrite -H// -H0// -eval_subst_bexp_eite//.
    rewrite -(eqP Heqn) -(eqP Heqn') -(eqP Heqn'') -(eqP H1)//.
  elim; intros; rewrite // /=.
  - rewrite -!eval_subst_exp_eite//.
  - rewrite -H //.
  - rewrite -H0 // -H //.
  - rewrite -H0 // -H //.
Qed.

Lemma eval_subst_spec_eite_eqn es b e1 e2 e' s:
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eite b e1 e2) e') s ->
  (QFBV.eval_bexp (qfbv_bexp_spec es) s
   = QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Eite b e1 e2) e') s).
Proof.
  intros; rewrite /=. 
  destruct es as [E (epre, rpre) pg (epst, rpst)]; rewrite/= . 
  case ((bexp_program E (rng_program pg))); rewrite /=.
  - rewrite /= in H. rewrite 2!andbT -!eval_subst_bexp_eite//.
  - intros. rewrite /= in H. rewrite -!eval_subst_bexp_eite//.
Qed.
    
Lemma eval_subst_spec_eite_iff es b e1 e2 e' s :
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eite b e1 e2) e') s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s <->
  QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Eite b e1 e2) e') s.
Proof.
  intros. split; rewrite -eval_subst_spec_eite_eqn//. Qed.

Lemma eval_subst_spec_eite_correct :
  forall es b e1 e2 e', 
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eite b e1 e2) e') s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s) <->
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq (QFBV.Eite b e1 e2) e') s ->
              QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) (QFBV.Eite b e1 e2) e') s).
Proof.
  split;
    (move => Hes s0 Heq; move : (Hes s0 Heq); rewrite -eval_subst_spec_eite_eqn//).
Qed.

Lemma eval_subst_exp_exp :
  forall el e e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq el e') s ->
    QFBV.eval_exp e s = QFBV.eval_exp (subst_eq_exp_exp e el e') s
with eval_subst_bexp_exp :
  forall el be e' s,
    QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq el e') s ->
    QFBV.eval_bexp be s = QFBV.eval_bexp (subst_eq_bexp_exp be el e') s.
Proof.
  case.
  - move => t e; move : e t. apply : eval_subst_exp_evar.
  - move => b e; move : e b. apply : eval_subst_exp_econst.
  - move => e e0 e1; move : e1 e e0. apply : eval_subst_exp_eunop.
  - move => e e0 e1 e2; move : e2 e e0 e1. apply eval_subst_exp_ebinop.
  - move => b e e0 e1; move : e1 b e e0. apply eval_subst_exp_eite.
  case.
  - move => t e; move : e t. apply : eval_subst_bexp_evar.
  - move => b e; move : e b. apply : eval_subst_bexp_econst.
  - move => e e0 e1; move : e1 e e0. apply : eval_subst_bexp_eunop.
  - move => e e0 e1 e2; move : e2 e e0 e1. apply eval_subst_bexp_ebinop.
  - move => b e e0 e1; move : e1 b e e0. apply eval_subst_bexp_eite.
Qed.

Lemma eval_subst_spec_bexp_eqn es e e' s:
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e e') s ->
  (QFBV.eval_bexp (qfbv_bexp_spec es) s
   = QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) e e') s).
Proof.
  intros; rewrite /=. 
  destruct es as [E (epre, rpre) pg (epst, rpst)]; rewrite/= . 
  case ((bexp_program E (rng_program pg))); rewrite /=.
  - rewrite /= in H. rewrite 2!andbT -!eval_subst_bexp_exp//.
  - intros. rewrite /= in H. rewrite -!eval_subst_bexp_exp//.
Qed.

Lemma eval_subst_spec_bexp_iff es e e' s :
  QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e e') s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s <->
  QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) e e') s.
Proof.
  intros. split; rewrite -eval_subst_spec_bexp_eqn//. Qed.

Lemma eval_subst_spec_bexp_correct :
  forall es e e', 
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e e') s ->
  QFBV.eval_bexp (qfbv_bexp_spec es) s) <->
  (forall s, QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e e') s ->
              QFBV.eval_bexp (subst_eq_bexp_exp (qfbv_bexp_spec es) e e') s).
Proof.
  split;
    (move => Hes s0 Heq; move : (Hes s0 Heq); rewrite -eval_subst_spec_bexp_eqn//).
Qed.
