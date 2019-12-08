
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State BBCommon.
From ssrlib Require Import Var SsrOrder ZAriths FSets FMaps Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope dsl with dsl.

Section Operators.

  Inductive eunop : Set :=
  | Eneg.

  Inductive ebinop : Set :=
  | Eadd
  | Esub
  | Emul.

  Inductive runop : Set :=
  | Rnegb
  | Rnotb.

  Inductive rbinop : Set :=
  | Radd
  | Rsub
  | Rmul
  | Rumod
  | Rsrem (* 2's complement signed remainder (sign follows dividend) *)
  | Rsmod (* 2's complement signed remainder (sign follows divisor) *)
  | Randb
  | Rorb
  | Rxorb.

  Inductive rcmpop : Set :=
  | Rult
  | Rule
  | Rugt
  | Ruge
  | Rslt
  | Rsle
  | Rsgt
  | Rsge.

  Definition eunop_eqn (o1 o2 : eunop) : bool :=
    match o1, o2 with
    | Eneg, Eneg => true
    end.

  Lemma eunop_eqn_refl o : eunop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma eunop_eqn_eq o1 o2 : eunop_eqn o1 o2 <-> o1 = o2.
  Proof. by split; case: o1; case: o2 => //=. Qed.

  Lemma eunop_eqP (o1 o2 : eunop) : reflect (o1 = o2) (eunop_eqn o1 o2).
  Proof.
    case H: (eunop_eqn o1 o2).
    - apply: ReflectT. apply/eunop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/eunop_eqn_eq.
      assumption.
  Qed.

  Definition eunop_eqMixin := EqMixin eunop_eqP.
  Canonical eunop_eqType := Eval hnf in EqType eunop eunop_eqMixin.

  Definition ebinop_eqn (o1 o2 : ebinop) : bool :=
    match o1, o2 with
    | Eadd, Eadd
    | Esub, Esub
    | Emul, Emul => true
    | _, _ => false
    end.

  Lemma ebinop_eqn_refl o : ebinop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma ebinop_eqn_eq o1 o2 : ebinop_eqn o1 o2 <-> o1 = o2.
  Proof. by split; case: o1; case: o2 => //=. Qed.

  Lemma ebinop_eqP (o1 o2 : ebinop) : reflect (o1 = o2) (ebinop_eqn o1 o2).
  Proof.
    case H: (ebinop_eqn o1 o2).
    - apply: ReflectT. apply/ebinop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/ebinop_eqn_eq.
      assumption.
  Qed.

  Definition ebinop_eqMixin := EqMixin ebinop_eqP.
  Canonical ebinop_eqType := Eval hnf in EqType ebinop ebinop_eqMixin.

  Definition runop_eqn (o1 o2 : runop) : bool :=
    match o1, o2 with
    | Rnegb, Rnegb
    | Rnotb, Rnotb => true
    | _, _ => false
    end.

  Lemma runop_eqn_refl o : runop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma runop_eqn_eq o1 o2 : runop_eqn o1 o2 <-> o1 = o2.
  Proof. by split; case: o1; case: o2 => //=. Qed.

  Lemma runop_eqP (o1 o2 : runop) : reflect (o1 = o2) (runop_eqn o1 o2).
  Proof.
    case H: (runop_eqn o1 o2).
    - apply: ReflectT. apply/runop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/runop_eqn_eq.
      assumption.
  Qed.

  Definition runop_eqMixin := EqMixin runop_eqP.
  Canonical runop_eqType := Eval hnf in EqType runop runop_eqMixin.

  Definition rbinop_eqn (o1 o2 : rbinop) : bool :=
    match o1, o2 with
    | Radd, Radd
    | Rsub, Rsub
    | Rmul, Rmul
    | Rumod, Rumod
    | Rsrem, Rsrem
    | Rsmod, Rsmod
    | Randb, Randb
    | Rorb, Rorb
    | Rxorb, Rxorb => true
    | _, _ => false
    end.

  Lemma rbinop_eqn_refl o : rbinop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma rbinop_eqn_eq o1 o2 : rbinop_eqn o1 o2 <-> o1 = o2.
  Proof. by split; case: o1; case: o2 => //=. Qed.

  Lemma rbinop_eqP (o1 o2 : rbinop) : reflect (o1 = o2) (rbinop_eqn o1 o2).
  Proof.
    case H: (rbinop_eqn o1 o2).
    - apply: ReflectT. apply/rbinop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/rbinop_eqn_eq.
      assumption.
  Qed.

  Definition rbinop_eqMixin := EqMixin rbinop_eqP.
  Canonical rbinop_eqType := Eval hnf in EqType rbinop rbinop_eqMixin.

  Definition rcmpop_eqn (o1 o2 : rcmpop) : bool :=
    match o1, o2 with
    | Rult, Rult
    | Rule, Rule
    | Rugt, Rugt
    | Ruge, Ruge
    | Rslt, Rslt
    | Rsle, Rsle
    | Rsgt, Rsgt
    | Rsge, Rsge => true
    | _, _ => false
    end.

  Lemma rcmpop_eqn_refl o : rcmpop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma rcmpop_eqn_eq o1 o2 : rcmpop_eqn o1 o2 <-> o1 = o2.
  Proof. by split; case: o1; case: o2 => //=. Qed.

  Lemma rcmpop_eqP (o1 o2 : rcmpop) : reflect (o1 = o2) (rcmpop_eqn o1 o2).
  Proof.
    case H: (rcmpop_eqn o1 o2).
    - apply: ReflectT. apply/rcmpop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/rcmpop_eqn_eq.
      assumption.
  Qed.

  Definition rcmpop_eqMixin := EqMixin rcmpop_eqP.
  Canonical rcmpop_eqType := Eval hnf in EqType rcmpop rcmpop_eqMixin.

End Operators.



Section DSLRaw.

  Variable var : eqType.

  Inductive eexp : Type :=
  | Evar : var -> eexp
  | Econst : Z -> eexp
  | Eunop : eunop -> eexp -> eexp
  | Ebinop : ebinop -> eexp -> eexp -> eexp.

  Definition evar v := Evar v.
  Definition econst n := Econst n.
  Definition eunary op e := Eunop op e.
  Definition ebinary op e1 e2 := Ebinop op e1 e2.
  Definition eneg e := Eunop Eneg e.
  Definition eadd e1 e2 := Ebinop Eadd e1 e2.
  Definition esub e1 e2 := Ebinop Esub e1 e2.
  Definition emul e1 e2 := Ebinop Emul e1 e2.
  Definition esq e := Ebinop Emul e e.

  Definition eadds (es : seq eexp) : eexp :=
    match es with
    | [::] => econst Z.zero
    | e::[::] => e
    | e::es => foldl (fun res e => eadd res e) e es
    end.

  Definition emuls (es : seq eexp) : eexp :=
    match es with
    | [::] => econst Z.one
    | e::[::] => e
    | e::es => foldl (fun res e => emul res e) e es
    end.

  Definition zexpn2 n := Z.pow 2%Z n.

  Definition eexpn2 n := econst (Z.pow 2%Z n).

  Fixpoint eexp_eqn (e1 e2 : eexp) : bool :=
    match e1, e2 with
    | Evar v1, Evar v2 => v1 == v2
    | Econst n1, Econst n2 => n1 == n2
    | Eunop op1 e1, Eunop op2 e2 => (op1 == op2) && eexp_eqn e1 e2
    | Ebinop op1 e1 e2, Ebinop op2 e3 e4 =>
      (op1 == op2) && eexp_eqn e1 e3 && eexp_eqn e2 e4
    | _, _ => false
    end.

  Lemma eexp_eqn_eq (e1 e2 : eexp) : eexp_eqn e1 e2 -> e1 = e2.
  Proof.
    elim: e1 e2 => [v1 | n1 | op1 e1 IH1 | op1 e1 IH1 e2 IH2] [] //=.
    - by move=> ? /eqP ->.
    - by move=> ? /eqP ->.
    - by move=> ? ? /andP [/eqP -> H]; rewrite (IH1 _ H).
    - by move=> ? ? ? /andP [/andP [/eqP -> H1] H2]; rewrite (IH1 _ H1) (IH2 _ H2).
  Qed.

  Lemma eexp_eqn_refl (e : eexp) : eexp_eqn e e.
  Proof.
    elim: e => //=.
    - by move=> ? ? ->; rewrite eqxx.
    - by move=> ? ? -> ? ->; rewrite eqxx.
  Qed.

  Lemma eexp_eqn_sym {e1 e2 : eexp} : eexp_eqn e1 e2 -> eexp_eqn e2 e1.
  Proof. move=> H; rewrite (eexp_eqn_eq H); exact: eexp_eqn_refl. Qed.

  Lemma eexp_eqn_trans {e1 e2 e3 : eexp} :
    eexp_eqn e1 e2 -> eexp_eqn e2 e3 -> eexp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (eexp_eqn_eq H1) (eexp_eqn_eq H2). exact: eexp_eqn_refl.
  Qed.

  Lemma eexp_eqP (e1 e2 : eexp) : reflect (e1 = e2) (eexp_eqn e1 e2).
  Proof.
    case H: (eexp_eqn e1 e2).
    - apply: ReflectT. exact: (eexp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: eexp_eqn_refl.
  Qed.

  Definition eexp_eqMixin := EqMixin eexp_eqP.
  Canonical eexp_eqType := Eval hnf in EqType eexp eexp_eqMixin.

  (* Limbs *)

  Fixpoint limbsi (i : nat) (r : Z) (es : seq eexp) :=
    match es with
    | [::] => econst Z.zero
    | e::[::] => e
    | e::es => eadd (emul e (eexpn2 (Z.of_nat i * r))) (limbsi (i + 1) r es)
    end.

  Definition limbs (r : Z) (es : seq eexp) := limbsi 0 r es.

  (* Range Expressions *)

  (* The first nat is the size of the subexpression *)
  Inductive rexp : Type :=
  | Rvar : var -> rexp
  | Rconst : nat -> bits -> rexp
  | Runop : nat -> runop -> rexp -> rexp
  | Rbinop : nat -> rbinop -> rexp -> rexp -> rexp
  | Ruext : nat -> rexp -> nat -> rexp
  | Rsext : nat -> rexp -> nat -> rexp.

  Definition rvar v := Rvar v.
  Definition rconst w n := Rconst w n.
  Definition rbits n := Rconst (size n) n.
  Definition runary w op e := Runop w op e.
  Definition rbinary w op e1 e2 := Rbinop w op e1 e2.
  Definition rnegb w e := Runop w Rnegb e.
  Definition rnotb w e := Runop w Rnotb e.
  Definition radd w e1 e2 := Rbinop w Radd e1 e2.
  Definition rsub w e1 e2 := Rbinop w Rsub e1 e2.
  Definition rmul w e1 e2 := Rbinop w Rmul e1 e2.
  Definition rumod w e1 e2 := Rbinop w Rumod e1 e2.
  Definition rsrem w e1 e2 := Rbinop w Rsrem e1 e2.
  Definition rsmod w e1 e2 := Rbinop w Rsmod e1 e2.
  Definition randb w e1 e2 := Rbinop w Randb e1 e2.
  Definition rorb w e1 e2 := Rbinop w Rorb e1 e2.
  Definition rxorb w e1 e2 := Rbinop w Rxorb e1 e2.
  Definition rsq w e := Rbinop w Rmul e e.

  Definition radds w es :=
    match es with
    | [::] => rbits (from_nat w 0)
    | e::[::] => e
    | e::es => foldl (fun res e => radd w res e) e es
    end.

  Definition rmuls w es :=
    match es with
    | [::] => rbits (from_nat w 1)
    | e::[::] => e
    | e::es => foldl (fun res e => rmul w res e) e es
    end.

  Fixpoint rexp_eqn (e1 e2 : rexp) : bool :=
    match e1, e2 with
    | Rvar v1, Rvar v2 => v1 == v2
    | Rconst w1 n1, Rconst w2 n2 => (w1 == w2) && (n1 == n2)
    | Runop w1 op1 e1, Runop w2 op2 e2 =>
      (w1 == w2) && (op1 == op2) && rexp_eqn e1 e2
    | Rbinop w1 op1 e1 e2, Rbinop w2 op2 e3 e4 =>
      (w1 == w2) && (op1 == op2) && rexp_eqn e1 e3 && rexp_eqn e2 e4
    | Ruext w1 e1 n1, Ruext w2 e2 n2
    | Rsext w1 e1 n1, Rsext w2 e2 n2 =>
      (w1 == w2) && (rexp_eqn e1 e2) && (n1 == n2)
    | _, _ => false
    end.

  Lemma rexp_eqn_eq (e1 e2 : rexp) : rexp_eqn e1 e2 -> e1 = e2.
  Proof.
    elim: e1 e2 => [v1 | w1 n1 | ow1 p1 e1 IH1 | w1 op1 e1 IH1 e2 IH2
                     | w1 e1 IH1 n1 | w1 e1 IH1 n1] [] //=.
    - by move=> ? /eqP ->.
    - by move=> ? ? /andP [/eqP -> /eqP ->].
    - by move=> ? ? ? /andP [/andP [/eqP -> /eqP ->] H]; rewrite (IH1 _ H).
    - by move=> ? ? ? ? /andP [/andP [/andP [/eqP -> /eqP ->] H1] H2];
                  rewrite (IH1 _ H1) (IH2 _ H2).
    - by move=> ? ? ? /andP [/andP [/eqP -> H] /eqP ->]; rewrite (IH1 _ H).
    - by move=> ? ? ? /andP [/andP [/eqP -> H] /eqP ->]; rewrite (IH1 _ H).
  Qed.

  Lemma rexp_eqn_refl (e : rexp) : rexp_eqn e e.
  Proof.
    elim: e => //=.
    - by move=> ? ?; rewrite !eqxx.
    - by move=> ? ? ? ->; rewrite !eqxx.
    - by move=> ? ? ? -> ? ->; rewrite !eqxx.
    - by move=> ? ? -> ?; rewrite !eqxx.
    - by move=> ? ? -> ?; rewrite !eqxx.
  Qed.

  Lemma rexp_eqn_sym {e1 e2 : rexp} : rexp_eqn e1 e2 -> rexp_eqn e2 e1.
  Proof. move=> H; rewrite (rexp_eqn_eq H); exact: rexp_eqn_refl. Qed.

  Lemma rexp_eqn_trans {e1 e2 e3 : rexp} :
    rexp_eqn e1 e2 -> rexp_eqn e2 e3 -> rexp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (rexp_eqn_eq H1) (rexp_eqn_eq H2). exact: rexp_eqn_refl.
  Qed.

  Lemma rexp_eqP (e1 e2 : rexp) : reflect (e1 = e2) (rexp_eqn e1 e2).
  Proof.
    case H: (rexp_eqn e1 e2).
    - apply: ReflectT. exact: (rexp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: rexp_eqn_refl.
  Qed.

  Definition rexp_eqMixin := EqMixin rexp_eqP.
  Canonical rexp_eqType := Eval hnf in EqType rexp rexp_eqMixin.

  (* Algebraic Predicates *)

  Inductive ebexp : Type :=
  | Etrue
  | Eeq : eexp -> eexp -> ebexp
  | Eeqmod : eexp -> eexp -> eexp -> ebexp
  | Eand : ebexp -> ebexp -> ebexp.

  Definition etrue := Etrue.
  Definition eeq e1 e2 := Eeq e1 e2.
  Definition eeqmod e1 e2 m := Eeqmod e1 e2 m.
  Definition eand b1 b2 := Eand b1 b2.

  Definition eands es := foldl (fun res e => eand res e) Etrue es.

  Fixpoint ebexp_eqn (e1 e2 : ebexp) : bool :=
    match e1, e2 with
    | Etrue, Etrue => true
    | Eeq e1 e2, Eeq e3 e4 => (e1 == e3) && (e2 == e4)
    | Eeqmod e1 e2 m1, Eeqmod e3 e4 m2 => (e1 == e3) && (e2 == e4) && (m1 == m2)
    | Eand e1 e2, Eand e3 e4 => ebexp_eqn e1 e3 && ebexp_eqn e2 e4
    | _, _ => false
    end.

  Lemma ebexp_eqn_eq (e1 e2 : ebexp) : ebexp_eqn e1 e2 -> e1 = e2.
  Proof.
    elim: e1 e2 => [| e1 e2 | e1 e2 m | e1 IH1 e2 IH2] [] //=.
    - by move=> ? ? /andP [/eqP -> /eqP ->].
    - by move=> ? ? ? /andP [/andP [/eqP -> /eqP ->] /eqP ->].
    - by move=> ? ? /andP [H1 H2]; rewrite (IH1 _ H1) (IH2 _ H2).
  Qed.

  Lemma ebexp_eqn_refl (e : ebexp) : ebexp_eqn e e.
  Proof.
    elim: e => //=; try by (move=> *; rewrite !eqxx). by move=> e1 -> e2 ->.
  Qed.

  Lemma ebexp_eqn_sym {e1 e2 : ebexp} : ebexp_eqn e1 e2 -> ebexp_eqn e2 e1.
  Proof. move=> H; rewrite (ebexp_eqn_eq H); exact: ebexp_eqn_refl. Qed.

  Lemma ebexp_eqn_trans {e1 e2 e3 : ebexp} :
    ebexp_eqn e1 e2 -> ebexp_eqn e2 e3 -> ebexp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (ebexp_eqn_eq H1) (ebexp_eqn_eq H2). exact: ebexp_eqn_refl.
  Qed.

  Lemma ebexp_eqP (e1 e2 : ebexp) : reflect (e1 = e2) (ebexp_eqn e1 e2).
  Proof.
    case H: (ebexp_eqn e1 e2).
    - apply: ReflectT. exact: (ebexp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq.
      exact: ebexp_eqn_refl.
  Qed.

  Definition ebexp_eqMixin := EqMixin ebexp_eqP.
  Canonical ebexp_eqType := Eval hnf in EqType ebexp ebexp_eqMixin.

  (* Range Predicates *)

  Inductive rbexp : Type :=
  | Rtrue
  | Req : nat -> rexp -> rexp -> rbexp
  | Rcmp : nat -> rcmpop -> rexp -> rexp -> rbexp
  | Rneg : rbexp -> rbexp
  | Rand : rbexp -> rbexp -> rbexp
  | Ror : rbexp -> rbexp -> rbexp.

  Definition rtrue := Rtrue.
  Definition rfalse := Rneg Rtrue.
  Definition req w e1 e2 := Req w e1 e2.
  Definition rcmp w op e1 e2 := Rcmp w op e1 e2.
  Definition rult w e1 e2 := Rcmp w Rult e1 e2.
  Definition rule w e1 e2 := Rcmp w Rule e1 e2.
  Definition rugt w e1 e2 := Rcmp w Rugt e1 e2.
  Definition ruge w e1 e2 := Rcmp w Ruge e1 e2.
  Definition rslt w e1 e2 := Rcmp w Rslt e1 e2.
  Definition rsle w e1 e2 := Rcmp w Rsle e1 e2.
  Definition rsgt w e1 e2 := Rcmp w Rsgt e1 e2.
  Definition rsge w e1 e2 := Rcmp w Rsge e1 e2.
  Definition reqmod w e1 e2 m :=
    req w (rsrem w (rsub w e1 e2) m) (rbits (from_nat w 0)).

  Definition rneg e :=
    match e with
    | Rneg e' => e'
    | _ => Rneg e
    end.

  Definition rand e1 e2 :=
    match e1, e2 with
    | Rtrue, e
    | e, Rtrue => e
    | Rneg Rtrue, _
    | _, Rneg Rtrue => Rneg Rtrue
    | _, _ => Rand e1 e2
    end.

  Definition ror e1 e2 :=
    match e1, e2 with
    | Rtrue, _
    | _, Rtrue => Rtrue
    | Rneg Rtrue, e
    | e, Rneg Rtrue => e
    | _, _ => Ror e1 e2
    end.

  Definition rands es := foldl (fun res e => rand res e) Rtrue es.
  Definition rors es := foldl (fun res e => ror res e) (Rneg Rtrue) es.

  Fixpoint rbexp_eqn (e1 e2 : rbexp) : bool :=
    match e1, e2 with
    | Rtrue, Rtrue => true
    | Req n1 e1 e2, Req n2 e3 e4 => (n1 == n2) && (e1 == e3) && (e2 == e4)
    | Rcmp n1 op1 e1 e2, Rcmp n2 op2 e3 e4 =>
      (n1 == n2) && (op1 == op2) && (e1 == e3) && (e2 == e4)
    | Rneg e1, Rneg e2 => rbexp_eqn e1 e2
    | Rand e1 e2, Rand e3 e4
    | Ror e1 e2, Ror e3 e4 => rbexp_eqn e1 e3 && rbexp_eqn e2 e4
    | _, _ => false
    end.

  Lemma rbexp_eqn_eq (e1 e2 : rbexp) : rbexp_eqn e1 e2 -> e1 = e2.
  Proof.
    elim: e1 e2 =>
    [| n1 e1 e2 | n1 op1 e1 e2 | e1 IH1 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2] [] //=.
    - by move=> ? ? ? /andP [/andP [/eqP -> /eqP ->] /eqP ->].
    - by move=> ? ? ? ? /andP [/andP [/andP [/eqP -> /eqP ->] /eqP ->] /eqP ->].
    - by move=> ? H; rewrite (IH1 _ H).
    - by move=> ? ? /andP [H1 H2]; rewrite (IH1 _ H1) (IH2 _ H2).
    - by move=> ? ? /andP [H1 H2]; rewrite (IH1 _ H1) (IH2 _ H2).
  Qed.

  Lemma rbexp_eqn_refl (e : rbexp) : rbexp_eqn e e.
  Proof.
    elim: e => //=; try by (move=> *; rewrite !eqxx).
    - by move=> e1 -> e2 ->.
    - by move=> e1 -> e2 ->.
  Qed.

  Lemma rbexp_eqn_sym {e1 e2 : rbexp} : rbexp_eqn e1 e2 -> rbexp_eqn e2 e1.
  Proof. move=> H; rewrite (rbexp_eqn_eq H); exact: rbexp_eqn_refl. Qed.

  Lemma rbexp_eqn_trans {e1 e2 e3 : rbexp} :
    rbexp_eqn e1 e2 -> rbexp_eqn e2 e3 -> rbexp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (rbexp_eqn_eq H1) (rbexp_eqn_eq H2). exact: rbexp_eqn_refl.
  Qed.

  Lemma rbexp_eqP (e1 e2 : rbexp) : reflect (e1 = e2) (rbexp_eqn e1 e2).
  Proof.
    case H: (rbexp_eqn e1 e2).
    - apply: ReflectT. exact: (rbexp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq.
      exact: rbexp_eqn_refl.
  Qed.

  Definition rbexp_eqMixin := EqMixin rbexp_eqP.
  Canonical rbexp_eqType := Eval hnf in EqType rbexp rbexp_eqMixin.

End DSLRaw.



Module MakeDSL
       (V : SsrOrder)
       (VS : SsrFSet with Module SE := V)
       (VM : SsrFMap with Module SE := V)
       (TE : TypEnv with Module SE := V)
       (S : BitsStore V TE).
  Local Open Scope dsl.
  Local Open Scope bits.

  Module VSLemmas := FSetLemmas VS.
  Module TELemmas := FMapLemmas TE.

  (* Variables *)

  Local Notation var := V.t.



  (* Algebraic Expressions *)

  Definition eexp := eexp V.T.

  Definition evar (v : V.t) : eexp := @Evar V.T v.
  Definition econst (n : Z) : eexp := @Econst V.T n.
  Definition eunary (op : eunop) (e : eexp) : eexp := @Eunop V.T op e.
  Definition ebinary (op : ebinop) (e1 e2 : eexp) : eexp := @Ebinop V.T op e1 e2.
  Definition eneg (e : eexp) : eexp := @Eunop V.T Eneg e.
  Definition eadd (e1 e2 : eexp) : eexp := @Ebinop V.T Eadd e1 e2.
  Definition esub (e1 e2 : eexp) : eexp := @Ebinop V.T Esub e1 e2.
  Definition emul (e1 e2 : eexp) : eexp := @Ebinop V.T Emul e1 e2.
  Definition esq (e : eexp) : eexp := @Ebinop V.T Emul e e.

  Definition eadds (es : seq eexp) : eexp := eadds es.
  Definition emuls (es : seq eexp) : eexp := emuls es.

  Definition zexpn2 n := Z.pow 2%Z n.
  Definition eexpn2 n := econst (Z.pow 2%Z n).

  Fixpoint vars_eexp (e : eexp) : VS.t :=
    match e with
    | Evar v => VS.singleton v
    | Econst n => VS.empty
    | Eunop op e => vars_eexp e
    | Ebinop op e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    end.



  (* Limbs *)

  Definition limbsi (i : nat) (r : Z) (es : seq eexp) : eexp := limbsi i r es.
  Definition limbs (r : Z) (es : seq eexp) : eexp := limbsi 0 r es.



  (* Range Expressions *)

  Definition rexp := rexp V.T.

  Fixpoint size_of_rexp (e : rexp) (te : TE.env) : nat :=
    match e with
    | Rvar v => TE.vsize v te
    | Rconst w n => w
    | Runop w _ _ => w
    | Rbinop w _ _ _ => w
    | Ruext w _ i => w + i
    | Rsext w _ i => w + i
    end.

  Definition rvar v : rexp := @Rvar V.T v.
  Definition rconst w (n : bits) : rexp := @Rconst V.T w n.
  Definition rbits (n : bits) : rexp := @rbits V.T n.
  Definition runary w (op : runop) (e : rexp) : rexp := @Runop V.T w op e.
  Definition rbinary w (op : rbinop) (e1 e2 : rexp) : rexp := @Rbinop V.T w op e1 e2.
  Definition rnegb w (e : rexp) : rexp := @Runop V.T w Rnegb e.
  Definition rnotb w (e : rexp) : rexp := @Runop V.T w Rnotb e.
  Definition radd w (e1 e2 : rexp) : rexp := @Rbinop V.T w Radd e1 e2.
  Definition rsub w (e1 e2 : rexp) : rexp := @Rbinop V.T w Rsub e1 e2.
  Definition rmul w (e1 e2 : rexp) : rexp := @Rbinop V.T w Rmul e1 e2.
  Definition rumod w (e1 e2 : rexp) : rexp := @Rbinop V.T w Rumod e1 e2.
  Definition rsrem w (e1 e2 : rexp) : rexp := @Rbinop V.T w Rsrem e1 e2.
  Definition rsmod w (e1 e2 : rexp) : rexp := @Rbinop V.T w Rsmod e1 e2.
  Definition randb w (e1 e2 : rexp) : rexp := @Rbinop V.T w Randb e1 e2.
  Definition rorb w (e1 e2 : rexp) : rexp := @Rbinop V.T w Rorb e1 e2.
  Definition rxorb w (e1 e2 : rexp) : rexp := @Rbinop V.T w Rxorb e1 e2.
  Definition rsq w (e : rexp) : rexp := @Rbinop V.T w Rmul e e.
  Definition ruext w (e : rexp) i : rexp := @Ruext V.T w e i.
  Definition rsext w (e : rexp) i : rexp := @Rsext V.T w e i.

  Definition radds w (es : seq rexp) : rexp := radds w es.
  Definition rmuls w (es : seq rexp) : rexp := rmuls w es.

  Fixpoint vars_rexp (e : rexp) : VS.t :=
    match e with
    | Rvar v => VS.singleton v
    | Rconst w n => VS.empty
    | Runop w op e => vars_rexp e
    | Rbinop w op e1 e2 => VS.union (vars_rexp e1) (vars_rexp e2)
    | Ruext w e i => vars_rexp e
    | Rsext w e i => vars_rexp e
    end.



  (* Algebraic Predicates *)

  Definition ebexp : Type := ebexp V.T.

  Definition etrue : ebexp := @Etrue V.T.
  Definition eeq (e1 e2 : eexp) : ebexp := @Eeq V.T e1 e2.
  Definition eeqmod (e1 e2 m : eexp) : ebexp := @Eeqmod V.T e1 e2 m.
  Definition eand (b1 b2 : ebexp) : ebexp := @Eand V.T b1 b2.

  Definition eands (es : seq ebexp) : ebexp := @eands V.T es.

  Fixpoint vars_ebexp (e : ebexp) : VS.t :=
    match e with
    | Etrue => VS.empty
    | Eeq e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    | Eeqmod e1 e2 m =>
      VS.union (vars_eexp e1) (VS.union (vars_eexp e2) (vars_eexp m))
    | Eand e1 e2 => VS.union (vars_ebexp e1) (vars_ebexp e2)
    end.



  (* Range Predicates *)

  Definition rbexp : Type := rbexp V.T.

  Definition rtrue : rbexp := @Rtrue V.T.
  Definition rfalse : rbexp := @Rneg V.T rtrue.
  Definition req w (e1 e2 : rexp) : rbexp := @Req V.T w e1 e2.
  Definition rcmp w (op : rcmpop) (e1 e2 : rexp) : rbexp := @Rcmp V.T w op e1 e2.
  Definition rult w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Rult e1 e2.
  Definition rule w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Rule e1 e2.
  Definition rugt w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Rugt e1 e2.
  Definition ruge w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Ruge e1 e2.
  Definition rslt w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Rslt e1 e2.
  Definition rsle w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Rsle e1 e2.
  Definition rsgt w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Rsgt e1 e2.
  Definition rsge w (e1 e2 : rexp) : rbexp := @Rcmp V.T w Rsge e1 e2.
  Definition reqmod w (e1 e2 m : rexp) : rbexp :=
    req w (rsrem w (rsub w e1 e2) m) (rbits (from_nat w 0)).

  Definition rneg (e : rbexp) : rbexp := @Rneg V.T e.
  Definition rand (e1 e2 : rbexp) : rbexp := @Rand V.T e1 e2.
  Definition ror (e1 e2 : rbexp) : rbexp := @Ror V.T e1 e2.

  Definition rands (es : seq rbexp) : rbexp := @rands V.T es.
  Definition rors (es : seq rbexp) : rbexp := @rors V.T es.

  Fixpoint vars_rbexp (e : rbexp) : VS.t :=
    match e with
    | Rtrue => VS.empty
    | Req w e1 e2 => VS.union (vars_rexp e1) (vars_rexp e2)
    | Rcmp w op e1 e2 => VS.union (vars_rexp e1) (vars_rexp e2)
    | Rneg e => vars_rbexp e
    | Rand e1 e2
    | Ror e1 e2 => VS.union (vars_rbexp e1) (vars_rbexp e2)
    end.



  (* Predicates *)

  Definition bexp : Type := ebexp * rbexp.

  Definition btrue : bexp := (etrue, rtrue).

  Definition eqn_bexp (e : bexp) : ebexp := e.1.
  Definition rng_bexp (e : bexp) : rbexp := e.2.

  Definition band (e1 e2 : bexp) : bexp :=
    match e1, e2 with
    | (Etrue, Rtrue), (ee, re)
    | (ee, re), (Etrue, Rtrue)
    | (Etrue, re), (ee, Rtrue)
    | (ee, Rtrue), (Etrue, re) => (ee, re)
    | (ee1, re1), (ee2, re2) => (eand ee1 ee2, rand re1 re2)
    end.

  Definition bands es := foldl (fun res e => band res e) btrue es.
  Definition bands2 es rs := (eands es, rands rs).

  Definition vars_bexp (e : bexp) : VS.t :=
    VS.union (vars_ebexp (eqn_bexp e)) (vars_rbexp (rng_bexp e)).

  Lemma vars_ebexp_subset e :
    VS.subset (vars_ebexp (eqn_bexp e)) (vars_bexp e).
  Proof.
    apply: VSLemmas.subset_union1. exact: VSLemmas.subset_refl.
  Qed.

  Lemma vars_rbexp_subset e :
    VS.subset (vars_rbexp (rng_bexp e)) (vars_bexp e).
  Proof.
    apply: VSLemmas.subset_union2. exact: VSLemmas.subset_refl.
  Qed.


  (* Instructions and programs *)

  Inductive atomic : Type :=
  | Avar : var -> atomic
  | Aconst : typ -> bits -> atomic.

  Definition atyp (a : atomic) (te : TE.env) : typ :=
    match a with
    | Avar v => TE.vtyp v te
    | Aconst ty _ => ty
    end.

  Definition asize (a : atomic) (te : TE.env) : nat := sizeof_typ (atyp a te).

  Inductive instr : Type :=
  (* Imov (v, a): v = a *)
  | Imov : var -> atomic -> instr
  (* Ishl (v, a, n): v = a * 2^n, overflow is forbidden *)
  | Ishl : var -> atomic -> nat -> instr
  (* Icshl (vh, vl, a1, a2, n) *)
  | Icshl : var -> var -> atomic -> atomic -> nat -> instr
  (* Inondet (v, t): v = a nondeterministic value of type t *)
  | Inondet : var -> typ -> instr
  (* Icmov (v, c, a1, a2): if c then v = a1 else v = a2 *)
  | Icmov : var -> atomic -> atomic -> atomic -> instr
  (* Inop: do nothing *)
  | Inop : instr
  (* Inot (v, t, a): v = not(a), the one's complement of a, v is of type t *)
  | Inot : var -> typ -> atomic -> instr
  (* Iadd (v, a1, a2): v = a1 + a2, overflow is forbidden *)
  | Iadd : var -> atomic -> atomic -> instr
  (* Iadds (c, v, a1, a2): v = a1 + a2, c = carry flag *)
  | Iadds : var -> var -> atomic -> atomic -> instr
  (* Iadc (v, a1, a2, y): v = a1 + a2 + y, overflow is forbidden *)
  | Iadc : var -> atomic -> atomic -> atomic -> instr
  (* Iadcs (c, v, a1, a2, y): v = a1 + a2 + y, c = carry flag *)
  | Iadcs : var -> var -> atomic -> atomic -> atomic -> instr
  (* Isub (v, a1, a2): v = a1 - a2, overflow is forbidden *)
  | Isub : var -> atomic -> atomic -> instr
  (* Isubc (c, v, a1, a2): v = a1 + not(a2) + 1, c = carry flag *)
  | Isubc : var -> var -> atomic -> atomic -> instr
  (* Isous (b, v, a1, a2): v = a1 - a2, b = borrow flag *)
  | Isubb : var -> var -> atomic -> atomic -> instr
  (* Isbc (v, a1, a2, y): v = a1 + not(a2) + y *)
  | Isbc : var -> atomic -> atomic -> atomic -> instr
  (* Isbcs (c, v, a1, a2, y): v = a1 + not(a2) + y, c = carry flag *)
  | Isbcs : var -> var -> atomic -> atomic -> atomic -> instr
  (* Isbb (v, a1, a2, y): v = a1 - a2 - y *)
  | Isbb : var -> atomic -> atomic -> atomic -> instr
  (* Isbbs (b, v, a1, a2, y): v = a1 - a2 - y, b = borrow flag *)
  | Isbbs : var -> var -> atomic -> atomic -> atomic -> instr
  (* Imul (v, a1, a2): v = a1 * a2, overflow is forbidden *)
  | Imul : var -> atomic -> atomic -> instr
  (* Imull (vh, vl, a1, a2): vh and vl are respectively the high part and
     the low part of the full multiplication a1 * a2 *)
  | Imull : var -> var -> atomic -> atomic -> instr
  (* Iumulj (v, a1, a2): v = the full multiplication of a1 * a2, which is equivalent
     to Iumull (vh, vl, a1, a2); Join (r, vh, vl) *)
  | Imulj : var -> atomic -> atomic -> instr
  (* Isplit (vh, vl, a, n): vh is the high (w - n) bits (signed extended to w bits)
     of a and vl is the low n bits (zero extended to w bits) of a where w is the
     bit-width of a *)
  | Isplit : var -> var -> atomic -> nat -> instr
  (* == Instructions that cannot be translated to polynomials == *)
  (* Iand (v, t, a1, a2): v = the bitwise AND of a1 and a2, v is of type t *)
  | Iand : var -> typ -> atomic -> atomic -> instr
  (* Ior (v, t, a1, a2): v = the bitwise OR of a1 and a2, v is of type t *)
  | Ior : var -> typ -> atomic -> atomic -> instr
  (* Ixor (v, t, a1, a2): v = the bitwise XOR of a1 and a2, v is of type t *)
  | Ixor : var -> typ -> atomic -> atomic -> instr
  (* == Type conversions == *)
  (* Icast (v, t, a): v = the value of a represented by the type t of v *)
  | Icast : var -> typ -> atomic -> instr
  (* Ivpc (v, t, a): v = a, value preserved casting to type t *)
  | Ivpc : var -> typ -> atomic -> instr
  (* Ijoin (v, ah, al): v = ah * 2^w + al where w is the bit-width of al *)
  | Ijoin : var -> atomic -> atomic -> instr
  (* Specifications *)
  | Iassume : bexp -> instr.

  Definition program := seq instr.

  Definition vars_atomic (a : atomic) : VS.t :=
    match a with
    | Avar v => VS.singleton v
    | Aconst _ _ => VS.empty
    end.

  Definition vars_instr (i : instr) : VS.t :=
    match i with
    | Imov v a
    | Ishl v a _ => VS.add v (vars_atomic a)
    | Icshl vh vl a1 a2 _ =>
      VS.add vh (VS.add vl (VS.union (vars_atomic a1) (vars_atomic a2)))
    | Inondet v _ => VS.singleton v
    | Icmov v c a1 a2 =>
      VS.add v (VS.union (vars_atomic c)
                         (VS.union (vars_atomic a1) (vars_atomic a2)))
    | Inop => VS.empty
    | Inot v _ a => VS.add v (vars_atomic a)
    | Iadd v a1 a2 => VS.add v (VS.union (vars_atomic a1) (vars_atomic a2))
    | Iadds c v a1 a2 =>
      VS.add c (VS.add v (VS.union (vars_atomic a1) (vars_atomic a2)))
    | Iadc v a1 a2 y =>
      VS.add v (VS.union (vars_atomic a1)
                         (VS.union (vars_atomic a2) (vars_atomic y)))
    | Iadcs c v a1 a2 y =>
      VS.add c (VS.add v (VS.union (vars_atomic a1)
                                   (VS.union (vars_atomic a2) (vars_atomic y))))
    | Isub v a1 a2 => VS.add v (VS.union (vars_atomic a1) (vars_atomic a2))
    | Isubc c v a1 a2
    | Isubb c v a1 a2 =>
      VS.add c (VS.add v (VS.union (vars_atomic a1) (vars_atomic a2)))
    | Isbc v a1 a2 y =>
      VS.add v (VS.union (vars_atomic a1)
                         (VS.union (vars_atomic a2) (vars_atomic y)))
    | Isbcs c v a1 a2 y =>
      VS.add c (VS.add v (VS.union (vars_atomic a1)
                                   (VS.union (vars_atomic a2) (vars_atomic y))))
    | Isbb v a1 a2 y =>
      VS.add v (VS.union (vars_atomic a1)
                         (VS.union (vars_atomic a2) (vars_atomic y)))
    | Isbbs c v a1 a2 y =>
      VS.add c (VS.add v (VS.union (vars_atomic a1)
                                   (VS.union (vars_atomic a2) (vars_atomic y))))
    | Imul v a1 a2 => VS.add v (VS.union (vars_atomic a1) (vars_atomic a2))
    | Imull vh vl a1 a2 =>
      VS.add vh (VS.add vl (VS.union (vars_atomic a1) (vars_atomic a2)))
    | Imulj v a1 a2 => VS.add v (VS.union (vars_atomic a1) (vars_atomic a2))
    | Isplit vh vl a n => VS.add vh (VS.add vl (vars_atomic a))
    | Iand v _ a1 a2
    | Ior v _ a1 a2
    | Ixor v _ a1 a2 => VS.add v (VS.union (vars_atomic a1) (vars_atomic a2))
    | Icast v t a
    | Ivpc v t a => VS.add v (vars_atomic a)
    | Ijoin v ah al => VS.add v (VS.union (vars_atomic ah) (vars_atomic al))
    | Iassume e => vars_bexp e
    end.

  Definition lvs_instr (i : instr) : VS.t :=
    match i with
    | Imov v _
    | Ishl v _ _ => VS.singleton v
    | Icshl vh vl _ _ _ => VS.add vh (VS.singleton vl)
    | Inondet v _
    | Icmov v _ _ _ => VS.singleton v
    | Inop => VS.empty
    | Inot v _ _
    | Iadd v _ _ => VS.singleton v
    | Iadds c v _ _ => VS.add c (VS.singleton v)
    | Iadc v _ _ _ => VS.singleton v
    | Iadcs c v _ _ _ => VS.add c (VS.singleton v)
    | Isub v _ _ => VS.singleton v
    | Isubc c v _ _
    | Isubb c v _ _ => VS.add c (VS.singleton v)
    | Isbc v _ _ _ => VS.singleton v
    | Isbcs c v _ _ _ => VS.add c (VS.singleton v)
    | Isbb v _ _ _ => VS.singleton v
    | Isbbs c v _ _ _ => VS.add c (VS.singleton v)
    | Imul v _ _ => VS.singleton v
    | Imull vh vl _ _ => VS.add vh (VS.singleton vl)
    | Imulj v _ _ => VS.singleton v
    | Isplit vh vl _ _ => VS.add vh (VS.singleton vl)
    | Iand v _ _ _
    | Ior v _ _ _
    | Ixor v _ _ _
    | Icast v _ _
    | Ivpc v _ _
    | Ijoin v _ _ => VS.singleton v
    | Iassume _ => VS.empty
    end.

  Definition rvs_instr (i : instr) : VS.t :=
    match i with
    | Imov _ a
    | Ishl _ a _ => vars_atomic a
    | Icshl _ _ a1 a2 _ => VS.union (vars_atomic a1) (vars_atomic a2)
    | Inondet _ _ => VS.empty
    | Icmov _ c a1 a2 => VS.union (vars_atomic c)
                                  (VS.union (vars_atomic a1) (vars_atomic a2))
    | Inop => VS.empty
    | Inot _ _ a => vars_atomic a
    | Iadd _ a1 a2
    | Iadds _ _ a1 a2 => VS.union (vars_atomic a1) (vars_atomic a2)
    | Iadc _ a1 a2 y
    | Iadcs _ _ a1 a2 y => VS.union (vars_atomic a1)
                                    (VS.union (vars_atomic a2) (vars_atomic y))
    | Isub _ a1 a2
    | Isubc _ _ a1 a2
    | Isubb _ _ a1 a2 => VS.union (vars_atomic a1) (vars_atomic a2)
    | Isbc _ a1 a2 y
    | Isbcs _ _ a1 a2 y
    | Isbb _ a1 a2 y
    | Isbbs _ _ a1 a2 y => VS.union (vars_atomic a1)
                                    (VS.union (vars_atomic a2) (vars_atomic y))
    | Imul _ a1 a2
    | Imull _ _ a1 a2
    | Imulj _ a1 a2 => VS.union (vars_atomic a1) (vars_atomic a2)
    | Isplit _ _ a _ => vars_atomic a
    | Iand _ _ a1 a2
    | Ior _ _ a1 a2
    | Ixor _ _ a1 a2 => VS.union (vars_atomic a1) (vars_atomic a2)
    | Icast _ _ a
    | Ivpc _ _ a => vars_atomic a
    | Ijoin _ ah al => VS.union (vars_atomic ah) (vars_atomic al)
    | Iassume e => vars_bexp e
    end.

  Fixpoint vars_program (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | hd::tl => VS.union (vars_instr hd) (vars_program tl)
    end.

  Fixpoint lvs_program (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | hd::tl => VS.union (lvs_instr hd) (lvs_program tl)
    end.

  Fixpoint rvs_program (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | hd::tl => VS.union (rvs_instr hd) (rvs_program tl)
    end.

  Lemma vars_instr_split i :
    VS.Equal (vars_instr i) (VS.union (lvs_instr i) (rvs_instr i)).
  Proof. case: i => /=; move=> *; by VSLemmas.dp_Equal. Qed.

  Lemma mem_vars_instr1 v i :
    VS.mem v (vars_instr i) -> VS.mem v (lvs_instr i) \/ VS.mem v (rvs_instr i).
  Proof. rewrite vars_instr_split => H. exact: (VSLemmas.mem_union1 H). Qed.

  Lemma mem_vars_instr2 v i : VS.mem v (lvs_instr i) -> VS.mem v (vars_instr i).
  Proof. rewrite vars_instr_split => H. by apply: VSLemmas.mem_union2. Qed.

  Lemma mem_vars_instr3 v i : VS.mem v (rvs_instr i) -> VS.mem v (vars_instr i).
  Proof. rewrite vars_instr_split => H. by apply: VSLemmas.mem_union3. Qed.

  Lemma lvs_instr_subset i : VS.subset (lvs_instr i) (vars_instr i).
  Proof. rewrite vars_instr_split. exact: VSLemmas.union_subset_1. Qed.

  Lemma rvs_instr_subset i : VS.subset (rvs_instr i) (vars_instr i).
  Proof. rewrite vars_instr_split. exact: VSLemmas.union_subset_2. Qed.

  Lemma vars_program_split p :
    VS.Equal (vars_program p) (VS.union (lvs_program p) (rvs_program p)).
  Proof.
    elim: p => [| hd tl IH] /=.
    - rewrite VSLemmas.union_emptyl. reflexivity.
    - have: VS.Equal (VS.union (VS.union (lvs_instr hd) (lvs_program tl))
                               (VS.union (rvs_instr hd) (rvs_program tl)))
                     (VS.union (VS.union (lvs_instr hd) (rvs_instr hd))
                               (VS.union (lvs_program tl) (rvs_program tl))) by
          VSLemmas.dp_Equal.
      move=> ->. rewrite -IH. rewrite -vars_instr_split. reflexivity.
  Qed.

  Lemma mem_vars_program1 v p :
    VS.mem v (vars_program p) -> VS.mem v (lvs_program p) \/ VS.mem v (rvs_program p).
  Proof. rewrite vars_program_split => H. exact: (VSLemmas.mem_union1 H). Qed.

  Lemma mem_vars_program2 v p : VS.mem v (lvs_program p) -> VS.mem v (vars_program p).
  Proof. rewrite vars_program_split => H. by apply: VSLemmas.mem_union2. Qed.

  Lemma mem_vars_program3 v p : VS.mem v (rvs_program p) -> VS.mem v (vars_program p).
  Proof. rewrite vars_program_split => H. by apply: VSLemmas.mem_union3. Qed.

  Lemma lvs_program_subset p : VS.subset (lvs_program p) (vars_program p).
  Proof. rewrite vars_program_split. exact: VSLemmas.union_subset_1. Qed.

  Lemma rvs_program_subset p : VS.subset (rvs_program p) (vars_program p).
  Proof. rewrite vars_program_split. exact: VSLemmas.union_subset_2. Qed.

  Lemma vars_program_concat p1 p2 :
    VS.Equal (vars_program (p1 ++ p2)) (VS.union (vars_program p1) (vars_program p2)).
  Proof.
    elim: p1 p2 => [| hd tl IH] p2 /=.
    - rewrite VSLemmas.union_emptyl. reflexivity.
    - rewrite IH VSLemmas.OP.P.union_assoc. reflexivity.
  Qed.

  Lemma lvs_program_concat p1 p2 :
    VS.Equal (lvs_program (p1 ++ p2)) (VS.union (lvs_program p1) (lvs_program p2)).
  Proof.
    elim: p1 p2 => [| hd tl IH] p2 /=.
    - rewrite VSLemmas.union_emptyl. reflexivity.
    - rewrite IH VSLemmas.OP.P.union_assoc. reflexivity.
  Qed.

  Lemma vars_program_rcons p i :
    VS.Equal (vars_program (rcons p i)) (VS.union (vars_program p) (vars_instr i)).
  Proof.
    rewrite -cats1 vars_program_concat /=. rewrite VSLemmas.union_emptyr. reflexivity.
  Qed.

  Lemma lvs_program_rcons p i :
    VS.Equal (lvs_program (rcons p i)) (VS.union (lvs_program p) (lvs_instr i)).
  Proof.
    rewrite -cats1 lvs_program_concat /=. rewrite VSLemmas.union_emptyr. reflexivity.
  Qed.



  (* Specifications *)

  Record spec : Type :=
    { sinputs : TE.env;
      spre : bexp;
      sprog : program;
      spost : bexp }.

  Record espec :=
    { esinputs : TE.env;
      espre : ebexp;
      esprog : program;
      espost : ebexp }.

  Record rspec :=
    { rsinputs : TE.env;
      rspre : rbexp;
      rsprog : program;
      rspost : rbexp }.

  Coercion espec_of_spec s :=
    {| esinputs := sinputs s;
       espre := eqn_bexp (spre s);
       esprog := sprog s;
       espost := eqn_bexp (spost s) |}.

  Coercion rspec_of_spec s :=
    {| rsinputs := sinputs s;
       rspre := rng_bexp (spre s);
       rsprog := sprog s;
       rspost := rng_bexp (spost s) |}.



  (* Semantics *)

  Definition eval_eunop (op : eunop) (v : Z) : Z :=
    match op with
    | Eneg => - v
    end.

  Definition eval_ebinop (op : ebinop) (v1 v2 : Z) : Z :=
    match op with
    | Eadd => v1 + v2
    | Esub => v1 - v2
    | Emul => v1 * v2
    end.

  Definition eval_runop (op : runop) (v : bits) : bits :=
    match op with
    | Rnegb => negB v
    | Rnotb => invB v
    end.

  Definition eval_rbinop (op : rbinop) (v1 v2 : bits) : bits :=
    match op with
    | Radd => addB v1 v2
    | Rsub => subB v1 v2
    | Rmul => mulB v1 v2
    | Rumod => [::] (* TODO: Add correct semantics *)
    | Rsrem => [::] (* TODO: Add correct semantics *)
    | Rsmod => [::] (* TODO: Add correct semantics *)
    | Randb => andB v1 v2
    | Rorb => orB v1 v2
    | Rxorb => xorB v1 v2
    end.

  Definition eval_rcmpop (op : rcmpop) (v1 v2 : bits) : bool :=
    match op with
    | Rult => ltB v1 v2
    | Rule => leB v1 v2
    | Rugt => gtB v1 v2
    | Ruge => geB v1 v2
    | Rslt => sltB v1 v2
    | Rsle => sleB v1 v2
    | Rsgt => sgtB v1 v2
    | Rsge => sgeB v1 v2
    end.

  Fixpoint eval_eexp (e : eexp) (te : TE.env) (s : S.t) : Z :=
    match e with
    | Evar v => match TE.vtyp v te with
                | Tuint _ => to_Zpos (S.acc v s)
                | Tsint _ => to_Z (S.acc v s)
                end
    | Econst n => n
    | Eunop op e => eval_eunop op (eval_eexp e te s)
    | Ebinop op e1 e2 => eval_ebinop op (eval_eexp e1 te s) (eval_eexp e2 te s)
    end.

  Fixpoint eval_rexp (e : rexp) (s : S.t) : bits :=
    match e with
    | Rvar v => S.acc v s
    | Rconst w n => n
    | Runop _ op e => eval_runop op (eval_rexp e s)
    | Rbinop _ op e1 e2 => eval_rbinop op (eval_rexp e1 s) (eval_rexp e2 s)
    | Ruext _ e i => zext i (eval_rexp e s)
    | Rsext _ e i => sext i (eval_rexp e s)
    end.

  Fixpoint eval_ebexp (e : ebexp) (te : TE.env) (s : S.t) : Prop :=
    match e with
    | Etrue => True
    | Eeq e1 e2 => eval_eexp e1 te s = eval_eexp e2 te s
    | Eeqmod e1 e2 p =>
      modulo (eval_eexp e1 te s) (eval_eexp e2 te s) (eval_eexp p te s)
    | Eand e1 e2 => eval_ebexp e1 te s /\ eval_ebexp e2 te s
    end.

  Fixpoint eval_rbexp (e : rbexp) (s : S.t) : Prop :=
    match e with
    | Rtrue => True
    | Req _ e1 e2 => eval_rexp e1 s = eval_rexp e2 s
    | Rcmp _ op e1 e2 => eval_rcmpop op (eval_rexp e1 s) (eval_rexp e2 s)
    | Rneg e => ~ (eval_rbexp e s)
    | Rand e1 e2 => eval_rbexp e1 s /\ eval_rbexp e2 s
    | Ror e1 e2 => eval_rbexp e1 s \/ eval_rbexp e2 s
    end.

  Definition eval_bexp (e : bexp) (te : TE.env) (s : S.t) : Prop :=
    eval_ebexp (eqn_bexp e) te s /\ eval_rbexp (rng_bexp e) s.

  Definition valid (e : bexp) (te : TE.env) : Prop :=
    forall s : S.t, S.conform s te -> eval_bexp e te s.

  Definition entails (f g : bexp) (te : TE.env) : Prop :=
    forall s : S.t, S.conform s te -> eval_bexp f te s -> eval_bexp g te s.

  Definition eval_atomic (a : atomic) (s : S.t) : bits :=
    match a with
    | Avar v => S.acc v s
    | Aconst _ n => n
    end.

  (* Note: the correctness relies on well-formedness of instr *)
  Definition instr_succ_typenv (i : instr) (te : TE.env) : TE.env :=
    match i with
    | Imov v a => TE.add v (atyp a te) te
    | Ishl v a _ => TE.add v (atyp a te) te
    | Icshl v1 v2 a1 a2 _ => TE.add v1 (atyp a1 te) (TE.add v2 (atyp a2 te) te)
    | Inondet v t => TE.add v t te
    | Icmov v c a1 a2 => TE.add v (atyp a1 te) te
    | Inop => te
    | Inot v t a => TE.add v t te
    | Iadd v a1 a2 => TE.add v (atyp a1 te) te
    | Iadds c v a1 a2 => TE.add c Tbit (TE.add v (atyp a1 te) te)
    | Iadc v a1 a2 y => TE.add v (atyp a1 te) te
    | Iadcs c v a1 a2 y => TE.add c Tbit (TE.add v (atyp a1 te) te)
    | Isub v a1 a2 => TE.add v (atyp a1 te) te
    | Isubc c v a1 a2
    | Isubb c v a1 a2 => TE.add c Tbit (TE.add v (atyp a1 te) te)
    | Isbc v a1 a2 y => TE.add v (atyp a1 te) te
    | Isbcs c v a1 a2 y => TE.add c Tbit (TE.add v (atyp a1 te) te)
    | Isbb v a1 a2 y => TE.add v (atyp a1 te) te
    | Isbbs c v a1 a2 y => TE.add c Tbit (TE.add v (atyp a1 te) te)
    | Imul v a1 a2 => TE.add v (atyp a1 te) te
    | Imull vh vl a1 a2 =>
      TE.add vh (atyp a1 te) (TE.add vl (unsigned_typ (atyp a2 te)) te)
    | Imulj v a1 a2 => TE.add v (double_typ (atyp a1 te)) te
    | Isplit vh vl a n =>
      TE.add vh (atyp a te) (TE.add vl (unsigned_typ (atyp a te)) te)
    | Iand v t a1 a2
    | Ior v t a1 a2
    | Ixor v t a1 a2 => TE.add v t te
    | Icast v t a
    | Ivpc v t a => TE.add v t te
    | Ijoin v ah al => TE.add v (double_typ (atyp ah te)) te
    | Iassume e => te
    end.

  Local Notation state := S.t.

  (* TODO: Finish this *)
  Inductive eval_instr (te : TE.env) : instr -> state -> state -> Prop :=
  | EImov v a s t :
      S.Upd v (eval_atomic a s) s t ->
      eval_instr te (Imov v a) s t
  | EIshl v a i s t :
      S.Upd v (shlB i (eval_atomic a s)) s t ->
      eval_instr te (Ishl v a i) s t
  | EIcshl vh vl a1 a2 i s t :
      S.Upd2 vl (shrB i
                      (low (size (eval_atomic a2 s))
                           (shlB i
                                 (cat (eval_atomic a2 s) (eval_atomic a1 s)))))
             vh (high (size (eval_atomic a1 s))
                      (shlB i
                            (cat (eval_atomic a2 s) (eval_atomic a1 s))))
             s t ->
      eval_instr te (Icshl vh vl a1 a2 i) s t
  | EInondet v ty s t n :
      size n = sizeof_typ ty ->
      S.Upd v n s t ->
      eval_instr te (Inondet v ty) s t
  | EIcmovT v c a1 a2 s t :
      to_bool (eval_atomic c s) ->
      S.Upd v (eval_atomic a1 s) s t ->
      eval_instr te (Icmov v c a1 a2) s t
  | EIcmovF v c a1 a2 s t :
      ~~ to_bool (eval_atomic c s) ->
      S.Upd v (eval_atomic a2 s) s t ->
      eval_instr te (Icmov v c a1 a2) s t
  | EInop s : eval_instr te Inop s s
  | EInot v ty a s t :
      S.Upd v (invB (eval_atomic a s)) s t ->
      eval_instr te (Inot v ty a) s t
  | EIadd v a1 a2 s t :
      S.Upd v (addB (eval_atomic a1 s) (eval_atomic a2 s)) s t ->
      eval_instr te (Iadd v a1 a2) s t
  | EIadds c v a1 a2 s t :
      S.Upd2 v (addB (eval_atomic a1 s) (eval_atomic a2 s))
             c (1-bits of bool
                       (carry_addB (eval_atomic a1 s) (eval_atomic a2 s)))
             s t ->
      eval_instr te (Iadds c v a1 a2) s t
  | EIadc v a1 a2 y s t :
      S.Upd v (adcB (to_bool (eval_atomic y s))
                    (eval_atomic a1 s)
                    (eval_atomic a2 s)).2
            s t ->
      eval_instr te (Iadc v a1 a2 y) s t
  | EIadcs c v a1 a2 y s t :
      S.Upd2 v (adcB (to_bool (eval_atomic y s))
                     (eval_atomic a1 s)
                     (eval_atomic a2 s)).2
             c (1-bits of bool
                       ((adcB (to_bool (eval_atomic y s))
                             (eval_atomic a1 s)
                             (eval_atomic a2 s)).1))
             s t ->
      eval_instr te (Iadcs c v a1 a2 y) s t
  | EIsub v a1 a2 s t :
      S.Upd v (subB (eval_atomic a1 s) (eval_atomic a2 s)) s t ->
      eval_instr te (Isub v a1 a2) s t
  | EIsubc c v a1 a2 s t :
      S.Upd2 v (addB (eval_atomic a1 s) (negB (eval_atomic a2 s)))
             c (1-bits of bool
                       (carry_addB (eval_atomic a1 s) (negB (eval_atomic a2 s))))
             s t ->
      eval_instr te (Isubc c v a1 a2) s t
  | EIsubb b v a1 a2 s t :
      S.Upd2 v (subB (eval_atomic a1 s) (eval_atomic a2 s))
             b (1-bits of bool
                       (borrow_subB (eval_atomic a1 s) (eval_atomic a2 s)))
             s t ->
      eval_instr te (Isubb b v a1 a2) s t
  | EIsbc v a1 a2 y s t :
      S.Upd v (adcB (to_bool (eval_atomic y s))
                    (eval_atomic a1 s)
                    (invB (eval_atomic a2 s))).2
            s t ->
      eval_instr te (Isbc v a1 a2 y) s t
  | EIsbcs c v a1 a2 y s t :
      S.Upd2 v (adcB (to_bool (eval_atomic y s))
                     (eval_atomic a1 s)
                     (invB (eval_atomic a2 s))).2
             c (1-bits of bool
                       ((adcB (to_bool (eval_atomic y s))
                             (eval_atomic a1 s)
                             (invB (eval_atomic a2 s))).1))
             s t ->
      eval_instr te (Isbcs c v a1 a2 y) s t
  | EIsbb v a1 a2 y s t :
      S.Upd v (sbbB (to_bool (eval_atomic y s))
                    (eval_atomic a1 s)
                    (eval_atomic a2 s)).2
            s t ->
      eval_instr te (Isbb v a1 a2 y) s t
  | EIsbbs b v a1 a2 y s t :
      S.Upd2 v (sbbB (to_bool (eval_atomic y s))
                     (eval_atomic a1 s)
                     (eval_atomic a2 s)).2
             b (1-bits of bool
                       ((sbbB (to_bool (eval_atomic y s))
                             (eval_atomic a1 s)
                             (eval_atomic a2 s)).1))
             s t ->
      eval_instr te (Isbbs b v a1 a2 y) s t
  | EImul v a1 a2 s t :
      S.Upd v (mulB (eval_atomic a1 s) (eval_atomic a2 s)) s t ->
      eval_instr te (Imul v a1 a2) s t
  | EImull vh vl a1 a2 s t :
      S.Upd2 vl (low (size (eval_atomic a2 s))
                     (full_mul (eval_atomic a1 s) (eval_atomic a2 s)))
             vh (high (size (eval_atomic a1 s))
                      (full_mul (eval_atomic a1 s) (eval_atomic a2 s)))
             s t ->
      eval_instr te (Imull vh vl a1 a2) s t
  | EImulj v a1 a2 s t :
      S.Upd v (full_mul (eval_atomic a1 s) (eval_atomic a2 s)) s t ->
      eval_instr te (Imulj v a1 a2) s t
  | EIsplitU vh vl a n s t :
      is_unsigned (atyp a te) ->
      S.Upd2 vl (zext ((size (eval_atomic a s)) - n)
                      (low n (eval_atomic a s)))
             vh (zext n (high ((size (eval_atomic a s)) - n)
                              (eval_atomic a s)))
             s t ->
      eval_instr te (Isplit vh vl a n) s t
  | EIsplitS vh vl a n s t :
      is_signed (atyp a te) ->
      S.Upd2 vl (zext ((size (eval_atomic a s)) - n)
                      (low n (eval_atomic a s)))
             vh (sext n (high ((size (eval_atomic a s)) - n)
                              (eval_atomic a s)))
             s t ->
      eval_instr te (Isplit vh vl a n) s t
  | EIand v ty a1 a2 s t :
      S.Upd v (andB (eval_atomic a1 s) (eval_atomic a2 s)) s t ->
      eval_instr te (Iand v ty a1 a2) s t
  | EIor v ty a1 a2 s t :
      S.Upd v (orB (eval_atomic a1 s) (eval_atomic a2 s)) s t ->
      eval_instr te (Ior v ty a1 a2) s t
  | EIxor v ty a1 a2 s t :
      S.Upd v (xorB (eval_atomic a1 s) (eval_atomic a2 s)) s t ->
      eval_instr te (Ixor v ty a1 a2) s t
  | EIcast v ty a s t :
      S.Upd v (tcast (eval_atomic a s) (atyp a te) ty) s t ->
      eval_instr te (Icast v ty a) s t
  | EIvpc v ty a s t :
      S.Upd v (tcast (eval_atomic a s) (atyp a te) ty) s t ->
      eval_instr te (Ivpc v ty a) s t
  | EIjoin v ah al s t :
      S.Upd v (cat (eval_atomic al s) (eval_atomic ah s)) s t ->
      eval_instr te (Ijoin v ah al) s t
  | EIassume e s :
      eval_bexp e te s -> eval_instr te (Iassume e) s s
  .

  Inductive eval_instrs (te : TE.env) : seq instr -> state -> state -> Prop :=
  | Enil s : eval_instrs te [::] s s
  | Econs hd tl s t u : eval_instr te hd s t ->
                  eval_instrs (instr_succ_typenv hd te) tl t u ->
                  eval_instrs te (hd::tl) s u.

  Definition program_succ_typenv (p : program) (te : TE.env) : TE.env :=
    foldl (fun te i => instr_succ_typenv i te) te p.

  Definition eval_program (te : TE.env) p s t : Prop := eval_instrs te p s t.

  Lemma eval_program_singleton i te1 s1 s2:
      eval_program te1 ([:: i]) s1 s2 ->
      eval_instr te1 i s1 s2.
  Proof.
    move=> H.
    inversion H; subst.
    inversion H5; subst.
    assumption.
  Qed.

  (* Partial correctness *)

  Definition valid_spec (s : spec) : Prop :=
    forall s1 s2,
      S.conform s1 (sinputs s) ->
      eval_bexp (spre s) (sinputs s) s1 ->
      eval_program (sinputs s) (sprog s) s1 s2 ->
      eval_bexp (spost s) (program_succ_typenv (sprog s) (sinputs s)) s2.

  Definition valid_espec (s : espec) : Prop :=
    forall s1 s2,
      S.conform s1 (esinputs s) ->
      eval_ebexp (espre s) (esinputs s) s1 ->
      eval_program (esinputs s) (esprog s) s1 s2 ->
      eval_ebexp (espost s) (program_succ_typenv (esprog s) (esinputs s)) s2.

  Definition valid_rspec (s : rspec) : Prop :=
    forall s1 s2,
      S.conform s1 (rsinputs s) ->
      eval_rbexp (rspre s) s1 ->
      eval_program (rsinputs s) (rsprog s) s1 s2 ->
      eval_rbexp (rspost s) s2.

  Lemma valid_spec_split (s : spec) :
    valid_espec (espec_of_spec s) ->
    valid_rspec (rspec_of_spec s) ->
    valid_spec s.
  Proof.
    move=> He Hr s1 s2 Hcon [Hepre Hrpre] Hprog. split.
    - exact: (He _ _ Hcon Hepre Hprog).
    - exact: (Hr _ _ Hcon Hrpre Hprog).
  Qed.

  (* clash with Ltac notation
  Local Notation "te , s |= f" := (eval_bexp f te s) (at level 74, no associativity).
  Local Notation "f ===> g" := (entails f g) (at level 82, no associativity).
  Local Notation "te |= {{ f }} p {{ g }}" :=
    (valid_spec {| sinputs := te;
                   spre := f;
                   sprog := p;
                   spost := g |}) (at level 83).
  Local Notation "te |='e' {{ f }} p {{ g }}" :=
    (valid_espec {| esinputs := te;
                    espre := f;
                    esprog := p;
                    espost := g |}) (at level 83).
  Local Notation "te |='r' {{ f }} p {{ g }}" :=
    (valid_espec {| rsinputs := te;
                    rspre := f;
                    rsprog := p;
                    rspost := g |}) (at level 83).
  *)

  (* Well-typedness *)

  (* Here we define well-typedness assuming all used variables are defined. *)
  (* Note: we could also check the definedness of variables in well-typedness. *)

  Fixpoint well_typed_eexp (te : TE.env) (e : eexp) : bool :=
    match e with
    | Evar v => true
    | Econst n => true
    | Eunop op e => well_typed_eexp te e
    | Ebinop op e1 e2 => (well_typed_eexp te e1) && (well_typed_eexp te e2)
    end.

  Fixpoint well_typed_rexp (te : TE.env) (e : rexp) : bool :=
    match e with
    | Rvar _
    | Rconst _ _ => true
    | Runop w op e => (well_typed_rexp te e) && (size_of_rexp e te == w)
    | Rbinop w op e1 e2 =>
      (well_typed_rexp te e1) && (size_of_rexp e1 te == w) &&
      (well_typed_rexp te e2) && (size_of_rexp e2 te == w)
    | Ruext w e i
    | Rsext w e i => (well_typed_rexp te e) && (size_of_rexp e te == w)
    end.

  Fixpoint well_typed_ebexp (te : TE.env) (e : ebexp) : bool :=
    match e with
    | Etrue => true
    | Eeq e1 e2 => (well_typed_eexp te e1) && (well_typed_eexp te e2)
    | Eeqmod e1 e2 p =>
      (well_typed_eexp te e1) && (well_typed_eexp te e2) && (well_typed_eexp te p)
    | Eand e1 e2 => (well_typed_ebexp te e1) && (well_typed_ebexp te e2)
    end.

  Fixpoint well_typed_rbexp (te : TE.env) (e : rbexp) : bool :=
    match e with
    | Rtrue => true
    | Req w e1 e2
    | Rcmp w _ e1 e2 =>
      (well_typed_rexp te e1) && (size_of_rexp e1 te == w) &&
      (well_typed_rexp te e2) && (size_of_rexp e2 te == w)
    | Rneg e => well_typed_rbexp te e
    | Rand e1 e2
    | Ror e1 e2 => (well_typed_rbexp te e1) && (well_typed_rbexp te e2)
    end.

  Definition well_typed_bexp (te : TE.env) (e : bexp) : bool :=
    (well_typed_ebexp te (eqn_bexp e)) && (well_typed_rbexp te (rng_bexp e)).

  Definition well_typed_instr (te : TE.env) (i : instr) : bool :=
    match i with
    | Imov v a => true
    | Ishl v a _ => true
    | Icshl v1 v2 a1 a2 _ =>
      is_unsigned (atyp a2 te) && compatible (atyp a1 te) (atyp a2 te)
    | Inondet v t => true
    | Icmov v c a1 a2 =>
      (atyp c te == Tbit) && (atyp a1 te == atyp a2 te)
    | Inop => true
    | Inot v t a => compatible t (atyp a te)
    | Iadd v a1 a2
    | Iadds _ v a1 a2 => atyp a1 te == atyp a2 te
    | Iadc v a1 a2 y
    | Iadcs _ v a1 a2 y =>
      (atyp a1 te == atyp a2 te) && (atyp y te == Tbit)
    | Isub v a1 a2
    | Isubc _ v a1 a2
    | Isubb _ v a1 a2 => atyp a1 te == atyp a2 te
    | Isbc v a1 a2 y
    | Isbcs _ v a1 a2 y =>
      (atyp a1 te == atyp a2 te) && (atyp y te == Tbit)
    | Isbb v a1 a2 y
    | Isbbs _ v a1 a2 y =>
      (atyp a1 te == atyp a2 te) && (atyp y te == Tbit)
    | Imul v a1 a2 => atyp a1 te == atyp a2 te
    | Imull vh vl a1 a2 => atyp a1 te == atyp a2 te
    | Imulj v a1 a2 => atyp a1 te == atyp a2 te
    | Isplit vh vl a n => true
    | Iand v t a1 a2
    | Ior v t a1 a2
    | Ixor v t a1 a2 =>
      compatible t (atyp a1 te) && (atyp a1 te == atyp a2 te)
    | Icast v t a
    | Ivpc v t a => true
    | Ijoin v ah al =>
      is_unsigned (atyp al te) && compatible (atyp ah te) (atyp al te)
    | Iassume e => well_typed_bexp te e
    end.


  (* Well-formedness *)

  Module TEKS := MapKeySet V TE VS.

  (* the set of defined variables *)
  Definition vars_env (te : TE.env) := TEKS.key_set te.

  (* Note: Use TE.mem v te to determine if v is defined *)
  Definition is_defined (v : var) (te : TE.env) : bool :=
    TE.mem v te.

  Definition are_defined (vs : VS.t) (te : TE.env) : bool :=
    VS.for_all (fun v => is_defined v te) vs.

  Lemma is_defined_mem v te :
    is_defined v te -> VS.mem v (vars_env te).
  Proof.
    rewrite /is_defined /vars_env. exact: TEKS.mem_key_set.
  Qed.

  (* Use VS.mem v (vars_env te) to determine if v is defined *)
  (*
  Definition is_defined (v : var) (te : TE.env) :=
    VS.mem v (vars_env te).

  Definition are_defined (vs : VS.t) (te : TE.env) :=
    VS.subset vs (vars_env te).
   *)

  Definition well_defined_instr (te : TE.env) (i : instr) : bool :=
    match i with
    | Imov v a => are_defined (vars_atomic a) te
    | Ishl v a _ => are_defined (vars_atomic a) te
    | Icshl v1 v2 a1 a2 _ =>
      (v1 != v2) && are_defined (vars_atomic a1) te
                 && are_defined (vars_atomic a2) te
    | Inondet v t => true
    | Icmov v c a1 a2 =>
      (are_defined (vars_atomic c) te) && are_defined (vars_atomic a1) te
                                       && are_defined (vars_atomic a2) te
    | Inop => true
    | Inot v t a => are_defined (vars_atomic a) te
    | Iadd v a1 a2 =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
    | Iadds c v a1 a2 =>
      (c != v) && are_defined (vars_atomic a1) te
               && are_defined (vars_atomic a2) te
    | Iadc v a1 a2 y =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
                  && are_defined (vars_atomic y) te
    | Iadcs c v a1 a2 y =>
      (c != v) && are_defined (vars_atomic a1) te
               && are_defined (vars_atomic a2) te
               && are_defined (vars_atomic y) te
    | Isub v a1 a2 =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
    | Isubc c v a1 a2
    | Isubb c v a1 a2 =>
      (c != v) && are_defined (vars_atomic a1) te
               && are_defined (vars_atomic a2) te
    | Isbc v a1 a2 y =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
                  && are_defined (vars_atomic y) te
    | Isbcs c v a1 a2 y =>
      (c != v) && are_defined (vars_atomic a1) te
               && are_defined (vars_atomic a2) te
               && are_defined (vars_atomic y) te
    | Isbb v a1 a2 y =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
                  && are_defined (vars_atomic y) te
    | Isbbs c v a1 a2 y =>
      (c != v) && are_defined (vars_atomic a1) te
               && are_defined (vars_atomic a2) te
               && are_defined (vars_atomic y) te
    | Imul v a1 a2 =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
    | Imull vh vl a1 a2 =>
      (vh != vl) && are_defined (vars_atomic a1) te
                 && are_defined (vars_atomic a2) te
    | Imulj v a1 a2 =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
    | Isplit vh vl a n => (vh != vl) && are_defined (vars_atomic a) te
    | Iand v t a1 a2
    | Ior v t a1 a2
    | Ixor v t a1 a2 =>
      are_defined (vars_atomic a1) te && are_defined (vars_atomic a2) te
    | Icast v t a
    | Ivpc v t a => are_defined (vars_atomic a) te
    | Ijoin v ah al =>
      are_defined (vars_atomic ah) te && are_defined (vars_atomic al) te
    | Iassume e => are_defined (vars_bexp e) te
    end.

  Definition well_formed_instr (te : TE.env) (i : instr) : bool :=
    well_defined_instr te i && well_typed_instr te i.

  Fixpoint well_formed_program (te : TE.env) (p : program) : bool :=
    match p with
    | [::] => true
    | hd::tl =>
      well_formed_instr te hd &&
      well_formed_program (instr_succ_typenv hd te) tl
    end.

  Fixpoint find_non_well_formed_instr (te : TE.env) (p : program) : option instr :=
    match p with
    | [::] => None
    | hd::tl =>
      if well_formed_instr te hd
      then find_non_well_formed_instr (instr_succ_typenv hd te) tl
      else Some hd
    end.

  Ltac check_well_formedness te p :=
    let res := constr:(find_non_well_formed_instr te p) in
    let res := eval compute in res in
        match res with
        | None => idtac "The program is well-formed."
        | Some ?i => idtac "The program is not well-formed,"
                           "caused by the following instruction."; idtac i
        end.

  Definition well_formed_bexp (te : TE.env) (e : bexp) :=
    are_defined (vars_bexp e) te && well_typed_bexp te e.

  Definition well_formed_spec (s : spec) : bool :=
    well_formed_bexp (sinputs s) (spre s) &&
    well_formed_program (sinputs s) (sprog s) &&
    well_formed_bexp (program_succ_typenv (sprog s) (sinputs s)) (spost s).


  Lemma well_formed_program_concat te p1 p2 :
    well_formed_program te (p1 ++ p2) =
    well_formed_program te p1 &&
                        well_formed_program (program_succ_typenv p1 te) p2.
  Proof.
    case H: (well_formed_program te p1 &&
             well_formed_program (program_succ_typenv p1 te) p2).
    - move/andP: H => [Hp1 Hp2].
      elim: p1 te p2 Hp1 Hp2 => /=.
      + done.
      + move=> hd tl IH te p2 /andP [Hhd Htl] Hp2.
        rewrite Hhd /=.
        apply: (IH _ _ Htl).
        exact: Hp2.
    - move/negP: H => Hneg.
      apply/negP => H; apply: Hneg; apply/andP.
      elim: p1 te p2 H => /=.
      + done.
      + move=> hd tl IH te p2 /andP [Hhd Htlp2].
        move: (IH _ _ Htlp2) => {IH Htlp2} [Htl Hp2].
        split.
        * by rewrite Hhd Htl.
        * exact: Hp2.
  Qed.

  Lemma well_formed_program_concat1 te p1 p2 :
    well_formed_program te (p1 ++ p2) ->
    well_formed_program te p1.
  Proof.
    rewrite well_formed_program_concat.
    by move=> /andP [H _].
  Qed.

  Lemma well_formed_program_concat2 te p1 p2 :
    well_formed_program te (p1 ++ p2) ->
    well_formed_program (program_succ_typenv p1 te) p2.
  Proof.
    rewrite well_formed_program_concat.
    by move=> /andP [_ H].
  Qed.

  Lemma well_formed_program_concat3 te p1 p2 :
    well_formed_program te p1 ->
    well_formed_program (program_succ_typenv p1 te) p2 ->
    well_formed_program te (p1 ++ p2).
  Proof.
    rewrite well_formed_program_concat.
    by move=> H1 H2; rewrite H1 H2.
  Qed.

  Lemma well_formed_program_cons1 te p i :
    well_formed_program te (i::p) ->
    well_formed_instr te i.
  Proof.
    by move=> /andP [H _].
  Qed.

  Lemma well_formed_program_cons2 te p i :
    well_formed_program te (i::p) ->
    well_formed_program (instr_succ_typenv i te) p.
  Proof.
    by move=> /andP [_ H].
  Qed.

  Lemma well_formed_program_cons3 te p i :
    well_formed_instr te i ->
    well_formed_program (instr_succ_typenv i te) p ->
    well_formed_program te (i::p).
  Proof.
    move=> H1 H2.
    by rewrite /= H1 H2.
  Qed.

  Lemma well_formed_program_rcons te p i :
    well_formed_program te (rcons p i) =
    well_formed_program te p &&
                        well_formed_instr (program_succ_typenv p te) i.
  Proof.
    rewrite -cats1.
    rewrite well_formed_program_concat /=.
    by rewrite Bool.andb_true_r.
  Qed.

  Lemma well_formed_program_rcons1 te p i :
    well_formed_program te (rcons p i) ->
    well_formed_program te p.
  Proof.
    rewrite well_formed_program_rcons.
    by move=> /andP [H _].
  Qed.

  Lemma well_formed_program_rcons2 te p i :
    well_formed_program te (rcons p i) ->
    well_formed_instr (program_succ_typenv p te) i.
  Proof.
    rewrite well_formed_program_rcons.
    by move=> /andP [_ H].
  Qed.

  Lemma well_formed_program_rcons3 te p i :
    well_formed_program te p ->
    well_formed_instr (program_succ_typenv p te) i ->
    well_formed_program te (rcons p i).
  Proof.
    rewrite well_formed_program_rcons.
    by move=> H1 H2; rewrite H1 H2.
  Qed.

  (* Probably useful *)
  (* TO BE confirmed: how to modify (VS.subset vs1 vs2) and (VS.Equal vs1 vs2) *)

  Lemma are_defined_compat te:
    SetoidList.compat_bool VS.SE.eq (fun v => is_defined v te).
  Proof.
    move=> x y Heq; rewrite (eqP Heq) // .
  Qed.

  Lemma are_defined_union te vs1 vs2:
    are_defined (VS.union vs1 vs2) te ->
    are_defined vs1 te && are_defined vs2 te.
  Proof.
    rewrite /are_defined.
    move=> H.
    move: (VS.for_all_2 (are_defined_compat te) H) => {H} H.
    rewrite (VS.for_all_1 (are_defined_compat te)).
    rewrite andTb.
    rewrite (VS.for_all_1 (are_defined_compat te)).
    done.
    intros x Hin.
    move: (VS.union_3 vs1 Hin) => Hin2.
    exact: (H _ Hin2).
    intros x Hin.
    move: (VS.union_2 vs2 Hin) => Hin2.
    exact: (H _ Hin2).
  Qed.

  Lemma are_defined_subset te vs:
    are_defined vs te <->
    VS.subset vs (vars_env te).
  Proof.
    rewrite /are_defined.
    split.
    - move=> H.
      move: (VS.for_all_2 (are_defined_compat te) H) => {H} H.
      have Hsub: (VS.Subset vs (vars_env te)).
      {
        intro.
        move=> Hin.
        move: (H _ Hin) => {Hin} Hin.
        move/idP: Hin => Hin.
        rewrite /is_defined in Hin.
        apply/VSLemmas.memP.
        exact: (TEKS.mem_key_set Hin).
      }
      rewrite -> VSLemmas.F.subset_iff in Hsub.
      exact: Hsub.
    - move=> Hsub.
      have Hsub2: (VS.subset vs (vars_env te) = true) by exact: Hsub.
      rewrite <- VSLemmas.F.subset_iff in Hsub2.
      rewrite /VS.Subset in Hsub2.
      rewrite (VS.for_all_1 (are_defined_compat te)).
      done.
      intros x Hin.
      move: (Hsub2 _ Hin) => Hin2.
      rewrite /is_defined.
      move/VSLemmas.memP: Hin2 => Hin2.
      move: (TEKS.key_set_mem Hin2) => Hin3.
      exact: Hin3.
  Qed.

  Lemma well_formed_instr_subset_rvs_aux te i :
    well_formed_instr te i ->
    VS.for_all (fun v => is_defined v te) (rvs_instr i).
  Proof.
    elim: i => /=; intros;
                (let rec tac :=
                     match goal with
                     | H : ?a |- ?a => assumption
                     | H : ?l \/ ?r |- _ => case: H => H; tac
                     | |- VS.For_all _ _ => intros x Hin; tac
                     | H: VS.In ?x (VS.union ?vs1 ?vs2) |- _
                       => let Hin := fresh "Hin" in move:(VS.union_1 H) => Hin; clear H; tac
                     | H : is_true(well_formed_instr ?te ?i) |- _  =>
                       let Hwd := fresh "Hwd" in let Hwt := fresh "Hwt" in
                                                 move/andP: H => [Hwd Hwt]; tac
                     | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
                       (rewrite /= in Hwd); tac
                     | H : is_true (_ && _) |- _ =>
                       let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]; tac
                     | |- is_true (VS.for_all (is_defined^~ ?te) _) =>
                       apply (VS.for_all_1 (are_defined_compat te)); tac
                     | Hin: VS.In ?x ?vs,Hwd: is_true (are_defined ?vs ?te)  |- is_defined ?x ?te = true
                         => exact: ((VS.for_all_2 (are_defined_compat te) Hwd) _ Hin)
                     | Hin: VS.In ?x VS.empty |- _ =>
                       (rewrite -> VSLemmas.empty_iff in Hin); inversion Hin
                     | |- _ => idtac
                     end
                 in tac).
  Qed.

  Lemma well_formed_instr_subset_rvs te i :
    well_formed_instr te i ->
    VS.subset (rvs_instr i) (vars_env te).
  Proof.
    move=> Hwf.
    move: (well_formed_instr_subset_rvs_aux Hwf) => Hsub_rvs.
    have H: (VS.Subset (rvs_instr i) (vars_env te)).
    {
      intro.
      move: (VS.for_all_2 (are_defined_compat te) Hsub_rvs) => Hsub_rvs2.
      move=> Hin.
      move: (Hsub_rvs2 _ Hin) => Hin2.
      rewrite /is_defined in Hin2.
      move/idP: Hin2 => Hin2.
      apply/VSLemmas.memP.
      exact: (TEKS.mem_key_set Hin2).
    }
    rewrite -> VSLemmas.F.subset_iff in H.
    exact: H.
  Qed.

  Lemma is_defined_submap k (te1 te2: TE.env):
    TELemmas.submap te1 te2 ->
    is_defined k te1 -> is_defined k te2.
  Proof.
    move=> Hsm.
    intros.
    move: (TELemmas.mem_find_some H) => Hfind1.
    destruct Hfind1.
    move: (Hsm k x H0) => Hfind2.
    apply TELemmas.find_some_mem with x.
    exact: Hfind2.
  Qed.

  Lemma are_defined_submap vs (te1 te2: TE.env):
    TELemmas.submap te1 te2 ->
    are_defined vs te1 -> are_defined vs te2.
  Proof.
    move=> Hsm Had1.
    rewrite /TELemmas.submap in Hsm.
    apply (VS.for_all_1 (are_defined_compat te2)).
    move=> v Hin.
    apply (is_defined_submap Hsm).
    move: (VS.for_all_2 (are_defined_compat te1) Had1) => Hwd2.
    exact: (Hwd2 v Hin).
  Qed.

  Lemma well_formed_instr_well_defined te1 te2 i :
    well_formed_instr te1 i ->
    TELemmas.submap te1 te2 ->
    well_defined_instr te2 i.
  Proof.
    elim: i te1 te2 => /=; intros;
                (let rec tac :=
                     match goal with
                     | H : ?a |- ?a => assumption
                     | H : ?l \/ ?r |- _ => case: H => H; tac
                     | |- ?l /\ ?r => split; tac
                     | |- is_true (_ && _) => apply /andP; tac
                     | H : is_true(well_formed_instr ?te ?i) |- _  =>
                       let Hwd := fresh "Hwd" in let Hwt := fresh "Hwt" in
                                                 move/andP: H => [Hwd Hwt]; tac
                     | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
                       (rewrite /= in Hwd); tac
                     | H : is_true (_ && _) |- _ =>
                       let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]; tac
                     | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined ?vs ?te1)
                       |- is_true (are_defined ?vs ?te2) =>
                       exact: (are_defined_submap Hsub Hwd); tac
                     | |- _ => idtac
                     end
                 in tac).
  Qed.

  Lemma atyp_submap a te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_atomic a) te1 ->
    atyp a te1 = atyp a te2.
  Proof.
    elim: a te1 te2.
    - move=> t te1 te2 Hsm Hd.
      rewrite /= in Hd.
      rewrite /are_defined in Hd.
      move: (VS.for_all_2 (are_defined_compat te1) Hd) => Hwd2.
      move: (VSLemmas.P.Dec.FSetDecideTestCases.test_In_singleton t) => Hin.
      move: (Hwd2 _ Hin) => Hid.
      rewrite /TELemmas.submap in Hsm.
      rewrite /=.
      rewrite /is_defined in Hid.
      move: (TELemmas.mem_find_some Hid) => Hfind.
      destruct Hfind.
      move: (Hsm _ _ H) => H2.
      rewrite (TE.find_some_vtyp H) (TE.find_some_vtyp H2).
      reflexivity.
    - done.
  Qed.

  Lemma well_typed_eexp_submap e te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_eexp e) te1 ->
    well_typed_eexp te1 e ->
    well_typed_eexp te2 e.
  Proof.
    elim: e te1 te2 => //=; intros.
    rewrite /are_defined in H2.
    move: (VS.for_all_2 (are_defined_compat te1) H2) => Hwd.
    rewrite /VS.For_all in Hwd.
    move/andP: H3 => [Hwte0 Hwte1].
    apply /andP.
    split.
    - apply H with te1.
      + done.
      + move/andP: (are_defined_union H2).
        by inversion 1.
      + done.
    - apply H0 with te1.
      + done.
      + move/andP: (are_defined_union H2).
        by inversion 1.
      + done.
  Qed.

  Lemma well_typed_ebexp_submap e te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_ebexp e) te1 ->
    well_typed_ebexp te1 e ->
    well_typed_ebexp te2 e.
  Proof.
    elim: e te1 te2 => //=; intros.
    - move/andP: H1 => [Hwte Hwte0].
      apply /andP.
      split.
      + apply well_typed_eexp_submap with te1.
        * done.
        * move/andP: (are_defined_union H0).
            by inversion 1.
        * done.
      + apply well_typed_eexp_submap with te1.
        * done.
        * move/andP: (are_defined_union H0).
            by inversion 1.
        * done.
      +  move/andP: H1 => [/andP [Hwte Hwte0] Hwte1].
         apply /andP. split.
         apply /andP. split.
         * apply well_typed_eexp_submap with te1.
           -- done.
           -- move/andP: (are_defined_union H0).
                by inversion 1.
           -- done.
         * apply well_typed_eexp_submap with te1.
           -- done.
           -- move/andP: (are_defined_union H0).
              destruct 1 as [H1 H2].
              move/andP: (are_defined_union H2).
              by inversion 1.
           -- done.
         * apply well_typed_eexp_submap with te1.
           -- done.
           -- move/andP: (are_defined_union H0).
              destruct 1 as [H1 H2].
              move/andP: (are_defined_union H2).
              by inversion 1.
           -- done.
    - move/andP: H3 => [Hwte Hwte0].
      apply /andP.
      move: (are_defined_union H2) => /andP [Hwd Hwd0].
      split.
      + apply H with te1; done.
      + apply H0 with te1; done.
  Qed.

  Lemma well_typed_size_of_rexp_submap r te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_rexp r) te1 ->
    size_of_rexp r te1 == size_of_rexp r te2.
  Proof.
    elim: r te1 te2 => //=.
    move=> x te1 te2 Hsm Hwd.
    move: (VS.for_all_2 (are_defined_compat te1) Hwd) => Hwd2.
    move: (VSLemmas.P.Dec.FSetDecideTestCases.test_In_singleton x) => Hin.
    move: (Hwd2 _ Hin) => Hid.
    rewrite /TELemmas.submap in Hsm.
    rewrite /=.
    rewrite /is_defined in Hid.
    move: (TELemmas.mem_find_some Hid) => Hfind.
    destruct Hfind.
    move: (Hsm _ _ H) => H2.
    have Htyp: (TE.vtyp x te1 = TE.vtyp x te2).
    {
      by rewrite (TE.find_some_vtyp H) (TE.find_some_vtyp H2).
    }
    remember (TE.vtyp x te1).
    symmetry in Heqt, Htyp.
    by rewrite (TE.vtyp_vsize Heqt) (TE.vtyp_vsize Htyp).
  Qed.

  Lemma well_typed_rexp_submap e te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_rexp e) te1 ->
    well_typed_rexp te1 e ->
    well_typed_rexp te2 e.
  Proof.
    elim: e te1 te2 => //=; intros.
    move/andP: H2 => [Hwte0 Hwte1].
    apply /andP.
    split.
    - apply H with te1.
      + done.
      + done.
      + done.
    - by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hwte1.
      move: H3 => /andP [/andP [/andP [Hwt0 Hsz0] Hwt1] Hsz1].
      move: (are_defined_union H2) => /andP [H2_1 H2_2].
    apply /andP. split.
    apply /andP. split.
    apply /andP. split.
    - apply H with te1.
      + done.
      + move/andP: (are_defined_union H2).
          by inversion 1.
      + done.
      + by rewrite (eqP (well_typed_size_of_rexp_submap H1 H2_1)) in Hsz0.
    - apply H0 with te1.
      + done.
      + move/andP: (are_defined_union H2).
          by inversion 1.
      + done.
      + by rewrite (eqP (well_typed_size_of_rexp_submap H1 H2_2)) in Hsz1.
    - move/andP: H2 => [Hwt Hsz].
      apply/andP. split.
      + apply H with te1; auto.
          by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hsz.
    - move/andP: H2 => [Hwt Hsz].
      apply/andP. split.
      + apply H with te1; auto.
          by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hsz.
  Qed.

  Ltac solve_well_typed_rexp_submap :=
    (let rec tac :=
         match goal with
         | H : ?a |- ?a => assumption
         | H : ?l \/ ?r |- _ => case: H => H; tac
         | H: is_true(are_defined (VS.union ?vs1 ?vs2) ?te) |- _ =>
           let Hr1 := fresh "Hr1" in
           let Hr2 := fresh "Hr2" in
           move: (are_defined_union H) => /andP [Hr1 Hr2]; clear H; tac
         | |- ?l /\ ?r => split; tac
         | |- is_true (_ && _) => apply /andP; tac
         | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined ?vs ?te1)
           |- is_true (are_defined ?vs ?te2) =>
           exact: (are_defined_submap Hsub Hwd); tac
         | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined ?vs ?te1)
           |- context [atyp ?a ?te2] =>
           rewrite -(atyp_submap Hsub Hwd); tac
         | Hsub: TELemmas.submap ?te1 ?te2
           |- is_true (well_typed_rexp ?te2 ?r) =>
           apply well_typed_rexp_submap with te1; tac
         | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined (vars_rexp ?r) ?te1),
                                                 Hsz: is_true (size_of_rexp ?r ?te1 == ?n)
           |- is_true (size_of_rexp ?r ?te2 == ?n) =>
             by rewrite (eqP (well_typed_size_of_rexp_submap Hsub Hwd)) in Hsz
         | |- ?e => progress (auto)
         | |- ?e => idtac
         end
     in tac).

  Lemma well_typed_rbexp_submap r te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_rbexp r) te1 ->
    well_typed_rbexp te1 r ->
    well_typed_rbexp te2 r.
  Proof with solve_well_typed_rexp_submap.
    elim: r te1 te2 => //=; intros; split_andb_hyps; split_andb_goal...
    - apply H with te1...
    - apply H0 with te1...
    - apply H with te1...
    - apply H0 with te1...
  Qed.

  Lemma well_typed_bexp_submap b te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_bexp b) te1 ->
    well_typed_bexp te1 b ->
    well_typed_bexp te2 b.
  Proof.
    elim: b te1 te2 => //=; intros.
    rewrite /well_typed_bexp /= in H1.
    rewrite /well_typed_bexp /=.
    rewrite /vars_bexp /= in H0.
    rewrite /are_defined in H0.
    move: (VS.for_all_2 (are_defined_compat te1) H0) => Hwd.
    rewrite /VS.For_all in Hwd.
    move/andP: H1 => [Hwte Hwtr].
    apply /andP.
    split.
    - apply well_typed_ebexp_submap with te1.
      + done.
      + rewrite /are_defined.
        rewrite (VS.for_all_1 (are_defined_compat te1)).
        done.
        intros x Hin.
        move: (VS.union_2 (vars_rbexp b) Hin) => Hin2.
        exact: (Hwd _ Hin2).
      + done.
    - apply well_typed_rbexp_submap with te1.
      + done.
      + rewrite /are_defined.
        rewrite (VS.for_all_1 (are_defined_compat te1)).
        done.
        intros x Hin.
        move: (VS.union_3 (vars_ebexp a) Hin) => Hin2.
        exact: (Hwd _ Hin2).
      + done.
  Qed.

  Lemma well_formed_instr_well_typed te1 te2 i :
    well_formed_instr te1 i ->
    TELemmas.submap te1 te2 ->
    well_typed_instr te2 i.
  Proof.
    elim: i te1 te2 => //=; intros;
                (let rec tac :=
                     match goal with
                     | H : ?a |- ?a => assumption
                     | H : ?l \/ ?r |- _ => case: H => H; tac
                     | |- ?l /\ ?r => split; tac
                     | |- is_true (_ && _) => apply /andP; tac
                     | H : is_true(well_formed_instr ?te ?i) |- _  =>
                       let Hwd := fresh "Hwd" in let Hwt := fresh "Hwt" in
                                                 move/andP: H => [Hwd Hwt]; tac
                     | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
                       (rewrite /= in Hwd); tac
                     | H : is_true(well_typed_instr ?te ?i) |- _  =>
                       (rewrite /= in H); tac
                     | H : is_true (_ && _) |- _ =>
                       let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]; tac
                     | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined ?vs ?te1)
                       |- is_true (are_defined ?vs ?te2) =>
                         exact: (are_defined_submap Hsub Hwd); tac
                     | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined ?vs ?te1)
                       |- context [atyp ?a ?te2] =>
                       rewrite -(atyp_submap Hsub Hwd); tac
                     | |- _ => idtac
                     end
                 in tac).
    exact: (well_typed_bexp_submap H0 Hwd Hwt).
  Qed.

  Lemma well_formed_instr_well_formed te1 te2 i :
    well_formed_instr te1 i ->
    TELemmas.submap te1 te2 ->
    well_formed_instr te2 i.
  Proof.
    move=> Hwf Hsm.
    rewrite /well_formed_instr.
      by rewrite (well_formed_instr_well_defined Hwf Hsm)
                 (well_formed_instr_well_typed Hwf Hsm).
  Qed.

  Lemma well_formed_instr_replace te1 te2 i :
    well_formed_instr te1 i ->
    TE.Equal te1 te2 ->
    well_formed_instr te2 i.
  Proof.
    move=> Hwell Heq.
    apply: (well_formed_instr_well_formed Hwell).
    intros x v Hfind.
    rewrite /TE.Equal in Heq.
    by rewrite -(Heq x).
  Qed.

  Lemma submap_add x v (te1 te2: TE.env) :
    TELemmas.submap te1 te2 ->
    TELemmas.submap (TE.add x v te1) (TE.add x v te2).
  Proof.
    move=> Hsm.
    intros k typ.
    case Heq: (k == x).
    - move/idP: Heq => Heq.
        by rewrite 2!(TELemmas.find_add_eq Heq).
    - move/idP: Heq => Hneq.
      rewrite 2!(TELemmas.find_add_neq Hneq).
      exact: Hsm.
  Qed.

  Local Hint Resolve submap_add.

  Lemma well_formed_instr_succ_typenv_submap i te1 te2:
    well_formed_instr te1 i ->
    TELemmas.submap te1 te2 ->
    TELemmas.submap (instr_succ_typenv i te1) (instr_succ_typenv i te2).
  Proof.
    elim: i te1 te2 => //=; intros;
      (let rec tac :=
           match goal with
           | H : ?a |- ?a => assumption
           | H : ?l \/ ?r |- _ => case: H => H; tac
           | |- ?l /\ ?r => split; tac
           | |- is_true (_ && _) => apply /andP; tac
           | H : is_true(well_formed_instr ?te ?i) |- _  =>
             let Hwd := fresh "Hwd" in let Hwt := fresh "Hwt" in
                                       move/andP: H => [Hwd Hwt]; tac
           | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
             (rewrite /= in Hwd); tac
           | H : is_true(well_typed_instr ?te ?i) |- _  =>
             (rewrite /= in H); tac
           | H : is_true (_ && _) |- _ =>
             let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]; tac
           | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined ?vs ?te1)
             |- is_true (are_defined ?vs ?te2) =>
             exact: (are_defined_submap Hsub Hwd); tac
           | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined (vars_atomic ?a) ?te1)
             |- context [atyp ?a ?te2] =>
             rewrite -(atyp_submap Hsub Hwd); tac
           | |- ?e => progress (auto)
           | |- _ => idtac
           end
       in tac).
  Qed.

  Lemma well_formed_program_well_submap te1 te2 p :
    well_formed_program te1 p ->
    TELemmas.submap te1 te2 ->
    well_formed_program te2 p.
  Proof.
    elim: p te1 te2 => //=.
    move=> hd tl IH te1 te2 /andP [Hhd Htl] Hsub.
    apply/andP; split.
    - exact: (well_formed_instr_well_formed Hhd Hsub).
    - apply: (IH _ _ Htl).
      exact: (well_formed_instr_succ_typenv_submap Hhd Hsub).
  Qed.

  (*
  Lemma well_formed_instr_vars te i :
    well_formed_instr te i ->
    VS.Equal (VS.union (vars_env te) (vars_instr i)) (VS.union (vars_env te) (lvs_instr i)).
  Proof.
    case: i => /=; intros; hyps_splitb; by VSLemmas.dp_Equal.
  Qed.
  *)

  (* Probably useful in slicing *)

  (*

  Lemma well_formed_program_vars vs p :
    well_formed_program vs p ->
    VS.Equal (VS.union vs (vars_program p)) (VS.union vs (lvs_program p)).
  Proof.
    elim: p vs => /=.
    - move=> vs _.
      reflexivity.
    - move=> hd tl IH vs /andP [Hhd Htl].
      move: (IH _ Htl) => {IH Htl} => Heq.
      rewrite -(@VSLemmas.OP.P.union_assoc _ (lvs_instr hd)).
      rewrite -{}Heq.
      rewrite -(well_formed_instr_vars Hhd).
      rewrite VSLemmas.OP.P.union_assoc.
      reflexivity.
  Qed.
  *)

  (* Some Lemmas for vars_env and instr_succ_typenv *)
  Lemma vars_env_instr_succ_typenv i te:
    vars_env (instr_succ_typenv i te) =
    VS.union (vars_env te) (lvs_instr i).
  Proof.
  Admitted.
  (* Non-blocking *)

  Definition is_assume (i : instr) : bool :=
    match i with
    | Iassume _ => true
    | _ => false
    end.

  (* Given a store, the evaluation of every instruction except assume
     should result in a store *)
  Lemma instr_nonblocking (te : TE.env) (i : instr) (s : S.t) :
    ~~ is_assume i ->
    exists (t : S.t), eval_instr te i s t.
  Proof.
    case: i => //=.
    - (* Imov *) move=> ? ? _. eexists. apply: EImov. exact: S.Upd_upd.
    - (* Ishl *) move=> ? ? ? _. eexists. apply: EIshl. exact: S.Upd_upd.
    - (* Icshl *) move=> ? ? ? ? ? _. eexists. apply: EIcshl. exact: S.Upd2_upd2.
    - (* Inondet *) move=> v ty _. eexists.
      apply: (@EInondet _ _ _ _ _ (((sizeof_typ ty)-bits of 0))).
      + by rewrite size_from_nat.
      + exact: S.Upd_upd.
    - (* Icmov *) move=> v c a1 a2 _. case H: (to_bool (eval_atomic c s)).
      + eexists. apply: (EIcmovT _ _ H). exact: S.Upd_upd.
      + move/idP/negP: H=> H. eexists. apply: (EIcmovF _ _ H). exact: S.Upd_upd.
    - (* Inop *) move=> _. exists s. exact: EInop.
    - (* Inot *) move=> ? ? ? _. eexists. apply: EInot. exact: S.Upd_upd.
    - (* Iadd *) move=> ? ? ? _. eexists. apply: EIadd. exact: S.Upd_upd.
    - (* Iadds *) move=> ? ? ? ? _. eexists. apply: EIadds. exact: S.Upd2_upd2.
    - (* Iadc *) move=> ? ? ? ? _. eexists. apply: EIadc. exact: S.Upd_upd.
    - (* Iadcs *) move=> ? ? ? ? ? _. eexists. apply: EIadcs. exact: S.Upd2_upd2.
    - (* Isub *) move=> ? ? ? _. eexists. apply: EIsub. exact: S.Upd_upd.
    - (* Isubc *) move=> ? ? ? ? _. eexists. apply: EIsubc. exact: S.Upd2_upd2.
    - (* Isubb *) move=> ? ? ? ? _. eexists. apply: EIsubb. exact: S.Upd2_upd2.
    - (* Isbc *) move=> ? ? ? ? _. eexists. apply: EIsbc. exact: S.Upd_upd.
    - (* Isbcs *) move=> ? ? ? ? ? _. eexists. apply: EIsbcs. exact: S.Upd2_upd2.
    - (* Isbb *) move=> ? ? ? ? _. eexists. apply: EIsbb. exact: S.Upd_upd.
    - (* Isbbs *) move=> ? ? ? ? ? _. eexists. apply: EIsbbs. exact: S.Upd2_upd2.
    - (* Imul *) move=> ? ? ? _. eexists. apply: EImul. exact: S.Upd_upd.
    - (* Imull *) move=> ? ? ? ? _. eexists. apply: EImull. exact: S.Upd2_upd2.
    - (* Imulj *) move=> ? ? ? _. eexists. apply: EImulj. exact: S.Upd_upd.
    - (* Isplit *) move=> vh vl a n _. case H: (is_signed (atyp a te)).
      + eexists. apply: (EIsplitS H). exact: S.Upd2_upd2.
      + move/idP/negP: H=> H. rewrite not_signed_is_unsigned in H. eexists.
        apply: (EIsplitU H). exact: S.Upd2_upd2.
    - (* Iand *) move=> ? ? ? ? _. eexists. apply: EIand. exact: S.Upd_upd.
    - (* Ior *) move=> ? ? ? ? _. eexists. apply: EIor. exact: S.Upd_upd.
    - (* Ixor *) move=> ? ? ? ? _. eexists. apply: EIxor. exact: S.Upd_upd.
    - (* Icast *) move=> ? ? ? _. eexists. apply: EIcast. exact: S.Upd_upd.
    - (* Ivpc *) move=> ? ? ? _. eexists. apply: EIvpc. exact: S.Upd_upd.
    - (* Ijoin *) move=> ? ? ? _. eexists. apply: EIjoin. exact: S.Upd_upd.
  Qed.

End MakeDSL.

Module DSL := MakeDSL VarOrder VS VM TE Store.
