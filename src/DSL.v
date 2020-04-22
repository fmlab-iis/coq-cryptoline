
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

  Definition z2expn n := Z.pow 2%Z n.

  Definition e2expn n := econst (z2expn n).

  Definition emul2p x n := emul x (e2expn n).

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
    | e::es => eadd (emul e (e2expn (Z.of_nat i * r))) (limbsi (i + 1) r es)
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

  Definition eands es := foldr (fun res e => eand res e) Etrue es.

  Fixpoint split_eand (e : ebexp) : seq ebexp :=
    match e with
    | Eand e1 e2 => (split_eand e1) ++ (split_eand e2)
    | _ => [:: e]
    end.

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

  Definition z2expn n := z2expn n.
  Definition e2expn n := @e2expn V.T n.
  Definition emul2p x n := @emul2p V.T x n.

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

  Definition split_eand (e : ebexp) : seq ebexp := @split_eand V.T e.

  Fixpoint vars_ebexp (e : ebexp) : VS.t :=
    match e with
    | Etrue => VS.empty
    | Eeq e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    | Eeqmod e1 e2 m =>
      VS.union (vars_eexp e1) (VS.union (vars_eexp e2) (vars_eexp m))
    | Eand e1 e2 => VS.union (vars_ebexp e1) (vars_ebexp e2)
    end.

  Lemma vars_eands_cons e es :
    VS.Equal (vars_ebexp (eands (e::es)))
             (VS.union (vars_ebexp e) (vars_ebexp (eands es))).
  Proof. reflexivity. Qed.

  Lemma vars_eands_cat es1 es2 :
    VS.Equal (vars_ebexp (eands (es1 ++ es2)))
             (VS.union (vars_ebexp (eands es1)) (vars_ebexp (eands es2))).
  Proof.
    elim: es1 => [| e1 es1 IH1] //=.
    - by VSLemmas.dp_Equal.
    - rewrite IH1. by VSLemmas.dp_Equal.
  Qed.

  Lemma vars_eands_split_eand e :
    VS.Equal (vars_ebexp (eands (split_eand e))) (vars_ebexp e).
  Proof.
    elim: e => /=; try (move=> *; by VSLemmas.dp_Equal).
    move=> e1 IH1 e2 IH2. rewrite vars_eands_cat IH1 IH2. reflexivity.
  Qed.


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



  (* Remove algebraic assumptions or range assumptions from programs *)

  Definition eqn_instr (i : instr) : instr :=
    match i with
    | Iassume (ee, re) => Iassume (ee, rtrue)
    | _ => i
    end.

  Definition rng_instr (i : instr) : instr :=
    match i with
    | Iassume (ee, re) => Iassume (etrue, re)
    | _ => i
    end.

  Fixpoint eqn_program (p : program) : program :=
    match p with
    | [::] => [::]
    | hd::tl => (eqn_instr hd)::(eqn_program tl)
    end.

  Fixpoint rng_program (p : program) : program :=
    match p with
    | [::] => [::]
    | hd::tl => (rng_instr hd)::(rng_program tl)
    end.

  Lemma rng_program_rcons p i :
    rng_program (rcons p i) = rcons (rng_program p) (rng_instr i).
  Proof.
    elim: p => [| hd tl IH] //=. rewrite IH. reflexivity.
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
       esprog := eqn_program (sprog s);
       espost := eqn_bexp (spost s) |}.

  Coercion rspec_of_spec s :=
    {| rsinputs := sinputs s;
       rspre := rng_bexp (spre s);
       rsprog := rng_program (sprog s);
       rspost := rng_bexp (spost s) |}.



  (* Conversion from bits to integer *)

  Definition bv2z (t : typ) (bs : bits) : Z :=
    match t with
    | Tuint _ => to_Zpos bs
    | Tsint _ => to_Z bs
    end.

  Definition acc2z (E : TE.env) (v : V.t) (s : S.t) : Z :=
    bv2z (TE.vtyp v E) (S.acc v s).

  Lemma acc2z_upd_eq {E x v bs sb} :
    x == v ->
    acc2z E x (S.upd v bs sb) = bv2z (TE.vtyp x E) bs.
  Proof. rewrite /acc2z => Heq. rewrite (S.acc_upd_eq Heq). reflexivity. Qed.

  Lemma acc2z_Upd_eq {E x v e s1 s2} :
    x == v ->
    S.Upd v e s1 s2 ->
    acc2z E x s2 = bv2z (TE.vtyp x E) e.
  Proof. rewrite /acc2z => Heq Hupd. rewrite (S.acc_Upd_eq Heq Hupd). reflexivity. Qed.

  Lemma acc2z_upd_neq {E x v bs sb} :
    x != v ->
    acc2z E x (S.upd v bs sb) = acc2z E x sb.
  Proof. rewrite /acc2z => Hne. rewrite (S.acc_upd_neq Hne). reflexivity. Qed.

  Lemma acc2z_Upd_neq {E x v e s1 s2} :
    x != v ->
    S.Upd v e s1 s2 ->
    acc2z E x s2 = acc2z E x s1.
  Proof.
    rewrite /acc2z => Hne Hupd. rewrite (S.acc_Upd_neq Hne Hupd). reflexivity.
  Qed.

  Lemma acc2z_upd2_eq1 {E x vl el vh eh s} :
    x == vl -> x != vh ->
    acc2z E x (S.upd2 vl el vh eh s) = bv2z (TE.vtyp x E) el.
  Proof.
    rewrite /acc2z => Heq Hne. rewrite (S.acc_upd2_eq1 Heq Hne). reflexivity.
  Qed.

  Lemma acc2z_Upd2_eq1 {E x vl el vh eh s1 s2} :
    x == vl -> x != vh ->
    S.Upd2 vl el vh eh s1 s2 ->
    acc2z E x s2 = bv2z (TE.vtyp x E) el.
  Proof.
    rewrite /acc2z => Heq Hne Hupd. rewrite (S.acc_Upd2_eq1 Heq Hne Hupd). reflexivity.
  Qed.

  Lemma acc2z_upd2_eq2 {E x vl el vh eh s} :
    x == vh ->
    acc2z E x (S.upd2 vl el vh eh s) = bv2z (TE.vtyp x E) eh.
  Proof. rewrite /acc2z => Heq. rewrite (S.acc_upd2_eq2 Heq). reflexivity. Qed.

  Lemma acc2z_Upd2_eq2 {E x vl el vh eh s1 s2} :
    x == vh ->
    S.Upd2 vl el vh eh s1 s2 ->
    acc2z E x s2 = bv2z (TE.vtyp x E) eh.
  Proof.
    rewrite /acc2z => Heq Hupd. rewrite (S.acc_Upd2_eq2 Heq Hupd). reflexivity.
  Qed.

  Lemma acc2z_upd2_neq {E x vl el vh eh s} :
    x != vl -> x != vh ->
    acc2z E x (S.upd2 vl el vh eh s) = acc2z E x s.
  Proof.
    rewrite /acc2z => Hne1 Hne2. rewrite (S.acc_upd2_neq Hne1 Hne2). reflexivity.
  Qed.

  Lemma acc2z_Upd2_neq {E x vl el vh eh s1 s2} :
    x != vl -> x != vh ->
    S.Upd2 vl el vh eh s1 s2 ->
    acc2z E x s2 = acc2z E x s1.
  Proof.
    rewrite /acc2z => Hne1 Hne2 Hupd. rewrite (S.acc_Upd2_neq Hne1 Hne2 Hupd).
    reflexivity.
  Qed.



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
    | Evar v => acc2z te v s
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

  Lemma eqn_instr_succ_typenv i te :
    instr_succ_typenv (eqn_instr i) te = instr_succ_typenv i te.
  Proof. case: i => //=. move=> [e r] /=. reflexivity. Qed.

  Lemma rng_instr_succ_typenv i te :
    instr_succ_typenv (rng_instr i) te = instr_succ_typenv i te.
  Proof. case: i => //=. move=> [e r] /=. reflexivity. Qed.

  Lemma rng_lvs_instr_subset i :
    VS.subset (lvs_instr (rng_instr i)) (lvs_instr i).
  Proof.
    case: i => /=; try (intros; apply: VSLemmas.subset_refl).
    case => _ r /=. exact: VSLemmas.subset_refl.
  Qed.

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
      S.Upd2 vl (shrB ((size (eval_atomic a s)) - n) (shlB ((size (eval_atomic a s)) - n) (eval_atomic a s)))
             vh (shrB n (eval_atomic a s))
             s t ->
      eval_instr te (Isplit vh vl a n) s t
  | EIsplitS vh vl a n s t :
      is_signed (atyp a te) ->
      S.Upd2 vl (shrB ((size (eval_atomic a s)) - n) (shlB ((size (eval_atomic a s)) - n) (eval_atomic a s)))
             vh (sarB n (eval_atomic a s))
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

  Lemma program_succ_typenv_cons E i p :
    program_succ_typenv (i::p) E = program_succ_typenv p (instr_succ_typenv i E).
  Proof. reflexivity. Qed.

  Lemma program_succ_typenv_rcons E p i :
    program_succ_typenv (rcons p i) E = instr_succ_typenv i (program_succ_typenv p E).
  Proof. by elim: p E => [| hd tl IH] //=. Qed.

  Lemma program_succ_typenv_cat E p1 p2 :
    program_succ_typenv (p1 ++ p2) E =
    program_succ_typenv p2 (program_succ_typenv p1 E).
  Proof. by elim: p1 E => [| hd1 tl1 IH] //=. Qed.

  Lemma eval_ebexp_split e te s :
    eval_ebexp e te s -> (forall se, se \in split_eand e -> eval_ebexp se te s).
  Proof.
    elim: e => /=.
    - move=> _ se Hin. rewrite mem_seq1 in Hin. rewrite (eqP Hin) /=. done.
    - move=> e1 e2 H se Hin. rewrite mem_seq1 in Hin. rewrite (eqP Hin) /=.
      assumption.
    - move=> e1 e2 m H se Hin. rewrite mem_seq1 in Hin. rewrite (eqP Hin) /=.
      assumption.
    - move=> e1 IH1 e2 IH2 [He1 He2] se Hin. rewrite mem_cat in Hin.
      case/orP: Hin => Hin.
      + exact: (IH1 He1 se Hin).
      + exact: (IH2 He2 se Hin).
  Qed.

  Lemma split_ebexp_eval e te s :
    (forall se, se \in split_eand e -> eval_ebexp se te s) -> eval_ebexp e te s.
  Proof.
    elim: e => /=.
    - done.
    - move=> e1 e2 H. apply: (H (Eeq e1 e2)). by rewrite mem_seq1 eqxx.
    - move=> e1 e2 m H. apply: (H (Eeqmod e1 e2 m)). by rewrite mem_seq1 eqxx.
    - move=> e1 IH1 e2 IH2 H; split.
      + apply: IH1 => se Hin. apply: H. by rewrite mem_cat Hin orTb.
      + apply: IH2 => se Hin. apply: H. by rewrite mem_cat Hin orbT.
  Qed.

  Lemma eval_ebexp_eands_cons E e es s :
    eval_ebexp (eands (e::es)) E s <-> eval_ebexp e E s /\ eval_ebexp (eands es) E s.
  Proof. done. Qed.

  Lemma eval_ebexp_eands_cat E es1 es2 s :
    eval_ebexp (eands (es1 ++ es2)) E s <->
    (eval_ebexp (eands es1) E s) /\ (eval_ebexp (eands es2) E s).
  Proof.
    elim: es1 es2 => [| e1 es1 IH] es2 /=.
    - by tauto.
    - split.
      + move=> [He1 H12]. move/IH: H12 => [Hes1 Hes2]. by tauto.
      + move=> [[He1 Hes1] Hes2]. split; first assumption.
        apply/IH. done.
  Qed.

  Lemma eqn_program_succ_typenv p te :
    program_succ_typenv (eqn_program p) te = program_succ_typenv p te.
  Proof.
    elim: p te => [| hd tl IH te] //=. rewrite eqn_instr_succ_typenv. exact: (IH _).
  Qed.

  Lemma rng_program_succ_typenv p te :
    program_succ_typenv (rng_program p) te = program_succ_typenv p te.
  Proof.
    elim: p te => [| hd tl IH te] //=. rewrite rng_instr_succ_typenv. exact: (IH _).
  Qed.

  Lemma eval_program_singleton i te1 s1 s2:
    eval_program te1 ([:: i]) s1 s2 -> eval_instr te1 i s1 s2.
  Proof.
    move=> H.
    inversion H; subst.
    inversion H5; subst.
    assumption.
  Qed.

  Lemma eval_program_cons E hd tl s1 s3 :
    eval_program E (hd :: tl) s1 s3 ->
    exists s2, eval_instr E hd s1 s2 /\
               eval_program (instr_succ_typenv hd E) tl s2 s3.
  Proof.
    move => Hev.
    inversion_clear Hev.
    exists t => //.
  Qed.

  Lemma eval_program_rcons E p i s1 s3 :
    eval_program E (rcons p i) s1 s3 ->
    exists s2, eval_program E p s1 s2 /\
               eval_instr (program_succ_typenv p E) i s2 s3.
  Proof.
    elim: p E s1 s3 => [| hd tl IH] E s1 s3 Hev /=.
    - inversion_clear Hev. move: H. inversion_clear H0. move=> Hev.
      exists s1. split; [exact: Enil | exact: Hev].
    - move: (eval_program_cons Hev) => [s2 [Hev_hd Hev_tli]].
      move: (IH _ _ _ Hev_tli) => [s4 [Hev_tl Hev_i]].
      exists s4. split.
      + exact: (Econs Hev_hd Hev_tl).
      + exact: Hev_i.
  Qed.

  Lemma eval_program_cat E p1 p2 s1 s3 :
    eval_program E (p1 ++ p2) s1 s3 ->
    exists s2, eval_program E p1 s1 s2 /\
               eval_program (program_succ_typenv p1 E) p2 s2 s3.
  Proof.
    elim: p1 p2 E s1 s3 => [| i1 p1 IH] p2 E s1 s3 Hev /=.
    - rewrite cat0s in Hev. exists s1. split; [exact: Enil | exact: Hev].
    - rewrite cat_cons in Hev. move: (eval_program_cons Hev) => [s4 [Hev_i1 Hev_cat]].
      move: (IH _ _ _ _ Hev_cat) => [s5 [Hev_p1 Hev_p2]]. exists s5. split.
      + exact: (Econs Hev_i1 Hev_p1).
      + exact: Hev_p2.
  Qed.

  Lemma eval_eqn_instr i te s1 s2 :
    eval_instr te i s1 s2 -> eval_instr te (eqn_instr i) s1 s2.
  Proof.
    case: i => //=. move=> [e r] H. inversion_clear H. move: H0 => [/= He Hr].
    apply: EIassume. split; [assumption | done].
  Qed.

  Lemma eval_rng_instr i te s1 s2 :
    eval_instr te i s1 s2 -> eval_instr te (rng_instr i) s1 s2.
  Proof.
    case: i => //=. move=> [e r] H. inversion_clear H. move: H0 => [/= He Hr].
    apply: EIassume. split; [done | assumption].
  Qed.

  Lemma eval_eqn_rng_instr i te s1 s2 :
    eval_instr te (eqn_instr i) s1 s2 -> eval_instr te (rng_instr i) s1 s2 ->
    eval_instr te i s1 s2.
  Proof.
    case: i => //=. move=> [e r]. move=> H1 H2. inversion_clear H1; inversion_clear H2.
    move: H H0 => [/= He _] [/= _ Hr]. by apply: EIassume.
  Qed.

  Lemma eval_eqn_program p te s1 s2 :
    eval_program te p s1 s2 -> eval_program te (eqn_program p) s1 s2.
  Proof.
    elim: p te s1 s2 => [| hd tl IH] te s1 s2 //=. move=> H. inversion_clear H.
    apply: (Econs (eval_eqn_instr H0)). apply: IH. rewrite eqn_instr_succ_typenv.
    assumption.
  Qed.

  Lemma eval_rng_program p te s1 s2 :
    eval_program te p s1 s2 -> eval_program te (rng_program p) s1 s2.
  Proof.
    elim: p te s1 s2 => [| hd tl IH] te s1 s2 //=. move=> H. inversion_clear H.
    apply: (Econs (eval_rng_instr H0)). apply: IH. rewrite rng_instr_succ_typenv.
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
    valid_espec (espec_of_spec s) -> valid_rspec (rspec_of_spec s) ->
    valid_spec s.
  Proof.
    move=> He Hr s1 s2 Hcon [Hepre Hrpre] Hprog. split.
    - move: (He s1 s2 Hcon Hepre (eval_eqn_program Hprog)) => /=.
      rewrite eqn_program_succ_typenv. by apply.
    - exact: (Hr s1 s2 Hcon Hrpre (eval_rng_program Hprog)).
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

  Definition well_sized_atomic (E : TE.env) (a : atomic) : bool :=
    is_unsigned (atyp a E) || (0 < asize a E).

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
      is_unsigned (atyp al te) && compatible (atyp ah te) (atyp al te) &&
      well_sized_atomic te ah
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
    VS.for_all (is_defined^~ te) vs.

  Lemma vars_env_mem v te: TE.mem v te = VS.mem v (vars_env te).
  Proof. rewrite TEKS.mem_key_set. reflexivity. Qed.

  Lemma mem_vars_env v te: VS.mem v (vars_env te) = TE.mem v te.
  Proof. exact: TEKS.mem_key_set. Qed.

  Lemma memenvP : forall v E, reflect (TE.mem v E) (VS.mem v (vars_env E)).
  Proof.
    move=> v E. case Hmem: (VS.mem v (vars_env E)).
    - apply: ReflectT. by rewrite vars_env_mem.
    - apply: ReflectF. move/negP: Hmem. by rewrite vars_env_mem.
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

  Definition well_formed_eexp (te : TE.env) (e : eexp) :=
    are_defined (vars_eexp e) te && well_typed_eexp te e.

  Definition well_formed_rexp (te : TE.env) (e : rexp) :=
    are_defined (vars_rexp e) te && well_typed_rexp te e.

  Definition well_formed_ebexp (te : TE.env) (e : ebexp) :=
    are_defined (vars_ebexp e) te && well_typed_ebexp te e.

  Definition well_formed_rbexp (te : TE.env) (e : rbexp) :=
    are_defined (vars_rbexp e) te && well_typed_rbexp te e.

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

  Lemma well_formed_program_cons E p i :
    well_formed_program E (i::p) =
    (well_formed_instr E i) && (well_formed_program (instr_succ_typenv i E) p).
  Proof.
    case H: ((well_formed_instr E i) &&
             (well_formed_program (instr_succ_typenv i E) p)).
    - move/andP: H=> [H1 H2]. exact: (well_formed_program_cons3 H1 H2).
    - apply/negP => Hcons. move/idP/negP: H. rewrite negb_and. case/orP=> H.
      + rewrite (well_formed_program_cons1 Hcons) in H. discriminate.
      + rewrite (well_formed_program_cons2 Hcons) in H. discriminate.
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

  Lemma atyp_add_mem a x t E :
    VS.mem x (vars_atomic a) -> atyp a (TE.add x t E) = t.
  Proof.
    case: a => /= [v Hmem | tb bs Hmem].
    - move: (VSLemmas.mem_singleton1 Hmem) => /idP Heq. rewrite eq_sym in Heq.
      exact: (TE.vtyp_add_eq Heq).
    - rewrite VSLemmas.mem_empty in Hmem. discriminate.
  Qed.

  Lemma atyp_add_not_mem a x t E :
    ~~ VS.mem x (vars_atomic a) -> atyp a (TE.add x t E) = atyp a E.
  Proof.
    case: a => /= [v Hmem | tb bs Hmem].
    - move: (VSLemmas.not_mem_singleton1 Hmem) => /negP Hne. rewrite eq_sym in Hne.
      exact: (TE.vtyp_add_neq Hne).
    - reflexivity.
  Qed.

  Lemma atyp_add_same E a v : atyp a (TE.add v (atyp a E) E) = atyp a E.
  Proof.
    case: a => //=. move=> x. case Hxv: (x == v).
    - rewrite (TE.vtyp_add_eq Hxv). reflexivity.
    - move/idP/negP: Hxv => Hne. rewrite (TE.vtyp_add_neq Hne). reflexivity.
  Qed.

  Lemma asize_add_same te a v :
    asize a (TE.add v (atyp a te) te) = (asize a te).
  Proof. rewrite /asize atyp_add_same. reflexivity. Qed.

  (* Probably useful *)
  (* TO BE confirmed: how to modify (VS.subset vs1 vs2) and (VS.Equal vs1 vs2) *)

  Lemma are_defined_compat te : SetoidList.compat_bool VS.SE.eq (is_defined^~ te).
  Proof. move=> x y Heq; by rewrite (eqP Heq) //. Qed.

  Lemma are_defined_singleton v te :
    are_defined (VS.singleton v) te = is_defined v te.
  Proof.
      by rewrite /are_defined (VSLemmas.for_all_singleton (are_defined_compat te)).
  Qed.

  Lemma are_defined_Empty s E : VS.Empty s -> are_defined s E.
  Proof.
    move=> Hemp. rewrite /are_defined. apply: (VS.for_all_1 (are_defined_compat E)).
    move=> x Hinx. move: (Hemp x) => Houtx. contradiction.
  Qed.

  Lemma are_defined_empty E : are_defined VS.empty E.
  Proof. exact: (are_defined_Empty E VS.empty_1). Qed.

  Lemma is_defined_add x y t E :
    is_defined x (TE.add y t E) = (x == y) || (is_defined x E).
  Proof.
    rewrite /is_defined. rewrite TELemmas.add_b /TELemmas.eqb.
    case: (TE.E.eq_dec y x).
    - move/eqP => Heq. rewrite Heq eqxx. reflexivity.
    - move/idP/negPf=> Hne. rewrite eq_sym Hne. reflexivity.
  Qed.

  Lemma is_defined_add_eq x t E : is_defined x (TE.add x t E).
  Proof. by rewrite is_defined_add eqxx orTb. Qed.

  Lemma is_defined_add_neq x y t E :
    x != y -> is_defined x (TE.add y t E) = is_defined x E.
  Proof. move/idP/negPf=> Hne. rewrite is_defined_add Hne orFb. reflexivity. Qed.

  Lemma are_defined_addl v vs E :
    are_defined (VS.add v vs) E = (is_defined v E) && (are_defined vs E).
  Proof.
    rewrite /are_defined. rewrite (VSLemmas.for_all_add (are_defined_compat E)).
    reflexivity.
  Qed.

  Lemma are_defined_Addl v vs1 vs2 E :
    VSLemmas.P.Add v vs1 vs2 ->
    are_defined vs2 E = is_defined v E && are_defined vs1 E.
  Proof.
    exact: (VSLemmas.for_all_Add (are_defined_compat E)).
  Qed.

  Lemma are_defined_addr vs x t E : are_defined vs E -> are_defined vs (TE.add x t E).
  Proof.
    move/(VS.for_all_2 (are_defined_compat E)) => Hdef.
    apply/(VS.for_all_1 (are_defined_compat _)) => y Hiny.
    move: (Hdef y Hiny) => {Hdef} Hdef. by rewrite is_defined_add Hdef orbT.
  Qed.

  Lemma are_defined_addr_not_mem vs x t E :
    are_defined vs (TE.add x t E) -> VS.mem x vs = false ->
    are_defined vs E.
  Proof.
    move/(VS.for_all_2 (are_defined_compat _)) => Hdef Hmem.
    apply/(VS.for_all_1 (are_defined_compat E)) => y Hiny.
    move: (Hdef y Hiny) => {Hdef} Hdef. rewrite is_defined_add in Hdef. case/orP: Hdef.
    - move/eqP=> Heq. rewrite Heq in Hiny. move/VSLemmas.memP: Hiny => Hmemx.
      rewrite Hmemx in Hmem; discriminate.
    - by apply.
  Qed.

  Lemma are_defined_add2 vs x t E :
    are_defined vs E -> are_defined (VS.add x vs) (TE.add x t E).
  Proof.
    move/(VS.for_all_2 (are_defined_compat E)) => Hall.
    rewrite are_defined_addl. rewrite is_defined_add_eq /=.
    apply: (VS.for_all_1 (are_defined_compat _)) => y Hiny.
    rewrite is_defined_add (Hall y Hiny) orbT. reflexivity.
  Qed.

  Lemma are_defined_union te vs1 vs2 :
    are_defined (VS.union vs1 vs2) te = are_defined vs1 te && are_defined vs2 te.
  Proof.
    rewrite /are_defined. exact: (VSLemmas.for_all_union (are_defined_compat te)).
  Qed.

  Lemma are_defined_subset te vs1 vs2 :
    VS.subset vs1 vs2 -> are_defined vs2 te -> are_defined vs1 te.
  Proof.
    move=> Hsub Hdef2.
    exact: (VSLemmas.for_all_subset (are_defined_compat te) Hsub Hdef2).
  Qed.

  Lemma are_defined_add_env vs x t E :
    are_defined vs (TE.add x t E) =
    (VS.mem x vs && are_defined (VS.remove x vs) E) || (are_defined vs E).
  Proof.
    case H: (VS.mem x vs && are_defined (VS.remove x vs) E || are_defined vs E).
    - case/orP: H => H.
      + move/andP: H=> [Hmem Hdef]. move: (are_defined_add2 x t Hdef) => {Hdef} Hdef.
        apply: (are_defined_subset _ Hdef). move/VSLemmas.memP: Hmem => Hin.
          rewrite (VSLemmas.P.add_remove Hin). exact: VSLemmas.subset_refl.
      + exact: (are_defined_addr _ _ H).
    - apply/negP=> Hdef. move/negP: H; apply. case H: (are_defined vs E);
                                                first by rewrite orbT.
      rewrite orbF. apply/andP; split.
      + case Hmem: (VS.mem x vs); first by trivial.
        apply: False_ind; move/negP: H; apply.
        exact: (are_defined_addr_not_mem Hdef Hmem).
      + move/(VS.for_all_2 (are_defined_compat _)): Hdef => Hdef.
        apply/(VS.for_all_1 (are_defined_compat _)) => y /VSLemmas.memP Hmemy.
        move: (VSLemmas.mem_remove1 Hmemy) => {Hmemy} [Hneq /VSLemmas.memP Hiny].
        move: (Hdef y Hiny) => Hdefy. move/negP: Hneq => Hneq.
        rewrite (is_defined_add_neq _ _ Hneq) in Hdefy. assumption.
  Qed.

  Lemma is_defined_mem_vars_env E v :
    is_defined v E = VS.mem v (vars_env E).
  Proof. rewrite /is_defined. rewrite TEKS.mem_key_set. reflexivity. Qed.

  Lemma are_defined_subset_env te vs: are_defined vs te = VS.subset vs (vars_env te).
  Proof.
    rewrite /are_defined. case Hsub: (VS.subset vs (vars_env te)).
    - apply: (VS.for_all_1 (are_defined_compat te)). move=> x Hin.
      rewrite /is_defined. move/VSLemmas.memP: Hin=> Hmem.
      move: (VSLemmas.mem_subset Hmem Hsub). by rewrite mem_vars_env.
    - apply/negP=> Hall. move/negP: Hsub; apply.
      move: (VS.for_all_2 (are_defined_compat te) Hall) => {Hall} Hall.
      apply: VS.subset_1 => x Hin. move: (Hall x Hin) => Hdef.
      apply/VSLemmas.memP. rewrite mem_vars_env. exact: Hdef.
  Qed.

  Lemma are_defined_trans vs te1 te2 :
    are_defined vs te1 -> are_defined (vars_env te1) te2 -> are_defined vs te2.
  Proof.
    move=> Hdef1 Hdef2. rewrite !are_defined_subset_env in Hdef1 Hdef2 *.
    exact: (VSLemmas.subset_trans Hdef1 Hdef2).
  Qed.

  Lemma are_defined_env_subset te1 te2 vs:
    are_defined vs te1 -> VS.subset (vars_env te1) (vars_env te2) ->
    are_defined vs te2.
  Proof.
    move=> Hdef1 Hsub. rewrite -are_defined_subset_env in Hsub.
    exact: (are_defined_trans Hdef1 Hsub).
  Qed.

  Lemma defmemP v E : reflect (is_defined v E) (TE.mem v E).
  Proof.
    case Hmem: (TE.mem v E).
    - apply: ReflectT. exact: Hmem.
    - apply: ReflectF. move/negP: Hmem. by apply.
  Qed.

  Lemma memdefP v E : reflect (TE.mem v E) (is_defined v E).
  Proof.
    case Hdef: (is_defined v E).
    - apply: ReflectT. exact: Hdef.
    - apply: ReflectF. move/negP: Hdef. by apply.
  Qed.

  Lemma defsubP vs E : reflect (are_defined vs E) (VS.subset vs (vars_env E)).
  Proof.
    case Hsub: (VS.subset vs (vars_env E)).
    - apply: ReflectT. by rewrite are_defined_subset_env Hsub.
    - apply: ReflectF. move/negP: Hsub. by rewrite are_defined_subset_env.
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
    move=> Hwf. move: (well_formed_instr_subset_rvs_aux Hwf) => Hsub_rvs.
    rewrite -(are_defined_subset_env te (rvs_instr i)). assumption.
  Qed.

  Lemma is_defined_submap k (te1 te2: TE.env):
    TELemmas.submap te1 te2 ->
    is_defined k te1 -> is_defined k te2.
  Proof. move=> Hsm Hdef1. exact: (TELemmas.submap_mem Hsm Hdef1). Qed.

  Lemma are_defined_submap vs (te1 te2: TE.env):
    TELemmas.submap te1 te2 ->
    are_defined vs te1 -> are_defined vs te2.
  Proof.
    move=> Hsubmap Hdef1. move: (TEKS.submap_key_set Hsubmap) => Hsubset.
    rewrite -are_defined_subset_env in Hsubset.
    exact: (are_defined_trans Hdef1 Hsubset).
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

  Lemma submap_vtyp E1 E2 v :
    TELemmas.submap E1 E2 ->
    is_defined v E1 ->
    TE.vtyp v E1 = TE.vtyp v E2.
  Proof.
    move=> Hsub Hdef. rewrite /is_defined in Hdef.
    move: (TELemmas.mem_find_some Hdef) => [ty Hfind1].
    rewrite (TE.find_some_vtyp Hfind1). move: (Hsub v ty Hfind1) => Hfind2.
    rewrite (TE.find_some_vtyp Hfind2). reflexivity.
  Qed.

  Lemma atyp_submap a te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_atomic a) te1 ->
    atyp a te1 = atyp a te2.
  Proof.
    case: a => //=. move=> v. rewrite are_defined_singleton=> Hsubmap Hdef1.
    move: (TELemmas.mem_find_some Hdef1) => [ty1 Hfind1].
    move: (Hsubmap v ty1 Hfind1) => Hfind2.
    rewrite (TE.find_some_vtyp Hfind1) (TE.find_some_vtyp Hfind2).
    reflexivity.
  Qed.

  Lemma asize_submap a E1 E2 :
    TELemmas.submap E1 E2 ->
    are_defined (vars_atomic a) E1 ->
    asize a E1 = asize a E2.
  Proof.
    move=> H1 H2. rewrite /asize (atyp_submap H1 H2). reflexivity.
  Qed.

  Lemma well_sized_atomic_submap a E1 E2 :
    TELemmas.submap E1 E2 ->
    are_defined (vars_atomic a) E1 ->
    well_sized_atomic E1 a = well_sized_atomic E2 a.
  Proof.
    move=> Hsub Hdef. rewrite /well_sized_atomic. rewrite (atyp_submap Hsub Hdef).
    rewrite (asize_submap Hsub Hdef). reflexivity.
  Qed.

  Lemma well_sized_atomic_atyp_eq E a1 a2 :
    atyp a1 E = atyp a2 E -> well_sized_atomic E a1 = well_sized_atomic E a2.
  Proof.
    rewrite /well_sized_atomic /asize. by move=> ->.
  Qed.

  Lemma submap_add_vtyp v t E1 E2 :
    TELemmas.submap (TE.add v t E1) E2 ->
    TE.vtyp v E2 = t.
  Proof.
    move=> Hsub. apply: TE.find_some_vtyp. apply: Hsub.
    apply: TELemmas.find_add_eq. reflexivity.
  Qed.

  Lemma submap_add_atyp a v t E1 E2 :
    TELemmas.submap (TE.add v t E1) E2 ->
    are_defined (vars_atomic a) E1 ->
    ~~ VS.mem v (vars_atomic a) ->
    atyp a E1 = atyp a E2.
  Proof.
    case: a => /=.
    - move=> x. rewrite are_defined_singleton=> Hsub Hdef Hmem.
      move: (VSLemmas.not_mem_singleton1 Hmem) => {Hmem} /negP Hne.
      rewrite eq_sym in Hne. move: (is_defined_add_neq t E1 Hne). rewrite Hdef.
      move=> Hdefadd. rewrite -(submap_vtyp Hsub Hdefadd).
      rewrite (TE.vtyp_add_neq Hne). reflexivity.
    - reflexivity.
  Qed.

  Lemma submap_acc2z {E1 E2 v s} :
    TELemmas.submap E1 E2 ->
    is_defined v E1 ->
    acc2z E1 v s = acc2z E2 v s.
  Proof.
    move=> Hsub Hdef. rewrite /acc2z. rewrite (submap_vtyp Hsub Hdef). reflexivity.
  Qed.

  Lemma submap_eval_eexp {E1 E2 e s} :
    TELemmas.submap E1 E2 ->
    are_defined (vars_eexp e) E1 ->
    eval_eexp e E1 s = eval_eexp e E2 s.
  Proof.
    move=> Hsub. elim: e => //=.
    - move=> v. rewrite are_defined_singleton=> Hdef. exact: (submap_acc2z Hsub Hdef).
    - move=> op e IH Hdef. rewrite (IH Hdef). reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
  Qed.

  Lemma submap_eval_ebexp {E1 E2 e s} :
    TELemmas.submap E1 E2 ->
    are_defined (vars_ebexp e) E1 ->
    eval_ebexp e E1 s <-> eval_ebexp e E2 s.
  Proof.
    move=> Hsub. elim: e => //=.
    - move=> e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (submap_eval_eexp Hsub Hdef1) (submap_eval_eexp Hsub Hdef2). done.
    - move=> e1 e2 em. rewrite !are_defined_union => /andP [Hdef1 /andP [Hdef2 Hdefm]].
      rewrite (submap_eval_eexp Hsub Hdef1) (submap_eval_eexp Hsub Hdef2)
              (submap_eval_eexp Hsub Hdefm). done.
    - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      move: (IH1 Hdef1) (IH2 Hdef2) => [H1 H2] [H3 H4]. split; move => [H5 H6].
      + exact: (conj (H1 H5) (H3 H6)).
      + exact: (conj (H2 H5) (H4 H6)).
  Qed.

  Lemma well_typed_eexp_submap e te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_eexp e) te1 ->
    well_typed_eexp te1 e ->
    well_typed_eexp te2 e.
  Proof.
    elim: e te1 te2 => //=; intros.
    move: (VS.for_all_2 (are_defined_compat te1) H2) => Hwd.
    move/andP: H3 => [Hwte0 Hwte1].
    rewrite are_defined_union in H2. move/andP: H2 => [H2 H3].
    apply /andP.
    split.
    - exact: (H _ _ H1 H2 Hwte0).
    - exact: (H0 _ _ H1 H3 Hwte1).
  Qed.

  Lemma well_typed_ebexp_submap e te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_ebexp e) te1 ->
    well_typed_ebexp te1 e ->
    well_typed_ebexp te2 e.
  Proof.
    elim: e te1 te2 => //=; intros.
    - move/andP: H1 => [Hwte Hwte0]. rewrite are_defined_union in H0.
      move/andP: H0 => [Hdef1 Hdef2]. apply /andP. split.
      + exact: (well_typed_eexp_submap H Hdef1 Hwte).
      + exact: (well_typed_eexp_submap H Hdef2 Hwte0).
      +  move/andP: H1 => [/andP [Hwte Hwte0] Hwte1]. rewrite !are_defined_union in H0.
         move/andP: H0 => [Hdef1 /andP [Hdef01 Hdef11]].
         apply/andP; split; [apply/andP; split |].
         * exact: (well_typed_eexp_submap H Hdef1 Hwte).
         * exact: (well_typed_eexp_submap H Hdef01 Hwte0).
         * exact: (well_typed_eexp_submap H Hdef11 Hwte1).
    - move/andP: H3 => [Hwte Hwte0]. rewrite are_defined_union in H2.
      move/andP: H2 => [Hdef1 Hdef2]. apply/andP. split.
      + exact: (H _ _ H1 Hdef1 Hwte).
      + exact: (H0 _ _ H1 Hdef2 Hwte0).
  Qed.

  Lemma well_typed_size_of_rexp_submap r te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_rexp r) te1 ->
    size_of_rexp r te1 == size_of_rexp r te2.
  Proof.
    elim: r te1 te2 => //=.
    move=> x te1 te2 Hsm Hwd.
    replace (VS.singleton x) with (vars_atomic (Avar x)) in Hwd by reflexivity.
    move: (atyp_submap Hsm Hwd) => /= Htyp.
    rewrite (TE.vtyp_vsize Htyp). move: (Logic.eq_sym Htyp) => {Htyp} Htyp.
    rewrite (TE.vtyp_vsize Htyp). rewrite Htyp. exact: eqxx.
  Qed.

  Lemma well_typed_rexp_submap e te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_rexp e) te1 ->
    well_typed_rexp te1 e ->
    well_typed_rexp te2 e.
  Proof.
    elim: e te1 te2 => //=; intros.
    - move/andP: H2 => [Hwte0 Hwte1]. apply/andP. split.
      + exact: (H _ _ H0 H1 Hwte0).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hwte1.
    - move: H3 => /andP [/andP [/andP [Hwt0 Hsz0] Hwt1] Hsz1].
      rewrite are_defined_union in H2. move/andP: H2=> [H2_1 H2_2].
      repeat (apply/andP; split).
      + exact: (H _ _ H1 H2_1 Hwt0).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H1 H2_1)) in Hsz0.
      + exact: (H0 _ _ H1 H2_2 Hwt1).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H1 H2_2)) in Hsz1.
    - move/andP: H2 => [Hwt Hsz]. apply/andP. split.
      + exact: (H _ _ H0 H1 Hwt).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hsz.
    - move/andP: H2 => [Hwt Hsz]. apply/andP. split.
      + exact: (H _ _ H0 H1 Hwt).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hsz.
  Qed.

  Ltac solve_well_typed_rexp_submap :=
    (let rec tac :=
         match goal with
         | H : ?a |- ?a => assumption
         | H : ?l \/ ?r |- _ => case: H => H; tac
         | H: is_true(are_defined (VS.union ?vs1 ?vs2) ?te) |- _ =>
           let Hr1 := fresh "Hr1" in
           let Hr2 := fresh "Hr2" in
           rewrite are_defined_union in H;
           move/andP: H => [Hr1 Hr2]; tac
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

  Lemma well_formed_eexp_submap E1 E2 e :
    TELemmas.submap E1 E2 -> well_formed_eexp E1 e -> well_formed_eexp E2 e.
  Proof.
    move=> Hsubm /andP [Hdef1 Hwt1]. rewrite /well_formed_eexp.
    rewrite (are_defined_submap Hsubm Hdef1)
            (well_typed_eexp_submap Hsubm Hdef1 Hwt1). done.
  Qed.

  Lemma well_formed_ebexp_submap E1 E2 e :
    TELemmas.submap E1 E2 -> well_formed_ebexp E1 e -> well_formed_ebexp E2 e.
  Proof.
    move=> Hsubm /andP [Hdef1 Hwt1]. rewrite /well_formed_ebexp.
    rewrite (are_defined_submap Hsubm Hdef1)
            (well_typed_ebexp_submap Hsubm Hdef1 Hwt1). done.
  Qed.

  Lemma well_formed_rexp_submap E1 E2 e :
    TELemmas.submap E1 E2 -> well_formed_rexp E1 e -> well_formed_rexp E2 e.
  Proof.
    move=> Hsubm /andP [Hdef1 Hwt1]. rewrite /well_formed_rexp.
    rewrite (are_defined_submap Hsubm Hdef1)
            (well_typed_rexp_submap Hsubm Hdef1 Hwt1). done.
  Qed.

  Lemma well_formed_rbexp_submap E1 E2 e :
    TELemmas.submap E1 E2 -> well_formed_rbexp E1 e -> well_formed_rbexp E2 e.
  Proof.
    move=> Hsubm /andP [Hdef1 Hwt1]. rewrite /well_formed_rbexp.
    rewrite (are_defined_submap Hsubm Hdef1)
            (well_typed_rbexp_submap Hsubm Hdef1 Hwt1). done.
  Qed.

  Lemma well_formed_instr_well_typed te1 te2 i :
    well_formed_instr te1 i ->
    TELemmas.submap te1 te2 ->
    well_typed_instr te2 i.
  Proof.
    (elim: i te1 te2 => //=); intros;
      (let rec tac :=
           match goal with
           | H : ?a |- ?a => assumption
           | H : ?l \/ ?r |- _ => case: H => H; tac
           | |- ?l /\ ?r => split; tac
           | |- is_true (_ && _) => apply /andP; tac
           | H : is_true (well_formed_instr ?te ?i) |- _  =>
             let Hwd := fresh "Hwd" in let Hwt := fresh "Hwt" in
                                       move/andP: H => [Hwd Hwt]; tac
           | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
             (rewrite /= in Hwd); tac
           | H : is_true (well_typed_instr ?te ?i) |- _  =>
             (rewrite /= in H); tac
           | H : is_true (_ && _) |- _ =>
             let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]; tac
           | Hsub : TELemmas.submap ?te1 ?te2, Hwd : is_true (are_defined ?vs ?te1)
             |- is_true (are_defined ?vs ?te2) =>
             exact: (are_defined_submap Hsub Hwd); tac
           | Hsub : TELemmas.submap ?te1 ?te2, Hwd : is_true (are_defined ?vs ?te1)
             |- context [atyp ?a ?te2] =>
             rewrite -(atyp_submap Hsub Hwd); tac
           | Hsub : TELemmas.submap ?E1 ?E2,
                    Hdef : is_true (are_defined (vars_atomic ?a) ?E1)
             |- is_true (well_sized_atomic ?E2 ?a) =>
             rewrite -(well_sized_atomic_submap Hsub Hdef); tac
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

  Lemma well_formed_program_submap te1 te2 p :
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

  Lemma well_formed_program_replace te1 te2 p :
    well_formed_program te1 p ->
    TE.Equal te1 te2 ->
    well_formed_program te2 p.
  Proof.
    move=> Hwell Heq.
    apply: (well_formed_program_submap Hwell).
    intros x v Hfind.
    rewrite /TE.Equal in Heq.
    by rewrite -(Heq x).
  Qed.

  Lemma same_program_succ_typenv_submap p te1 te2:
    well_formed_program te1 p ->
    TELemmas.submap te1 te2 ->
    TELemmas.submap (program_succ_typenv p te1)
                        (program_succ_typenv p te2).
  Proof.
    elim: p te1 te2.
    - move=> te1 te2 Hsub //=.
    - move=> hd tl IH te1 te2 /= /andP [Hwf_hd Hwf_tl] Hsub /=.
      apply IH.
      exact: Hwf_tl.
      exact: well_formed_instr_succ_typenv_submap.
  Qed.

  Lemma vars_env_add_union te t ty:
    VS.Equal (vars_env (TE.add t ty te)) (VS.union (vars_env te) (VS.singleton t)).
  Proof.
    rewrite /vars_env. rewrite TEKS.key_set_add.
    rewrite -VSLemmas.add_union_singleton2. reflexivity.
  Qed.

  Lemma vars_env_add2_union te x xty y yty:
    VS.Equal (vars_env (TE.add x xty (TE.add y yty te)))
             (VS.union (vars_env te) (VS.add x (VS.singleton y))).
  Proof.
    rewrite /vars_env. rewrite !TEKS.key_set_add.
    rewrite (VSLemmas.OP.P.union_sym (TEKS.key_set te)).
    rewrite (VSLemmas.add_union_singleton1 x (VS.singleton y)).
    rewrite VSLemmas.OP.P.union_assoc.
    rewrite -!VSLemmas.add_union_singleton1. reflexivity.
  Qed.

  Lemma vars_env_instr_succ_typenv i te:
    VS.Equal (vars_env (instr_succ_typenv i te))
    (VS.union (vars_env te) (lvs_instr i)).
  Proof.
    elim: i te => //=; intros;
      (let rec tac :=
           match goal with
           | H : ?a |- ?a => assumption
           | |- ?l /\ ?r => split; tac
           | |- is_true (_ && _) => apply /andP; tac
           | H : is_true (_ && _) |- _ =>
             let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]; tac
           | |- VS.Equal (vars_env (TE.add ?t ?ty ?te)) (VS.union (vars_env ?te) (VS.singleton ?t))
             => exact: vars_env_add_union
           | |-     VS.Equal (vars_env (TE.add ?x ?xty (TE.add ?y ?yty ?te)))
                             (VS.union (vars_env ?te) (VS.add ?x (VS.singleton ?y)))
             => exact: vars_env_add2_union
           | |- VS.Equal (vars_env ?te) (VS.union (vars_env ?te) VS.empty)
                         => rewrite VSLemmas.union_emptyr; exact: VSLemmas.P.equal_refl
           | H : ?l \/ ?r |- _ => case: H => H; tac
           | |- ?e => progress (auto)
           | |- _ => idtac
           end
       in tac).
  Qed.

  Lemma vars_env_program_succ_typenv p E :
    VS.Equal (vars_env (program_succ_typenv p E))
             (VS.union (vars_env E) (lvs_program p)).
  Proof.
    elim: p E => [| i p IH] E /=.
    - rewrite VSLemmas.union_emptyr. reflexivity.
    - rewrite IH. rewrite vars_env_instr_succ_typenv. by VSLemmas.dp_Equal.
  Qed.

  Lemma mem_instr_succ_typenv x i E :
    TE.mem x E -> TE.mem x (instr_succ_typenv i E).
  Proof.
    move/memenvP => H. apply/memenvP/VSLemmas.memP.
    move: (@vars_env_instr_succ_typenv i E x) => [_ Himp]. apply: Himp.
    apply/VSLemmas.memP. rewrite VSLemmas.mem_union H. reflexivity.
  Qed.


  Lemma well_typed_bexp_split te e :
    well_typed_bexp te e = (well_typed_ebexp te (eqn_bexp e))
                             && (well_typed_rbexp te (rng_bexp e)).
  Proof. reflexivity. Qed.

  Lemma well_formed_bexp_split te e :
    well_formed_bexp te e = (well_formed_ebexp te (eqn_bexp e))
                              && (well_formed_rbexp te (rng_bexp e)).
  Proof.
    case: e => [e r] /=. rewrite /well_formed_bexp /=.
    rewrite /vars_bexp /=. rewrite are_defined_union well_typed_bexp_split.
    rewrite -Bool.andb_assoc. rewrite (Bool.andb_comm (are_defined (vars_rbexp r) te)).
    rewrite Bool.andb_assoc. rewrite Bool.andb_assoc.
    rewrite -(Bool.andb_assoc
                (are_defined (vars_ebexp e) te
                             && well_typed_ebexp te (eqn_bexp (e, r)))).
    rewrite (Bool.andb_comm (well_typed_rbexp te (rng_bexp (e, r)))). reflexivity.
  Qed.

  Lemma well_typed_eqn_bexp te e :
    well_typed_bexp te e -> well_typed_ebexp te (eqn_bexp e).
  Proof. rewrite well_typed_bexp_split. by move/andP=> [? ?]. Qed.

  Lemma well_typed_rng_bexp te e :
    well_typed_bexp te e -> well_typed_rbexp te (rng_bexp e).
  Proof. rewrite well_typed_bexp_split. by move/andP=> [? ?]. Qed.

  Lemma well_formed_eqn_bexp te e :
    well_formed_bexp te e -> well_formed_ebexp te (eqn_bexp e).
  Proof. rewrite well_formed_bexp_split. by move/andP=> [? ?]. Qed.

  Lemma well_formed_rng_bexp te e :
    well_formed_bexp te e -> well_formed_rbexp te (rng_bexp e).
  Proof. rewrite well_formed_bexp_split. by move/andP=> [? ?]. Qed.

  Lemma well_defined_rng_instr E i :
    well_defined_instr E i -> well_defined_instr E (rng_instr i).
  Proof.
    case: i => //=. case => e r //=. rewrite /vars_bexp /=.
    rewrite !are_defined_union. move/andP => [Hdefe Hdefr].
    rewrite Hdefr are_defined_empty. exact: is_true_true.
  Qed.

  Lemma well_typed_rng_instr E i :
    well_typed_instr E i -> well_typed_instr E (rng_instr i).
  Proof.
    case: i => //=. case => e r //=. rewrite /well_typed_bexp.
    move/andP=> /= [Hwte Hwtr]. exact: Hwtr.
  Qed.

  Lemma well_formed_rng_instr E i :
    well_formed_instr E i -> well_formed_instr E (rng_instr i).
  Proof.
    case: i => //=. case => e r //=. move/andP => [H1 H2]. apply/andP. split.
  - exact: (well_defined_rng_instr H1).
  - exact: (well_typed_rng_instr H2).
  Qed.

  Lemma well_formed_rng_program E p :
    well_formed_program E p ->
    well_formed_program E (rng_program p).
  Proof.
    elim: p E => [| i p IH] E Hwf //=. rewrite well_formed_program_cons in Hwf.
    move/andP: Hwf => [Hwf_i Hwf_p]. rewrite (well_formed_rng_instr Hwf_i) andTb.
    rewrite rng_instr_succ_typenv. exact: (IH _ Hwf_p).
  Qed.


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



  (* Lemmas about conform *)

  Lemma conform_Upd te s1 s2 ty x v :
    Typ.sizeof_typ ty = size v -> S.conform s1 te -> S.Upd x v s1 s2 ->
    S.conform s2 (TE.add x ty te).
  Proof. move => Hszeq Hcon HUpd. exact: (S.conform_Upd Hszeq HUpd Hcon). Qed.

  Lemma conform_Upd2 te s1 s2 ty1 ty2 x1 x2 v1 v2 :
    x1 != x2 ->
    Typ.sizeof_typ ty1 = size v1 -> Typ.sizeof_typ ty2 = size v2 ->
    S.Upd2 x2 v2 x1 v1 s1 s2 -> S.conform s1 te ->
    S.conform s2 (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Proof.
    move => Hneq Hty1 Hty2 HUpd2 Hcon.
    exact: (S.conform_Upd2 Hneq Hty1 Hty2 HUpd2 Hcon).
  Qed.

  Lemma conform_submap E1 E2 s :
    TELemmas.submap E1 E2 -> S.conform s E2 -> S.conform s E1.
  Proof.
    move=> Hsubm Hco. apply: S.conform_def => x Hmem1.
    move: (TELemmas.submap_mem Hsubm Hmem1) => Hmem2.
    move: (TELemmas.mem_find_some Hmem1) => [ty Hfind1].
    move: (Hsubm x ty Hfind1) => Hfind2. move: (TE.find_some_vtyp Hfind1) => Hty1.
    move: (TE.find_some_vtyp Hfind2) => Hty2. rewrite -(S.conform_mem Hco Hmem2).
    rewrite (TE.vtyp_vsize Hty1) (TE.vtyp_vsize Hty2). reflexivity.
  Qed.

  Lemma conform_size_eval_atomic te s a :
    VS.subset (vars_atomic a) (vars_env te) -> S.conform s te ->
    size (eval_atomic a s) = Typ.sizeof_typ (atyp a te).
  Proof.
    case: a => /=.
    - move => v. rewrite VSLemmas.subset_singleton => /memenvP Hmem Hcon.
      rewrite -(S.conform_mem Hcon Hmem). apply: TE.vtyp_vsize. reflexivity.
    - move => t b _ _.
  (* size of (Aconst t b) = b but
     Typ.sizeof_typ (atyp (Aconst t b)) = t,
     why is b = t?
   *)
  Admitted.

  Lemma size_eval_atomic_asize te a s :
    VS.subset (vars_atomic a) (vars_env te) -> S.conform s te ->
    size (eval_atomic a s) = asize a te.
  Proof.
    move => Hsub Hcon. rewrite (conform_size_eval_atomic Hsub Hcon). reflexivity.
  Qed.

  Lemma tbit_var_size E s v :
    S.conform s E -> TE.mem v E -> TE.vtyp v E = Tbit -> size (S.acc v s) = 1.
  Proof.
    move=> Hco Hmem Htyp. rewrite -(S.conform_mem Hco Hmem).
    rewrite (TE.vtyp_vsize Htyp). reflexivity.
  Qed.

  Lemma tbit_var_singleton E s v :
    S.conform s E -> TE.mem v E -> TE.vtyp v E = Tbit ->
    exists b, S.acc v s = [:: b].
  Proof.
    move=> Hco Hmem Htyp. move: (tbit_var_size Hco Hmem Htyp).
    clear Hco Hmem Htyp. case: (S.acc v s) => [| b1 [| b2 bs]] //=.
    move=> _; by exists b1.
  Qed.

  Lemma tbit_atomic_size E s a :
    S.conform s E -> atyp a E = Typ.Tbit ->
    VS.subset (vars_atomic a) (vars_env E) ->
    size (eval_atomic a s) = 1.
  Proof.
    move=> Hco Htyp Hsub. move: (size_eval_atomic_asize Hsub Hco) => Hsc.
    rewrite /asize Htyp /= in Hsc. exact: Hsc.
  Qed.

  Lemma tbit_atomic_singleton E s a :
    S.conform s E -> atyp a E = Typ.Tbit ->
    VS.subset (vars_atomic a) (vars_env E) ->
    exists b, eval_atomic a s = [:: b].
  Proof.
    move=> Hco Htyp Hsub. move: (tbit_atomic_size Hco Htyp Hsub).
    clear Hco Htyp Hsub. case: (eval_atomic a s) => [| b1 [| b2 bs]] //=.
    move=> _. by exists b1.
  Qed.

  Lemma size_eval_atomic_same te s a0 a1 :
    S.conform s te ->
    VS.subset (vars_atomic a0) (vars_env te) ->
    VS.subset (vars_atomic a1) (vars_env te) ->
    atyp a0 te = atyp a1 te ->
    size (eval_atomic a0 s) = size (eval_atomic a1 s) .
  Proof .
    move => Hcon Hsub0 Hsub1 Hatypeq .
    move : (conform_size_eval_atomic Hsub0 Hcon)
             (conform_size_eval_atomic Hsub1 Hcon) .
    rewrite Hatypeq. by move=> -> ->.
  Qed .

  Lemma conform_eval_succ_typenv_Imov te t a s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Imov t a) ->
    well_typed_instr te (Imov t a) ->
    eval_instr te (Imov t a) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Imov t a) te).
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env => Hdef _ Hev.
    inversion_clear Hev.
    apply : (conform_Upd _ Hcon H). by rewrite (size_eval_atomic_asize Hdef).
  Qed.

  Lemma conform_eval_succ_typenv_Ishl te t a n s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ishl t a n) ->
    well_typed_instr te (Ishl t a n) ->
    eval_instr te (Ishl t a n) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ishl t a n) te) .
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env => Hdef _ Hev .
    inversion_clear Hev .
    apply : (conform_Upd _ Hcon H) .
      by rewrite size_shlB (size_eval_atomic_asize Hdef) .
  Qed .

  Lemma conform_eval_succ_typenv_Icshl te t t0 a a0 n s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Icshl t t0 a a0 n) ->
    well_typed_instr te (Icshl t t0 a a0 n) ->
    eval_instr te (Icshl t t0 a a0 n) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Icshl t t0 a a0 n) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] _ Hev .
    inversion_clear Hev .
    apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + by rewrite size_high (size_eval_atomic_asize Hdef0) .
    + by rewrite size_shrB size_low (size_eval_atomic_asize Hdef1) .
  Qed .

  Lemma conform_eval_succ_typenv_Inondet te t t0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Inondet t t0) ->
    well_typed_instr te (Inondet t t0) ->
    eval_instr te (Inondet t t0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Inondet t t0) te) .
  Proof .
    move => Hcon _ _ Hev .
    inversion_clear Hev .
      by apply : (conform_Upd _ Hcon H0) .
  Qed .

  Lemma conform_eval_succ_typenv_Icmov te t a a0 a1 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Icmov t a a0 a1) ->
    well_typed_instr te (Icmov t a a0 a1) ->
    eval_instr te (Icmov t a a0 a1) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Icmov t a a0 a1) te) .
  Proof .
    move => Hcon /=; rewrite 3!are_defined_subset_env =>
    /andP [/andP [Hdefc Hdef0] Hdef1] /andP [_ Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H0);
      [ by rewrite (size_eval_atomic_asize Hdef0)
      | rewrite (size_eval_atomic_asize Hdef1) //;
        by rewrite (eqP Hty) ] .
  Qed .

  Lemma conform_eval_succ_typenv_Inop te s1 s2 :
    S.conform s1 te ->
    well_defined_instr te Inop ->
    well_typed_instr te Inop ->
    eval_instr te Inop s1 s2 ->
    S.conform s2 (instr_succ_typenv Inop te) .
  Proof .
    move => Hcon _ _ Hev .
    inversion Hev .
      by rewrite -H1 .
  Qed .

  Lemma conform_eval_succ_typenv_Inot te t t0 a s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Inot t t0 a) ->
    well_typed_instr te (Inot t t0 a) ->
    eval_instr te (Inot t t0 a) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Inot t t0 a) te) .
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env => Hdef Hty Hev .
    rewrite /Typ.compatible in Hty .
    inversion_clear Hev .
    apply : (conform_Upd _ Hcon H) => // .
      by rewrite size_invB (eqP Hty) (size_eval_atomic_asize Hdef).
  Qed .

  Lemma conform_eval_succ_typenv_Iadd te t a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iadd t a a0) ->
    well_typed_instr te (Iadd t a a0) ->
    eval_instr te (Iadd t a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iadd t a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_addB (size_eval_atomic_asize Hdef0) // .
    rewrite (size_eval_atomic_asize Hdef1) // .
      by rewrite /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Iadds te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iadds t t0 a a0) ->
    well_typed_instr te (Iadds t t0 a a0) ->
    eval_instr te (Iadds t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iadds t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + rewrite size_addB (size_eval_atomic_asize Hdef0) //;
              rewrite (size_eval_atomic_asize Hdef1) //;
        by rewrite /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Iadc te t a a0 a1 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iadc t a a0 a1) ->
    well_typed_instr te (Iadc t a a0 a1) ->
    eval_instr te (Iadc t a a0 a1) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iadc t a a0 a1) te) .
  Proof .
    move => Hcon /=; rewrite 3!are_defined_subset_env =>
    /andP [/andP [Hdef0 Hdef1] Hdefc] /andP [Hty Htyc] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite /adcB /full_adder size_full_adder_zip
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Iadcs te t t0 a a0 a1 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iadcs t t0 a a0 a1) ->
    well_typed_instr te (Iadcs t t0 a a0 a1) ->
    eval_instr te (Iadcs t t0 a a0 a1) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iadcs t t0 a a0 a1) te) .
  Proof .
    move => Hcon /=; rewrite 3!are_defined_subset_env =>
    /andP [/andP [/andP [Hneq Hdef0] Hdef1] Hdefc] /andP [Hty Htyc] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite /adcB /full_adder size_full_adder_zip
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Isub te t a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isub t a a0) ->
    well_typed_instr te (Isub t a a0) ->
    eval_instr te (Isub t a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isub t a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_subB (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Isubc te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isubc t t0 a a0) ->
    well_typed_instr te (Isubc t t0 a a0) ->
    eval_instr te (Isubc t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isubc t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite size_addB size_negB
                              (size_eval_atomic_asize Hdef0) //
                              (size_eval_atomic_asize Hdef1) //
                              /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Isubb te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isubb t t0 a a0) ->
    well_typed_instr te (Isubb t t0 a a0) ->
    eval_instr te (Isubb t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isubb t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite size_subB
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Isbc te t a a0 a1 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isbc t a a0 a1) ->
    well_typed_instr te (Isbc t a a0 a1) ->
    eval_instr te (Isbc t a a0 a1) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isbc t a a0 a1) te) .
  Proof .
    move => Hcon /=; rewrite 3!are_defined_subset_env =>
    /andP [/andP [Hdef0 Hdef1] Hdefc] /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite /adcB /full_adder size_full_adder_zip
         size_invB
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Isbcs te t t0 a a0 a1 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isbcs t t0 a a0 a1) ->
    well_typed_instr te (Isbcs t t0 a a0 a1) ->
    eval_instr te (Isbcs t t0 a a0 a1) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isbcs t t0 a a0 a1) te) .
  Proof .
    move => Hcon /=; rewrite 3!are_defined_subset_env =>
    /andP [/andP [/andP [Hneq Hdef0] Hdef1] Hdefc] /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite /adcB /full_adder size_full_adder_zip
         size_invB
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Isbb te t a a0 a1 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isbb t a a0 a1) ->
    well_typed_instr te (Isbb t a a0 a1) ->
    eval_instr te (Isbb t a a0 a1) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isbb t a a0 a1) te) .
  Proof .
    move => Hcon /=; rewrite 3!are_defined_subset_env =>
    /andP [/andP [Hdef0 Hdef1] Hdefc] /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_sbbB
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Isbbs te t t0 a a0 a1 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isbbs t t0 a a0 a1) ->
    well_typed_instr te (Isbbs t t0 a a0 a1) ->
    eval_instr te (Isbbs t t0 a a0 a1) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isbbs t t0 a a0 a1) te) .
  Proof .
    move => Hcon /=; rewrite 3!are_defined_subset_env =>
    /andP [/andP [/andP [Hneq Hdef0] Hdef1] Hdefc] /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon); first done .
      by rewrite size_sbbB
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize !(eqP Hty) minnE subKn .
  Qed .

  Lemma conform_eval_succ_typenv_Imul te t a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Imul t a a0) ->
    well_typed_instr te (Imul t a a0) ->
    eval_instr te (Imul t a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Imul t a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_mulB
                 (size_eval_atomic_asize Hdef0) .
  Qed .

  Lemma conform_eval_succ_typenv_Imull te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Imull t t0 a a0) ->
    well_typed_instr te (Imull t t0 a a0) ->
    eval_instr te (Imull t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Imull t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon);
      [ by rewrite size_high
                   (size_eval_atomic_asize Hdef0)
      | rewrite size_low
                (size_eval_atomic_asize Hdef1) // ] .
      by rewrite size_unsigned_typ .
  Qed .

  Lemma conform_eval_succ_typenv_Imulj te t a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Imulj t a a0) ->
    well_typed_instr te (Imulj t a a0) ->
    eval_instr te (Imulj t a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Imulj t a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_full_mul //
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize -(eqP Hty) .
    rewrite /Typ.double_typ /= .
      by case (atyp a te) => /= // n;
                               rewrite mul2n addnn // .
  Qed .

  Lemma conform_eval_succ_typenv_Isplit te t t0 a n s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isplit t t0 a n) ->
    well_typed_instr te (Isplit t t0 a n) ->
    eval_instr te (Isplit t t0 a n) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isplit t t0 a n) te) .
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env =>
    /andP [Hneq Hdef] _ Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H0 Hcon);
      [ by rewrite size_shrB (size_eval_atomic_asize Hdef)
      | by rewrite size_shrB size_shlB size_unsigned_typ
                   (size_eval_atomic_asize Hdef)
      | by rewrite size_sarB (size_eval_atomic_asize Hdef)
      | by rewrite size_shrB size_shlB size_unsigned_typ
                   (size_eval_atomic_asize Hdef) ] .
  Qed .

  Lemma conform_eval_succ_typenv_Iand te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iand t t0 a a0) ->
    well_typed_instr te (Iand t t0 a a0) ->
    eval_instr te (Iand t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iand t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [Htyc Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_lift
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize -(eqP Hty) maxnn (eqP Htyc) .
  Qed .

  Lemma conform_eval_succ_typenv_Ior te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ior t t0 a a0) ->
    well_typed_instr te (Ior t t0 a a0) ->
    eval_instr te (Ior t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ior t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [Htyc Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_lift
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize -(eqP Hty) maxnn (eqP Htyc) .
  Qed .

  Lemma conform_eval_succ_typenv_Ixor te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ixor t t0 a a0) ->
    well_typed_instr te (Ixor t t0 a a0) ->
    eval_instr te (Ixor t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ixor t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [Htyc Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_lift
                 (size_eval_atomic_asize Hdef0) //
                 (size_eval_atomic_asize Hdef1) //
                 /asize -(eqP Hty) maxnn (eqP Htyc) .
  Qed .

  Lemma conform_eval_succ_typenv_Icast te t t0 a s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Icast t t0 a) ->
    well_typed_instr te (Icast t t0 a) ->
    eval_instr te (Icast t t0 a) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Icast t t0 a) te) .
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env => Hdef _ Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_tcast .
  Qed .

  Lemma conform_eval_succ_typenv_Ivpc te t t0 a s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ivpc t t0 a) ->
    well_typed_instr te (Ivpc t t0 a) ->
    eval_instr te (Ivpc t t0 a) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ivpc t t0 a) te) .
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env => Hdef _ Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_tcast .
  Qed .

  Lemma conform_eval_succ_typenv_Ijoin te t a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ijoin t a a0) ->
    well_typed_instr te (Ijoin t a a0) ->
    eval_instr te (Ijoin t a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ijoin t a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [/andP [Hun Hty] Hws] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_cat
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize -(eqP Hty) /Typ.double_typ .
      by case (atyp a te) => /= n;
                               rewrite mul2n addnn .
  Qed .

  Lemma conform_eval_succ_typenv_Iassume te b s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iassume b) ->
    well_typed_instr te (Iassume b) ->
    eval_instr te (Iassume b) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iassume b) te) .
  Proof .
    move => Hcon Hdef _ Hev .
      by inversion Hev; rewrite -H2 // .
  Qed .

  Lemma conform_instr_succ_typenv te i s1 s2 :
    well_formed_instr te i ->
    S.conform s1 te ->
    eval_instr te i s1 s2 ->
    S.conform s2 (instr_succ_typenv i te) .
  Proof .
    move => /andP [Hdef Hty] Hcon .
    case : i Hcon Hdef Hty .
    - move => v a; apply conform_eval_succ_typenv_Imov .
    - move => v a n; apply conform_eval_succ_typenv_Ishl .
    - move => u v a0 a1 n; apply conform_eval_succ_typenv_Icshl .
    - move => v t; apply conform_eval_succ_typenv_Inondet .
    - move => v ac a0 a1; apply conform_eval_succ_typenv_Icmov .
    - apply conform_eval_succ_typenv_Inop .
    - move => v t a; apply conform_eval_succ_typenv_Inot .
    - move => v a0 a1; apply conform_eval_succ_typenv_Iadd .
    - move => c v a0 a1; apply conform_eval_succ_typenv_Iadds .
    - move => v a0 a1 ac; apply conform_eval_succ_typenv_Iadc .
    - move => c v a0 a1 ac; apply conform_eval_succ_typenv_Iadcs .
    - move => v a0 a1; apply conform_eval_succ_typenv_Isub .
    - move => c v a0 a1; apply conform_eval_succ_typenv_Isubc .
    - move => b v a0 a1; apply conform_eval_succ_typenv_Isubb .
    - move => v a0 a1 ac; apply conform_eval_succ_typenv_Isbc .
    - move => c v a0 a1 ac; apply conform_eval_succ_typenv_Isbcs .
    - move => v a0 a1 ab; apply conform_eval_succ_typenv_Isbb .
    - move => b v a0 a1 ab; apply conform_eval_succ_typenv_Isbbs .
    - move => v a0 a1; apply conform_eval_succ_typenv_Imul .
    - move => u v a0 a1; apply conform_eval_succ_typenv_Imull .
    - move => v a0 a1; apply conform_eval_succ_typenv_Imulj .
    - move => u v a0 a1; apply conform_eval_succ_typenv_Isplit .
    - move => v t a0 a1; apply conform_eval_succ_typenv_Iand .
    - move => v t a0 a1; apply conform_eval_succ_typenv_Ior .
    - move => v t a0 a1; apply conform_eval_succ_typenv_Ixor .
    - move => v t a; apply conform_eval_succ_typenv_Icast .
    - move => v t a; apply conform_eval_succ_typenv_Ivpc .
    - move => v a0 a1; apply conform_eval_succ_typenv_Ijoin .
    - move => b; apply conform_eval_succ_typenv_Iassume .
  Qed .

  Lemma conform_program_succ_typenv E p s1 s2 :
    well_formed_program E p ->
    S.conform s1 E ->
    eval_program E p s1 s2 ->
    S.conform s2 (program_succ_typenv p E).
  Proof.
    elim: p E s1 s2 => [| i p IH] E s1 s2 Hwf Hco Hep /=.
    - move: Hco. inversion_clear Hep. by apply.
    - inversion_clear Hep. rewrite well_formed_program_cons in Hwf.
      move/andP: Hwf => [Hwf_i Hwf_p]. apply: (IH _ _ _ Hwf_p _ H0).
      exact: (conform_instr_succ_typenv Hwf_i Hco H).
  Qed.

End MakeDSL.

Module DSL := MakeDSL VarOrder VS VM TE Store.
