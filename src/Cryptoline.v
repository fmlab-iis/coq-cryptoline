
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From BitBlasting Require Import Typ Var TypEnv State QFBV CNF.
From ssrlib Require Import SsrOrdered ZAriths Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope cryptoline with cryptoline.
Local Open Scope cryptoline.

Section Cryptoline.

  (* Operators *)

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



  (* Algebraic Expressions *)

  Inductive eexp : Set :=
  | Evar : var -> eexp
  | Econst : Z -> eexp
  | Eunop : eunop -> eexp -> eexp
  | Ebinop : ebinop -> eexp -> eexp -> eexp.

  Definition evar v := Evar v.
  Definition econst n := Econst n.
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

  Definition e2pow n := Z.pow 2%Z n.

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

  Fixpoint vars_eexp (e : eexp) : VS.t :=
    match e with
    | Evar v => VS.singleton v
    | Econst n => VS.empty
    | Eunop op e => vars_eexp e
    | Ebinop op e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    end.


  (* Limbs *)

  Fixpoint limbsi (i : nat) (r : Z) (es : seq eexp) :=
    match es with
    | [::] => econst Z.zero
    | e::[::] => e
    | e::es => eadd (emul e (econst (e2pow (Z.of_nat i * r)))) (limbsi (i + 1) r es)
    end.

  Definition limbs (r : Z) (es : seq eexp) := limbsi 0 r es.



  (* Range Expressions *)

  (* The first nat is the size of the subexpression *)
  Inductive rexp : Set :=
  | Rvar : var -> rexp
  | Rconst : nat -> bits -> rexp
  | Runop : nat -> runop -> rexp -> rexp
  | Rbinop : nat -> rbinop -> rexp -> rexp -> rexp
  | Ruext : nat -> rexp -> nat -> rexp
  | Rsext : nat -> rexp -> nat -> rexp.

  Fixpoint size_of_rexp (e : rexp) (te : TypEnv.t) : nat :=
    match e with
    | Rvar v => TypEnv.vsize v te
    | Rconst w n => w
    | Runop w _ _ => w
    | Rbinop w _ _ _ => w
    | Ruext w _ i => w + i
    | Rsext w _ i => w + i
    end.

  Definition rvar v := Rvar v.
  Definition rconst n := Rconst (size n) n.
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
    | [::] => rconst (from_nat w 0)
    | e::[::] => e
    | e::es => foldl (fun res e => radd w res e) e es
    end.

  Definition rmuls w es :=
    match es with
    | [::] => rconst (from_nat w 1)
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

  Inductive ebexp : Set :=
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

  Fixpoint vars_ebexp (e : ebexp) : VS.t :=
    match e with
    | Etrue => VS.empty
    | Eeq e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    | Eeqmod e1 e2 m =>
      VS.union (VS.union (vars_eexp e1) (vars_eexp e2)) (vars_eexp m)
    | Eand e1 e2 => VS.union (vars_ebexp e1) (vars_ebexp e2)
    end.



  (* Range Predicates *)

  Inductive rbexp : Set :=
  | Rtrue
  | Req : nat -> rexp -> rexp -> rbexp
  | Rcmp : nat -> rcmpop -> rexp -> rexp -> rbexp
  | Rneg : rbexp -> rbexp
  | Rand : rbexp -> rbexp -> rbexp
  | Ror : rbexp -> rbexp -> rbexp.

  Definition rtrue := Rtrue.
  Definition rfalse := Rneg Rtrue.
  Definition req w e1 e2 := Req w e1 e2.
  Definition rult w e1 e2 := Rcmp w Rult e1 e2.
  Definition rule w e1 e2 := Rcmp w Rule e1 e2.
  Definition rugt w e1 e2 := Rcmp w Rugt e1 e2.
  Definition ruge w e1 e2 := Rcmp w Ruge e1 e2.
  Definition rslt w e1 e2 := Rcmp w Rslt e1 e2.
  Definition rsle w e1 e2 := Rcmp w Rsle e1 e2.
  Definition rsgt w e1 e2 := Rcmp w Rsgt e1 e2.
  Definition rsge w e1 e2 := Rcmp w Rsge e1 e2.
  Definition reqmod w e1 e2 m :=
    req w (rsrem w (rsub w e1 e2) m) (rconst (from_nat w 0)).

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

  Definition bexp : Set := ebexp * rbexp.

  Definition btrue : bexp := (Etrue, Rtrue).

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



  (* Instructions and programs *)

  Inductive prove_with_spec : Set :=
  | Precondition
  | AllCuts
  | AllAssumes
  | AllGhosts.

  Inductive atomic : Set :=
  | Avar : var -> atomic
  | Aconst : typ -> bits -> atomic.

  Definition atyp (a : atomic) (te : TypEnv.t) : typ :=
    match a with
    | Avar v => TypEnv.find v te
    | Aconst ty _ => ty
    end.

  Inductive instr : Type :=
  (* Imov (v, a): v = a *)
  | Imov of var * atomic
  (* Ishl (v, a, n): v = a * 2^n, overflow is forbidden *)
  | Ishl of var * atomic * nat
  (* Icshl (vh, vl, a1, a2, n) *)
  | Icshl of var * var * atomic * atomic * nat
  (* Inondet v: v = a nondeterministic value *)
  | Inondet of var
  (* Icmov (v, c, a1, a2): if c then v = a1 else v = a2 *)
  | Icmov of var * atomic * atomic * atomic
  (* Inop: do nothing *)
  | Inop
  (* Inot (v, a): v = not(a), the one's complement of a *)
  | Inot of var * atomic
  (* Iadd (v, a1, a2): v = a1 + a2, overflow is forbidden *)
  | Iadd of var * atomic * atomic
  (* Iadds (c, v, a1, a2): v = a1 + a2, c = carry flag *)
  | Iadds of var * var * atomic * atomic
  (* Iaddr (c, v, a1, a2): v = a1 + a2, c = 0 *)
  | Iaddr of var * var * atomic * atomic
  (* Iadc (v, a1, a2, y): v = a1 + a2 + y, overflow is forbidden *)
  | Iadc of var * atomic * atomic * atomic
  (* Iadcs (c, v, a1, a2, y): v = a1 + a2 + y, c = carry flag *)
  | Iadcs of var * var * atomic * atomic * atomic
  (* Iadcr (c, v, a1, a2, y): v = a1 + a2 + y, c = 0 *)
  | Iadcr of var * var * atomic * atomic * atomic
  (* Isub (v, a1, a2): v = a1 - a2, overflow is forbidden *)
  | Isub of var * atomic * atomic
  (* Isubc (c, v, a1, a2): v = a1 + not(a2) + 1, c = carry flag *)
  | Isubc of var * var * atomic * atomic
  (* Isous (b, v, a1, a2): v = a1 - a2, b = borrow flag *)
  | Isubb of var * var * atomic * atomic
  (* Isubr (c, v, a1, a2): v = a1 - a2, c = 0 *)
  | Isubr of var * var * atomic * atomic
  (* Isbc (v, a1, a2, y): v = a1 + not(a2) + y *)
  | Isbc of var * atomic * atomic * atomic
  (* Isbcs (c, v, a1, a2, y): v = a1 + not(a2) + y, c = carry flag *)
  | Isbcs of var * var * atomic * atomic * atomic
  (* Isbcr (c, v, a1, a2, y): v = a1 + not(a2) + y, c = 0 *)
  | Isbcr of var * var * atomic * atomic * atomic
  (* Isbb (v, a1, a2, y): v = a1 - a2 - y *)
  | Isbb of var * atomic * atomic * atomic
  (* Isbbs (b, v, a1, a2, y): v = a1 - a2 - y, b = borrow flag *)
  | Isbbs of var * var * atomic * atomic * atomic
  (* Isbbr (b, v, a1, a2, y): v = a1 - a2 - y, b = 0 *)
  | Isbbr of var * var * atomic * atomic * atomic
  (* Imul (v, a1, a2): v = a1 * a2, overflow is forbidden *)
  | Imul of var * atomic * atomic
  | Imuls of var * var * atomic * atomic
  | Imulr of var * var * atomic * atomic
  (* Imull (vh, vl, a1, a2): vh and vl are respectively the high part and
     the low part of the full multiplication a1 * a2 *)
  | Imull of var * var * atomic * atomic
  (* Iumulj (v, a1, a2): v = the full multiplication of a1 * a2, which is equivalent
     to Iumull (vh, vl, a1, a2); Join (r, vh, vl) *)
  | Imulj of var * atomic * atomic
  (* Isplit (vh, vl, a, n): vh is the high (w - n) bits (signed extended to w bits)
     of a and vl is the low n bits (zero extended to w bits) of a where w is the
     bit-width of a *)
  | Isplit of var * var * atomic * nat
  (* == Instructions that cannot be translated to polynomials == *)
  (* Iand (v, a1, a2): v = the bitwise AND of a1 and a2 *)
  | Iand of var * atomic * atomic
  (* Ior (v, a1, a2): v = the bitwise OR of a1 and a2 *)
  | Ior of var * atomic * atomic
  (* Ixor (v, a1, a2): v = the bitwise XOR of a1 and a2 *)
  | Ixor of var * atomic * atomic
  (* == Type conversions == *)
  (* Icast (v, a): v = the value of a represented by the type of v *)
  | Icast of var * atomic
  (* Ivpc (v, a): v = a, value preserved casting *)
  | Ivpc of var * atomic
  (* Ijoin (v, ah, al): v = ah * 2^w + al where w is the bit-width of al *)
  | Ijoin of var * atomic * atomic
  (* Specifications *)
  | Iassert of bexp
  | Iassume of bexp
  | Iecut of ebexp * seq prove_with_spec
  | Ircut of rbexp * seq prove_with_spec
  | Ighost of VS.t * bexp.

  Record program := { pinputs : TypEnv.t;
                      pbody : seq instr }.



  (* Specifications *)

  Record spec : Type :=
    { spre : bexp;
      sprog : program;
      spost : bexp;
      sepwss : seq prove_with_spec;
      srpwss : seq prove_with_spec }.

  Record espec :=
    { espre : ebexp;
      esprog : program;
      espost : ebexp;
      espwss : seq prove_with_spec }.

  Record rspec :=
    { rspre : rbexp;
      rsprog : program;
      rspost : rbexp;
      rspwss : seq prove_with_spec }.

  Coercion espec_of_spec s :=
    {| espre := eqn_bexp (spre s);
       esprog := sprog s;
       espost := eqn_bexp (spost s);
       espwss := sepwss s |}.

  Coercion rspec_of_spec s :=
    {| rspre := rng_bexp (spre s);
       rsprog := sprog s;
       rspost := rng_bexp (spost s);
       rspwss := srpwss s |}.

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
    | Rslt => false (* TODO: Add correct semantics *)
    | Rsle => false (* TODO: Add correct semantics *)
    | Rsgt => false (* TODO: Add correct semantics *)
    | Rsge => false (* TODO: Add correct semantics *)
    end.

  Fixpoint eval_eexp (e : eexp) (te : TypEnv.t) (s : Store.t) : Z :=
    match e with
    | Evar v => match TypEnv.find v te with
                | Tuint _ => to_Zpos (Store.acc v s)
                | Tsint _ => to_Z (Store.acc v s)
                end
    | Econst n => n
    | Eunop op e => eval_eunop op (eval_eexp e te s)
    | Ebinop op e1 e2 => eval_ebinop op (eval_eexp e1 te s) (eval_eexp e2 te s)
    end.

  Fixpoint eval_rexp (e : rexp) (te : TypEnv.t) (s : Store.t) : bits :=
    match e with
    | Rvar v => Store.acc v s
    | Rconst w n => n
    | Runop _ op e => eval_runop op (eval_rexp e te s)
    | Rbinop _ op e1 e2 => eval_rbinop op (eval_rexp e1 te s) (eval_rexp e2 te s)
    | Ruext _ e i => zext i (eval_rexp e te s)
    | Rsext _ e i => sext i (eval_rexp e te s)
    end.

  Fixpoint eval_ebexp (e : ebexp) (te : TypEnv.t) (s : Store.t) : Prop :=
    match e with
    | Etrue => True
    | Eeq e1 e2 => eval_eexp e1 te s = eval_eexp e2 te s
    | Eeqmod e1 e2 p =>
      modulo (eval_eexp e1 te s) (eval_eexp e2 te s) (eval_eexp p te s)
    | Eand e1 e2 => eval_ebexp e1 te s /\ eval_ebexp e2 te s
    end.

  Fixpoint eval_rbexp (e : rbexp) (te : TypEnv.t) (s : Store.t) : Prop :=
    match e with
    | Rtrue => True
    | Req _ e1 e2 => eval_rexp e1 te s = eval_rexp e2 te s
    | Rcmp _ op e1 e2 => eval_rcmpop op (eval_rexp e1 te s) (eval_rexp e2 te s)
    | Rneg e => ~ (eval_rbexp e te s)
    | Rand e1 e2 => eval_rbexp e1 te s /\ eval_rbexp e2 te s
    | Ror e1 e2 => eval_rbexp e1 te s \/ eval_rbexp e2 te s
    end.

  Definition eval_bexp (e : bexp) (te : TypEnv.t) (s : Store.t) : Prop :=
    eval_ebexp (eqn_bexp e) te s /\ eval_rbexp (rng_bexp e) te s.

  Definition valid (e : bexp) (te : TypEnv.t) : Prop :=
    forall s : Store.t, conform s te -> eval_bexp e te s.

  Definition entails (f g : bexp) (te : TypEnv.t) : Prop :=
    forall s : Store.t, conform s te -> eval_bexp f te s -> eval_bexp g te s.

  Definition eval_atomic (a : atomic) (te : TypEnv.t) (s : Store.t) : bits :=
    match a with
    | Avar v => Store.acc v s
    | Aconst _ n => n
    end.

  (* Note: the correctness relies on well-formedness of instr *)
  Definition instr_typenv (i : instr) (te : TypEnv.t) : TypEnv.t :=
    match i with
    | Imov (v, a) => TypEnv.add v (atyp a te) te
    | Ishl (v, a, _) => TypEnv.add v (atyp a te) te
    | Icshl (v1, v2, a1, a2, _) =>
      TypEnv.add v1 (atyp a1 te) (TypEnv.add v2 (atyp a2 te) te)
    | Inondet v => te
    | Icmov (v, c, a1, a2) => TypEnv.add v (atyp a1 te) te
    | Inop => te
    | _ => te (* TODO: Correct this *)
    end.

  (* TODO: Finish this *)
  Inductive eval_instr (te : TypEnv.t) : instr -> state -> state -> Prop :=
  | Eerr i : eval_instr te i ERR ERR
  | Emov v a s t :
      Store.Upd v (eval_atomic a te s) s t ->
      eval_instr te (Imov (v, a)) (OK s) (OK t)
  | Eshl v a i s t :
      Store.Upd v (shlB i (eval_atomic a te s)) s t ->
      eval_instr te (Ishl (v, a, i)) (OK s) (OK t)
  | Enondet v s t n :
      size n = size (Store.acc v s) ->
      Store.Upd v n s t ->
      eval_instr te (Inondet v) (OK s) (OK t)
  | Eassume e s :
      eval_bexp e te s -> eval_instr te (Iassume e) (OK s) (OK s)
  | EassertOK e s :
      eval_bexp e te s -> eval_instr te (Iassert e) (OK s) (OK s)
  | EassertERR e s :
      ~ eval_bexp e te s -> eval_instr te (Iassert e) (OK s) ERR
  .

  Inductive eval_instrs (te : TypEnv.t) : seq instr -> state -> state -> Prop :=
  | Enil s : eval_instrs te [::] s s
  | Econs hd tl s t u : eval_instr te hd s t ->
                  eval_instrs (instr_typenv hd te) tl t u ->
                  eval_instrs te (hd::tl) s u.

  Definition eval_program p s t : Prop := eval_instrs (pinputs p) (pbody p) s t.

  (* TODO: Define well-formedness *)

End Cryptoline.

