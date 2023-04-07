
(** * Common operators and expressions for DSL *)

From Coq Require Import Ascii ZArith String.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ.
From ssrlib Require Import ZAriths Strings.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Declare Scope dsl.
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

  Definition string_of_eunop op :=
    match op with
    | Eneg => "-"%string
    end.

  Definition string_of_ebinop op :=
    match op with
    | Eadd => "+"%string
    | Esub => "-"%string
    | Emul => "*"%string
    end.

  Definition string_of_runop op :=
    match op with
    | Rnegb => "-"%string
    | Rnotb => "!"%string
    end.

  Definition string_of_rbinop op :=
    match op with
    | Radd => "+"%string
    | Rsub => "-"%string
    | Rmul => "*"%string
    | Rumod => "umod"%string
    | Rsrem => "srem"%string
    | Rsmod => "smod"%string
    | Randb => "&"%string
    | Rorb => "|"%string
    | Rxorb => "xor"%string
    end.

  Definition string_of_rcmpop op :=
    match op with
    | Rult => "<u"%string
    | Rule => "<=u"%string
    | Rugt => ">u"%string
    | Ruge => ">=u"%string
    | Rslt => "<s"%string
    | Rsle => "<=s"%string
    | Rsgt => ">s"%string
    | Rsge => ">=s"%string
    end.

End Operators.


Section DSLRaw.

  Variable var : eqType.

  Inductive eexp : Type :=
  | Evar : var -> eexp
  | Econst : Z -> eexp
  | Eunop : eunop -> eexp -> eexp
  | Ebinop : ebinop -> eexp -> eexp -> eexp
  | Epow : eexp -> N -> eexp.

  Definition evar v := Evar v.
  Definition econst n := Econst n.
  Definition eunary op e := Eunop op e.
  Definition ebinary op e1 e2 := Ebinop op e1 e2.
  Definition eneg e := Eunop Eneg e.
  Definition eadd e1 e2 := Ebinop Eadd e1 e2.
  Definition esub e1 e2 := Ebinop Esub e1 e2.
  Definition emul e1 e2 := Ebinop Emul e1 e2.
  Definition esq e := Ebinop Emul e e.
  Definition epow e n := Epow e n.

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
    | Epow e1 n1, Epow e2 n2 =>
        (eexp_eqn e1 e2) && (n1 == n2)
    | _, _ => false
    end.

  Lemma eexp_eqn_eq (e1 e2 : eexp) : eexp_eqn e1 e2 -> e1 = e2.
  Proof.
    elim: e1 e2 => [v1 | n1 | op1 e1 IH1 | op1 e1 IH1 e2 IH2 | e1 IH1 n1] [] //=.
    - by move=> ? /eqP ->.
    - by move=> ? /eqP ->.
    - by move=> ? ? /andP [/eqP -> H]; rewrite (IH1 _ H).
    - by move=> ? ? ? /andP [/andP [/eqP -> H1] H2]; rewrite (IH1 _ H1) (IH2 _ H2).
    - by move=> ? ? /andP [H1 /eqP ->]; rewrite (IH1 _ H1).
  Qed.

  Lemma eexp_eqn_refl (e : eexp) : eexp_eqn e e.
  Proof.
    elim: e => //=.
    - by move=> ? ? ->; rewrite eqxx.
    - by move=> ? ? -> ? ->; rewrite eqxx.
    - by move=> ? -> ?; rewrite eqxx.
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
  | Eeqmod : eexp -> eexp -> seq eexp -> ebexp
  | Eand : ebexp -> ebexp -> ebexp.

  Definition etrue := Etrue.
  Definition eeq e1 e2 := Eeq e1 e2.
  Definition eeqmod e1 e2 ms := Eeqmod e1 e2 ms.
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
    | Eeqmod e1 e2 ms1, Eeqmod e3 e4 ms2 => (e1 == e3) && (e2 == e4) && (ms1 == ms2)
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

  Fixpoint split_rand (e : rbexp) : seq rbexp :=
    match e with
    | Rand e1 e2 => (split_rand e1) ++ (split_rand e2)
    | _ => [:: e]
    end.

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


  (* Atoms *)

  Inductive atom : Type :=
  | Avar : var -> atom
  | Aconst : typ -> bits -> atom.

  Definition atom_eqn (a1 a2 : atom) : bool :=
    match a1, a2 with
    | Avar v1, Avar v2 => v1 == v2
    | Aconst ty1 n1, Aconst ty2 n2 => (ty1 == ty2) && (n1 == n2)
    | _, _ => false
    end.

  Lemma atom_eqn_eq a1 a2 : atom_eqn a1 a2 <-> a1 = a2.
  Proof.
    split; case: a1; case: a2 => //=.
    - move=> ? ? /eqP ->. reflexivity.
    - move=> ? ? ? ? /andP [/eqP -> /eqP] ->. reflexivity.
    - move=> ? ? [] ->. exact: eqxx.
    - move=> ? ? ? ? [] -> ->. by rewrite !eqxx.
  Qed.

  Lemma atom_eqP (a1 a2 : atom) : reflect (a1 = a2) (atom_eqn a1 a2).
  Proof.
    case H: (atom_eqn a1 a2).
    - apply: ReflectT. apply/atom_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/atom_eqn_eq.
      assumption.
  Qed.

  Definition atom_eqMixin := EqMixin atom_eqP.
  Canonical atom_eqType := Eval hnf in EqType atom atom_eqMixin.


  (* String outputs *)

  Variable string_of_var : var -> string.

  Definition is_eexp_atomic (e : eexp) : bool :=
    match e with
    | Evar _ | Econst _ => true
    | _ => false
    end.

  Fixpoint string_of_eexp (e : eexp) : string :=
    match e with
    | Evar v => string_of_var v
    | Econst n => string_of_Z n
    | Eunop op e =>
        (string_of_eunop op ++ " " ++ string_of_eexp' e)%string
    | Ebinop op e1 e2 =>
        (string_of_eexp' e1 ++ " " ++ string_of_ebinop op ++ " " ++ string_of_eexp' e2)%string
    | Epow e n => (string_of_eexp' e ++ " ^ " ++ string_of_N n)%string
    end
  with
  string_of_eexp' (e : eexp) : string :=
    match e with
    | Evar v => string_of_var v
    | Econst n => string_of_Z n
    | Eunop op e =>
        ("(" ++ string_of_eunop op ++ " " ++ string_of_eexp e ++ ")")%string
    | Ebinop op e1 e2 =>
        ("(" ++ string_of_eexp e1 ++ " " ++ string_of_ebinop op ++ " "
             ++ string_of_eexp e2 ++ ")")%string
    | Epow e n => ("(" ++ string_of_eexp e ++ " ^ " ++ string_of_N n ++ ")")%string
    end
    .

    Fixpoint string_of_eexps glue (es : list eexp) : string :=
      match es with
      | [::] => ""%string
      | hd::tl => (string_of_eexp hd ++ glue ++ string_of_eexps glue tl)%string
      end.

    Fixpoint string_of_ebexp (e : ebexp) : string :=
      match e with
      | Etrue => "true"
      | Eeq e1 e2 => (string_of_eexp e1 ++ " = " ++ string_of_eexp e2)%string
      | Eeqmod e1 e2 ms =>
          (string_of_eexp e1 ++ " = " ++ string_of_eexp e2
                          ++ "(mod [" ++ string_of_eexps ", " ms ++ "])")%string
      | Eand e1 e2 => (string_of_ebexp e1 ++ " /\ " ++ string_of_ebexp e2)%string
      end.

    Definition is_rexp_atomic (e : rexp) : bool :=
      match e with
      | Rvar _ | Rconst _ _ => true
      | _ => false
      end.

    Fixpoint string_of_rexp (e : rexp) : string :=
      match e with
      | Rvar v => string_of_var v
      | Rconst w bs => to_hex bs ++ "@" ++ string_of_nat w
      | Runop w op e => (string_of_runop op ++ " " ++ string_of_rexp' e)%string
      | Rbinop w op e1 e2 =>
          (string_of_rexp' e1 ++ " " ++ string_of_rbinop op
                           ++ " " ++ string_of_rexp' e2)%string
      | Ruext w e i => ("uext " ++ string_of_rexp' e ++ " " ++ string_of_nat i)%string
      | Rsext w e i => ("sext " ++ string_of_rexp' e ++ " " ++ string_of_nat i)%string
      end
    with
    string_of_rexp' (e : rexp) : string :=
      match e with
      | Rvar v => string_of_var v
      | Rconst w bs => to_hex bs
      | Runop w op e => ("(" ++ string_of_runop op ++ " " ++ string_of_rexp e ++ ")")%string
      | Rbinop w op e1 e2 =>
          ("(" ++ string_of_rexp e1 ++ " " ++ string_of_rbinop op
               ++ " " ++ string_of_rexp' e2 ++ ")")%string
      | Ruext w e i => ("(uext " ++ string_of_rexp e ++ " " ++ string_of_nat i ++ ")")%string
      | Rsext w e i => ("(sext " ++ string_of_rexp e ++ " " ++ string_of_nat i ++ ")")%string
      end.

    Definition is_rbexp_or (e : rbexp) : bool :=
      match e with
      | Ror _ _ => true
      | _ => false
      end.

    Fixpoint string_of_rbexp (e : rbexp) : string :=
      match e with
      | Rtrue => "true"
      | Req w e1 e2 => (string_of_rexp e1 ++ " = " ++ string_of_rexp e2)%string
      | Rcmp w op e1 e2 =>
          (string_of_rexp e1 ++ " " ++ string_of_rcmpop op ++ " " ++ string_of_rexp e2)%string
      | Rneg e => ("~ " ++ string_of_rbexp e)%string
      | Rand e1 e2 =>
          (if is_rbexp_or e1 then "(" ++ string_of_rbexp e1 ++ ")"
           else string_of_rbexp e1)%string
                                   ++ " /\ "
                                   ++ (if is_rbexp_or e2 then "(" ++ string_of_rbexp e2 ++ ")"
                                       else string_of_rbexp e2)%string
      | Ror e1 e2 => (string_of_rbexp e1 ++ " \/ " ++ string_of_rbexp e2)%string
      end.

    Definition string_of_typ (t : typ) : string :=
      match t with
      | Tuint n => "uint" ++ string_of_nat n
      | Tsint n => "sint" ++ string_of_nat n
      end.

    Definition string_of_atom (a : atom) : string :=
      match a with
      | Avar v => string_of_var v
      | Aconst ty n => to_hex n ++ "@" ++ string_of_typ ty
    end.

End DSLRaw.

Arguments Aconst [var].
