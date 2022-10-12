
(** Typed CryptoLine. *)

From Coq Require Import List Ascii ZArith OrderedType String Decimal DecimalString.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State BBCommon.
From ssrlib Require Import Var SsrOrder ZAriths Store FSets FMaps Tactics Seqs Nats.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope dsl with dsl.


Section DecimalStringConversions.

  (*
    Decimal.int is renamed to Decimal.signed_int to avoid name clashes since 8.16.0.
    Do not use Decimal.int or any function involving Decimal.int to avoid name clashes.
    See https://github.com/coq/coq/issues/7017.
   *)

  Local Open Scope string_scope.

  Definition newline := String (Ascii.ascii_of_N 10) EmptyString.

  Variant signed_int := Pos (d : uint) | Neg (d : uint).

  Definition nat_to_signed_int (n : nat) : signed_int := Pos (Nat.to_uint n).

  Definition positive_to_signed_int (n : positive) : signed_int := Pos (Pos.to_uint n).

  Definition N_to_signed_int (n : N) : signed_int := Pos (N.to_uint n).

  Definition Z_to_signed_int (n : Z) : signed_int :=
    match n with
    | Z0 => Pos (Nat.to_uint O)
    | Zpos m => Pos (Pos.to_uint m)
    | Zneg m => Neg (Pos.to_uint m)
    end.

  Definition string_of_signed_int (d : signed_int) :=
    match d with
    | Pos d => NilEmpty.string_of_uint d
    | Neg d => String.String "-" (NilEmpty.string_of_uint d)
    end.

  Definition string_of_nat (n : nat) : string :=
    string_of_signed_int (nat_to_signed_int n).

  Definition string_of_positive (n : positive) : string :=
    string_of_signed_int (positive_to_signed_int n).

  Definition string_of_N (n : N) : string :=
    string_of_signed_int (N_to_signed_int n).

  Definition string_of_Z (n : Z) : string :=
    string_of_signed_int (Z_to_signed_int n).

End DecimalStringConversions.


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
        ("(" ++ string_of_eunop op ++ " " ++ string_of_eexp' e ++ ")")%string
    | Ebinop op e1 e2 =>
        ("(" ++ string_of_eexp' e1 ++ " " ++ string_of_ebinop op ++ " "
             ++ string_of_eexp' e2 ++ ")")%string
    | Epow e n => ("(" ++ string_of_eexp' e ++ " ^ " ++ string_of_N n ++ ")")%string
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
      | Runop w op e => ("(" ++ string_of_runop op ++ " " ++ string_of_rexp' e ++ ")")%string
      | Rbinop w op e1 e2 =>
          ("(" ++ string_of_rexp' e1 ++ " " ++ string_of_rbinop op
               ++ " " ++ string_of_rexp' e2 ++ ")")%string
      | Ruext w e i => ("(uext " ++ string_of_rexp' e ++ " " ++ string_of_nat i ++ ")")%string
      | Rsext w e i => ("(sext " ++ string_of_rexp' e ++ " " ++ string_of_nat i ++ ")")%string
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

End DSLRaw.



Module Type Printer.
  Variable t : Type.
  Variable to_string : t -> string.
End Printer.

Module MakeDSL
       (V : SsrOrder)
       (VP : Printer with Definition t := V.t)
       (VS : SsrFSet with Module SE := V)
       (VM : SsrFMap with Module SE := V)
       (TE : TypEnv with Module SE := V with Definition t := VM.t)
       (S : BitsStore V TE).
  Local Open Scope dsl.
  Local Open Scope bits.

  Module VSLemmas := SsrFSetLemmas VS.
  Module TELemmas := FMapLemmas TE.
  Hint Immediate S.Upd_upd S.Upd2_upd2 : dsl.

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
  Definition epow (e : eexp) (n : N) := @Epow V.T e n.

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
    | Epow e _ => vars_eexp e
    end.

  Fixpoint vars_eexps (es : seq eexp) : VS.t :=
    match es with
    | [::] => VS.empty
    | e::es => VS.union (vars_eexp e) (vars_eexps es)
    end.

  Definition eexp_eqP (e1 e2 : eexp) : reflect (e1 = e2) (eexp_eqn e1 e2) :=
    eexp_eqP e1 e2.

  Definition eexp_eqMixin := EqMixin eexp_eqP.
  Canonical eexp_eqType := Eval hnf in EqType eexp eexp_eqMixin.
  Definition eexp_eqn := @eexp_eqn V.T.


  (* Limbs *)

  Definition limbsi (i : nat) (r : Z) (es : seq eexp) : eexp := limbsi i r es.
  Definition limbs (r : Z) (es : seq eexp) : eexp := limbsi 0 r es.



  (* Range Expressions *)

  Definition rexp := rexp V.T.

  Definition size_of_rexp (e : rexp) (te : TE.env) : nat :=
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

  Definition rexp_eqP (e1 e2 : rexp) : reflect (e1 = e2) (rexp_eqn e1 e2) :=
    rexp_eqP e1 e2.

  Definition rexp_eqMixin := EqMixin rexp_eqP.
  Canonical rexp_eqType := Eval hnf in EqType rexp rexp_eqMixin.
  Definition rexp_eqn := @rexp_eqn V.T.



  (* Algebraic Predicates *)

  Definition ebexp : Type := ebexp V.T.

  Definition etrue : ebexp := @Etrue V.T.
  Definition eeq (e1 e2 : eexp) : ebexp := @Eeq V.T e1 e2.
  Definition eeqmod (e1 e2 : eexp) (ms : seq eexp) : ebexp := @Eeqmod V.T e1 e2 ms.
  Definition eand (b1 b2 : ebexp) : ebexp := @Eand V.T b1 b2.

  Definition eands (es : seq ebexp) : ebexp := @eands V.T es.

  Definition split_eand (e : ebexp) : seq ebexp := @split_eand V.T e.

  Fixpoint vars_ebexp (e : ebexp) : VS.t :=
    match e with
    | Etrue => VS.empty
    | Eeq e1 e2 => VS.union (vars_eexp e1) (vars_eexp e2)
    | Eeqmod e1 e2 ms =>
      VS.union (vars_eexp e1) (VS.union (vars_eexp e2) (vars_eexps ms))
    | Eand e1 e2 => VS.union (vars_ebexp e1) (vars_ebexp e2)
    end.

  Definition ebexp_eqP (e1 e2 : ebexp) : reflect (e1 = e2) (ebexp_eqn e1 e2) :=
    ebexp_eqP e1 e2.

  Definition ebexp_eqMixin := EqMixin ebexp_eqP.
  Canonical ebexp_eqType := Eval hnf in EqType ebexp ebexp_eqMixin.
  Definition ebexp_eqn := @ebexp_eqn V.T.

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

  Definition rbexp_eqP (e1 e2 : rbexp) : reflect (e1 = e2) (rbexp_eqn e1 e2) :=
    rbexp_eqP e1 e2.

  Definition rbexp_eqMixin := EqMixin rbexp_eqP.
  Canonical rbexp_eqType := Eval hnf in EqType rbexp rbexp_eqMixin.
  Definition rbexp_eqn := @rbexp_eqn V.T.


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

  Inductive atom : Type :=
  | Avar : var -> atom
  | Aconst : typ -> bits -> atom.

  Definition atyp (a : atom) (te : TE.env) : typ :=
    match a with
    | Avar v => TE.vtyp v te
    | Aconst ty _ => ty
    end.

  Definition asize (a : atom) (te : TE.env) : nat := sizeof_typ (atyp a te).

  Inductive instr : Type :=
  (* Imov (v, a): v = a *)
  | Imov : var -> atom -> instr
  (* Ishl (v, a, n): v = a * 2^n, overflow is forbidden *)
  | Ishl : var -> atom -> nat -> instr
  (* Icshl (vh, vl, a1, a2, n) *)
  | Icshl : var -> var -> atom -> atom -> nat -> instr
  (* Inondet (v, t): v = a nondeterministic value of type t *)
  | Inondet : var -> typ -> instr
  (* Icmov (v, c, a1, a2): if c then v = a1 else v = a2 *)
  | Icmov : var -> atom -> atom -> atom -> instr
  (* Inop: do nothing *)
  | Inop : instr
  (* Inot (v, t, a): v = not(a), the one's complement of a, v is of type t *)
  | Inot : var -> typ -> atom -> instr
  (* Iadd (v, a1, a2): v = a1 + a2, overflow is forbidden *)
  | Iadd : var -> atom -> atom -> instr
  (* Iadds (c, v, a1, a2): v = a1 + a2, c = carry flag *)
  | Iadds : var -> var -> atom -> atom -> instr
  (* Iadc (v, a1, a2, y): v = a1 + a2 + y, overflow is forbidden *)
  | Iadc : var -> atom -> atom -> atom -> instr
  (* Iadcs (c, v, a1, a2, y): v = a1 + a2 + y, c = carry flag *)
  | Iadcs : var -> var -> atom -> atom -> atom -> instr
  (* Isub (v, a1, a2): v = a1 - a2, overflow is forbidden *)
  | Isub : var -> atom -> atom -> instr
  (* Isubc (c, v, a1, a2): v = a1 + not(a2) + 1, c = carry flag *)
  | Isubc : var -> var -> atom -> atom -> instr
  (* Isous (b, v, a1, a2): v = a1 - a2, b = borrow flag *)
  | Isubb : var -> var -> atom -> atom -> instr
  (* Isbc (v, a1, a2, y): v = a1 + not(a2) + y *)
  | Isbc : var -> atom -> atom -> atom -> instr
  (* Isbcs (c, v, a1, a2, y): v = a1 + not(a2) + y, c = carry flag *)
  | Isbcs : var -> var -> atom -> atom -> atom -> instr
  (* Isbb (v, a1, a2, y): v = a1 - a2 - y *)
  | Isbb : var -> atom -> atom -> atom -> instr
  (* Isbbs (b, v, a1, a2, y): v = a1 - a2 - y, b = borrow flag *)
  | Isbbs : var -> var -> atom -> atom -> atom -> instr
  (* Imul (v, a1, a2): v = a1 * a2, overflow is forbidden *)
  | Imul : var -> atom -> atom -> instr
  (* Imull (vh, vl, a1, a2): vh and vl are respectively the high part and
     the low part of the full multiplication a1 * a2 *)
  | Imull : var -> var -> atom -> atom -> instr
  (* Iumulj (v, a1, a2): v = the full multiplication of a1 * a2, which is equivalent
     to Iumull (vh, vl, a1, a2); Join (r, vh, vl) *)
  | Imulj : var -> atom -> atom -> instr
  (* Isplit (vh, vl, a, n): vh is the high (w - n) bits (signed extended to w bits)
     of a and vl is the low n bits (zero extended to w bits) of a where w is the
     bit-width of a *)
  | Isplit : var -> var -> atom -> nat -> instr
  (* == Instructions that cannot be translated to polynomials == *)
  (* Iand (v, t, a1, a2): v = the bitwise AND of a1 and a2, v is of type t *)
  | Iand : var -> typ -> atom -> atom -> instr
  (* Ior (v, t, a1, a2): v = the bitwise OR of a1 and a2, v is of type t *)
  | Ior : var -> typ -> atom -> atom -> instr
  (* Ixor (v, t, a1, a2): v = the bitwise XOR of a1 and a2, v is of type t *)
  | Ixor : var -> typ -> atom -> atom -> instr
  (* == Type conversions == *)
  (* Icast (v, t, a): v = the value of a represented by the type t of v *)
  | Icast : var -> typ -> atom -> instr
  (* Ivpc (v, t, a): v = a, value preserved casting to type t *)
  | Ivpc : var -> typ -> atom -> instr
  (* Ijoin (v, ah, al): v = ah * 2^w + al where w is the bit-width of al *)
  | Ijoin : var -> atom -> atom -> instr
  (* Specifications *)
  | Iassume : bexp -> instr.

  Definition program := seq instr.


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

  Definition instr_eqn (i1 i2 : instr) : bool :=
    match i1, i2 with
    | Imov a1 a2, Imov b1 b2 => (a1 == b1) && (a2 == b2)
    | Ishl a1 a2 a3, Ishl b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Icshl a1 a2 a3 a4 a5, Icshl b1 b2 b3 b4 b5 =>
        (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4) && (a5 == b5)
    | Inondet a1 a2, Inondet b1 b2 => (a1 == b1) && (a2 == b2)
    | Icmov a1 a2 a3 a4, Icmov b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Inop, Inop => true
    | Inot a1 a2 a3, Inot b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Iadd a1 a2 a3, Iadd b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Iadds a1 a2 a3 a4, Iadds b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Iadc a1 a2 a3 a4, Iadc b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Iadcs a1 a2 a3 a4 a5, Iadcs b1 b2 b3 b4 b5 =>
        (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4) && (a5 == b5)
    | Isub a1 a2 a3, Isub b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Isubc a1 a2 a3 a4, Isubc b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Isubb a1 a2 a3 a4, Isubb b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Isbc a1 a2 a3 a4, Isbc b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Isbcs a1 a2 a3 a4 a5, Isbcs b1 b2 b3 b4 b5 =>
        (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4) && (a5 == b5)
    | Isbb a1 a2 a3 a4, Isbb b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Isbbs a1 a2 a3 a4 a5, Isbbs b1 b2 b3 b4 b5 =>
        (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4) && (a5 == b5)
    | Imul a1 a2 a3, Imul b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Imull a1 a2 a3 a4, Imull b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Imulj a1 a2 a3, Imulj b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Isplit a1 a2 a3 a4, Isplit b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Iand a1 a2 a3 a4, Iand b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Ior a1 a2 a3 a4, Ior b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Ixor a1 a2 a3 a4, Ixor b1 b2 b3 b4 => (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)
    | Icast a1 a2 a3, Icast b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Ivpc a1 a2 a3, Ivpc b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Ijoin a1 a2 a3, Ijoin b1 b2 b3 => (a1 == b1) && (a2 == b2) && (a3 == b3)
    | Iassume a1, Iassume b1 => (a1 == b1)
    | _, _ => false
    end.

  Lemma instr_eqn_eq i1 i2 : instr_eqn i1 i2 <-> i1 = i2.
  Proof.
    split; (case: i1; case: i2 => //=); intros; by t_auto.
  Qed.

  Lemma instr_eqP (i1 i2 : instr) : reflect (i1 = i2) (instr_eqn i1 i2).
  Proof.
    case H: (instr_eqn i1 i2).
    - apply: ReflectT. apply/instr_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/instr_eqn_eq.
      assumption.
  Qed.

  Definition instr_eqMixin := EqMixin instr_eqP.
  Canonical instr_eqType := Eval hnf in EqType instr instr_eqMixin.


  (** Variables in programs *)

  Definition vars_atom (a : atom) : VS.t :=
    match a with
    | Avar v => VS.singleton v
    | Aconst _ _ => VS.empty
    end.

  Definition vars_instr (i : instr) : VS.t :=
    match i with
    | Imov v a
    | Ishl v a _ => VS.add v (vars_atom a)
    | Icshl vh vl a1 a2 _ =>
      VS.add vh (VS.add vl (VS.union (vars_atom a1) (vars_atom a2)))
    | Inondet v _ => VS.singleton v
    | Icmov v c a1 a2 =>
      VS.add v (VS.union (vars_atom c)
                         (VS.union (vars_atom a1) (vars_atom a2)))
    | Inop => VS.empty
    | Inot v _ a => VS.add v (vars_atom a)
    | Iadd v a1 a2 => VS.add v (VS.union (vars_atom a1) (vars_atom a2))
    | Iadds c v a1 a2 =>
      VS.add c (VS.add v (VS.union (vars_atom a1) (vars_atom a2)))
    | Iadc v a1 a2 y =>
      VS.add v (VS.union (vars_atom a1)
                         (VS.union (vars_atom a2) (vars_atom y)))
    | Iadcs c v a1 a2 y =>
      VS.add c (VS.add v (VS.union (vars_atom a1)
                                   (VS.union (vars_atom a2) (vars_atom y))))
    | Isub v a1 a2 => VS.add v (VS.union (vars_atom a1) (vars_atom a2))
    | Isubc c v a1 a2
    | Isubb c v a1 a2 =>
      VS.add c (VS.add v (VS.union (vars_atom a1) (vars_atom a2)))
    | Isbc v a1 a2 y =>
      VS.add v (VS.union (vars_atom a1)
                         (VS.union (vars_atom a2) (vars_atom y)))
    | Isbcs c v a1 a2 y =>
      VS.add c (VS.add v (VS.union (vars_atom a1)
                                   (VS.union (vars_atom a2) (vars_atom y))))
    | Isbb v a1 a2 y =>
      VS.add v (VS.union (vars_atom a1)
                         (VS.union (vars_atom a2) (vars_atom y)))
    | Isbbs c v a1 a2 y =>
      VS.add c (VS.add v (VS.union (vars_atom a1)
                                   (VS.union (vars_atom a2) (vars_atom y))))
    | Imul v a1 a2 => VS.add v (VS.union (vars_atom a1) (vars_atom a2))
    | Imull vh vl a1 a2 =>
      VS.add vh (VS.add vl (VS.union (vars_atom a1) (vars_atom a2)))
    | Imulj v a1 a2 => VS.add v (VS.union (vars_atom a1) (vars_atom a2))
    | Isplit vh vl a n => VS.add vh (VS.add vl (vars_atom a))
    | Iand v _ a1 a2
    | Ior v _ a1 a2
    | Ixor v _ a1 a2 => VS.add v (VS.union (vars_atom a1) (vars_atom a2))
    | Icast v t a
    | Ivpc v t a => VS.add v (vars_atom a)
    | Ijoin v ah al => VS.add v (VS.union (vars_atom ah) (vars_atom al))
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
    | Ishl _ a _ => vars_atom a
    | Icshl _ _ a1 a2 _ => VS.union (vars_atom a1) (vars_atom a2)
    | Inondet _ _ => VS.empty
    | Icmov _ c a1 a2 => VS.union (vars_atom c)
                                  (VS.union (vars_atom a1) (vars_atom a2))
    | Inop => VS.empty
    | Inot _ _ a => vars_atom a
    | Iadd _ a1 a2
    | Iadds _ _ a1 a2 => VS.union (vars_atom a1) (vars_atom a2)
    | Iadc _ a1 a2 y
    | Iadcs _ _ a1 a2 y => VS.union (vars_atom a1)
                                    (VS.union (vars_atom a2) (vars_atom y))
    | Isub _ a1 a2
    | Isubc _ _ a1 a2
    | Isubb _ _ a1 a2 => VS.union (vars_atom a1) (vars_atom a2)
    | Isbc _ a1 a2 y
    | Isbcs _ _ a1 a2 y
    | Isbb _ a1 a2 y
    | Isbbs _ _ a1 a2 y => VS.union (vars_atom a1)
                                    (VS.union (vars_atom a2) (vars_atom y))
    | Imul _ a1 a2
    | Imull _ _ a1 a2
    | Imulj _ a1 a2 => VS.union (vars_atom a1) (vars_atom a2)
    | Isplit _ _ a _ => vars_atom a
    | Iand _ _ a1 a2
    | Ior _ _ a1 a2
    | Ixor _ _ a1 a2 => VS.union (vars_atom a1) (vars_atom a2)
    | Icast _ _ a
    | Ivpc _ _ a => vars_atom a
    | Ijoin _ ah al => VS.union (vars_atom ah) (vars_atom al)
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

  Lemma vars_program_cat p1 p2 :
    VS.Equal (vars_program (p1 ++ p2)) (VS.union (vars_program p1) (vars_program p2)).
  Proof.
    elim: p1 p2 => [| hd tl IH] p2 /=.
    - rewrite VSLemmas.union_emptyl. reflexivity.
    - rewrite IH VSLemmas.OP.P.union_assoc. reflexivity.
  Qed.

  Lemma lvs_program_cat p1 p2 :
    VS.Equal (lvs_program (p1 ++ p2)) (VS.union (lvs_program p1) (lvs_program p2)).
  Proof.
    elim: p1 p2 => [| hd tl IH] p2 /=.
    - rewrite VSLemmas.union_emptyl. reflexivity.
    - rewrite IH VSLemmas.OP.P.union_assoc. reflexivity.
  Qed.

  Lemma vars_program_rcons p i :
    VS.Equal (vars_program (rcons p i)) (VS.union (vars_program p) (vars_instr i)).
  Proof.
    rewrite -cats1 vars_program_cat /=. rewrite VSLemmas.union_emptyr. reflexivity.
  Qed.

  Lemma lvs_program_rcons p i :
    VS.Equal (lvs_program (rcons p i)) (VS.union (lvs_program p) (lvs_instr i)).
  Proof.
    rewrite -cats1 lvs_program_cat /=. rewrite VSLemmas.union_emptyr. reflexivity.
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

  Lemma vars_eqn_bexp e : VS.subset (vars_ebexp (eqn_bexp e)) (vars_bexp e).
  Proof. case: e => [e r] //=. rewrite /vars_bexp /=. by VSLemmas.dp_subset. Qed.

  Lemma vars_rng_bexp e : VS.subset (vars_rbexp (rng_bexp e)) (vars_bexp e).
  Proof. case: e => [e r] //=. rewrite /vars_bexp /=. by VSLemmas.dp_subset. Qed.

  Lemma vars_eqn_instr i : VS.subset (vars_instr (eqn_instr i)) (vars_instr i).
  Proof.
    case: i => //=; intros; try VSLemmas.dp_subset. case: b => [e r] //=.
    rewrite /vars_bexp /=. by VSLemmas.dp_subset.
  Qed.

  Lemma vars_rng_instr i : VS.subset (vars_instr (rng_instr i)) (vars_instr i).
  Proof.
    case: i => //=; intros; try VSLemmas.dp_subset. case: b => [e r] //=.
    rewrite /vars_bexp /=. by VSLemmas.dp_subset.
  Qed.

  Lemma vars_eqn_program p : VS.subset (vars_program (eqn_program p)) (vars_program p).
  Proof.
    elim: p => [| i p IH] /=.
    - by VSLemmas.dp_subset.
    - move: (vars_eqn_instr i) => H. by VSLemmas.dp_subset.
  Qed.

  Lemma vars_rng_program p : VS.subset (vars_program (rng_program p)) (vars_program p).
  Proof.
    elim: p => [| i p IH] /=.
    - by VSLemmas.dp_subset.
    - move: (vars_rng_instr i) => H. by VSLemmas.dp_subset.
  Qed.


  (* Specifications *)

  Record spec : Type :=
    mkSpec { sinputs : TE.env;
             spre : bexp;
             sprog : program;
             spost : bexp }.

  Record espec :=
    mkEspec { esinputs : TE.env;
              espre : bexp;
              esprog : program;
              espost : ebexp }.

  Record rspec :=
    mkRspec { rsinputs : TE.env;
              rspre : rbexp;
              rsprog : program;
              rspost : rbexp }.

  (* The program is `sprog s` instead of `eqn_program (sprog s)` because we need
     to prove the following lemma:
       forall E p s :
         ssa_program_algsnd_at E p s ->
           ssa_program_algsnd_at E (eqn_program p) s.
     `eval_instr E i s1 s2` cannot be proved from `eval_instr E (rng_instr (eqn_instr i)) s1 s2`
   *)
  Coercion espec_of_spec s :=
    mkEspec (sinputs s) (spre s) (sprog s) (eqn_bexp (spost s)).

  Coercion rspec_of_spec s :=
    mkRspec (sinputs s) (rng_bexp (spre s)) (rng_program (sprog s)) (rng_bexp (spost s)).

  Definition vars_spec (s : spec) : VS.t :=
    VS.union
      (vars_bexp (spre s))
      (VS.union
         (vars_program (sprog s))
         (vars_bexp (spost s))).

  Definition vars_espec (s : espec) : VS.t :=
    VS.union
      (vars_bexp (espre s))
      (VS.union
         (vars_program (esprog s))
         (vars_ebexp (espost s))).

  Definition vars_rspec (s : rspec) : VS.t :=
    VS.union
      (vars_rbexp (rspre s))
      (VS.union
         (vars_program (rsprog s))
         (vars_rbexp (rspost s))).

  Lemma vars_espec_of_spec s :
    VS.subset (vars_espec (espec_of_spec s)) (vars_spec s).
  Proof.
    case: s => [E f p g]. rewrite /vars_spec /vars_espec /=. move: (vars_ebexp_subset g) => Hg.
    by VSLemmas.dp_subset.
  Qed.

  Lemma vars_rspec_of_spec s :
    VS.subset (vars_rspec (rspec_of_spec s)) (vars_spec s).
  Proof.
    case: s => [E f p g]. rewrite /vars_spec /vars_rspec /=.
    move: (vars_rbexp_subset f) (vars_rng_program p) (vars_rbexp_subset g) => Hf Hp Hg.
    by VSLemmas.dp_subset.
  Qed.


  (** String outputs *)

  Section StringOutputs.

    Local Open Scope string_scope.

    Definition string_of_eunop := @string_of_eunop.
    Definition string_of_ebinop := @string_of_ebinop.
    Definition string_of_runop := @string_of_runop.
    Definition string_of_rbinop := @string_of_rbinop.
    Definition string_of_rcmpop := @string_of_rcmpop.
    Definition string_of_eexp := @string_of_eexp V.T VP.to_string.
    Definition string_of_eexps := @string_of_eexps V.T VP.to_string.
    Definition string_of_ebexp := @string_of_ebexp V.T VP.to_string.
    Definition string_of_rexp := @string_of_rexp V.T VP.to_string.
    Definition string_of_rbexp := @string_of_rbexp V.T VP.to_string.
    Definition string_of_bexp e :=
      string_of_ebexp (eqn_bexp e) ++ " && " ++ string_of_rbexp (rng_bexp e).

    Definition string_of_typ (t : typ) : string :=
      match t with
      | Tuint n => "uint" ++ string_of_nat n
      | Tsint n => "sint" ++ string_of_nat n
      end.

    Definition string_of_var_with_typ (vt : var * typ) : string :=
      VP.to_string (fst vt) ++ "@" ++ string_of_typ (snd vt).

    Definition string_of_vars (vs : VS.t) :=
      (concat ", " (tmap VP.to_string (VS.elements vs)))%string.

    Definition string_of_atom (a : atom) : string :=
      match a with
      | Avar v => VP.to_string v
      | Aconst ty n => to_hex n ++ "@" ++ string_of_typ ty
    end.

    Definition string_of_instr (i : instr) : string :=
      match i with
      | Imov v a => "mov " ++ VP.to_string v ++ " " ++ string_of_atom a
      | Ishl v a _ => "shl " ++ VP.to_string v ++ " " ++ string_of_atom a
      | Icshl v1 v2 a1 a2 _ => "cshl " ++ VP.to_string v1 ++ " " ++ VP.to_string v2 ++ " "
                                       ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Inondet v t => "nondet " ++ VP.to_string v ++ "@" ++ string_of_typ t
      | Icmov v c a1 a2 => "cmov " ++ VP.to_string v ++ " " ++ string_of_atom c ++ " "
                                   ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Inop => "nop"
      | Inot v t a => "not " ++ string_of_var_with_typ (v, t) ++ " "
                             ++ string_of_atom a
      | Iadd v a1 a2 => "add " ++ VP.to_string v ++ " "
                               ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Iadds c v a1 a2 => "adds " ++ VP.to_string c ++ " " ++ VP.to_string v ++ " "
                                   ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Iadc v a1 a2 y => "adc " ++ VP.to_string v ++ " "
                                 ++ string_of_atom a1 ++ " " ++ string_of_atom a2 ++ " "
                                 ++ string_of_atom y
      | Iadcs c v a1 a2 y => "adcs " ++ VP.to_string c ++ " " ++ VP.to_string v ++ " "
                                     ++ string_of_atom a1 ++ " " ++ string_of_atom a2 ++ " "
                                     ++ string_of_atom y
      | Isub v a1 a2 => "sub " ++ VP.to_string v ++ " "
                               ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Isubc c v a1 a2 => "subc " ++ VP.to_string c ++ " " ++ VP.to_string v ++ " "
                                   ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Isubb c v a1 a2 => "subb " ++ VP.to_string c ++ " " ++ VP.to_string v ++ " "
                                   ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Isbc v a1 a2 y => "sbc " ++ VP.to_string v ++ " "
                                 ++ string_of_atom a1 ++ " " ++ string_of_atom a2 ++ " "
                                 ++ string_of_atom y
      | Isbcs c v a1 a2 y => "sbcs " ++ VP.to_string c ++ " " ++ VP.to_string v ++ " "
                                     ++ string_of_atom a1 ++ " " ++ string_of_atom a2 ++ " "
                                     ++ string_of_atom y
      | Isbb v a1 a2 y => "sbb " ++ VP.to_string v ++ " "
                                 ++ string_of_atom a1 ++ " " ++ string_of_atom a2 ++ " "
                                 ++ string_of_atom y
      | Isbbs c v a1 a2 y => "sbbs " ++ VP.to_string c ++ " " ++ VP.to_string v ++ " "
                                     ++ string_of_atom a1 ++ " " ++ string_of_atom a2 ++ " "
                                     ++ string_of_atom y
      | Imul v a1 a2 => "mul " ++ VP.to_string v ++ " "
                               ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Imull vh vl a1 a2 => "mull " ++ VP.to_string vh ++ " " ++ VP.to_string vl ++ " "
                                     ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Imulj v a1 a2 => "mulj " ++ VP.to_string v ++ " "
                                 ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Isplit vh vl a n => "split " ++ VP.to_string vh ++ " " ++ VP.to_string vl ++ " "
                                     ++ string_of_atom a ++ " " ++ string_of_nat n
      | Iand v t a1 a2 => "and " ++ string_of_var_with_typ (v, t) ++ " "
                                 ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Ior v t a1 a2 => "or " ++ string_of_var_with_typ (v, t) ++ " "
                               ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Ixor v t a1 a2 => "xor " ++ string_of_var_with_typ (v, t) ++ " "
                                 ++ string_of_atom a1 ++ " " ++ string_of_atom a2
      | Icast v t a => "cast " ++ VP.to_string v ++ "@" ++ string_of_typ t ++ " "
                               ++ string_of_atom a
      | Ivpc v t a => "vpc " ++ string_of_var_with_typ (v, t) ++ " "
                             ++ string_of_atom a
      | Ijoin v ah al => "join " ++ VP.to_string v ++ " "
                                 ++ string_of_atom ah ++ " " ++ string_of_atom al
      | Iassume e => "assume " ++ string_of_bexp e
      end.

    Definition string_of_instr' (i : instr) : string := string_of_instr i ++ ";".

    Definition string_of_program (p : program) : string :=
      concat newline (tmap string_of_instr' p).

    Definition string_of_typenv (E : TE.env) : string :=
      concat ", " (tmap string_of_var_with_typ (TE.elements E)).

    Definition string_of_spec (s : spec) : string :=
      "proc main(" ++ string_of_typenv (sinputs s) ++ ") =" ++ newline
                   ++ "{ " ++ string_of_bexp (spre s) ++ "}" ++ newline
                   ++ string_of_program (sprog s) ++ newline
                   ++ "{ " ++ string_of_bexp (spost s) ++ "}" ++ newline.

    Definition string_of_espec (s : espec) : string :=
      "proc main(" ++ string_of_typenv (esinputs s) ++ ") =" ++ newline
                   ++ "{ " ++ string_of_bexp (espre s) ++ "}" ++ newline
                   ++ string_of_program (esprog s) ++ newline
                   ++ "{ " ++ string_of_ebexp (espost s) ++ "}" ++ newline.

    Definition string_of_rspec (s : rspec) : string :=
      "proc main(" ++ string_of_typenv (rsinputs s) ++ ") = ++ newline"
                   ++ "{ " ++ string_of_rbexp (rspre s) ++ "}" ++ newline
                   ++ string_of_program (rsprog s) ++ newline
                   ++ "{ " ++ string_of_rbexp (rspost s) ++ "} ++ newline".

  End StringOutputs.


  (* Range programs *)

  Fixpoint is_rng_instr (i : instr) :=
    match i with
    | Iassume (e, r) => e == etrue
    | _ => true
    end.

  Definition is_rng_program (p : program) := all is_rng_instr p.

  Definition is_rng_rspec (s : rspec) := is_rng_program (rsprog s).

  Lemma rng_instr_is_rng_instr (i : instr) : is_rng_instr (rng_instr i).
  Proof. case: i => //=. by case=> [e r] //=. Qed.

  Lemma rng_program_is_rng_program (p : program) : is_rng_program (rng_program p).
  Proof. elim: p => [| i p IH] //=. by rewrite rng_instr_is_rng_instr IH. Qed.

  Lemma rspec_of_spec_is_rng_rspec s : is_rng_rspec (rspec_of_spec s).
  Proof. exact: rng_program_is_rng_program. Qed.

  Lemma is_rng_rspec_rprog E f p g :
    is_rng_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := g |} <->
      is_rng_program p.
  Proof. done. Qed.


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
    | Rumod => uremB v1 v2
    | Rsrem => sremB v1 v2
    | Rsmod => smodB v1 v2
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
    | Epow e n => Z.pow (eval_eexp e te s) (Z.of_N n)
    end.

  Definition eval_eexps (es : seq eexp) (te : TE.env) (s : S.t) : seq Z :=
    map (fun e => eval_eexp e te s) es.

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
    | Eeqmod e1 e2 ms =>
      zeqms (eval_eexp e1 te s) (eval_eexp e2 te s) (eval_eexps ms te s)
    | Eand e1 e2 => eval_ebexp e1 te s /\ eval_ebexp e2 te s
    end.

  Fixpoint eval_rbexp (e : rbexp) (s : S.t) : bool :=
    match e with
    | Rtrue => true
    | Req _ e1 e2 => eval_rexp e1 s == eval_rexp e2 s
    | Rcmp _ op e1 e2 => eval_rcmpop op (eval_rexp e1 s) (eval_rexp e2 s)
    | Rneg e => ~~ (eval_rbexp e s)
    | Rand e1 e2 => (eval_rbexp e1 s) && (eval_rbexp e2 s)
    | Ror e1 e2 => (eval_rbexp e1 s) || (eval_rbexp e2 s)
    end.

  Definition eval_bexp (e : bexp) (te : TE.env) (s : S.t) : Prop :=
    eval_ebexp (eqn_bexp e) te s /\ eval_rbexp (rng_bexp e) s.

  Definition valid (e : bexp) (te : TE.env) : Prop :=
    forall s : S.t, S.conform s te -> eval_bexp e te s.

  Definition entails (f g : bexp) (te : TE.env) : Prop :=
    forall s : S.t, S.conform s te -> eval_bexp f te s -> eval_bexp g te s.

  Definition eval_atom (a : atom) (s : S.t) : bits :=
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

  Lemma eqn_lvs_instr_subset i :
    VS.subset (lvs_instr (eqn_instr i)) (lvs_instr i).
  Proof.
    case: i => /=; try (intros; apply: VSLemmas.subset_refl).
    case => _ r /=. exact: VSLemmas.subset_refl.
  Qed.

  Lemma rng_lvs_instr_subset i :
    VS.subset (lvs_instr (rng_instr i)) (lvs_instr i).
  Proof.
    case: i => /=; try (intros; apply: VSLemmas.subset_refl).
    case => _ r /=. exact: VSLemmas.subset_refl.
  Qed.

  Local Notation state := S.t.

  Inductive eval_instr (te : TE.env) : instr -> state -> state -> Prop :=
  | EImov v a s t :
      S.Upd v (eval_atom a s) s t ->
      eval_instr te (Imov v a) s t
  | EIshl v a i s t :
      S.Upd v (shlB i (eval_atom a s)) s t ->
      eval_instr te (Ishl v a i) s t
  | EIcshl vh vl a1 a2 i s t :
      S.Upd2 vl (shrB i
                      (low (size (eval_atom a2 s))
                           (shlB i
                                 (cat (eval_atom a2 s) (eval_atom a1 s)))))
             vh (high (size (eval_atom a1 s))
                      (shlB i
                            (cat (eval_atom a2 s) (eval_atom a1 s))))
             s t ->
      eval_instr te (Icshl vh vl a1 a2 i) s t
  | EInondet v ty s t n :
      size n = sizeof_typ ty ->
      S.Upd v n s t ->
      eval_instr te (Inondet v ty) s t
  | EIcmovT v c a1 a2 s t :
      to_bool (eval_atom c s) ->
      S.Upd v (eval_atom a1 s) s t ->
      eval_instr te (Icmov v c a1 a2) s t
  | EIcmovF v c a1 a2 s t :
      ~~ to_bool (eval_atom c s) ->
      S.Upd v (eval_atom a2 s) s t ->
      eval_instr te (Icmov v c a1 a2) s t
  | EInop s : eval_instr te Inop s s
  | EInot v ty a s t :
      S.Upd v (invB (eval_atom a s)) s t ->
      eval_instr te (Inot v ty a) s t
  | EIadd v a1 a2 s t :
      S.Upd v (addB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Iadd v a1 a2) s t
  | EIadds c v a1 a2 s t :
      S.Upd2 v (addB (eval_atom a1 s) (eval_atom a2 s))
             c (1-bits of bool
                       (carry_addB (eval_atom a1 s) (eval_atom a2 s)))
             s t ->
      eval_instr te (Iadds c v a1 a2) s t
  | EIadc v a1 a2 y s t :
      S.Upd v (adcB (to_bool (eval_atom y s))
                    (eval_atom a1 s)
                    (eval_atom a2 s)).2
            s t ->
      eval_instr te (Iadc v a1 a2 y) s t
  | EIadcs c v a1 a2 y s t :
      S.Upd2 v (adcB (to_bool (eval_atom y s))
                     (eval_atom a1 s)
                     (eval_atom a2 s)).2
             c (1-bits of bool
                       ((adcB (to_bool (eval_atom y s))
                             (eval_atom a1 s)
                             (eval_atom a2 s)).1))
             s t ->
      eval_instr te (Iadcs c v a1 a2 y) s t
  | EIsub v a1 a2 s t :
      S.Upd v (subB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Isub v a1 a2) s t
  | EIsubc c v a1 a2 s t :
      S.Upd2 v ((adcB true (eval_atom a1 s) (invB (eval_atom a2 s))).2)
             c (1-bits of bool
                       ((adcB true (eval_atom a1 s) (invB (eval_atom a2 s))).1))
             s t ->
      eval_instr te (Isubc c v a1 a2) s t
  | EIsubb b v a1 a2 s t :
      S.Upd2 v (subB (eval_atom a1 s) (eval_atom a2 s))
             b (1-bits of bool
                       (borrow_subB (eval_atom a1 s) (eval_atom a2 s)))
             s t ->
      eval_instr te (Isubb b v a1 a2) s t
  | EIsbc v a1 a2 y s t :
      S.Upd v (adcB (to_bool (eval_atom y s))
                    (eval_atom a1 s)
                    (invB (eval_atom a2 s))).2
            s t ->
      eval_instr te (Isbc v a1 a2 y) s t
  | EIsbcs c v a1 a2 y s t :
      S.Upd2 v (adcB (to_bool (eval_atom y s))
                     (eval_atom a1 s)
                     (invB (eval_atom a2 s))).2
             c (1-bits of bool
                       ((adcB (to_bool (eval_atom y s))
                             (eval_atom a1 s)
                             (invB (eval_atom a2 s))).1))
             s t ->
      eval_instr te (Isbcs c v a1 a2 y) s t
  | EIsbb v a1 a2 y s t :
      S.Upd v (sbbB (to_bool (eval_atom y s))
                    (eval_atom a1 s)
                    (eval_atom a2 s)).2
            s t ->
      eval_instr te (Isbb v a1 a2 y) s t
  | EIsbbs b v a1 a2 y s t :
      S.Upd2 v (sbbB (to_bool (eval_atom y s))
                     (eval_atom a1 s)
                     (eval_atom a2 s)).2
             b (1-bits of bool
                       ((sbbB (to_bool (eval_atom y s))
                             (eval_atom a1 s)
                             (eval_atom a2 s)).1))
             s t ->
      eval_instr te (Isbbs b v a1 a2 y) s t
  | EImul v a1 a2 s t :
      S.Upd v (mulB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Imul v a1 a2) s t
  | EImullU vh vl a1 a2 s t :
      is_unsigned (atyp a1 te) ->
      S.Upd2 vl (low (size (eval_atom a2 s))
                     (mulB (zext (size (eval_atom a1 s)) (eval_atom a1 s))
                           (zext (size (eval_atom a1 s)) (eval_atom a2 s))))
             vh (high (size (eval_atom a1 s))
                      (mulB (zext (size (eval_atom a1 s)) (eval_atom a1 s))
                            (zext (size (eval_atom a1 s)) (eval_atom a2 s))))
             s t ->
      eval_instr te (Imull vh vl a1 a2) s t
  | EImullS vh vl a1 a2 s t :
      is_signed (atyp a1 te) ->
      S.Upd2 vl (low (size (eval_atom a2 s))
                     (mulB (sext (size (eval_atom a1 s)) (eval_atom a1 s))
                           (sext (size (eval_atom a1 s)) (eval_atom a2 s))))
             vh (high (size (eval_atom a1 s))
                      (mulB (sext (size (eval_atom a1 s)) (eval_atom a1 s))
                            (sext (size (eval_atom a1 s)) (eval_atom a2 s))))
             s t ->
      eval_instr te (Imull vh vl a1 a2) s t
  | EImuljU v a1 a2 s t :
      is_unsigned (atyp a1 te) ->
      S.Upd v (mulB (zext (size (eval_atom a1 s)) (eval_atom a1 s))
                    (zext (size (eval_atom a1 s)) (eval_atom a2 s)))
            s t ->
      eval_instr te (Imulj v a1 a2) s t
  | EImuljS v a1 a2 s t :
      is_signed (atyp a1 te) ->
      S.Upd v (mulB (sext (size (eval_atom a1 s)) (eval_atom a1 s))
                    (sext (size (eval_atom a1 s)) (eval_atom a2 s)))
            s t ->
      eval_instr te (Imulj v a1 a2) s t
  | EIsplitU vh vl a n s t :
      is_unsigned (atyp a te) ->
      S.Upd2 vl (shrB ((size (eval_atom a s)) - n) (shlB ((size (eval_atom a s)) - n) (eval_atom a s)))
             vh (shrB n (eval_atom a s))
             s t ->
      eval_instr te (Isplit vh vl a n) s t
  | EIsplitS vh vl a n s t :
      is_signed (atyp a te) ->
      S.Upd2 vl (shrB ((size (eval_atom a s)) - n) (shlB ((size (eval_atom a s)) - n) (eval_atom a s)))
             vh (sarB n (eval_atom a s))
             s t ->
      eval_instr te (Isplit vh vl a n) s t
  | EIand v ty a1 a2 s t :
      S.Upd v (andB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Iand v ty a1 a2) s t
  | EIor v ty a1 a2 s t :
      S.Upd v (orB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Ior v ty a1 a2) s t
  | EIxor v ty a1 a2 s t :
      S.Upd v (xorB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Ixor v ty a1 a2) s t
  | EIcast v ty a s t :
      S.Upd v (tcast (eval_atom a s) (atyp a te) ty) s t ->
      eval_instr te (Icast v ty a) s t
  | EIvpc v ty a s t :
      S.Upd v (tcast (eval_atom a s) (atyp a te) ty) s t ->
      eval_instr te (Ivpc v ty a) s t
  | EIjoin v ah al s t :
      S.Upd v (cat (eval_atom al s) (eval_atom ah s)) s t ->
      eval_instr te (Ijoin v ah al) s t
  | EIassume e s :
      eval_bexp e te s -> eval_instr te (Iassume e) s s
  .

  Hint Constructors eval_instr : dsl.

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

  Lemma atyp_equal E1 E2 a: TE.Equal E1 E2 -> atyp a E1 = atyp a E2.
  Proof.
    move=> Heq. case: a => //=. move=> v.
    move: (TELemmas.find_m (eqxx v) Heq) => Hfind2.
    move: (Logic.eq_sym Hfind2) => {Hfind2} Hfind2.
    case Hfind1: (TE.find v E1).
    - rewrite Hfind1 in Hfind2.
      rewrite (TE.find_some_vtyp Hfind1) (TE.find_some_vtyp Hfind2).
      reflexivity.
    - rewrite Hfind1 in Hfind2.
      rewrite (TE.find_none_vtyp Hfind1) (TE.find_none_vtyp Hfind2).
      reflexivity.
  Qed.

  Lemma asize_equal E1 E2 a : TE.Equal E1 E2 -> asize a E1 = asize a E2.
  Proof.
    rewrite /asize. move=> Heq. rewrite (atyp_equal _ Heq). reflexivity.
  Qed.

  Lemma instr_succ_typenv_equal E1 E2 i :
    TE.Equal E1 E2 -> TE.Equal (instr_succ_typenv i E1) (instr_succ_typenv i E2).
  Proof.
    move=> Heq.
    (case: i => //=); intros;
      by repeat
        match goal with
        | H : TE.Equal ?E1 ?E2 |- context f [atyp ?a ?E1] =>
          rewrite (atyp_equal a Heq)
        | |- TE.Equal (TE.add _ _ _) (TE.add _ _ _) =>
          apply: TELemmas.F.add_m
        | |- TE.SE.eq ?x ?x =>
          exact: eqxx
        | |- ?e = ?e => reflexivity
        | H : ?p |- ?p => assumption
        end.
  Qed.

  Lemma program_succ_typenv_equal E1 E2 p :
    TE.Equal E1 E2 -> TE.Equal (program_succ_typenv p E1) (program_succ_typenv p E2).
  Proof.
    elim: p E1 E2 => [| i p IH] E1 E2 //= Heq.
    move: (instr_succ_typenv_equal i Heq) => {Heq} Heq. exact: (IH _ _ Heq).
  Qed.

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
    - move=> e1 e2 ms H. apply: (H (Eeqmod e1 e2 ms)). by rewrite mem_seq1 eqxx.
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

  Lemma eval_eands_split_eand e E s :
    eval_ebexp (eands (split_eand e)) E s <-> eval_ebexp e E s.
  Proof.
    elim: e => //=.
    - move=> e1 e2; split.
      + move=> [H _]; assumption.
      + move=> H; by split.
    - move=> e1 e2 ms; split.
      + move=> [H _]; assumption.
      + move=> H; by split.
    - move=> e1 IH1 e2 IH2; split.
      + rewrite eval_ebexp_eands_cat; tauto.
      + rewrite eval_ebexp_eands_cat; tauto.
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
      eval_bexp (espre s) (esinputs s) s1 ->
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
    - exact: (He s1 s2 Hcon (conj Hepre Hrpre) Hprog).
    - exact: (Hr s1 s2 Hcon Hrpre (eval_rng_program Hprog)).
  Qed.

  Lemma valid_espec_eand E f p e1 e2 :
    valid_espec {| esinputs := E; espre := f; esprog := p; espost := Eand e1 e2 |} <->
      valid_espec {| esinputs := E; espre := f; esprog := p; espost := e1 |} /\
        valid_espec {| esinputs := E; espre := f; esprog := p; espost := e2 |}.
  Proof.
    rewrite /valid_espec /=. split.
    - move=> H; split; move=> s1 s2 Hco Hpre Hprog; move: (H s1 s2 Hco Hpre Hprog); tauto.
    - move=> [H1 H2] s1 s2 Hco Hpre Hprog.
      exact: (conj (H1 s1 s2 Hco Hpre Hprog) (H2 s1 s2 Hco Hpre Hprog)).
  Qed.

  Lemma valid_rspec_rand E f p e1 e2 :
    valid_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := Rand e1 e2 |} <->
      valid_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := e1 |} /\
        valid_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := e2 |}.
  Proof.
    rewrite /valid_rspec /=. split.
    - move=> H; split; move=> s1 s2 Hco Hpre Hprog; move: (H s1 s2 Hco Hpre Hprog);
                              move/andP; tauto.
    - move=> [H1 H2] s1 s2 Hco Hpre Hprog.
      by rewrite (H1 s1 s2 Hco Hpre Hprog) (H2 s1 s2 Hco Hpre Hprog).
  Qed.


  (* Well-typedness *)

  (* Here we define well-typedness assuming all used variables are defined. *)
  (* Note: we could also check the definedness of variables in well-typedness. *)

  Fixpoint well_typed_eexp (te : TE.env) (e : eexp) : bool :=
    match e with
    | Evar v => true
    | Econst n => true
    | Eunop op e => well_typed_eexp te e
    | Ebinop op e1 e2 => (well_typed_eexp te e1) && (well_typed_eexp te e2)
    | Epow e _ => well_typed_eexp te e
    end.

  Fixpoint well_typed_eexps (te : TE.env) (es : seq eexp) : bool :=
    match es with
    | [::] => true
    | e::es => (well_typed_eexp te e) && (well_typed_eexps te es)
    end.

  Fixpoint well_typed_rexp (te : TE.env) (e : rexp) : bool :=
    match e with
    | Rvar v => 0 < TE.vsize v te
    | Rconst w n => (0 < w) && (size n == w)
    | Runop w op e =>
      (0 < w) && (well_typed_rexp te e) && (size_of_rexp e te == w)
    | Rbinop w op e1 e2 =>
      (0 < w) &&
      (well_typed_rexp te e1) && (size_of_rexp e1 te == w) &&
      (well_typed_rexp te e2) && (size_of_rexp e2 te == w)
    | Ruext w e i
    | Rsext w e i =>
      (0 < w) && (well_typed_rexp te e) && (size_of_rexp e te == w)
    end.

  Fixpoint well_typed_ebexp (te : TE.env) (e : ebexp) : bool :=
    match e with
    | Etrue => true
    | Eeq e1 e2 => (well_typed_eexp te e1) && (well_typed_eexp te e2)
    | Eeqmod e1 e2 ms =>
      (well_typed_eexp te e1) && (well_typed_eexp te e2) && (well_typed_eexps te ms)
    | Eand e1 e2 => (well_typed_ebexp te e1) && (well_typed_ebexp te e2)
    end.

  Fixpoint well_typed_rbexp (te : TE.env) (e : rbexp) : bool :=
    match e with
    | Rtrue => true
    | Req w e1 e2
    | Rcmp w _ e1 e2 =>
      (0 < w) &&
      (well_typed_rexp te e1) && (size_of_rexp e1 te == w) &&
      (well_typed_rexp te e2) && (size_of_rexp e2 te == w)
    | Rneg e => well_typed_rbexp te e
    | Rand e1 e2
    | Ror e1 e2 => (well_typed_rbexp te e1) && (well_typed_rbexp te e2)
    end.

  Definition well_typed_bexp (te : TE.env) (e : bexp) : bool :=
    (well_typed_ebexp te (eqn_bexp e)) && (well_typed_rbexp te (rng_bexp e)).

  (* The size of an atom must be larger than 0. *)
  Definition well_sized_atom E (a : atom) : bool :=
    if is_unsigned (atyp a E) then 0 < asize a E
    else 1 < asize a E.

  (*
   * If an atom is a constant, size of the constant must match
   * the type of the atom.
   *)
  Definition size_matched_atom (a : atom) : bool :=
    match a with
    | Avar _ => true
    | Aconst t n => size n == sizeof_typ t
    end.

  Definition well_typed_atom (E : TE.env) (a : atom) : bool :=
    well_sized_atom E a && size_matched_atom a.

  Definition well_typed_instr (E : TE.env) (i : instr) : bool :=
    match i with
    | Imov v a => well_typed_atom E a
    | Ishl v a n => (well_typed_atom E a) && (n < asize a E)
    | Icshl v1 v2 a1 a2 n => is_unsigned (atyp a2 E) &&
                             compatible (atyp a1 E) (atyp a2 E) &&
                             (well_typed_atom E a1) && (well_typed_atom E a2) &&
                             (n <= asize a2 E)
    | Inondet v t => true
    | Icmov v c a1 a2 => (atyp c E == Tbit) && (atyp a1 E == atyp a2 E) &&
                         (well_typed_atom E a1) && (well_typed_atom E a2) &&
                         (well_typed_atom E c)
    | Inop => true
    | Inot v t a => compatible t (atyp a E) && (well_typed_atom E a)
    | Iadd v a1 a2
    | Iadds _ v a1 a2 => (atyp a1 E == atyp a2 E) && (well_typed_atom E a1) &&
                         (well_typed_atom E a2)
    | Iadc v a1 a2 y
    | Iadcs _ v a1 a2 y => (atyp a1 E == atyp a2 E) && (atyp y E == Tbit) &&
                           (well_typed_atom E a1) && (well_typed_atom E a2) &&
                           (well_typed_atom E y)
    | Isub v a1 a2
    | Isubc _ v a1 a2
    | Isubb _ v a1 a2 => (atyp a1 E == atyp a2 E) && (well_typed_atom E a1) &&
                         (well_typed_atom E a2)
    | Isbc v a1 a2 y
    | Isbcs _ v a1 a2 y => (atyp a1 E == atyp a2 E) && (atyp y E == Tbit) &&
                           (well_typed_atom E a1) && (well_typed_atom E a2) &&
                           (well_typed_atom E y)
    | Isbb v a1 a2 y
    | Isbbs _ v a1 a2 y => (atyp a1 E == atyp a2 E) && (atyp y E == Tbit) &&
                           (well_typed_atom E a1) && (well_typed_atom E a2) &&
                           (well_typed_atom E y)
    | Imul v a1 a2 => (atyp a1 E == atyp a2 E) &&
                      (well_typed_atom E a1) && (well_typed_atom E a2)
    | Imull vh vl a1 a2 => (atyp a1 E == atyp a2 E) &&
                           (well_typed_atom E a1) && (well_typed_atom E a2)
    | Imulj v a1 a2 => (atyp a1 E == atyp a2 E) &&
                       (well_typed_atom E a1) && (well_typed_atom E a2)
    | Isplit vh vl a n => (well_typed_atom E a) && (n < asize a E)
    | Iand v t a1 a2
    | Ior v t a1 a2
    | Ixor v t a1 a2 =>
      compatible t (atyp a1 E) && compatible t (atyp a2 E) &&
      (well_typed_atom E a1) && (well_typed_atom E a2)
    | Icast v t a
    | Ivpc v t a => (well_typed_atom E a)
    | Ijoin v ah al =>
      is_unsigned (atyp al E) && compatible (atyp ah E) (atyp al E) &&
      (well_typed_atom E ah) && (well_typed_atom E al)
    | Iassume e => well_typed_bexp E e
    end.

  Lemma well_typed_eexp_true E e : well_typed_eexp E e.
  Proof.
    elim: e => //=. move=> op e1 Hwt1 e2 Hwt2. by rewrite Hwt1 Hwt2.
  Qed.

  Lemma well_typed_eexps_true E es : well_typed_eexps E es.
  Proof.
    elim: es => [| e es IH] //=. by rewrite well_typed_eexp_true IH.
  Qed.

  Lemma well_typed_ebexp_true E e : well_typed_ebexp E e.
  Proof.
    elim: e => //=.
    - move=> e1 e2. by rewrite !well_typed_eexp_true.
    - move=> e1 e2 ms. by rewrite !well_typed_eexp_true well_typed_eexps_true.
    - move=> e1 Hwt1 e2 Hwt2. by rewrite Hwt1 Hwt2.
  Qed.


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

  Definition well_defined_instr (te : TE.env) (i : instr) : bool :=
    match i with
    | Imov v a => are_defined (vars_atom a) te
    | Ishl v a _ => are_defined (vars_atom a) te
    | Icshl v1 v2 a1 a2 _ =>
      (v1 != v2) && are_defined (vars_atom a1) te
                 && are_defined (vars_atom a2) te
    | Inondet v t => true
    | Icmov v c a1 a2 =>
      (are_defined (vars_atom c) te) && are_defined (vars_atom a1) te
                                       && are_defined (vars_atom a2) te
    | Inop => true
    | Inot v t a => are_defined (vars_atom a) te
    | Iadd v a1 a2 =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
    | Iadds c v a1 a2 =>
      (c != v) && are_defined (vars_atom a1) te
               && are_defined (vars_atom a2) te
    | Iadc v a1 a2 y =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
                  && are_defined (vars_atom y) te
    | Iadcs c v a1 a2 y =>
      (c != v) && are_defined (vars_atom a1) te
               && are_defined (vars_atom a2) te
               && are_defined (vars_atom y) te
    | Isub v a1 a2 =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
    | Isubc c v a1 a2
    | Isubb c v a1 a2 =>
      (c != v) && are_defined (vars_atom a1) te
               && are_defined (vars_atom a2) te
    | Isbc v a1 a2 y =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
                  && are_defined (vars_atom y) te
    | Isbcs c v a1 a2 y =>
      (c != v) && are_defined (vars_atom a1) te
               && are_defined (vars_atom a2) te
               && are_defined (vars_atom y) te
    | Isbb v a1 a2 y =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
                  && are_defined (vars_atom y) te
    | Isbbs c v a1 a2 y =>
      (c != v) && are_defined (vars_atom a1) te
               && are_defined (vars_atom a2) te
               && are_defined (vars_atom y) te
    | Imul v a1 a2 =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
    | Imull vh vl a1 a2 =>
      (vh != vl) && are_defined (vars_atom a1) te
                 && are_defined (vars_atom a2) te
    | Imulj v a1 a2 =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
    | Isplit vh vl a n => (vh != vl) && are_defined (vars_atom a) te
    | Iand v t a1 a2
    | Ior v t a1 a2
    | Ixor v t a1 a2 =>
      are_defined (vars_atom a1) te && are_defined (vars_atom a2) te
    | Icast v t a
    | Ivpc v t a => are_defined (vars_atom a) te
    | Ijoin v ah al =>
      are_defined (vars_atom ah) te && are_defined (vars_atom al) te
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

  Fixpoint well_formed_eexps (te : TE.env) (es : seq eexp) :=
    match es with
    | [::] => true
    | e::es => (well_formed_eexp te e) && (well_formed_eexps te es)
    end.

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

  Definition well_formed_espec (s : espec) : bool :=
    well_formed_bexp (esinputs s) (espre s) &&
    well_formed_program (esinputs s) (esprog s) &&
    well_formed_ebexp (program_succ_typenv (esprog s) (esinputs s)) (espost s).

  Definition well_formed_rspec (s : rspec) : bool :=
    well_formed_rbexp (rsinputs s) (rspre s) &&
    well_formed_program (rsinputs s) (rsprog s) &&
    well_formed_rbexp (program_succ_typenv (rsprog s) (rsinputs s)) (rspost s).


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


  Lemma well_formed_eexp_defined E e : well_formed_eexp E e -> are_defined (vars_eexp e) E.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_eexp_typed E e : well_formed_eexp E e -> well_typed_eexp E e.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_ebexp_defined E e : well_formed_ebexp E e -> are_defined (vars_ebexp e) E.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_ebexp_typed E e : well_formed_ebexp E e -> well_typed_ebexp E e.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_rexp_defined E e : well_formed_rexp E e -> are_defined (vars_rexp e) E.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_rexp_typed E e : well_formed_rexp E e -> well_typed_rexp E e.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_rbexp_defined E e : well_formed_rbexp E e -> are_defined (vars_rbexp e) E.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_rbexp_typed E e : well_formed_rbexp E e -> well_typed_rbexp E e.
  Proof. by move/andP=> [H1 H2]. Qed.

  Lemma well_formed_eexps_defined E es : well_formed_eexps E es -> are_defined (vars_eexps es) E.
  Proof.
    elim: es => [| e es IH] //=.
    - by rewrite are_defined_empty.
    - move=> /andP [Hwf1 Hwf2]. rewrite are_defined_union.
      by rewrite (well_formed_eexp_defined Hwf1) (IH Hwf2).
  Qed.

  Lemma well_formed_eexps_typed E es : well_formed_eexps E es -> well_typed_eexps E es.
  Proof.
    elim: es => [| e es IH] //=. move/andP=> [Hwf1 Hwf2].
    by rewrite (well_formed_eexp_typed Hwf1) (IH Hwf2).
  Qed.

  Lemma well_formed_eexps_defined_typed E es :
    well_formed_eexps E es <-> are_defined (vars_eexps es) E /\ well_typed_eexps E es.
  Proof.
    split.
    - move=> H. by rewrite (well_formed_eexps_defined H) (well_formed_eexps_typed H).
    - elim: es => [| e es IH] //=. rewrite are_defined_union.
      move=> [/andP [Hdef1 Hdef2] /andP [Hwt1 Hwt2]]. rewrite (IH (conj Hdef2 Hwt2)) andbT.
      by rewrite /well_formed_eexp Hdef1 Hwt1.
  Qed.

  Lemma well_formed_ebexp_etrue E : well_formed_ebexp E etrue.
  Proof. rewrite /well_formed_ebexp /=. by rewrite are_defined_empty. Qed.

  Lemma well_formed_ebexp_eeq E e1 e2 :
    well_formed_ebexp E (Eeq e1 e2) <-> well_formed_eexp E e1 /\ well_formed_eexp E e2.
  Proof.
    rewrite /well_formed_ebexp /well_formed_eexp /=. rewrite are_defined_union; split; by t_auto.
  Qed.

  Lemma well_formed_ebexp_eeqmod E e1 e2 ms :
    well_formed_ebexp E (Eeqmod e1 e2 ms) <->
      well_formed_eexp E e1 /\ well_formed_eexp E e2 /\ well_formed_eexps E ms.
  Proof.
    rewrite /well_formed_ebexp /well_formed_eexp /=. rewrite !are_defined_union.
    split; try t_auto.
    - by apply/well_formed_eexps_defined_typed.
    - move/well_formed_eexps_defined_typed: b; by t_auto.
  Qed.

  Lemma well_formed_ebexp_eand E e1 e2 :
    well_formed_ebexp E (Eand e1 e2) <-> well_formed_ebexp E e1 /\ well_formed_ebexp E e2.
  Proof.
    rewrite /well_formed_ebexp /=. rewrite are_defined_union. split; by t_auto.
  Qed.

  Lemma well_formed_rbexp_rtrue E : well_formed_rbexp E rtrue.
  Proof. rewrite /well_formed_rbexp /=. by rewrite are_defined_empty. Qed.

  Lemma well_formed_rbexp_req E n e1 e2 :
    well_formed_rbexp E (Req n e1 e2) ->
    well_formed_rexp E e1 /\ well_formed_rexp E e2 /\
      0 < n /\ size_of_rexp e1 E = n /\ size_of_rexp e2 E = n.
  Proof.
    rewrite /well_formed_rbexp /well_formed_rexp /=. rewrite are_defined_union.
    by t_auto.
  Qed.

  Lemma well_formed_rbexp_rcmp E n op e1 e2 :
    well_formed_rbexp E (Rcmp n op e1 e2) ->
    well_formed_rexp E e1 /\ well_formed_rexp E e2 /\
      0 < n /\ size_of_rexp e1 E = n /\ size_of_rexp e2 E = n.
  Proof.
    rewrite /well_formed_rbexp /well_formed_rexp /=. rewrite are_defined_union.
    by t_auto.
  Qed.

  Lemma well_formed_rbexp_rneg E e :
    well_formed_rbexp E (Rneg e) <-> well_formed_rbexp E e.
  Proof. rewrite /well_formed_rbexp /=. tauto. Qed.

  Lemma well_formed_rbexp_rand E e1 e2 :
    well_formed_rbexp E (Rand e1 e2) <-> well_formed_rbexp E e1 /\ well_formed_rbexp E e2.
  Proof.
    rewrite /well_formed_rbexp /=. rewrite are_defined_union. split; by t_auto.
  Qed.

  Lemma well_formed_rbexp_ror E e1 e2 :
    well_formed_rbexp E (Ror e1 e2) <-> well_formed_rbexp E e1 /\ well_formed_rbexp E e2.
  Proof.
    rewrite /well_formed_rbexp /=. rewrite are_defined_union. split; by t_auto.
  Qed.

  Lemma well_formed_rexp_unop E w op e :
    well_formed_rexp E (Runop w op e) ->
    well_formed_rexp E e /\ 0 < w /\ size_of_rexp e E = w.
  Proof.
    move/andP => /= [Hdef /andP [/andP [Hw Hwt] /eqP Hs]].
    split => //=. apply/andP; split; assumption.
  Qed.

  Lemma well_formed_rexp_binop E w op e1 e2 :
    well_formed_rexp E (Rbinop w op e1 e2) ->
    well_formed_rexp E e1 /\ well_formed_rexp E e2 /\
    0 < w /\ size_of_rexp e1 E = w /\ size_of_rexp e2 E = w.
  Proof.
    move/andP => /= [Hdef /andP [/andP [/andP [/andP [Hw Hwt1]
                                                /eqP Hs1] Hwt2] /eqP Hs2]].
    rewrite are_defined_union in Hdef. move/andP: Hdef => [Hdef1 Hdef2].
    repeat split => //; (apply/andP; split; assumption).
  Qed.

  Lemma well_formed_rexp_uext E w e n :
    well_formed_rexp E (Ruext w e n) ->
    well_formed_rexp E e /\ 0 < w /\ size_of_rexp e E = w.
  Proof.
    move/andP=> /= [Hdef /andP [/andP [Hw Hwt] /eqP Hs]]. split => //=.
    apply/andP; split; assumption.
  Qed.

  Lemma well_formed_rexp_sext E w e n :
    well_formed_rexp E (Rsext w e n) ->
    well_formed_rexp E e /\ 0 < w /\ size_of_rexp e E = w.
  Proof.
    move/andP=> /= [Hdef /andP [/andP [Hw Hwt] /eqP Hs]]. split=> //=.
    apply/andP; split; assumption.
  Qed.

  Lemma well_formed_rbexp_eq E w e1 e2 :
    well_formed_rbexp E (Req w e1 e2) ->
    well_formed_rexp E e1 /\ well_formed_rexp E e2 /\
    0 < w /\ size_of_rexp e1 E = w /\ size_of_rexp e2 E = w.
  Proof.
    move/andP => /= [Hdef /andP [/andP [/andP [/andP [Hw Hwt1]
                                                /eqP Hs1] Hwt2] /eqP Hs2]].
    rewrite are_defined_union in Hdef. move/andP: Hdef => [Hdef1 Hdef2].
    repeat split => //; (apply/andP; split; assumption).
  Qed.

  Lemma well_formed_rbexp_cmp E w op e1 e2 :
    well_formed_rbexp E (Rcmp w op e1 e2) ->
    well_formed_rexp E e1 /\ well_formed_rexp E e2 /\
    0 < w /\ size_of_rexp e1 E = w /\ size_of_rexp e2 E = w.
  Proof.
    move/andP => /= [Hdef /andP [/andP [/andP [/andP [Hw Hwt1]
                                                /eqP Hs1] Hwt2] /eqP Hs2]].
    rewrite are_defined_union in Hdef. move/andP: Hdef => [Hdef1 Hdef2].
    repeat split => //; (apply/andP; split; assumption).
  Qed.

  Lemma well_formed_rbexp_neg E e :
    well_formed_rbexp E (Rneg e) -> well_formed_rbexp E e.
  Proof.
    move/andP=> /= [Hdef Hwt]. apply/andP; split; assumption.
  Qed.

  Lemma well_formed_rbexp_and E e1 e2 :
    well_formed_rbexp E (Rand e1 e2) ->
    well_formed_rbexp E e1 /\ well_formed_rbexp E e2.
  Proof.
    move/andP=> /= [Hdef /andP [Hwt1 Hwt2]].
    rewrite are_defined_union in Hdef. move/andP: Hdef => [Hdef1 Hdef2].
    split; apply/andP; split; assumption.
  Qed.

  Lemma well_formed_rbexp_or E e1 e2 :
    well_formed_rbexp E (Ror e1 e2) ->
    well_formed_rbexp E e1 /\ well_formed_rbexp E e2.
  Proof.
    move/andP=> /= [Hdef /andP [Hwt1 Hwt2]].
    rewrite are_defined_union in Hdef. move/andP: Hdef => [Hdef1 Hdef2].
    split; apply/andP; split; assumption.
  Qed.


  Lemma well_formed_program_cat te p1 p2 :
    well_formed_program te (p1 ++ p2) =
    well_formed_program te p1 &&
                        well_formed_program (program_succ_typenv p1 te) p2.
  Proof.
    case H: (well_formed_program te p1 &&
             well_formed_program (program_succ_typenv p1 te) p2).
    - move/andP: H => [Hp1 Hp2]. elim: p1 te p2 Hp1 Hp2 => /=.
      + done.
      + move=> hd tl IH te p2 /andP [Hhd Htl] Hp2. rewrite Hhd /=.
        apply: (IH _ _ Htl). exact: Hp2.
    - move/negP: H => Hneg. apply/negP => H; apply: Hneg; apply/andP.
      elim: p1 te p2 H => /=.
      + done.
      + move=> hd tl IH te p2 /andP [Hhd Htlp2].
        move: (IH _ _ Htlp2) => {IH Htlp2} [Htl Hp2]. split.
        * by rewrite Hhd Htl.
        * exact: Hp2.
  Qed.

  Lemma well_formed_program_cat1 te p1 p2 :
    well_formed_program te (p1 ++ p2) -> well_formed_program te p1.
  Proof. rewrite well_formed_program_cat. by move=> /andP [H _]. Qed.

  Lemma well_formed_program_cat2 te p1 p2 :
    well_formed_program te (p1 ++ p2) ->
    well_formed_program (program_succ_typenv p1 te) p2.
  Proof. rewrite well_formed_program_cat. by move=> /andP [_ H]. Qed.

  Lemma well_formed_program_cat3 te p1 p2 :
    well_formed_program te p1 ->
    well_formed_program (program_succ_typenv p1 te) p2 ->
    well_formed_program te (p1 ++ p2).
  Proof. rewrite well_formed_program_cat. by move=> H1 H2; rewrite H1 H2. Qed.

  Lemma well_formed_program_cons1 te p i :
    well_formed_program te (i::p) -> well_formed_instr te i.
  Proof. by move=> /andP [H _]. Qed.

  Lemma well_formed_program_cons2 te p i :
    well_formed_program te (i::p) ->
    well_formed_program (instr_succ_typenv i te) p.
  Proof. by move=> /andP [_ H]. Qed.

  Lemma well_formed_program_cons3 te p i :
    well_formed_instr te i ->
    well_formed_program (instr_succ_typenv i te) p ->
    well_formed_program te (i::p).
  Proof. move=> H1 H2. by rewrite /= H1 H2. Qed.

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
    rewrite well_formed_program_cat /=.
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
    VS.mem x (vars_atom a) -> atyp a (TE.add x t E) = t.
  Proof.
    case: a => /= [v Hmem | tb bs Hmem].
    - move: (VSLemmas.mem_singleton1 Hmem) => /idP Heq. rewrite eq_sym in Heq.
      exact: (TE.vtyp_add_eq Heq).
    - rewrite VSLemmas.mem_empty in Hmem. discriminate.
  Qed.

  Lemma atyp_add_not_mem a x t E :
    ~~ VS.mem x (vars_atom a) -> atyp a (TE.add x t E) = atyp a E.
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
                       => let Hin := fresh "Hin" in
                          move:(VS.union_1 H) => Hin; clear H; tac
                     | H : is_true(well_formed_instr ?te ?i) |- _  =>
                       let Hwd := fresh "Hwd" in let Hwt := fresh "Hwt" in
                                                 move/andP: H => [Hwd Hwt]; tac
                     | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
                       (rewrite /= in Hwd); tac
                     | H : is_true (_ && _) |- _ =>
                       let H1 := fresh in
                       let H2 := fresh in
                       move/andP: H => [H1 H2]; tac
                     | |- is_true (VS.for_all (is_defined^~ ?te) _) =>
                       apply (VS.for_all_1 (are_defined_compat te)); tac
                     | Hin: VS.In ?x ?vs,Hwd: is_true (are_defined ?vs ?te)
                       |- is_defined ?x ?te = true
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

  Lemma well_formed_instr_well_defined E i :
    well_formed_instr E i -> well_defined_instr E i.
  Proof. by move/andP => [H1 H2]. Qed.

  Lemma well_formed_instr_well_typed E i :
    well_formed_instr E i -> well_typed_instr E i.
  Proof. by move/andP => [H1 H2]. Qed.

  Lemma well_defined_instr_submap te1 te2 i :
    well_defined_instr te1 i -> TELemmas.submap te1 te2 ->
    well_defined_instr te2 i.
  Proof.
    elim: i te1 te2 => /=; intros;
                (let rec tac :=
                     match goal with
                     | H : ?a |- ?a => assumption
                     | H : ?l \/ ?r |- _ => case: H => H; tac
                     | |- ?l /\ ?r => split; tac
                     | |- is_true (_ && _) => apply /andP; tac
                     | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
                       (rewrite /= in Hwd); tac
                     | H : is_true (_ && _) |- _ =>
                       let H1 := fresh in
                       let H2 := fresh in
                       move/andP: H => [H1 H2]; tac
                     | Hsub: TELemmas.submap ?te1 ?te2,
                       Hwd: is_true (are_defined ?vs ?te1)
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

  Lemma submap_vsize E1 E2 v :
    TELemmas.submap E1 E2 ->
    is_defined v E1 ->
    TE.vsize v E1 = TE.vsize v E2.
  Proof.
    move=> Hsub Hdef. rewrite !TE.vtyp_vsize (submap_vtyp Hsub Hdef).
    reflexivity.
  Qed.

  Lemma atyp_submap a te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_atom a) te1 ->
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
    are_defined (vars_atom a) E1 ->
    asize a E1 = asize a E2.
  Proof.
    move=> H1 H2. rewrite /asize (atyp_submap H1 H2). reflexivity.
  Qed.

  Lemma well_typed_atom_well_sized E a :
    well_typed_atom E a -> well_sized_atom E a.
  Proof. by move/andP=> [? ?]. Qed.

  Lemma well_typed_atom_size_matched E a :
    well_typed_atom E a -> size_matched_atom a.
  Proof. by move/andP=> [? ?]. Qed.

  Lemma well_sized_atom_unsigned E a :
    is_unsigned (atyp a E) -> well_sized_atom E a ->
    0 < asize a E.
  Proof. rewrite /well_sized_atom => ->. by apply. Qed.

  Lemma well_sized_atom_signed E a :
    is_signed (atyp a E) -> well_sized_atom E a ->
    1 < asize a E.
  Proof.
    rewrite /well_sized_atom -not_unsigned_is_signed. move/negPf => ->.
      by apply.
  Qed.

  Lemma well_sized_atom_gt0 E a : well_sized_atom E a -> 0 < asize a E.
  Proof.
    rewrite /well_sized_atom. case: (is_unsigned (atyp a E)).
    - by apply.
    - move=> H. have H01: (0 < 1) by done. exact: (ltn_trans H01 H).
  Qed.

  Lemma well_sized_atom_submap a E1 E2 :
    TELemmas.submap E1 E2 ->
    are_defined (vars_atom a) E1 ->
    well_sized_atom E1 a = well_sized_atom E2 a.
  Proof.
    move=> Hsub Hdef. rewrite /well_sized_atom /asize.
    rewrite (atyp_submap Hsub Hdef). reflexivity.
  Qed.

  Lemma well_typed_atom_submap a E1 E2 :
    TELemmas.submap E1 E2 ->
    are_defined (vars_atom a) E1 ->
    well_typed_atom E1 a = well_typed_atom E2 a.
  Proof.
    move=> Hsub Hdef. rewrite /well_typed_atom.
    rewrite (well_sized_atom_submap Hsub Hdef). reflexivity.
  Qed.

  Lemma well_sized_atom_atyp_eq E a1 a2 :
    atyp a1 E = atyp a2 E -> well_sized_atom E a1 = well_sized_atom E a2.
  Proof.
    rewrite /well_sized_atom /asize. by move=> ->.
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

  Lemma well_typed_eexps_submap es te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_eexps es) te1 ->
    well_typed_eexps te1 es ->
    well_typed_eexps te2 es.
  Proof.
    elim: es => [| e es IH] //=. move=> Hsub Hdef /andP [Hwell1 Hwell2].
    rewrite are_defined_union in Hdef. move/andP: Hdef => [Hdef1 Hdef2].
    by rewrite (well_typed_eexp_submap Hsub Hdef1 Hwell1) (IH Hsub Hdef2 Hwell2).
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
         * exact: (well_typed_eexps_submap H Hdef11 Hwte1).
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
    replace (VS.singleton x) with (vars_atom (Avar x)) in Hwd by reflexivity.
    move: (atyp_submap Hsm Hwd) => /= Htyp.
    rewrite !TE.vtyp_vsize Htyp. exact: eqxx.
  Qed.

  Lemma well_typed_rexp_submap e te1 te2:
    TELemmas.submap te1 te2 ->
    are_defined (vars_rexp e) te1 ->
    well_typed_rexp te1 e ->
    well_typed_rexp te2 e.
  Proof.
    elim: e te1 te2 => //=; intros.
    - rewrite are_defined_singleton in H0. rewrite -(submap_vsize H H0).
      assumption.
    - move/andP: H2 => [/andP [Hw Hwte0] Hwte1]. repeat splitb; first assumption.
      + exact: (H _ _ H0 H1 Hwte0).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hwte1.
    - move: H3 => /andP [/andP [/andP [/andP [Hw Hwt0] Hsz0] Hwt1] Hsz1].
      rewrite are_defined_union in H2. move/andP: H2=> [H2_1 H2_2].
      repeat splitb; first assumption.
      + exact: (H _ _ H1 H2_1 Hwt0).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H1 H2_1)) in Hsz0.
      + exact: (H0 _ _ H1 H2_2 Hwt1).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H1 H2_2)) in Hsz1.
    - move/andP: H2 => [/andP [Hw Hwt] Hsz]. repeat splitb; first assumption.
      + exact: (H _ _ H0 H1 Hwt).
      + by rewrite (eqP (well_typed_size_of_rexp_submap H0 H1)) in Hsz.
    - move/andP: H2 => [/andP [Hw Hwt] Hsz]. repeat splitb; first assumption.
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
         | Hsub: TELemmas.submap ?te1 ?te2,
           Hwd: is_true (are_defined (vars_rexp ?r) ?te1),
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

  Lemma well_formed_eexps_submap E1 E2 es :
    TELemmas.submap E1 E2 -> well_formed_eexps E1 es -> well_formed_eexps E2 es.
  Proof.
    elim: es => [| e es IH] //=. move=> Hsub /andP [Hwf1 Hwf2].
    by rewrite (well_formed_eexp_submap Hsub Hwf1) (IH Hsub Hwf2).
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

  Lemma well_typed_instr_submap te1 te2 i :
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
           | Hsub : TELemmas.submap ?te1 ?te2, Hwd : is_true (are_defined ?vs ?te1)
             |- context [asize ?a ?te2] =>
             rewrite -(asize_submap Hsub Hwd); tac
           | Hsub : TELemmas.submap ?E1 ?E2,
                    Hdef : is_true (are_defined (vars_atom ?a) ?E1)
             |- is_true (well_typed_atom ?E2 ?a) =>
             rewrite -(well_typed_atom_submap Hsub Hdef); tac
           | |- _ => idtac
           end
       in tac).
    exact: (well_typed_bexp_submap H0 Hwd Hwt).
  Qed.

  Lemma well_formed_instr_submap te1 te2 i :
    well_formed_instr te1 i ->
    TELemmas.submap te1 te2 ->
    well_formed_instr te2 i.
  Proof.
    move=> Hwf Hsm. rewrite /well_formed_instr.
      by rewrite (well_defined_instr_submap (well_formed_instr_well_defined Hwf) Hsm)
                 (well_typed_instr_submap Hwf Hsm).
  Qed.

  Lemma well_formed_instr_replace te1 te2 i :
    well_formed_instr te1 i ->
    TE.Equal te1 te2 ->
    well_formed_instr te2 i.
  Proof.
    move=> Hwell Heq.
    apply: (well_formed_instr_submap Hwell).
    intros x v Hfind.
    rewrite /TE.Equal in Heq.
    by rewrite -(Heq x).
  Qed.

  (* TODO: move to coq-ssrlib FMaps.v *)
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

  Lemma submap_instr_succ_typenv i te1 te2:
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
             let Hwd := fresh "Hwd" in
             let Hwt := fresh "Hwt" in
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
           | Hsub: TELemmas.submap ?te1 ?te2,
             Hwd: is_true (are_defined (vars_atom ?a) ?te1)
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
    - exact: (well_formed_instr_submap Hhd Hsub).
    - apply: (IH _ _ Htl).
      exact: (submap_instr_succ_typenv Hhd Hsub).
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

  Lemma submap_program_succ_typenv p te1 te2:
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
      exact: submap_instr_succ_typenv.
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
           | |- VS.Equal (vars_env (TE.add ?t ?ty ?te))
                         (VS.union (vars_env ?te) (VS.singleton ?t))
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

  Lemma mem_program_succ_typenv x p E :
    TE.mem x E -> TE.mem x (program_succ_typenv p E).
  Proof.
    move/memenvP => H. apply/memenvP/VSLemmas.memP.
    move: (@vars_env_program_succ_typenv p E x) => [_ Himp]. apply: Himp.
    apply/VSLemmas.memP. rewrite VSLemmas.mem_union H. reflexivity.
  Qed.

  Lemma is_defined_instr_succ_typenv E i v :
    is_defined v E -> is_defined v (instr_succ_typenv i E).
  Proof.
    move/memdefP => Hmem. apply/memdefP. exact: (mem_instr_succ_typenv i Hmem).
  Qed.

  Lemma are_defined_lvs_instr_succ_typenv E i :
    are_defined (lvs_instr i) (instr_succ_typenv i E).
  Proof.
    apply/defsubP. rewrite vars_env_instr_succ_typenv.
    apply: VSLemmas.subset_union2. exact: VSLemmas.subset_refl.
  Qed.

  Lemma are_defined_lvs_program_succ_typenv E p :
    are_defined (lvs_program p) (program_succ_typenv p E).
  Proof.
    apply/defsubP. rewrite vars_env_program_succ_typenv.
    apply: VSLemmas.subset_union2. exact: VSLemmas.subset_refl.
  Qed.

  Lemma are_defined_instr_succ_typenv E i vs :
    are_defined vs E -> are_defined vs (instr_succ_typenv i E).
  Proof.
    move/defsubP=> H. apply/defsubP. rewrite vars_env_instr_succ_typenv.
    apply: VSLemmas.subset_union1. assumption.
  Qed.

  Lemma is_defined_program_succ_typenv E p v :
    is_defined v E -> is_defined v (program_succ_typenv p E).
  Proof.
    move/memdefP => Hmem. apply/memdefP. exact: (mem_program_succ_typenv p Hmem).
  Qed.

  Lemma are_defined_program_succ_typenv E p vs :
    are_defined vs E -> are_defined vs (program_succ_typenv p E).
  Proof.
    move/defsubP=> H. apply/defsubP. rewrite vars_env_program_succ_typenv.
    apply: VSLemmas.subset_union1. assumption.
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

  Lemma well_formed_bexp_submap E1 E2 e :
    TELemmas.submap E1 E2 -> well_formed_bexp E1 e -> well_formed_bexp E2 e.
  Proof.
    move=> Hsub. rewrite !well_formed_bexp_split => /andP [He Hr].
    rewrite (well_formed_ebexp_submap Hsub He) (well_formed_rbexp_submap Hsub Hr).
    exact: is_true_true.
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

  Lemma well_defined_eqn_instr E i :
    well_defined_instr E i -> well_defined_instr E (eqn_instr i).
  Proof.
    case: i => //=. case => e r //=. rewrite /vars_bexp /=.
    rewrite !are_defined_union. move/andP => [Hdefe Hdefr].
    rewrite Hdefe are_defined_empty. exact: is_true_true.
  Qed.

  Lemma well_typed_eqn_instr E i :
    well_typed_instr E i -> well_typed_instr E (eqn_instr i).
  Proof.
    case: i => //=. case => e r //=. rewrite /well_typed_bexp.
    move/andP=> /= [Hwte Hwtr]. by rewrite Hwte.
  Qed.

  Lemma well_formed_eqn_instr E i :
    well_formed_instr E i -> well_formed_instr E (eqn_instr i).
  Proof.
    case: i => //=. case => e r //=. move/andP => [H1 H2]. apply/andP. split.
  - exact: (well_defined_eqn_instr H1).
  - exact: (well_typed_eqn_instr H2).
  Qed.

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

  Lemma well_formed_eqn_spec s :
    well_formed_spec s -> well_formed_espec (espec_of_spec s).
  Proof.
    move/andP => [/andP [Hwf_f Hwf_p] Hwf_g]. rewrite /well_formed_espec.
    by rewrite Hwf_f Hwf_p (well_formed_eqn_bexp Hwf_g).
  Qed.

  Lemma well_formed_rng_spec s :
    well_formed_spec s -> well_formed_rspec (rspec_of_spec s).
  Proof.
    move/andP => [/andP [Hwf_f Hwf_p] Hwf_g]. rewrite /well_formed_rspec.
    rewrite (well_formed_rng_bexp Hwf_f) (well_formed_rng_program Hwf_p) /=.
    by rewrite rng_program_succ_typenv (well_formed_rng_bexp Hwf_g).
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
    are_defined (vars_atom a) E1 ->
    ~~ VS.mem v (vars_atom a) ->
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
    - move=> e IH n Hdef. rewrite (IH Hdef). reflexivity.
  Qed.

  Lemma submap_eval_eexps {E1 E2 es s} :
    TELemmas.submap E1 E2 ->
    are_defined (vars_eexps es) E1 ->
    eval_eexps es E1 s = eval_eexps es E2 s.
  Proof.
    elim: es => [| e es IH] //=. move=> Hsub. rewrite are_defined_union.
    move/andP => [Hdef1 Hdef2]. rewrite (submap_eval_eexp Hsub Hdef1).
    rewrite (IH Hsub Hdef2). reflexivity.
  Qed.

  Lemma submap_eval_ebexp {E1 E2 e s} :
    TELemmas.submap E1 E2 ->
    are_defined (vars_ebexp e) E1 ->
    eval_ebexp e E1 s <-> eval_ebexp e E2 s.
  Proof.
    move=> Hsub. elim: e => //=.
    - move=> e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (submap_eval_eexp Hsub Hdef1) (submap_eval_eexp Hsub Hdef2). done.
    - move=> e1 e2 ms. rewrite !are_defined_union => /andP [Hdef1 /andP [Hdef2 Hdefms]].
      rewrite (submap_eval_eexp Hsub Hdef1) (submap_eval_eexp Hsub Hdef2)
              (submap_eval_eexps Hsub Hdefms). done.
    - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      move: (IH1 Hdef1) (IH2 Hdef2) => [H1 H2] [H3 H4]. split; move => [H5 H6].
      + exact: (conj (H1 H5) (H3 H6)).
      + exact: (conj (H2 H5) (H4 H6)).
  Qed.

  Lemma submap_eval_bexp {E1 E2 e s} :
    TELemmas.submap E1 E2 ->
    are_defined (vars_bexp e) E1 ->
    eval_bexp e E1 s <-> eval_bexp e E2 s.
  Proof.
    case: e => [e r]. rewrite /vars_bexp are_defined_union /=.
    move=> Hsub /andP [Hdefe Hdefr]. rewrite /eval_bexp /=.
    split; move=> [H1 H2]; move/(submap_eval_ebexp Hsub Hdefe) : H1; tauto.
  Qed.

  Lemma submap_eval_instr E1 E2 i s t :
    TELemmas.submap E1 E2 -> well_defined_instr E1 i ->
    eval_instr E1 i s t <-> eval_instr E2 i s t.
  Proof.
    move=> Hsub. (case: i => //=); intros;
                   repeat match goal with
                          | H : is_true (_ && _) |- _ =>
                            let H1 := fresh in
                            let H2 := fresh in
                            move/andP: H => [H1 H2]
                          | |- _ <-> _ => let H := fresh in split; move=> H
                          | H : eval_instr _ _ _ _ |- _ =>
                            inversion_clear H
                          end; try eauto with dsl.
    Ltac mytac :=
      repeat
        match goal with
        | Hsub : TELemmas.submap ?E1 ?E2,
          Hdef : is_true (are_defined (vars_atom ?a) ?E1)
          |- context f [atyp ?a ?E2] =>
          rewrite -(atyp_submap Hsub Hdef)
        | Hsub : TELemmas.submap ?E1 ?E2,
          Hdef : is_true (are_defined (vars_atom ?a) ?E1),
          H : context f [atyp ?a ?E2] |- _ =>
          rewrite -(atyp_submap Hsub Hdef) in H
        | H : ?p |- ?p => assumption
      end.
    - apply: EImullU; last assumption. by mytac.
    - apply: EImullS; last assumption. by mytac.
    - apply: EImullU; last assumption. by mytac.
    - apply: EImullS; last assumption. by mytac.
    - apply: EImuljU; last assumption. by mytac.
    - apply: EImuljS; last assumption. by mytac.
    - apply: EImuljU; last assumption. by mytac.
    - apply: EImuljS; last assumption. by mytac.
    - apply: EIsplitU; last assumption. by mytac.
    - apply: EIsplitS; last assumption. by mytac.
    - apply: EIsplitU; last assumption. by mytac.
    - apply: EIsplitS; last assumption. by mytac.
    - apply: EIcast. by mytac.
    - apply: EIcast. by mytac.
    - apply: EIvpc. by mytac.
    - apply: EIvpc. by mytac.
    - apply: EIassume. apply/(submap_eval_bexp Hsub H). assumption.
    - apply: EIassume. apply/(submap_eval_bexp Hsub H). assumption.
  Qed.

  Lemma submap_eval_program E1 E2 p s t :
    TELemmas.submap E1 E2 -> well_formed_program E1 p ->
    eval_program E1 p s t <-> eval_program E2 p s t.
  Proof.
    elim: p E1 E2 s t => [| i p IH] E1 E2 s t /=.
    - move=> _ _. split; move=> Hev; inversion_clear Hev; exact: Enil.
    - move=> Hsub /andP [Hwf_Ei Hwf_iEp].
      move: (well_formed_instr_well_defined Hwf_Ei) => Hwd_Ei.
      split; move=> Hev; inversion_clear Hev.
      + apply: (@Econs _ _ _ _ t0).
        * apply/(submap_eval_instr s t0 Hsub Hwd_Ei). assumption.
        * apply/(IH (instr_succ_typenv i E1) _ _ _
                    (submap_instr_succ_typenv Hwf_Ei Hsub) Hwf_iEp).
          assumption.
      + apply: (@Econs _ _ _ _ t0).
        * apply/(submap_eval_instr s t0 Hsub Hwd_Ei). assumption.
        * apply/(IH (instr_succ_typenv i E1) _ _ _
                    (submap_instr_succ_typenv Hwf_Ei Hsub) Hwf_iEp).
          assumption.
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
    - (* Icmov *) move=> v c a1 a2 _. case H: (to_bool (eval_atom c s)).
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
    - (* Imull *) move=> vh vl a1 a2 _. case H: (is_signed (atyp a1 te)).
      + eexists. apply: (EImullS H). exact: S.Upd2_upd2.
      + move/idP/negP: H=> H. rewrite not_signed_is_unsigned in H. eexists.
        apply: (EImullU H). exact: S.Upd2_upd2.
    - (* Imulj *) move=> v a1 a2 _. case H: (is_signed (atyp a1 te)).
      + eexists. apply: (EImuljS H). exact: S.Upd_upd.
      + move/idP/negP: H=> H. rewrite not_signed_is_unsigned in H. eexists.
        apply: (EImuljU H). exact: S.Upd_upd.
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
  Proof. exact: S.conform_submap. Qed.

  Lemma conform_size_eval_atom te s a :
    VS.subset (vars_atom a) (vars_env te) -> S.conform s te ->
    size_matched_atom a ->
    size (eval_atom a s) = Typ.sizeof_typ (atyp a te).
  Proof.
    case: a => /=.
    - move => v. rewrite VSLemmas.subset_singleton => /memenvP Hmem Hcon _.
      rewrite -(S.conform_mem Hcon Hmem). exact: TE.vtyp_vsize.
    - move => t b _ _ H. exact: (eqP H).
  Qed.

  Lemma size_eval_atom_asize te a s :
    VS.subset (vars_atom a) (vars_env te) -> S.conform s te ->
    size_matched_atom a ->
    size (eval_atom a s) = asize a te.
  Proof.
    move => Hsub Hcon Hsm. rewrite (conform_size_eval_atom Hsub Hcon Hsm).
    reflexivity.
  Qed.

  Lemma tbit_var_size E s v :
    S.conform s E -> TE.mem v E -> TE.vtyp v E = Tbit -> size (S.acc v s) = 1.
  Proof.
    move=> Hco Hmem Htyp. rewrite -(S.conform_mem Hco Hmem).
    rewrite TE.vtyp_vsize Htyp. reflexivity.
  Qed.

  Lemma tbit_var_singleton E s v :
    S.conform s E -> TE.mem v E -> TE.vtyp v E = Tbit ->
    exists b, S.acc v s = [:: b].
  Proof.
    move=> Hco Hmem Htyp. move: (tbit_var_size Hco Hmem Htyp).
    clear Hco Hmem Htyp. case: (S.acc v s) => [| b1 [| b2 bs]] //=.
    move=> _; by exists b1.
  Qed.

  Lemma tbit_atom_size E s a :
    S.conform s E -> size_matched_atom a -> atyp a E = Typ.Tbit ->
    VS.subset (vars_atom a) (vars_env E) ->
    size (eval_atom a s) = 1.
  Proof.
    move=> Hco Hsm Htyp Hsub. move: (size_eval_atom_asize Hsub Hco Hsm) => Hsc.
    rewrite /asize Htyp /= in Hsc. exact: Hsc.
  Qed.

  Lemma tbit_atom_singleton E s a :
    S.conform s E -> size_matched_atom a -> atyp a E = Typ.Tbit ->
    VS.subset (vars_atom a) (vars_env E) ->
    exists b, eval_atom a s = [:: b].
  Proof.
    move=> Hco Hsm Htyp Hsub. move: (tbit_atom_size Hco Hsm Htyp Hsub).
    clear Hco Htyp Hsub. case: (eval_atom a s) => [| b1 [| b2 bs]] //=.
    move=> _. by exists b1.
  Qed.

  Lemma size_eval_atom_same te s a0 a1 :
    S.conform s te -> size_matched_atom a0 -> size_matched_atom a1 ->
    VS.subset (vars_atom a0) (vars_env te) ->
    VS.subset (vars_atom a1) (vars_env te) ->
    sizeof_typ (atyp a0 te) = sizeof_typ (atyp a1 te) ->
    size (eval_atom a0 s) = size (eval_atom a1 s) .
  Proof .
    move => Hcon Hsm0 Hsm1 Hsub0 Hsub1 Hatypeq .
    move : (conform_size_eval_atom Hsub0 Hcon Hsm0)
             (conform_size_eval_atom Hsub1 Hcon Hsm1) .
    rewrite Hatypeq. by move=> -> ->.
  Qed .

  Lemma conform_eval_succ_typenv_Imov te t a s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Imov t a) ->
    well_typed_instr te (Imov t a) ->
    eval_instr te (Imov t a) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Imov t a) te).
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env => Hdef Hsm Hev.
    inversion_clear Hev. apply : (conform_Upd _ Hcon H).
      by rewrite (size_eval_atom_asize
                    Hdef Hcon (well_typed_atom_size_matched Hsm)).
  Qed.

  Lemma conform_eval_succ_typenv_Ishl te t a n s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ishl t a n) ->
    well_typed_instr te (Ishl t a n) ->
    eval_instr te (Ishl t a n) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ishl t a n) te) .
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env =>
    Hdef /andP [Hsm _] Hev . inversion_clear Hev .
    apply : (conform_Upd _ Hcon H) .
      by rewrite size_shlB
                 (size_eval_atom_asize Hdef Hcon
                                         (well_typed_atom_size_matched Hsm)) .
  Qed .

  Lemma conform_eval_succ_typenv_Icshl te t t0 a a0 n s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Icshl t t0 a a0 n) ->
    well_typed_instr te (Icshl t t0 a a0 n) ->
    eval_instr te (Icshl t t0 a a0 n) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Icshl t t0 a a0 n) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] /andP [/andP [/andP [_ Hsm0] Hsm1] _] Hev .
    inversion_clear Hev .
    apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + by rewrite size_high
                 (size_eval_atom_asize Hdef0 Hcon
                                         (well_typed_atom_size_matched Hsm0)) .
    + by rewrite size_shrB size_low
                 (size_eval_atom_asize Hdef1 Hcon
                                         (well_typed_atom_size_matched Hsm1)).
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
    /andP [/andP [Hdefc Hdef0] Hdef1]
     /andP [/andP [/andP [/andP [_ Hty] Hsm0] Hsm1] _] Hev.
    inversion_clear Hev; apply : (conform_Upd _ Hcon H0);
      [ by rewrite (size_eval_atom_asize Hdef0 Hcon
                                           (well_typed_atom_size_matched Hsm0))
      | rewrite (size_eval_atom_asize Hdef1 Hcon
                                        (well_typed_atom_size_matched Hsm1)) //;
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
    rewrite /Typ.compatible in Hty . move/andP: Hty=> [Hty Hsm].
    inversion_clear Hev .
    apply : (conform_Upd _ Hcon H) => // .
      by rewrite size_invB (eqP Hty)
                 (size_eval_atom_asize
                    Hdef Hcon (well_typed_atom_size_matched Hsm)).
  Qed .

  Lemma conform_eval_succ_typenv_Iadd te t a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iadd t a a0) ->
    well_typed_instr te (Iadd t a a0) ->
    eval_instr te (Iadd t a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iadd t a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_addB
            (size_eval_atom_asize Hdef0 Hcon
                                    (well_typed_atom_size_matched Hsm0)).
    rewrite (size_eval_atom_asize
               Hdef1 Hcon (well_typed_atom_size_matched Hsm1)).
      by rewrite /asize !(eqP Hty) minnE subKn.
  Qed .

  Lemma conform_eval_succ_typenv_Iadds te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iadds t t0 a a0) ->
    well_typed_instr te (Iadds t t0 a a0) ->
    eval_instr te (Iadds t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iadds t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + (rewrite size_addB
              (size_eval_atom_asize
                 Hdef0 Hcon (well_typed_atom_size_matched Hsm0)));
        (rewrite (size_eval_atom_asize
                    Hdef1 Hcon (well_typed_atom_size_matched Hsm1)));
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
    /andP [/andP [Hdef0 Hdef1] Hdefc] /andP
     [/andP [/andP [/andP [Hty _] Hsm0] Hsm1] _] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite /adcB /full_adder size_full_adder_zip
                 (size_eval_atom_asize
                    Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
                 (size_eval_atom_asize
                    Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [/andP [/andP [Hneq Hdef0] Hdef1] Hdefc] /andP
     [/andP [/andP [/andP [Hty _] Hsm0] Hsm1] _] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite /adcB /full_adder size_full_adder_zip
                 (size_eval_atom_asize
                    Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
                 (size_eval_atom_asize
                    Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [Hdef0 Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite size_subB
                 (size_eval_atom_asize
                    Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
                 (size_eval_atom_asize
                    Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [/andP [Hneq Hdef0] Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite
           size_adcB size_invB
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
           (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [/andP [Hneq Hdef0] Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite
           size_subB
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
           (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [/andP [Hdef0 Hdef1] Hdefc] /andP
     [/andP [/andP [/andP [Hty _] Hsm0] Hsm1] _] Hev.
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite /adcB /full_adder size_full_adder_zip
         size_invB
            (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
            (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [/andP [/andP [Hneq Hdef0] Hdef1] Hdefc] /andP
     [/andP [/andP [/andP [Hty _] Hsm0] Hsm1] _] Hev.
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon) .
    + done .
    + by rewrite /adcB /full_adder size_full_adder_zip
         size_invB
            (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
            (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [/andP [Hdef0 Hdef1] Hdefc] /andP
     [/andP [/andP [/andP [Hty _] Hsm0] Hsm1] _] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite
           size_sbbB
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
           (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [/andP [/andP [Hneq Hdef0] Hdef1] Hdefc] /andP
          [/andP [/andP [/andP [Hty _] Hsm0] Hsm1] _] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H Hcon); first done .
      by rewrite
           size_sbbB
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
           (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
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
    /andP [Hdef0 Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
      by rewrite
           size_mulB
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0)).
  Qed .

  Lemma conform_eval_succ_typenv_Imull te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Imull t t0 a a0) ->
    well_typed_instr te (Imull t t0 a a0) ->
    eval_instr te (Imull t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Imull t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [/andP [Hneq Hdef0] Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ H0 Hcon);
      [ by rewrite
             size_high
             (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
      | rewrite
          size_low
          (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
      | by rewrite
             size_high
             (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
      | rewrite
          size_low
          (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))];
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
    /andP [Hdef0 Hdef1] /andP [/andP [Hty Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H0);
      rewrite size_mulB ?size_zext ?size_sext
              (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
              /asize /Typ.double_typ;
      by case (atyp a te) => /= // n; rewrite mul2n addnn // .
  Qed .

  Lemma conform_eval_succ_typenv_Isplit te t t0 a n s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Isplit t t0 a n) ->
    well_typed_instr te (Isplit t t0 a n) ->
    eval_instr te (Isplit t t0 a n) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Isplit t t0 a n) te) .
  Proof .
    move => Hcon /=; rewrite are_defined_subset_env =>
    /andP [Hneq Hdef] /andP [Hsm _] Hev .
    inversion_clear Hev; apply: (conform_Upd2 Hneq _ _ H0 Hcon);
      [ by rewrite
             size_shrB
             (size_eval_atom_asize Hdef Hcon (well_typed_atom_size_matched Hsm))
      | by rewrite
             size_shrB size_shlB size_unsigned_typ
             (size_eval_atom_asize Hdef Hcon (well_typed_atom_size_matched Hsm))
      | by rewrite
             size_sarB
             (size_eval_atom_asize Hdef Hcon (well_typed_atom_size_matched Hsm))
      | by rewrite
             size_shrB size_shlB size_unsigned_typ
             (size_eval_atom_asize Hdef Hcon (well_typed_atom_size_matched Hsm)) ].
  Qed.

  Lemma conform_eval_succ_typenv_Iand te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iand t t0 a a0) ->
    well_typed_instr te (Iand t t0 a a0) ->
    eval_instr te (Iand t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Iand t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [/andP [/andP [Hty1 Hty2] Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite /compatible in Hty1 Hty2.
      by rewrite
           size_lift
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
           (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
           /asize -(eqP Hty1) -(eqP Hty2) maxnn.
  Qed .

  Lemma conform_eval_succ_typenv_Ior te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ior t t0 a a0) ->
    well_typed_instr te (Ior t t0 a a0) ->
    eval_instr te (Ior t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ior t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [/andP [/andP [Hty1 Hty2] Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite /compatible in Hty1 Hty2.
      by rewrite
           size_lift
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
           (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
           /asize -(eqP Hty1) -(eqP Hty2) maxnn .
  Qed .

  Lemma conform_eval_succ_typenv_Ixor te t t0 a a0 s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Ixor t t0 a a0) ->
    well_typed_instr te (Ixor t t0 a a0) ->
    eval_instr te (Ixor t t0 a a0) s1 s2 ->
    S.conform s2 (instr_succ_typenv (Ixor t t0 a a0) te) .
  Proof .
    move => Hcon /=; rewrite 2!are_defined_subset_env =>
    /andP [Hdef0 Hdef1] /andP [/andP [/andP [Hty1 Hty2] Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite /compatible in Hty1 Hty2.
      by rewrite
           size_lift
           (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
           (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
           /asize -(eqP Hty1) -(eqP Hty2) maxnn .
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
    /andP [Hdef0 Hdef1] /andP [/andP [/andP [Hun Hty] Hsm0] Hsm1] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_cat
            (size_eval_atom_asize Hdef0 Hcon (well_typed_atom_size_matched Hsm0))
            (size_eval_atom_asize Hdef1 Hcon (well_typed_atom_size_matched Hsm1))
            /asize -(eqP Hty) /Typ.double_typ .
      by ((case (atyp a te) => /= n); rewrite mul2n addnn).
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


  Section BvsEqi.

    Definition bvs_eqi (E : TE.env) (s1 s2 : S.t) :=
      forall x, TE.mem x E -> S.acc x s1 = S.acc x s2.

    Lemma bvs_eqi_refl E s : bvs_eqi E s s.
    Proof. move=> *; reflexivity. Qed.

    Lemma bvs_eqi_sym E s1 s2 : bvs_eqi E s1 s2 -> bvs_eqi E s2 s1.
    Proof. move=> Heqi x Hx. exact: (Logic.eq_sym (Heqi x Hx)). Qed.

    Lemma bvs_eqi_trans E s1 s2 s3 :
      bvs_eqi E s1 s2 -> bvs_eqi E s2 s3 -> bvs_eqi E s1 s3.
    Proof.
      move=> H12 H23 x Hx. rewrite (H12 x Hx) (H23 x Hx). reflexivity.
    Qed.

    Lemma bvs_eqi_submap E1 E2 s1 s2 :
      TELemmas.submap E1 E2 -> bvs_eqi E2 s1 s2 -> bvs_eqi E1 s1 s2.
    Proof.
      move=> Hsubm Heqi x Hx. exact: (Heqi x (TELemmas.submap_mem Hsubm Hx)).
    Qed.

    Lemma bvs_eqi_conform E s1 s2 :
      bvs_eqi E s1 s2 -> S.conform s1 E -> S.conform s2 E.
    Proof.
      move=> Heqi Hco. apply: S.conform_def. move=> x Hmem.
      rewrite (S.conform_mem Hco Hmem). rewrite (Heqi x Hmem). reflexivity.
    Qed.

    Lemma bvs_eqi_acc2z E s1 s2 x :
      bvs_eqi E s1 s2 -> TE.mem x E -> acc2z E x s1 = acc2z E x s2.
    Proof.
      move=> Heqi Hmem. rewrite /acc2z. rewrite (Heqi x Hmem). reflexivity.
    Qed.

    Lemma bvs_eqi_eval_atom E s1 s2 a :
      bvs_eqi E s1 s2 -> are_defined (vars_atom a) E ->
      eval_atom a s1 = eval_atom a s2.
    Proof.
      move=> Heqi. case: a => //=. move=> x. rewrite are_defined_singleton => Hdef.
      exact: (Heqi x Hdef).
    Qed.

    Lemma bvs_eqi_Upd_eqi E s1 s2 t1 t2 x v :
      bvs_eqi E s1 t1 -> S.Upd x v s1 s2 -> S.Upd x v t1 t2 ->
      bvs_eqi E s2 t2.
    Proof.
      move=> Heqi Hupd1 Hupd2 y Hmemy. case Hyx: (y == x).
      - rewrite (S.acc_Upd_eq Hyx Hupd1) (S.acc_Upd_eq Hyx Hupd2). reflexivity.
      - move/idP/negP: Hyx => Hyx.
        rewrite (S.acc_Upd_neq Hyx Hupd1) (S.acc_Upd_neq Hyx Hupd2).
        exact: (Heqi y Hmemy).
    Qed.

    Lemma bvs_eqi_Upd2_eqi E s1 s2 t1 t2 x1 v1 x2 v2 :
      bvs_eqi E s1 t1 -> S.Upd2 x1 v1 x2 v2 s1 s2 -> S.Upd2 x1 v1 x2 v2 t1 t2 ->
      bvs_eqi E s2 t2.
    Proof.
      move=> Heqi Hupd1 Hupd2 y Hmemy. case Hyx2: (y == x2).
      - rewrite (S.acc_Upd2_eq2 Hyx2 Hupd1) (S.acc_Upd2_eq2 Hyx2 Hupd2).
        reflexivity.
      - move/idP/negP: Hyx2 => Hyx2. case Hyx1: (y == x1).
        + rewrite (S.acc_Upd2_eq1 Hyx1 Hyx2 Hupd1) (S.acc_Upd2_eq1 Hyx1 Hyx2 Hupd2).
          reflexivity.
        + move/idP/negP: Hyx1 => Hyx1.
          rewrite (S.acc_Upd2_neq Hyx1 Hyx2 Hupd1) (S.acc_Upd2_neq Hyx1 Hyx2 Hupd2).
          exact: (Heqi y Hmemy).
    Qed.

    Lemma bvs_eqi_add_Upd_eqi E s1 s2 t1 t2 x v ty :
      bvs_eqi E s1 t1 -> S.Upd x v s1 s2 -> S.Upd x v t1 t2 ->
      bvs_eqi (TE.add x ty E) s2 t2.
    Proof.
      move=> Heqi Hupd1 Hupd2 y Hmemy. case Hyx: (y == x).
      - rewrite (S.acc_Upd_eq Hyx Hupd1) (S.acc_Upd_eq Hyx Hupd2). reflexivity.
      - move/idP/negP: Hyx => Hyx.
        rewrite (S.acc_Upd_neq Hyx Hupd1) (S.acc_Upd_neq Hyx Hupd2).
        move/negPn: Hyx => Hyx. rewrite (TELemmas.mem_add_neq Hyx) in Hmemy.
        exact: (Heqi y Hmemy).
    Qed.

    Lemma bvs_eqi_add_Upd2_eqi E s1 s2 t1 t2 x1 v1 ty1 x2 v2 ty2 :
      bvs_eqi E s1 t1 -> S.Upd2 x1 v1 x2 v2 s1 s2 -> S.Upd2 x1 v1 x2 v2 t1 t2 ->
      bvs_eqi (TE.add x2 ty2 (TE.add x1 ty1 E)) s2 t2.
    Proof.
      move=> Heqi Hupd1 Hupd2 y Hmemy. case Hyx2: (y == x2).
      - rewrite (S.acc_Upd2_eq2 Hyx2 Hupd1) (S.acc_Upd2_eq2 Hyx2 Hupd2).
        reflexivity.
      - move/idP/negP: Hyx2 => Hyx2. case Hyx1: (y == x1).
        + rewrite (S.acc_Upd2_eq1 Hyx1 Hyx2 Hupd1) (S.acc_Upd2_eq1 Hyx1 Hyx2 Hupd2).
          reflexivity.
        + move/idP/negP: Hyx1 => Hyx1.
          rewrite (S.acc_Upd2_neq Hyx1 Hyx2 Hupd1) (S.acc_Upd2_neq Hyx1 Hyx2 Hupd2).
          move/negPn: Hyx1 => Hyx1. move/negPn: Hyx2 => Hyx2.
          rewrite (TELemmas.mem_add_neq Hyx2) (TELemmas.mem_add_neq Hyx1) in Hmemy.
          exact: (Heqi y Hmemy).
    Qed.

    Lemma bvs_eqi_eval_eexp E e s1 s2 :
      are_defined (vars_eexp e) E -> bvs_eqi E s1 s2 ->
      eval_eexp e E s1 = eval_eexp e E s2.
    Proof.
      elim: e => //=.
      - move=> v Hdef Heqi. rewrite are_defined_singleton in Hdef.
        move/memdefP: Hdef => Hmem. exact: (bvs_eqi_acc2z Heqi Hmem).
      - move=> op e IH Hdef Heqi. rewrite (IH Hdef Heqi). reflexivity.
      - move=> op e1 IH1 e2 IH2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2].
        rewrite (IH1 Hdef1 Heqi) (IH2 Hdef2 Heqi). reflexivity.
      - move=> e IH n Hdef Heqi. rewrite (IH Hdef Heqi). reflexivity.
    Qed.

    Lemma bvs_eqi_eval_eexps E es s1 s2 :
      are_defined (vars_eexps es) E -> bvs_eqi E s1 s2 ->
      eval_eexps es E s1 = eval_eexps es E s2.
    Proof.
      elim: es => [| e es IH] //=. rewrite are_defined_union.
      move/andP => [Hdef1 Hdef2] Heqi. rewrite (bvs_eqi_eval_eexp Hdef1 Heqi).
      rewrite (IH Hdef2 Heqi). reflexivity.
    Qed.

    Lemma bvs_eqi_eval_ebexp E e s1 s2 :
      are_defined (vars_ebexp e) E -> bvs_eqi E s1 s2 ->
      eval_ebexp e E s1 <-> eval_ebexp e E s2.
    Proof.
      elim: e => //=.
      - move=> e1 e2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2].
        rewrite (bvs_eqi_eval_eexp Hdef1 Heqi) (bvs_eqi_eval_eexp Hdef2 Heqi). done.
      - move=> e1 e2 ms Hdef Heqi. repeat rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 /andP [Hdef2 Hdefms]].
        rewrite (bvs_eqi_eval_eexp Hdef1 Heqi) (bvs_eqi_eval_eexp Hdef2 Heqi)
                (bvs_eqi_eval_eexps Hdefms Heqi). done.
      - move=> e1 IH1 e2 IH2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2]. move: (IH1 Hdef1 Heqi) (IH2 Hdef2 Heqi).
        tauto.
    Qed.

    Lemma bvs_eqi_eval_rexp E e s1 s2 :
      are_defined (vars_rexp e) E -> bvs_eqi E s1 s2 ->
      eval_rexp e s1 = eval_rexp e s2.
    Proof.
      elim: e => //=.
      - move=> x Hdef Heqi. rewrite are_defined_singleton in Hdef.
        move/memdefP: Hdef => Hmem. exact: (Heqi x Hmem).
      - move=> _ op e IH Hdef Heqi. rewrite (IH Hdef Heqi). reflexivity.
      - move=> _ op e1 IH1 e2 IH2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2]. rewrite (IH1 Hdef1 Heqi) (IH2 Hdef2 Heqi).
        reflexivity.
      - move=> _ e IH n Hdef Heqi. rewrite (IH Hdef Heqi). reflexivity.
      - move=> _ e IH n Hdef Heqi. rewrite (IH Hdef Heqi). reflexivity.
    Qed.

    Lemma bvs_eqi_eval_rbexp E e s1 s2 :
      are_defined (vars_rbexp e) E -> bvs_eqi E s1 s2 ->
      eval_rbexp e s1 <-> eval_rbexp e s2.
    Proof.
      elim: e => //=.
      - move=> _ e1 e2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2].
        rewrite (bvs_eqi_eval_rexp Hdef1 Heqi) (bvs_eqi_eval_rexp Hdef2 Heqi). done.
      - move=> _ op e1 e2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2].
        rewrite (bvs_eqi_eval_rexp Hdef1 Heqi) (bvs_eqi_eval_rexp Hdef2 Heqi). done.
      - move=> e IH Hdef Heqi. move: (IH Hdef Heqi)=> H. by iffb_tac.
      - move=> e1 IH1 e2 IH2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2]. move: (IH1 Hdef1 Heqi) (IH2 Hdef2 Heqi) => H1 H2.
        by iffb_tac.
      - move=> e1 IH1 e2 IH2 Hdef Heqi. rewrite are_defined_union in Hdef.
        move/andP: Hdef => [Hdef1 Hdef2]. move: (IH1 Hdef1 Heqi) (IH2 Hdef2 Heqi) => H1 H2.
        by iffb_tac.
    Qed.

    Lemma bvs_eqi_eval_bexp E e s1 s2 :
      are_defined (vars_bexp e) E -> bvs_eqi E s1 s2 ->
      eval_bexp e E s1 <-> eval_bexp e E s2.
    Proof.
      case: e => [e r]. rewrite /vars_bexp /=.
      rewrite are_defined_union => /andP [Hdefe Hdefr] Heqi.
      rewrite /eval_bexp /=.
      move: (bvs_eqi_eval_ebexp Hdefe Heqi) => He.
      move: (bvs_eqi_eval_rbexp Hdefr Heqi) => Hr. tauto.
    Qed.

    Ltac mytac ::=
      repeat
        match goal with
        | H : is_true (_ && _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/andP: H => [H1 H2]
        | Heqi : bvs_eqi _ ?s1 _,
          Hev : eval_instr _ _ ?s1 _ |- _ =>
          let H := fresh "Heqi" in
          move: Heqi; inversion_clear Hev; move=> H
        | Hdef : is_true (are_defined (vars_atom ?a) ?E),
          Heqi : bvs_eqi ?E ?s1 ?s2
          |- context f [eval_atom ?a ?s1] =>
          rewrite (bvs_eqi_eval_atom Heqi Hdef)
        | Hdef : is_true (are_defined (vars_atom ?a) ?E),
          Heqi : bvs_eqi ?E ?s1 ?s2,
          H : context f [eval_atom ?a ?s1] |- _ =>
          rewrite (bvs_eqi_eval_atom Heqi Hdef) in H
        | Heqi : bvs_eqi ?E ?s1 ?t1,
          Hupd : S.Upd ?x ?v ?s1 ?s2
          |- exists _ : S.t, _ =>
          exists (S.upd x v t1)
        | Heqi : bvs_eqi ?E ?s1 ?t1,
          Hupd : S.Upd2 ?x1 ?v1 ?x2 ?v2 ?s1 ?s2
          |- exists _ : S.t, _ =>
          exists (S.upd2 x1 v1 x2 v2 t1)
        | |- _ /\ _ => split
        | Heqi : bvs_eqi ?E ?s1 ?t1,
          Hupd : S.Upd ?x ?v ?s1 ?s2
          |- bvs_eqi (TE.add ?x ?ty ?E) ?s2 (S.upd ?x ?v ?t1) =>
          exact: (bvs_eqi_add_Upd_eqi Heqi Hupd (S.Upd_upd x v t1))
        | Heqi : bvs_eqi ?E ?s1 ?t1,
          Hupd : S.Upd2 ?x1 ?v1 ?x2 ?v2 ?s1 ?s2
          |- bvs_eqi (TE.add ?x2 ?ty2 (TE.add ?x1 ?ty1 ?E)) ?s2
                     (S.upd2 ?x1 ?v1 ?x2 ?v2 ?t1) =>
          exact: (bvs_eqi_add_Upd2_eqi Heqi Hupd (S.Upd2_upd2 x1 v1 x2 v2 t1))
        end.

    Lemma bvs_eqi_eval_instr_eqi E i s1 s2 t1 :
      well_defined_instr E i -> bvs_eqi E s1 t1 -> eval_instr E i s1 s2 ->
      exists t2, eval_instr E i t1 t2 /\ bvs_eqi (instr_succ_typenv i E) s2 t2.
    Proof.
      case: i => /=; try (move=> *; mytac; by eauto with dsl).
      (* Iassume *)
      move=> e Hdef Heqi Hev. move: Heqi. inversion_clear Hev => Heqi.
      exists t1. split; last assumption. apply: EIassume.
      apply/(bvs_eqi_eval_bexp Hdef Heqi). assumption.
    Qed.

  End BvsEqi.


  (* Update state values according to an environment such that
     it conforms to the environment*)
  Section ForceConform.

    Fixpoint force_conform_vars E vs s :=
      match vs with
      | [::] => s
      | v::vs => S.upd v (zeros (TE.vsize v E)) (force_conform_vars E vs s)
      end.

    Lemma force_conform_vars_notin E vs s v :
      v \notin vs -> S.acc v (force_conform_vars E vs s) = S.acc v s.
    Proof.
      elim: vs => [| x xs IH] //=. rewrite in_cons negb_or.
      move/andP=> [Hne Hnotin]. rewrite (S.acc_upd_neq Hne). rewrite (IH Hnotin).
      reflexivity.
    Qed.

    Lemma force_conform_vars_in E vs s v :
      v \in vs -> S.acc v (force_conform_vars E vs s) = zeros (TE.vsize v E).
    Proof.
      elim: vs => [| x xs IH] //=. rewrite in_cons. case H: (v == x) => //=.
      - move=> _. rewrite (S.acc_upd_eq H). rewrite (eqP H). reflexivity.
      - move=> Hin. move/idP/negP: H => H. rewrite (S.acc_upd_neq H).
        exact: (IH Hin).
    Qed.

    Lemma force_conform_vars_incl E vs1 vs2 s :
      incl vs1 vs2 -> incl vs2 vs1 ->
      S.Equal (force_conform_vars E vs1 s) (force_conform_vars E vs2 s).
    Proof.
      move=> H12 H21. apply/S.Equal_def. move=> v. case H1: (v \in vs1).
      - rewrite (force_conform_vars_in E s H1). move/Seqs.in_In: H1 => H1.
        move: (H12 _ H1). move/Seqs.in_In => H2.
        rewrite (force_conform_vars_in E s H2). reflexivity.
      - move/idP/negP: H1 => H1. rewrite (force_conform_vars_notin E s H1).
        have H2: (v \notin vs2).
        { apply/negP => H2. move/negP: H1; apply. apply/Seqs.in_In.
          apply: H21. apply/Seqs.in_In. exact: H2. }
        rewrite (force_conform_vars_notin E s H2). reflexivity.
    Qed.

    Lemma force_conform_vars_set_equal E vs1 vs2 s :
      VS.Equal vs1 vs2 ->
      S.Equal (force_conform_vars E (VS.elements vs1) s)
              (force_conform_vars E (VS.elements vs2) s).
    Proof.
      move=> Heq. move/(VSLemmas.P.double_inclusion _ _): Heq. move=> [Hsub1 Hsub2].
      move: (VSLemmas.Subset_incl Hsub1) (VSLemmas.Subset_incl Hsub2).
      exact: force_conform_vars_incl.
    Qed.

    Lemma force_conform_vars_env E s :
      S.conform (force_conform_vars E (VS.elements (vars_env E)) s) E.
    Proof.
      apply: S.conform_def. move=> x Hmem. rewrite force_conform_vars_in.
      - rewrite size_zeros. reflexivity.
      - rewrite vars_env_mem in Hmem. exact: (VSLemmas.mem_in_elements Hmem).
    Qed.

    Definition force_conform (E1 E2 : TE.env) (s : S.t) : S.t :=
      force_conform_vars E2 (VS.elements (VS.diff (vars_env E2) (vars_env E1))) s.

    Lemma force_conform_acc_mem1 E1 E2 s v :
      is_defined v E1 -> S.acc v (force_conform E1 E2 s) = S.acc v s.
    Proof.
      rewrite /is_defined /force_conform. move=> Hmem1.
      move: (VSLemmas.diff_b (vars_env E2) (vars_env E1) v).
      rewrite -(vars_env_mem v E1) Hmem1 andbF => Hmem_diff.
      have: ~~ (v \in (VS.elements (VS.diff (vars_env E2) (vars_env E1)))).
      { apply/negP => H. move/negP: Hmem_diff; apply.
        exact: (VSLemmas.in_elements_mem H). }
      move=> {Hmem_diff Hmem1}.
      move: {E1} (VS.elements (VS.diff (vars_env E2) (vars_env E1))).
      elim => [| hd tl IH] //=.
      rewrite in_cons negb_or. move/andP=> [Hhd Htl].
      rewrite (S.acc_upd_neq Hhd). exact: (IH Htl).
    Qed.

    Lemma force_conform_acc_mem2 E1 E2 s v :
      ~~ is_defined v E1 -> is_defined v E2 ->
      S.acc v (force_conform E1 E2 s) = zeros (TE.vsize v E2).
    Proof.
      rewrite /is_defined /force_conform. move=> /negPf Hmem1 Hmem2.
      move: (VSLemmas.diff_b (vars_env E2) (vars_env E1) v).
      rewrite -!vars_env_mem Hmem1 Hmem2 /=.
      move=> {Hmem1 Hmem2} Hmem. move: (VSLemmas.mem_in_elements Hmem).
      move: {Hmem E1} (VS.elements (VS.diff (vars_env E2) (vars_env E1))).
      elim => [| hd tl IH] //=. rewrite in_cons. case Hvhd: (v == hd) => /=.
      - move=> _. rewrite (S.acc_upd_eq Hvhd). rewrite (eqP Hvhd). reflexivity.
      - move=> Htl. move/idP/negP: Hvhd => Hvhd. rewrite (S.acc_upd_neq Hvhd).
        exact: (IH Htl).
    Qed.

    Lemma force_conform_acc_not_mem E1 E2 s v :
      ~~ is_defined v E1 -> ~~ is_defined v E2 ->
      S.acc v (force_conform E1 E2 s) = S.acc v s.
    Proof.
      rewrite /is_defined /force_conform. move=> /negPf Hmem1 /negPf Hmem2.
      move: (VSLemmas.diff_b (vars_env E2) (vars_env E1) v).
      rewrite -!vars_env_mem Hmem1 Hmem2 /=. move=> Hmem.
      have: ~~ (v \in (VS.elements (VS.diff (vars_env E2) (vars_env E1)))).
      { apply/negP => H. move/negP: Hmem; apply.
        exact: (VSLemmas.in_elements_mem H). }
      move=> {Hmem Hmem1 Hmem2}.
      move: {E1} (VS.elements (VS.diff (vars_env E2) (vars_env E1))).
      elim => [| hd tl IH] //=.
      rewrite in_cons negb_or. move/andP=> [Hhd Htl].
      rewrite (S.acc_upd_neq Hhd). exact: (IH Htl).
    Qed.

    Lemma force_conform_conform E1 E2 s :
      TELemmas.submap E1 E2 -> S.conform s E1 ->
      S.conform (force_conform E1 E2 s) E2.
    Proof.
      move=> Hsub Hco. apply: S.conform_def. move=> x Hmem2.
      case Hmem1: (TE.mem x E1).
      - rewrite (force_conform_acc_mem1 _ _ Hmem1).
        rewrite -(submap_vsize Hsub Hmem1). exact: (S.conform_mem Hco Hmem1).
      - move/idP/negP: Hmem1 => Hmem1.
        rewrite (force_conform_acc_mem2 s Hmem1 Hmem2).
        rewrite size_zeros. reflexivity.
    Qed.

    Lemma force_conform_eval_eexp E1 E2 e s :
       TELemmas.submap E1 E2 -> are_defined (vars_eexp e) E1 ->
      eval_eexp e E2 (force_conform E1 E2 s) = eval_eexp e E1 s.
    Proof.
      move=> Hsub Hdef. rewrite -(submap_eval_eexp Hsub Hdef).
      elim: e Hdef => //=.
      - move=> v. rewrite are_defined_singleton => Hdef.
        rewrite /acc2z. rewrite (force_conform_acc_mem1 _ _ Hdef). reflexivity.
      - move=> op e IH Hdef. rewrite (IH Hdef). reflexivity.
      - move=> op e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
      - move=> e IH n Hdef. rewrite (IH Hdef). reflexivity.
    Qed.

    Lemma force_conform_eval_eexps E1 E2 es s :
       TELemmas.submap E1 E2 -> are_defined (vars_eexps es) E1 ->
      eval_eexps es E2 (force_conform E1 E2 s) = eval_eexps es E1 s.
    Proof.
      elim: es => [| e es IH] //=. rewrite are_defined_union.
      move=> Hsub /andP [Hdef1 Hdef2]. rewrite (force_conform_eval_eexp s Hsub Hdef1).
      rewrite (IH Hsub Hdef2). reflexivity.
    Qed.

    Lemma force_conform_eval_ebexp E1 E2 e s :
      TELemmas.submap E1 E2 -> are_defined (vars_ebexp e) E1 ->
      eval_ebexp e E2 (force_conform E1 E2 s) <-> eval_ebexp e E1 s.
    Proof.
      move=> Hsub. elim: e => //=.
      - move=> e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        rewrite (force_conform_eval_eexp _ Hsub Hdef1)
                (force_conform_eval_eexp _ Hsub Hdef2).
        done.
      - move=> e1 e2 ms.
        rewrite !are_defined_union => /andP [Hdef1 /andP [Hdef2 Hdefms]].
        rewrite (force_conform_eval_eexp _ Hsub Hdef1)
                (force_conform_eval_eexp _ Hsub Hdef2)
                (force_conform_eval_eexps _ Hsub Hdefms). done.
      - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        move: (IH1 Hdef1) (IH2 Hdef2) => [H1 H2] [H3 H4]. tauto.
    Qed.

    Lemma force_conform_eval_rexp E1 E2 e s :
      TELemmas.submap E1 E2 -> are_defined (vars_rexp e) E1 ->
      eval_rexp e (force_conform E1 E2 s) = eval_rexp e s.
    Proof.
      move=> Hsub. elim: e => //=.
      - move=> v. rewrite are_defined_singleton => Hdef.
        exact: (force_conform_acc_mem1 _ _ Hdef).
      - move=> _ op e IH Hdef. rewrite (IH Hdef). reflexivity.
      - move=> _ op e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
      - move=> _ e IH n Hdef. rewrite (IH Hdef). reflexivity.
      - move=> _ e IH n Hdef. rewrite (IH Hdef). reflexivity.
    Qed.

    Lemma force_conform_eval_rbexp E1 E2 e s :
      TELemmas.submap E1 E2 -> are_defined (vars_rbexp e) E1 ->
      eval_rbexp e (force_conform E1 E2 s) <-> eval_rbexp e s.
    Proof.
      move=> Hsub. elim: e => //=.
      - move=> _ e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        rewrite (force_conform_eval_rexp _ Hsub Hdef1)
                (force_conform_eval_rexp _ Hsub Hdef2). done.
      - move=> _ op e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        rewrite (force_conform_eval_rexp _ Hsub Hdef1)
                (force_conform_eval_rexp _ Hsub Hdef2). done.
      - move=> e IH Hdef. move: (IH Hdef) => H. by iffb_tac.
      - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        move: (IH1 Hdef1) (IH2 Hdef2) => H1 H2. by iffb_tac.
      - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
        move: (IH1 Hdef1) (IH2 Hdef2) => H1 H2. by iffb_tac.
    Qed.

    Lemma force_conform_bvs_eqi E1 E2 s :
      TELemmas.submap E1 E2 -> bvs_eqi E1 s (force_conform E1 E2 s).
    Proof.
      move=> Hsub. move=> x Hmemx. rewrite (force_conform_acc_mem1 _ _ Hmemx).
      reflexivity.
    Qed.

  End ForceConform.


  (* Spec splitting *)

  Definition split_espec (s : espec) : seq espec :=
    tmap (fun q =>
            {|
              esinputs := esinputs s;
              espre := espre s;
              esprog := esprog s;
              espost := q
            |}) (split_eand (espost s)).

  Definition split_rspec (s : rspec) : seq rspec :=
    tmap (fun q =>
            {|
              rsinputs := rsinputs s;
              rspre := rspre s;
              rsprog := rsprog s;
              rspost := q
            |}) (split_rand (rspost s)).

  Definition valid_especs (es : seq espec) : Prop :=
    forall s, In s es -> valid_espec s.

  Definition valid_rspecs (es : seq rspec) : Prop :=
    forall s, In s es -> valid_rspec s.

  Lemma split_espec_eand E f p e1 e2 :
    split_espec {| esinputs := E; espre := f; esprog := p; espost := Eand e1 e2 |}
    = split_espec {| esinputs := E; espre := f; esprog := p; espost := e1 |} ++
                  split_espec {| esinputs := E; espre := f; esprog := p; espost := e2 |}.
  Proof.
    rewrite /split_espec /=. rewrite !tmap_map map_cat. reflexivity.
  Qed.

  Lemma split_rspec_rand E f p e1 e2 :
    split_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := Rand e1 e2 |}
    = split_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := e1 |} ++
                  split_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := e2 |}.
  Proof.
    rewrite /split_rspec /=. rewrite !tmap_map map_cat. reflexivity.
  Qed.

  Lemma valid_especs_empty : valid_especs [::].
  Proof. move=> s Hin. apply: False_ind. exact: (List.in_nil Hin). Qed.

  Lemma valid_rspecs_empty : valid_rspecs [::].
  Proof. move=> s Hin. apply: False_ind. exact: (List.in_nil Hin). Qed.

  Lemma valid_especs_singleton s : valid_espec s <-> valid_especs [:: s].
  Proof.
    split; move=> H.
    - move=> ss. case => //=. move=> <-. assumption.
    - apply: H. left. reflexivity.
  Qed.

  Lemma valid_rspecs_singleton s : valid_rspec s <-> valid_rspecs [:: s].
  Proof.
    split; move=> H.
    - move=> ss. case => //=. move=> <-. assumption.
    - apply: H. left. reflexivity.
  Qed.

  Lemma valid_especs_cons1 s ss :
    valid_especs (s::ss) -> valid_espec s /\ valid_especs ss.
  Proof.
    move=> H; split.
    + apply: H. exact: in_eq.
    + move=> t Hin; apply: H. exact: (List.in_cons _ _ _ Hin).
  Qed.

  Lemma valid_especs_cons2 s ss :
    valid_espec s -> valid_especs ss -> valid_especs (s::ss).
  Proof.
    move=> Hs Hss t Hin. case: (in_inv Hin) => {}Hin.
    - subst. assumption.
    - exact: (Hss _ Hin).
  Qed.

  Lemma valid_rspecs_cons1 s ss :
    valid_rspecs (s::ss) -> valid_rspec s /\ valid_rspecs ss.
  Proof.
    move=> H; split.
    + apply: H. exact: in_eq.
    + move=> t Hin; apply: H. exact: (List.in_cons _ _ _ Hin).
  Qed.

  Lemma valid_rspecs_cons2 s ss :
    valid_rspec s -> valid_rspecs ss -> valid_rspecs (s::ss).
  Proof.
    move=> Hs Hss t Hin. case: (in_inv Hin) => {}Hin.
    - subst. assumption.
    - exact: (Hss _ Hin).
  Qed.

  Lemma valid_especs_cat1 ss1 ss2 :
    valid_especs (ss1 ++ ss2) -> valid_especs ss1 /\ valid_especs ss2.
  Proof.
    move=> H; split; move=> s Hin; apply: H.
    - exact: (in_cat_l _ Hin).
    - exact: (in_cat_r _ Hin).
  Qed.

  Lemma valid_especs_cat2 ss1 ss2 :
    valid_especs ss1 -> valid_especs ss2 -> valid_especs (ss1 ++ ss2).
  Proof.
    move=> H1 H2 s Hin. case: (in_cat Hin) => {}Hin.
    - exact: (H1 _ Hin).
    - exact: (H2 _ Hin).
  Qed.

  Lemma valid_rspecs_cat1 ss1 ss2 :
    valid_rspecs (ss1 ++ ss2) -> valid_rspecs ss1 /\ valid_rspecs ss2.
  Proof.
    move=> H; split; move=> s Hin; apply: H.
    - exact: (in_cat_l _ Hin).
    - exact: (in_cat_r _ Hin).
  Qed.

  Lemma valid_rspecs_cat2 ss1 ss2 :
    valid_rspecs ss1 -> valid_rspecs ss2 -> valid_rspecs (ss1 ++ ss2).
  Proof.
    move=> H1 H2 s Hin. case: (in_cat Hin) => {}Hin.
    - exact: (H1 _ Hin).
    - exact: (H2 _ Hin).
  Qed.

  Lemma split_rspec_rng_spec s t :
    List.In t (split_rspec s) -> is_rng_rspec s -> is_rng_rspec t.
  Proof.
    rewrite /split_rspec. rewrite tmap_map. case: s => [E f p g] /=. elim: g => //=.
    - case => //. move=> ?; subst. by apply.
    - move=> n e1 e2 [] //. move=> ?; subst. by apply.
    - move=> n op e1 e2 [] //. move=> ?; subst. by apply.
    - move=> e IH [] //. move=> ?; subst. by apply.
    - move=> e1 IH1 e2 IH2. rewrite map_cat. move=> H; case: (in_cat H) => {}H.
      + exact: (IH1 H).
      + exact: (IH2 H).
    - move=> e1 IH1 e2 IH2 [] //. move=> ?; subst. by apply.
  Qed.

  Lemma split_espec_esinputs s t : In t (split_espec s) -> esinputs t = esinputs s.
  Proof.
    rewrite /split_espec tmap_map. case: s => [E f p g]. elim: g => //=.
    - case; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 e2 ms []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. case: (in_cat H) => {} H.
      + exact: (IH1 H).
      + exact: (IH2 H).
  Qed.

  Lemma split_rspec_rsinputs s t : In t (split_rspec s) -> rsinputs t = rsinputs s.
  Proof.
    rewrite /split_rspec tmap_map. case: s => [E f p g]. elim: g => //=.
    - case; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> n e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> n op e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e IH []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. case: (in_cat H) => {} H.
      + exact: (IH1 H).
      + exact: (IH2 H).
    - move=> e1 IH1 e2 IH2 []; [move=> ?; subst; simpl | done]. reflexivity.
  Qed.

  Lemma split_espec_espre s t : In t (split_espec s) -> espre t = espre s.
  Proof.
    rewrite /split_espec tmap_map. case: s => [E f p g]. elim: g => //=.
    - case; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 e2 ms []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. case: (in_cat H) => {} H.
      + exact: (IH1 H).
      + exact: (IH2 H).
  Qed.

  Lemma split_rspec_rspre s t : In t (split_rspec s) -> rspre t = rspre s.
  Proof.
    rewrite /split_rspec tmap_map. case: s => [E f p g]. elim: g => //=.
    - case; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> n e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> n op e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e IH []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. case: (in_cat H) => {} H.
      + exact: (IH1 H).
      + exact: (IH2 H).
    - move=> e1 IH1 e2 IH2 []; [move=> ?; subst; simpl | done]. reflexivity.
  Qed.

  Lemma split_espec_esprog s t : In t (split_espec s) -> esprog t = esprog s.
  Proof.
    rewrite /split_espec tmap_map. case: s => [E f p g]. elim: g => //=.
    - case; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 e2 ms []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. case: (in_cat H) => {} H.
      + exact: (IH1 H).
      + exact: (IH2 H).
  Qed.

  Lemma split_rspec_rsprog s t : In t (split_rspec s) -> rsprog t = rsprog s.
  Proof.
    rewrite /split_rspec tmap_map. case: s => [E f p g]. elim: g => //=.
    - case; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> n e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> n op e1 e2 []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e IH []; [move=> ?; subst; simpl | done]. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. case: (in_cat H) => {} H.
      + exact: (IH1 H).
      + exact: (IH2 H).
    - move=> e1 IH1 e2 IH2 []; [move=> ?; subst; simpl | done]. reflexivity.
  Qed.

  Lemma split_espec_correct s :
    valid_especs (split_espec s) <-> valid_espec s.
  Proof.
    case: s => E f p q. elim: q => /=.
    - rewrite /split_espec /tmap /mapr /=. split.
      + done.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
    - move=> e1 e2. rewrite /split_espec /tmap /mapr /=. split.
      + apply. exact: in_eq.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
    - move=> e1 e2 ms. rewrite /split_espec /tmap /mapr /=. split.
      + apply. exact: in_eq.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
    - move=> e1 [IH11 IH12] e2 [IH21 IH22]. rewrite split_espec_eand valid_espec_eand. split.
      + move=> H. move: (valid_especs_cat1 H) => [H1 H2].
        move: (IH11 H1) (IH21 H2). tauto.
      + move=> [H1 H2]. move: (IH12 H1) (IH22 H2) => {}H1 {}H2.
        apply: valid_especs_cat2; tauto.
  Qed.

  Lemma split_rspec_correct s :
    valid_rspecs (split_rspec s) <-> valid_rspec s.
  Proof.
    case: s => E f p g. elim: g => /=.
    - rewrite /split_rspec /tmap /mapr /=. split.
      + done.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
    - move=> e1 e2. rewrite /split_rspec /tmap /mapr /=. split.
      + apply. exact: in_eq.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
    - move=> e1 e2 ms. rewrite /split_rspec /tmap /mapr /=. split.
      + apply. exact: in_eq.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
    - move=> e _. rewrite /split_rspec /tmap /mapr /=. split.
      + apply. exact: in_eq.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
    - move=> e1 [IH11 IH12] e2 [IH21 IH22]. rewrite split_rspec_rand valid_rspec_rand. split.
      + move=> H. move: (valid_rspecs_cat1 H) => [H1 H2].
        move: (IH11 H1) (IH21 H2). tauto.
      + move=> [H1 H2]. move: (IH12 H1) (IH22 H2) => {}H1 {}H2.
        apply: valid_rspecs_cat2; tauto.
    - move=> e1 _ e2 _. rewrite /split_rspec /tmap /mapr /=. split.
      + apply. exact: in_eq.
      + move=> H s Hin. move: (in_singleton Hin) => ?; subst. done.
  Qed.


  Lemma well_formed_espec_eand E f p g1 g2 :
    well_formed_espec {| esinputs := E; espre := f; esprog := p; espost := Eand g1 g2 |}
    <-> well_formed_espec {| esinputs := E; espre := f; esprog := p; espost := g1 |} /\
          well_formed_espec {| esinputs := E; espre := f; esprog := p; espost := g2 |}.
  Proof.
    rewrite /well_formed_espec /=. split.
    - move=> /andP [/andP [Hf Hp] /well_formed_ebexp_eand [Hg1 Hg2]].
      by rewrite Hf Hp Hg1 Hg2.
    - move=> [/andP [/andP [Hf Hp] Hg1] /andP [/andP [_ _] Hg2]]. rewrite Hf Hp /=.
      apply/well_formed_ebexp_eand. by rewrite Hg1 Hg2.
  Qed.

  Lemma well_formed_rspec_rand E f p g1 g2 :
    well_formed_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := Rand g1 g2 |}
    <-> well_formed_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := g1 |} /\
          well_formed_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := g2 |}.
  Proof.
    rewrite /well_formed_rspec /=. split.
    - move=> /andP [/andP [Hf Hp] /well_formed_rbexp_rand [Hg1 Hg2]].
      by rewrite Hf Hp Hg1 Hg2.
    - move=> [/andP [/andP [Hf Hp] Hg1] /andP [/andP [_ _] Hg2]]. rewrite Hf Hp /=.
      apply/well_formed_rbexp_rand. by rewrite Hg1 Hg2.
  Qed.

  Lemma well_formed_espec_split_espec s t:
    List.In t (split_espec s) -> well_formed_espec s -> well_formed_espec t.
  Proof.
    case: s => [E f p g]. rewrite /split_espec /=. rewrite tmap_map. elim: g => //=.
    - case=> //. move=> ?; subst. by apply.
    - move=> e1 e2 [] //. move=> ?; subst. by apply.
    - move=> e1 e2 ms [] //. move=> ?; subst. by apply.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. move/well_formed_espec_eand => [Hwf1 Hwf2].
      case: (in_cat H) => {}H.
      + exact: (IH1 H Hwf1).
      + exact: (IH2 H Hwf2).
  Qed.

  Lemma well_formed_rspec_split_rspec s t:
    List.In t (split_rspec s) -> well_formed_rspec s -> well_formed_rspec t.
  Proof.
    case: s => [E f p g]. rewrite /split_rspec /=. rewrite tmap_map. elim: g => //=.
    - case=> //. move=> ?; subst. by apply.
    - move=> n e1 e2 [] //. move=> ?; subst. by apply.
    - move=> n op e1 e2 [] //. move=> ?; subst. by apply.
    - move=> e IH [] //. move=> ?; subst. by apply.
    - move=> e1 IH1 e2 IH2. rewrite map_cat => H. move/well_formed_rspec_rand => [Hwf1 Hwf2].
      case: (in_cat H) => {}H.
      + exact: (IH1 H Hwf1).
      + exact: (IH2 H Hwf2).
    - move=> e1 IH1 e2 IH2 [] //. move=> ?; subst. by apply.
  Qed.

  Lemma split_espec_well_formed_espec s :
    (forall t, List.In t (split_espec s) -> well_formed_espec t) <-> well_formed_espec s.
  Proof.
    case: s => [E f p g]. rewrite /split_espec /=. rewrite tmap_map. split.
    - elim: g => //=.
      + move=> H. apply: H. by left.
      + move=> e1 e2 H. apply: H. by left.
      + move=> e1 e2 ms H. apply: H. by left.
      + move=> e1 IH1 e2 IH2. rewrite map_cat => H. apply/well_formed_espec_eand. split.
        * apply: IH1 => Ht Hin. apply: H. apply: in_cat_l. assumption.
        * apply: IH2 => Ht Hin. apply: H. apply: in_cat_r. assumption.
    - elim: g => //=.
      + move=> H t [] //. move=> <-. assumption.
      + move=> e1 e2 H t [] //. move=> <-. assumption.
      + move=> e1 e2 ms H t [] //. move=> <-. assumption.
      + move=> e1 IH1 e2 IH2 /well_formed_espec_eand [H1 H2] t Hin.
        rewrite map_cat in Hin. case: (in_cat Hin) => {}Hin.
        * exact: (IH1 H1 _ Hin).
        * exact: (IH2 H2 _ Hin).
  Qed.

  Lemma split_rspec_well_formed_rspec s :
    (forall t, List.In t (split_rspec s) -> well_formed_rspec t) <-> well_formed_rspec s.
  Proof.
    case: s => [E f p g]. rewrite /split_rspec /=. rewrite tmap_map. split.
    - elim: g => //=.
      + move=> H. apply: H. by left.
      + move=> n e1 e2 H. apply: H. by left.
      + move=> n op e1 e2 H. apply: H. by left.
      + move=> e IH H. apply: H. by left.
      + move=> e1 IH1 e2 IH2. rewrite map_cat => H. apply/well_formed_rspec_rand. split.
        * apply: IH1 => Ht Hin. apply: H. apply: in_cat_l. assumption.
        * apply: IH2 => Ht Hin. apply: H. apply: in_cat_r. assumption.
      + move=> e1 _ e2 _ H. apply: H. by left.
    - elim: g => //=.
      + move=> H t [] //. move=> <-. assumption.
      + move=> n e1 e2 H t [] //. move=> <-. assumption.
      + move=> n op e1 e2 H t [] //. move=> <-. assumption.
      + move=> e IH H t [] //. move=> <-. assumption.
      + move=> e1 IH1 e2 IH2 /well_formed_rspec_rand [H1 H2] t Hin.
        rewrite map_cat in Hin. case: (in_cat Hin) => {}Hin.
        * exact: (IH1 H1 _ Hin).
        * exact: (IH2 H2 _ Hin).
      + move=> e1 _ e2 _ H t [] //. move=> <-. assumption.
  Qed.


  (* State eqmod *)

  Module TSEQM := TStateEqmod V BitsValueType S VS.

  Section StateEqm.

    Lemma state_eqmod_eval_eexp E vs e s1 s2 :
      TSEQM.state_eqmod vs s1 s2 ->
      VS.subset (vars_eexp e) vs ->
      eval_eexp e E s1 = eval_eexp e E s2.
    Proof.
      move=> Heqm. elim: e => //=.
      - move=> x Hsub. rewrite /acc2z /bv2z.
        move: (TSEQM.VSLemmas.subset_singleton1 Hsub) => Hmem.
        rewrite (Heqm x Hmem). reflexivity.
      - move=> op e IH Hsub. rewrite (IH Hsub). reflexivity.
      - move=> op e1 IH1 e2 IH2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2. rewrite (IH1 Hsub1) (IH2 Hsub2). reflexivity.
      - move=> e IH n Hsub. rewrite (IH Hsub). reflexivity.
    Qed.

    Lemma state_eqmod_eval_eexps E vs es s1 s2 :
      TSEQM.state_eqmod vs s1 s2 ->
      VS.subset (vars_eexps es) vs ->
      eval_eexps es E s1 = eval_eexps es E s2.
    Proof.
      move=> Heqm. elim: es => [| e es IH] //=. move=> Hsub.
      move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
          => Hsub1 Hsub2. rewrite (state_eqmod_eval_eexp _ Heqm Hsub1) (IH Hsub2).
      reflexivity.
    Qed.

    Lemma state_eqmod_eval_ebexp E vs e s1 s2 :
      TSEQM.state_eqmod vs s1 s2 ->
      VS.subset (vars_ebexp e) vs ->
      eval_ebexp e E s1 <-> eval_ebexp e E s2.
    Proof.
      move=> Heqm. elim: e => //=.
      - move=> e1 e2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2. rewrite (state_eqmod_eval_eexp _ Heqm Hsub1)
                                    (state_eqmod_eval_eexp _ Heqm Hsub2). tauto.
      - move=> e1 e2 ms Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2.
        move: (TSEQM.VSLemmas.subset_union4 Hsub2) (TSEQM.VSLemmas.subset_union5 Hsub2)
            => {} Hsub2 Hsub3.
        rewrite (state_eqmod_eval_eexp _ Heqm Hsub1)
                (state_eqmod_eval_eexp _ Heqm Hsub2)
                (state_eqmod_eval_eexps _ Heqm Hsub3). tauto.
      - move=> e1 IH1 e2 IH2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2. move: (IH1 Hsub1) (IH2 Hsub2). tauto.
    Qed.

    Lemma state_eqmod_eval_rexp vs e s1 s2 :
      TSEQM.state_eqmod vs s1 s2 ->
      VS.subset (vars_rexp e) vs ->
      eval_rexp e s1 = eval_rexp e s2.
    Proof.
      move=> Heqm. elim: e => //=.
      - move=> x Hsub. move: (TSEQM.VSLemmas.subset_singleton1 Hsub) => Hmem.
        rewrite (Heqm x Hmem). reflexivity.
      - move=> _ op e IH Hsub. rewrite (IH Hsub). reflexivity.
      - move=> _ op e1 IH1 e2 IH2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2. rewrite (IH1 Hsub1) (IH2 Hsub2). reflexivity.
      - move=> _ e IH n Hsub. rewrite (IH Hsub). reflexivity.
      - move=> _ e IH n Hsub. rewrite (IH Hsub). reflexivity.
    Qed.

    Lemma state_eqmod_eval_rbexp vs e s1 s2 :
      TSEQM.state_eqmod vs s1 s2 ->
      VS.subset (vars_rbexp e) vs ->
      eval_rbexp e s1 = eval_rbexp e s2.
    Proof.
      move=> Heqm. elim: e => //=.
      - move=> _ e1 e2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2. rewrite (state_eqmod_eval_rexp Heqm Hsub1)
                                    (state_eqmod_eval_rexp Heqm Hsub2). reflexivity.
      - move=> _ op e1 e2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2.
        rewrite (state_eqmod_eval_rexp Heqm Hsub1)
                (state_eqmod_eval_rexp Heqm Hsub2). reflexivity.
      - move=> e IH Hsub. rewrite (IH Hsub). reflexivity.
      - move=> e1 IH1 e2 IH2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2. rewrite (IH1 Hsub1) (IH2 Hsub2). reflexivity.
      - move=> e1 IH1 e2 IH2 Hsub.
        move: (TSEQM.VSLemmas.subset_union4 Hsub) (TSEQM.VSLemmas.subset_union5 Hsub)
            => Hsub1 Hsub2. rewrite (IH1 Hsub1) (IH2 Hsub2). reflexivity.
    Qed.

    Lemma state_eqmod_eval_atom vs a s1 s2 :
      TSEQM.state_eqmod vs s1 s2 ->
      VS.subset (vars_atom a) vs ->
      eval_atom a s1 = eval_atom a s2.
    Proof.
      case: a => //=. move=> v Heqm Hsub.
      move: (TSEQM.VSLemmas.subset_singleton1 Hsub) => Hmem.
      rewrite (Heqm v Hmem). reflexivity.
    Qed.

  End StateEqm.


  (* Agree *)

  Module MA := MapAgree V TE VS.

  Section Agree.

    Lemma agree_vtyp v E1 E2 :
      MA.agree (VS.singleton v) E1 E2 -> TE.vtyp v E1 = TE.vtyp v E2.
    Proof.
      move=> H; move: (H v (VSLemmas.mem_singleton2 (eq_refl v))) => Hfind.
      case Hf: (TE.find v E2).
      - rewrite Hf in Hfind. rewrite (TE.find_some_vtyp Hf) (TE.find_some_vtyp Hfind).
        reflexivity.
      - rewrite Hf in Hfind. rewrite (TE.find_none_vtyp Hf) (TE.find_none_vtyp Hfind).
        reflexivity.
    Qed.

    Lemma agree_vsize v E1 E2 :
      MA.agree (VS.singleton v) E1 E2 -> TE.vsize v E1 = TE.vsize v E2.
    Proof.
      move=> Hag. rewrite !TE.vtyp_vsize. rewrite (agree_vtyp Hag). reflexivity.
    Qed.

    Lemma agree_atyp a E1 E2 :
      MA.agree (vars_atom a) E1 E2 -> atyp a E1 = atyp a E2.
    Proof. case: a => //=. move=> v Ha. exact: (agree_vtyp Ha). Qed.

    Lemma agree_asize a E1 E2 :
      MA.agree (vars_atom a) E1 E2 -> asize a E1 = asize a E2.
    Proof.
      move=> Ha; rewrite /asize; rewrite (agree_atyp Ha). reflexivity.
    Qed.

    Ltac inversion_eval_instr :=
      match goal with
      | H : eval_instr _ _ _ _ |- _ => inversion_clear H
      end.

    Ltac dec_atom_typ :=
      MA.simpl_agree;
      repeat
        match goal with
        | H : MA.agree (vars_atom ?a) ?E1 ?E2 |- context f [atyp ?a ?E2] =>
            rewrite -(agree_atyp H)
        | H : MA.agree (vars_atom ?a) ?E1 ?E2 |- context f [atyp ?a ?E2] =>
            rewrite -(agree_atyp H)
        | H : ?e |- ?e => assumption
        end.

    Lemma agree_eval_eexp E1 E2 e s :
      MA.agree (vars_eexp e) E1 E2 -> eval_eexp e E1 s = eval_eexp e E2 s.
    Proof.
      elim: e => //=.
      - move=> v Ha. rewrite /acc2z. rewrite (agree_vtyp Ha). reflexivity.
      - move=> op e IH Ha. rewrite (IH Ha). reflexivity.
      - move=> op e1 IH1 e2 IH2 Ha. MA.simpl_agree.
        rewrite (IH1 H) (IH2 H0). reflexivity.
      - move=> e IH n Ha. rewrite (IH Ha). reflexivity.
    Qed.

    Lemma agree_eval_eexps E1 E2 es s :
      MA.agree (vars_eexps es) E1 E2 -> eval_eexps es E1 s = eval_eexps es E2 s.
    Proof.
      elim: es => [| e es IH] //=. move=> H. MA.simpl_agree.
      rewrite (agree_eval_eexp _ H0) (IH H1). reflexivity.
    Qed.

    Lemma agree_eval_ebexp E1 E2 e s :
      MA.agree (vars_ebexp e) E1 E2 -> eval_ebexp e E1 s <-> eval_ebexp e E2 s.
    Proof.
      elim: e => //=.
      - move=> e1 e2 Ha. MA.simpl_agree.
        rewrite (agree_eval_eexp _ H) (agree_eval_eexp _ H0). tauto.
      - move=> e1 e2 ms Ha. MA.simpl_agree.
        rewrite (agree_eval_eexp _ H) (agree_eval_eexp _ H1)  (agree_eval_eexps _ H2). tauto.
      - move=> e1 IH1 e2 IH2 Ha. MA.simpl_agree.
        move: (IH1 H) (IH2 H0). tauto.
    Qed.

    Lemma agree_eval_bexp E1 E2 e s :
      MA.agree (vars_ebexp (eqn_bexp e)) E1 E2 -> eval_bexp e E1 s <-> eval_bexp e E2 s.
    Proof.
      case: e => [e r] /=. split; move=> [/= He Hr]; split => /=; try assumption.
      - apply/(agree_eval_ebexp _ H). assumption.
      - apply/(agree_eval_ebexp _ H). assumption.
    Qed.

    Lemma agree_rvs_instr_succ_typenv i vs E1 E2 :
      MA.agree vs E1 E2 ->
      MA.agree (rvs_instr i) E1 E2 ->
      MA.agree vs (instr_succ_typenv i E1) (instr_succ_typenv i E2).
    Proof.
      case: i => //=; intros; dec_atom_typ; by MA.dp_agree.
    Qed.

    Lemma agree_instr_succ_typenv i vs E1 E2 :
      MA.agree vs E1 E2 ->
      MA.agree (vars_instr i) E1 E2 ->
      MA.agree vs (instr_succ_typenv i E1) (instr_succ_typenv i E2).
    Proof.
      case: i => //=; intros; dec_atom_typ; by MA.dp_agree.
    Qed.

    Lemma agree_program_succ_typenv p vs E1 E2 :
      MA.agree vs E1 E2 ->
      MA.agree (vars_program p) E1 E2 ->
      MA.agree vs (program_succ_typenv p E1) (program_succ_typenv p E2).
    Proof.
      elim: p vs E1 E2 => [| i p IH] vs E1 E2 //=.
      move=> Ha1 Ha2. MA.simpl_agree. apply: IH.
      - exact: (agree_instr_succ_typenv Ha1 H).
      - exact: (agree_instr_succ_typenv H0 H).
    Qed.

    Lemma agree_eval_instr E1 E2 i s1 s2 :
      eval_instr E1 i s1 s2 -> MA.agree (vars_instr i) E1 E2 ->
      eval_instr E2 i s1 s2.
    Proof.
      case: i => //=; intros; inversion_eval_instr.
      - apply: EImov; assumption.
      - apply: EIshl; assumption.
      - apply: EIcshl; assumption.
      - apply: (EInondet _ H1); assumption.
      - apply: (EIcmovT _ _ H1); assumption.
      - apply: (EIcmovF _ _ H1); assumption.
      - exact: EInop.
      - apply: EInot; assumption.
      - apply: EIadd; assumption.
      - apply: EIadds; assumption.
      - apply: EIadc; assumption.
      - apply: EIadcs; assumption.
      - apply: EIsub; assumption.
      - apply: EIsubc; assumption.
      - apply: EIsubb; assumption.
      - apply: EIsbc; assumption.
      - apply: EIsbcs; assumption.
      - apply: EIsbb; assumption.
      - apply: EIsbbs; assumption.
      - apply: EImul; assumption.
      - apply: EImullU; by dec_atom_typ.
      - apply: EImullS; by dec_atom_typ.
      - apply: EImuljU; by dec_atom_typ.
      - apply: EImuljS; by dec_atom_typ.
      - apply: EIsplitU; by dec_atom_typ.
      - apply: EIsplitS; by dec_atom_typ.
      - apply: EIand; assumption.
      - apply: EIor; assumption.
      - apply: EIxor; assumption.
      - apply: EIcast; by dec_atom_typ.
      - apply: EIvpc; by dec_atom_typ.
      - apply: EIjoin; assumption.
      - apply: EIassume. apply/agree_eval_bexp; last exact: H1.
        apply: MA.agree_sym. apply: (MA.subset_set_agree _ H0) => {H0 H1}.
        case: b => [e r] /=. rewrite /vars_bexp /=. exact: VSLemmas.union_subset_1.
    Qed.

    Lemma agree_eval_program E1 E2 p s1 s2 :
      eval_program E1 p s1 s2 -> MA.agree (vars_program p) E1 E2 ->
      eval_program E2 p s1 s2.
    Proof.
      elim: p E1 E2 s1 s2 => [| i p IH] /= E1 E2 s1 s2.
      - move=> Hev; inversion_clear Hev. move=> _. exact: Enil.
      - move=> Hev; inversion_clear Hev. move=> Ha. MA.simpl_agree.
        apply: (Econs (agree_eval_instr H H1)). apply: (IH _ _ _ _ H0).
        exact: (agree_instr_succ_typenv H2 H1).
    Qed.

    Lemma agree_are_defined vs E1 E2 :
      MA.agree vs E1 E2 -> are_defined vs E1 = are_defined vs E2.
    Proof.
      rewrite /are_defined. move=> Hag. case H2: (VS.for_all (is_defined^~ E2) vs).
      - apply/(VS.for_all_1 (are_defined_compat E1)).
        move/(VS.for_all_2 (are_defined_compat E2)): H2 => H2.
        move=> x Hin. move: (H2 x Hin) => Hdef2. move/VSLemmas.memP: Hin => Hin.
        move: (Hag x Hin) => Hfind. rewrite /is_defined.
        rewrite (TELemmas.find_eq_mem_eq Hfind). exact: Hdef2.
      - apply/negP => H1. move/negP: H2; apply.
        apply/(VS.for_all_1 (are_defined_compat E2)).
        move/(VS.for_all_2 (are_defined_compat E1)): H1 => H1.
        move=> x Hin. move: (H1 x Hin) => Hdef1. move/VSLemmas.memP: Hin => Hin.
        move: (Hag x Hin) => Hfind. rewrite /is_defined.
        rewrite -(TELemmas.find_eq_mem_eq Hfind). exact: Hdef1.
    Qed.

    Lemma agree_well_typed_eexp E1 E2 e :
      MA.agree (vars_eexp e) E1 E2 -> well_typed_eexp E1 e = well_typed_eexp E2 e.
    Proof.
      elim: e => //=. move=> op e1 IH1 e2 IH2 Hag. move/MA.agree_union_set: Hag => [Hag1 Hag2].
      rewrite (IH1 Hag1) (IH2 Hag2). reflexivity.
    Qed.

    Lemma agree_well_typed_eexps E1 E2 es :
      MA.agree (vars_eexps es) E1 E2 -> well_typed_eexps E1 es = well_typed_eexps E2 es.
    Proof.
      elim: es => [| e es IH] //=. move/MA.agree_union_set => [Hag1 Hag2].
      rewrite (agree_well_typed_eexp Hag1) (IH Hag2). reflexivity.
    Qed.

    Lemma agree_well_typed_ebexp E1 E2 e :
      MA.agree (vars_ebexp e) E1 E2 -> well_typed_ebexp E1 e = well_typed_ebexp E2 e.
    Proof.
      elim: e => //=.
      - move=> e1 e2 /MA.agree_union_set [Hag1 Hag2].
        rewrite (agree_well_typed_eexp Hag1) (agree_well_typed_eexp Hag2). reflexivity.
      - move=> e1 e2 ms /MA.agree_union_set [Hag1 /MA.agree_union_set [Hag2 Hag3]].
        rewrite (agree_well_typed_eexp Hag1) (agree_well_typed_eexp Hag2)
          (agree_well_typed_eexps Hag3). reflexivity.
      - move=> e1 IH1 e2 IH2 /MA.agree_union_set [Hag1 Hag2].
        rewrite (IH1 Hag1) (IH2 Hag2). reflexivity.
    Qed.

    Lemma agree_size_of_rexp E1 E2 e :
      MA.agree (vars_rexp e) E1 E2 -> size_of_rexp e E1 = size_of_rexp e E2.
    Proof. case: e => //=. move=> x Hag. exact: (agree_vsize Hag). Qed.

    Lemma agree_well_typed_rexp E1 E2 e :
      MA.agree (vars_rexp e) E1 E2 -> well_typed_rexp E1 e = well_typed_rexp E2 e.
    Proof.
      elim: e => //=.
      - move=> x Hag. rewrite (agree_vsize Hag). reflexivity.
      - move=> n _ e IH Hag. rewrite (IH Hag) (agree_size_of_rexp Hag). reflexivity.
      - move=> n _ e1 IH1 e2 IH2 /MA.agree_union_set [Hag1 Hag2].
        rewrite (IH1 Hag1) (IH2 Hag2) (agree_size_of_rexp Hag1) (agree_size_of_rexp Hag2).
        reflexivity.
      - move=> n e IH _ Hag. rewrite (IH Hag) (agree_size_of_rexp Hag). reflexivity.
      - move=> n e IH _ Hag. rewrite (IH Hag) (agree_size_of_rexp Hag). reflexivity.
    Qed.

    Lemma agree_well_typed_rbexp E1 E2 e :
      MA.agree (vars_rbexp e) E1 E2 -> well_typed_rbexp E1 e = well_typed_rbexp E2 e.
    Proof.
      elim: e => //=.
      - move=> n e1 e2 /MA.agree_union_set [Hag1 Hag2].
        rewrite (agree_well_typed_rexp Hag1) (agree_well_typed_rexp Hag2)
          (agree_size_of_rexp Hag1) (agree_size_of_rexp Hag2). reflexivity.
      - move=> n _ e1 e2 /MA.agree_union_set [Hag1 Hag2].
        rewrite (agree_well_typed_rexp Hag1) (agree_well_typed_rexp Hag2)
          (agree_size_of_rexp Hag1) (agree_size_of_rexp Hag2). reflexivity.
      - move=> e1 IH1 e2 IH2 /MA.agree_union_set [Hag1 Hag2].
        rewrite (IH1 Hag1) (IH2 Hag2). reflexivity.
      - move=> e1 IH1 e2 IH2 /MA.agree_union_set [Hag1 Hag2].
        rewrite (IH1 Hag1) (IH2 Hag2). reflexivity.
    Qed.

    Lemma agree_well_typed_bexp E1 E2 e :
      MA.agree (vars_bexp e) E1 E2 -> well_typed_bexp E1 e = well_typed_bexp E2 e.
    Proof.
      case: e => [e r] /=. rewrite /vars_bexp /well_typed_bexp /=.
      move/MA.agree_union_set => [Hage Hagr].
      rewrite (agree_well_typed_ebexp Hage) (agree_well_typed_rbexp Hagr). reflexivity.
    Qed.

    Lemma agree_well_formed_eexp E1 E2 e :
      MA.agree (vars_eexp e) E1 E2 -> well_formed_eexp E1 e = well_formed_eexp E2 e.
    Proof.
      rewrite /well_formed_eexp => Hag.
      rewrite (agree_are_defined Hag) (agree_well_typed_eexp Hag). reflexivity.
    Qed.

    Lemma agree_well_formed_eexps E1 E2 es :
      MA.agree (vars_eexps es) E1 E2 -> well_formed_eexps E1 es = well_formed_eexps E2 es.
    Proof.
      elim: es => [| e es IH] //=. move/MA.agree_union_set => [Hag1 Hag2].
      rewrite (agree_well_formed_eexp Hag1) (IH Hag2). reflexivity.
    Qed.

    Lemma agree_well_formed_ebexp E1 E2 e :
      MA.agree (vars_ebexp e) E1 E2 -> well_formed_ebexp E1 e = well_formed_ebexp E2 e.
    Proof.
      rewrite /well_formed_ebexp => Hag.
      rewrite (agree_are_defined Hag) (agree_well_typed_ebexp Hag). reflexivity.
    Qed.

    Lemma agree_well_formed_rexp E1 E2 e :
      MA.agree (vars_rexp e) E1 E2 -> well_formed_rexp E1 e = well_formed_rexp E2 e.
    Proof.
      rewrite /well_formed_rexp => Hag.
      rewrite (agree_are_defined Hag) (agree_well_typed_rexp Hag). reflexivity.
    Qed.

    Lemma agree_well_formed_rbexp E1 E2 e :
      MA.agree (vars_rbexp e) E1 E2 -> well_formed_rbexp E1 e = well_formed_rbexp E2 e.
    Proof.
      rewrite /well_formed_rbexp => Hag.
      rewrite (agree_are_defined Hag) (agree_well_typed_rbexp Hag). reflexivity.
    Qed.

    Lemma agree_well_formed_bexp E1 E2 e :
      MA.agree (vars_bexp e) E1 E2 -> well_formed_bexp E1 e = well_formed_bexp E2 e.
    Proof.
      rewrite /well_formed_bexp /vars_bexp /=. move=> Hag. rewrite (agree_well_typed_bexp Hag).
      case: e Hag => [e r] /=. move/MA.agree_union_set => [Hage Hagr]. rewrite !are_defined_union.
      rewrite !(agree_are_defined Hage) !(agree_are_defined Hagr). reflexivity.
    Qed.

    Lemma agree_well_typed_atom E1 E2 a :
      MA.agree (vars_atom a) E1 E2 -> well_typed_atom E1 a = well_typed_atom E2 a.
    Proof.
      case: a => //=. rewrite /well_typed_atom /well_sized_atom => v Hag.
      rewrite /atyp /asize /=. rewrite (agree_vtyp Hag). reflexivity.
    Qed.

    Ltac agree_rewrite_well_formed :=
      repeat
        match goal with
        | H : MA.agree ?vs ?E1 ?E2 |- context c [are_defined ?vs ?E1] => rewrite (agree_are_defined H)
        | H : MA.agree (vars_eexp ?e) ?E1 ?E2 |- context c [well_typed_eexp ?E1 ?e] =>
            rewrite (agree_well_typed_eexp H)
        | H : MA.agree (vars_eexps ?es) ?E1 ?E2 |- context c [well_typed_eexps ?E1 ?es] =>
            rewrite (agree_well_typed_eexps H)
        | H : MA.agree (vars_ebexp ?e) ?E1 ?E2 |- context c [well_typed_ebexp ?E1 ?e] =>
            rewrite (agree_well_typed_ebexp H)
        | H : MA.agree (vars_rexp ?e) ?E1 ?E2 |- context c [well_typed_rexp ?E1 ?e] =>
            rewrite (agree_well_typed_rexp H)
        | H : MA.agree (vars_rbexp ?e) ?E1 ?E2 |- context c [well_typed_rbexp ?E1 ?e] =>
            rewrite (agree_well_typed_rbexp H)
        | H : MA.agree (vars_bexp ?e) ?E1 ?E2 |- context c [well_typed_bexp ?E1 ?e] =>
            rewrite (agree_well_typed_bexp H)
        | H : MA.agree (vars_eexp ?e) ?E1 ?E2 |- context c [well_formed_eexp ?E1 ?e] =>
          rewrite (agree_well_formed_eexp H)
        | H : MA.agree (vars_eexps ?es) ?E1 ?E2 |- context c [well_formed_eexps ?E1 ?es] =>
            rewrite (agree_well_formed_eexps H)
        | H : MA.agree (vars_ebexp ?e) ?E1 ?E2 |- context c [well_formed_ebexp ?E1 ?e] =>
            rewrite (agree_well_formed_ebexp H)
        | H : MA.agree (vars_rexp ?e) ?E1 ?E2 |- context c [well_formed_rexp ?E1 ?e] =>
            rewrite (agree_well_formed_rexp H)
        | H : MA.agree (vars_rbexp ?e) ?E1 ?E2 |- context c [well_formed_rbexp ?E1 ?e] =>
            rewrite (agree_well_formed_rbexp H)
        | H : MA.agree (vars_bexp ?e) ?E1 ?E2 |- context c [well_formed_bexp ?E1 ?e] =>
            rewrite (agree_well_formed_bexp H)
        | H : MA.agree (vars_atom ?a) ?E1 ?E2 |- context c [well_typed_atom ?E1 ?a] =>
            rewrite (agree_well_typed_atom H)
        | H : MA.agree (vars_atom ?a) ?E1 ?E2 |- context c [asize ?a ?E1] =>
            rewrite (agree_asize H)
        | H : MA.agree (vars_atom ?a) ?E1 ?E2 |- context c [atyp ?a ?E1] =>
            rewrite (agree_atyp H)
        end.

    Lemma agree_well_formed_instr E1 E2 i :
      MA.agree (vars_instr i) E1 E2 -> well_formed_instr E1 i = well_formed_instr E2 i.
    Proof.
      case: i => //=; rewrite /well_formed_instr /=; intros; MA.simpl_agree;
                   by (agree_rewrite_well_formed; reflexivity).
    Qed.

    Lemma agree_well_formed_program E1 E2 p :
      MA.agree (vars_program p) E1 E2 -> well_formed_program E1 p = well_formed_program E2 p.
    Proof.
      elim: p E1 E2 => [| i p IH] E1 E2 //=. move/MA.agree_union_set => [Hagi Hagp].
      rewrite (agree_well_formed_instr Hagi).
      rewrite (IH (instr_succ_typenv i E1)  (instr_succ_typenv i E2)); first reflexivity.
      exact: (agree_instr_succ_typenv Hagp Hagi).
    Qed.

  End Agree.


  (* Slicing *)

  Section Slicing.

    Definition depvars_ebexp vs e :=
      foldl (fun vs e => let vse := vars_ebexp e in
                         if VSLemmas.disjoint vs vse then vs
                         else VS.union vs vse) vs (split_eand e).

    Definition depvars_rexp vs e :=
      let vse := vars_rexp e in
      if VSLemmas.disjoint vs vse then vs
      else VS.union vs vse.

    Definition depvars_rbexp vs e :=
      foldl (fun vs e => let vse := vars_rbexp e in
                         if VSLemmas.disjoint vs vse then vs
                         else VS.union vs vse) vs (split_rand e).

    Definition depvars_einstr vs i :=
      match i with
      | Iassume (e, r) => depvars_ebexp vs e
      (* It is possible that there is `mov x y` (or `vpc x@t y`)
         but some relevant assumption only mentions x. *)
      | Imov _ (Avar _) => if VSLemmas.disjoint vs (vars_instr i) then vs
                           else VS.union vs (vars_instr i)
      | Ivpc _ _ (Avar _) => if VSLemmas.disjoint vs (vars_instr i) then vs
                             else VS.union vs (vars_instr i)
      | _ => if VSLemmas.disjoint vs (lvs_instr i) then vs
             else VS.union vs (vars_instr i)
      end.

    Definition depvars_rinstr vs i :=
      match i with
      | Iassume (e, r) => depvars_rbexp vs r
      | Imov _ (Avar _) => if VSLemmas.disjoint vs (vars_instr i) then vs
                           else VS.union vs (vars_instr i)
      | Ivpc _ _ (Avar _) => if VSLemmas.disjoint vs (vars_instr i) then vs
                             else VS.union vs (vars_instr i)
      | _ => if VSLemmas.disjoint vs (lvs_instr i) then vs
             else VS.union vs (vars_instr i)
      end.

    Definition depvars_eprogram vs p :=
      foldl depvars_einstr vs (rev p).

    Definition depvars_rprogram vs p :=
      foldl depvars_rinstr vs (rev p).

    Definition depvars_epre_eprogram vs e p :=
      depvars_ebexp (depvars_eprogram vs p) e.

    Definition depvars_rpre_rprogram vs e p :=
      depvars_rbexp (depvars_rprogram vs p) e.


    Lemma depvars_eand vs e1 e2 :
      depvars_ebexp vs (Eand e1 e2) = depvars_ebexp (depvars_ebexp vs e1) e2.
    Proof. rewrite /depvars_ebexp /=. rewrite foldl_cat. reflexivity. Qed.

    Lemma depvars_rand vs e1 e2 :
      depvars_rbexp vs (Rand e1 e2) = depvars_rbexp (depvars_rbexp vs e1) e2.
    Proof. rewrite /depvars_rbexp /=. rewrite foldl_cat. reflexivity. Qed.

    Lemma depvars_eprogram_rcons vs p i :
      depvars_eprogram vs (rcons p i) =
        depvars_eprogram (depvars_einstr vs i) p.
    Proof.
      move: p i vs. rewrite /depvars_eprogram.
      apply: last_ind => [| p j _] i vs //=. rewrite rev_rcons /=. reflexivity.
    Qed.

    Lemma depvars_rprogram_rcons vs p i :
      depvars_rprogram vs (rcons p i) =
        depvars_rprogram (depvars_rinstr vs i) p.
    Proof.
      move: p i vs. rewrite /depvars_rprogram.
      apply: last_ind => [| p j _] i vs //=. rewrite rev_rcons /=. reflexivity.
    Qed.

    Lemma depvars_epre_eprogram_rcons vs e p i :
      depvars_epre_eprogram vs e (rcons p i) =
        depvars_epre_eprogram (depvars_einstr vs i) e p.
    Proof.
      rewrite /depvars_epre_eprogram.
      rewrite depvars_eprogram_rcons. reflexivity.
    Qed.

    Lemma depvars_rpre_rprogram_rcons vs e p i :
      depvars_rpre_rprogram vs e (rcons p i) =
        depvars_rpre_rprogram (depvars_rinstr vs i) e p.
    Proof.
      rewrite /depvars_rpre_rprogram.
      rewrite depvars_rprogram_rcons. reflexivity.
    Qed.

    Ltac case_if' :=
      repeat
        case_if ||
        match goal with
        | |- context c [let (_, _) := ?b in _] =>
            let e := fresh in
            let r := fresh in
            case: b => e r
        end.

    Ltac case_match_atom :=
      repeat
        match goal with
        | H : context c [match ?a with
                         | Avar _ => _
                         | Aconst _ _ => _
                         end] |- _ =>
            (repeat match goal with
                    | H : context c [a] |- _ => move: H
                    end); case: a; simpl; intros
        | |- context c [match ?a with
                        | Avar _ => _
                        | Aconst _ _ => _
                        end] =>
            (repeat match goal with
                    | H : context c [a] |- _ => move: H
                    end); case: a; simpl; intros
        end.

    Ltac mytac ::=
      match goal with
      | |- VS.Equal ?s ?s => exact: VSLemmas.OP.P.equal_refl
      | Heq : VS.Equal ?s1 ?s2,
          H1 : VSLemmas.disjoint ?s1 ?s = ?b1,
            H2 : VSLemmas.disjoint ?s2 ?s = ?b2 |- _ =>
          match b1 with
          | true => match b2 with
                    | false => rewrite Heq H2 in H1; discriminate
                    | _ => idtac
                    end
          | false => match b2 with
                     | true => rewrite Heq H2 in H1; discriminate
                     | _ => idtac
                     end
          end
      end.

    Global Instance add_proper_depvars_ebexp_set :
      Proper (VS.Equal ==> eq ==> VS.Equal) depvars_ebexp.
    Proof.
      move=> s1 s2 Heq e1 e2 ?; subst. elim: e2 s1 s2 Heq => /=.
      - move=> s1 s2 Heq. rewrite /depvars_ebexp /=. case_if; VSLemmas.simpl_union; assumption.
      - move=> e1 e2 s1 s2 Heq. rewrite /depvars_ebexp /=. case_if; rewrite Heq; by mytac.
      - move=> e1 e2 ms s1 s2 Heq. rewrite /depvars_ebexp /=. case_if; rewrite Heq; by mytac.
      - move=> e1 IH1 e2 IH2 s1 s2 Heq. rewrite !depvars_eand.
        apply: IH2. apply: IH1. assumption.
    Qed.

    Global Instance add_proper_depvars_rbexp_set :
      Proper (VS.Equal ==> eq ==> VS.Equal) depvars_rbexp.
    Proof.
      move=> s1 s2 Heq e1 e2 ?; subst. elim: e2 s1 s2 Heq => /=.
      - move=> s1 s2 Heq. rewrite /depvars_rbexp /=. case_if; VSLemmas.simpl_union; assumption.
      - move=> n e1 e2 s1 s2 Heq. rewrite /depvars_rbexp /=. case_if; rewrite Heq; by mytac.
      - move=> n op e1 e2 s1 s2 Heq. rewrite /depvars_rbexp /=. case_if; rewrite Heq; by mytac.
      - move=> e IH s1 s2 Heq. rewrite /depvars_rbexp /=. case_if; rewrite Heq; by mytac.
      - move=> e1 IH1 e2 IH2 s1 s2 Heq. rewrite !depvars_rand.
        apply: IH2. apply: IH1. assumption.
      - move=> e1 IH1 e2 IH2 s1 s2 Heq. rewrite /depvars_rbexp /=. case_if; rewrite Heq; by mytac.
    Qed.

    Global Instance add_proper_depvars_einstr_set :
      Proper (VS.Equal ==> eq ==> VS.Equal) depvars_einstr.
    Proof.
      move=> s1 s2 Heq i1 i2 ?; subst.
      (case: i2 => /=); intros; case_match_atom; case_if'; rewrite Heq; by mytac.
    Qed.

    Global Instance add_proper_depvars_rinstr_set :
      Proper (VS.Equal ==> eq ==> VS.Equal) depvars_rinstr.
    Proof.
      move=> s1 s2 Heq i1 i2 ?; subst.
      (case: i2 => /=); intros; case_match_atom; case_if'; rewrite Heq; by mytac.
    Qed.

    Global Instance add_proper_depvars_eprogram_set :
      Proper (VS.Equal ==> eq ==> VS.Equal) depvars_eprogram.
    Proof.
      move=> s1 s2 Heq p1 p2 ?; subst. move: p2 s1 s2 Heq.
      apply: last_ind => [| p i IH] s1 s2 Heq //=. rewrite !depvars_eprogram_rcons.
      apply: IH. rewrite Heq. reflexivity.
    Qed.

    Global Instance add_proper_depvars_rprogram_set :
      Proper (VS.Equal ==> eq ==> VS.Equal) depvars_rprogram.
    Proof.
      move=> s1 s2 Heq p1 p2 ?; subst. move: p2 s1 s2 Heq.
      apply: last_ind => [| p i IH] s1 s2 Heq //=. rewrite !depvars_rprogram_rcons.
      apply: IH. rewrite Heq. reflexivity.
    Qed.

    Global Instance add_proper_depvars_epre_eprogram_set :
      Proper (VS.Equal ==> eq ==> eq ==> VS.Equal) depvars_epre_eprogram.
    Proof.
      move=> s1 s2 Heq e1 e2 ? p1 p2 ?; subst. rewrite /depvars_epre_eprogram.
      rewrite Heq. reflexivity.
    Qed.

    Global Instance add_proper_depvars_rpre_rprogram_set :
      Proper (VS.Equal ==> eq ==> eq ==> VS.Equal) depvars_rpre_rprogram.
    Proof.
      move=> s1 s2 Heq e1 e2 ? p1 p2 ?; subst. rewrite /depvars_rpre_rprogram.
      rewrite Heq. reflexivity.
    Qed.


    Lemma depvars_ebexp_lb vs e :
      VS.subset vs (depvars_ebexp vs e).
    Proof.
      rewrite /depvars_ebexp. elim: e vs => //=; intros; case_if; try VSLemmas.dp_subset.
      rewrite foldl_cat. apply: (VSLemmas.subset_trans (H vs)). exact: H0.
    Qed.

    Lemma depvars_ebexp_ub vs e :
      VS.subset (depvars_ebexp vs e) (VS.union vs (vars_ebexp e)).
    Proof.
      rewrite /depvars_ebexp. elim: e vs => //=; intros; case_if; try VSLemmas.dp_subset.
      rewrite foldl_cat. rewrite -VSLemmas.P.union_assoc.
      apply: (VSLemmas.subset_trans
                (H0
                   ((foldl
                       (fun (vs0 : VS.t) (e1 : ebexp) =>
                          if VSLemmas.disjoint vs0 (vars_ebexp e1) then vs0 else VS.union vs0 (vars_ebexp e1)) vs
                       (split_eand e))))).
        apply: VSLemmas.union_subsets.
      - exact: H.
      - exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_rexp_lb vs e : VS.subset vs (depvars_rexp vs e).
    Proof.
      rewrite /depvars_rexp. case (VSLemmas.disjoint vs (vars_rexp e)).
      - exact: VSLemmas.subset_refl.
      - exact: VSLemmas.union_subset_1.
    Qed.

    Lemma depvars_rexp_ub vs e :
      VS.subset (depvars_rexp vs e) (VS.union vs (vars_rexp e)).
    Proof.
      rewrite /depvars_rexp. case (VSLemmas.disjoint vs (vars_rexp e)).
      - exact: VSLemmas.union_subset_1.
      - exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_rbexp_lb vs e :
      VS.subset vs (depvars_rbexp vs e).
    Proof.
      rewrite /depvars_rbexp. elim: e vs => //=.
      - move=> vs. case: (VSLemmas.disjoint vs VS.empty).
        + exact: VSLemmas.subset_refl.
        + rewrite VSLemmas.union_emptyr. exact: VSLemmas.subset_refl.
      - move=> _ e1 e2 vs.
        case: (VSLemmas.disjoint vs (VS.union (vars_rexp e1) (vars_rexp e2))).
        + exact: VSLemmas.subset_refl.
        + exact: VSLemmas.union_subset_1.
      - move=> _ _ e1 e2 vs.
        case: (VSLemmas.disjoint vs (VS.union (vars_rexp e1) (vars_rexp e2))).
        + exact: VSLemmas.subset_refl.
        + exact: VSLemmas.union_subset_1.
      - move=> e _ vs. case: (VSLemmas.disjoint vs (vars_rbexp e)).
        + exact: VSLemmas.subset_refl.
        + exact: VSLemmas.union_subset_1.
      - move=> e1 IH1 e2 IH2 vs. rewrite foldl_cat.
        apply: (VSLemmas.subset_trans (IH1 vs)). exact: IH2.
      - move=> e1 _ e2 _ vs.
        case: (VSLemmas.disjoint vs (VS.union (vars_rbexp e1) (vars_rbexp e2))).
        + exact: VSLemmas.subset_refl.
        + exact: VSLemmas.union_subset_1.
    Qed.

    Lemma depvars_rbexp_ub vs e :
      VS.subset (depvars_rbexp vs e) (VS.union vs (vars_rbexp e)).
    Proof.
      rewrite /depvars_rbexp. elim: e vs => //=.
      - move=> vs. case: (VSLemmas.disjoint vs VS.empty).
        + exact: VSLemmas.union_subset_1.
        + exact: VSLemmas.subset_refl.
      - move=> _ e1 e2 vs.
        case: (VSLemmas.disjoint vs (VS.union (vars_rexp e1) (vars_rexp e2))).
        + exact: VSLemmas.union_subset_1.
        + exact: VSLemmas.subset_refl.
      - move=> _ _ e1 e2 vs.
        case: (VSLemmas.disjoint vs (VS.union (vars_rexp e1) (vars_rexp e2))).
        + exact: VSLemmas.union_subset_1.
        + exact: VSLemmas.subset_refl.
      - move=> e _ vs. case: (VSLemmas.disjoint vs (vars_rbexp e)).
        + exact: VSLemmas.union_subset_1.
        + exact: VSLemmas.subset_refl.
      - move=> e1 IH1 e2 IH2 vs. rewrite foldl_cat.
        apply: (VSLemmas.subset_trans
                  (IH2
                     (foldl
                        (fun (vs0 : VS.t) (e : rbexp) =>
                           if VSLemmas.disjoint vs0 (vars_rbexp e) then vs0 else VS.union vs0 (vars_rbexp e))
                        vs (split_rand e1)))).
        rewrite -VSLemmas.P.union_assoc. apply: VSLemmas.union_subsets.
        + exact: (IH1 vs).
        + exact: VSLemmas.subset_refl.
      - move=> e1 _ e2 _ vs.
        case: (VSLemmas.disjoint vs (VS.union (vars_rbexp e1) (vars_rbexp e2))).
        + exact: VSLemmas.union_subset_1.
        + exact: VSLemmas.subset_refl.
    Qed.

    Ltac mytac ::=
      (repeat match goal with
              | |- context f [if ?e then _ else _] =>
                  dcase e; case; intros
              end); repeat case_match_atom; try VSLemmas.dp_subset.

    Lemma depvars_einstr_lb vs i :
      VS.subset vs (depvars_einstr vs i).
    Proof.
      case: i => //=; intros; mytac. case: b => e _. exact: depvars_ebexp_lb.
    Qed.

    Lemma depvars_einstr_ub vs i :
      VS.subset (depvars_einstr vs i) (VS.union vs (vars_instr i)).
    Proof.
      case: i => //=; intros; mytac. case: b => e r. rewrite /vars_bexp /=.
      apply: (VSLemmas.subset_trans (depvars_ebexp_ub vs e)).
      by VSLemmas.dp_subset.
    Qed.

    Lemma depvars_rinstr_lb vs i :
      VS.subset vs (depvars_rinstr vs i).
    Proof.
      case: i => //=; intros; mytac. case: b => _ r.
      exact: depvars_rbexp_lb.
    Qed.

    Lemma depvars_rinstr_ub vs i :
      VS.subset (depvars_rinstr vs i) (VS.union vs (vars_instr i)).
    Proof.
      case: i => //=; intros; mytac. case: b => e r. rewrite /vars_bexp /=.
      apply: (VSLemmas.subset_trans (depvars_rbexp_ub vs r)).
      by VSLemmas.dp_subset.
    Qed.

    Lemma depvars_eprogram_lb vs p :
      VS.subset vs (depvars_eprogram vs p).
    Proof.
      move: p vs. apply: last_ind => [| p i IH] vs //=.
      - exact: VSLemmas.subset_refl.
      - rewrite depvars_eprogram_rcons. apply: (VSLemmas.subset_trans _ (IH _)).
        exact: (depvars_einstr_lb vs i).
    Qed.

    Lemma depvars_eprogram_ub vs p :
      VS.subset (depvars_eprogram vs p) (VS.union vs (vars_program p)).
    Proof.
      move: p vs. apply: last_ind => [| p i IH] vs //=.
      - exact: VSLemmas.union_subset_1.
      - rewrite depvars_eprogram_rcons. rewrite vars_program_rcons.
        rewrite (VSLemmas.P.union_sym (vars_program p)). rewrite -VSLemmas.P.union_assoc.
        apply: (VSLemmas.subset_trans (IH _)).
        apply: VSLemmas.union_subsets; last exact: VSLemmas.subset_refl.
        exact: (depvars_einstr_ub vs i).
    Qed.

    Lemma depvars_rprogram_lb vs p :
      VS.subset vs (depvars_rprogram vs p).
    Proof.
      move: p vs. apply: last_ind => [| p i IH] vs //=.
      - exact: VSLemmas.subset_refl.
      - rewrite depvars_rprogram_rcons. apply: (VSLemmas.subset_trans _ (IH _)).
        exact: (depvars_rinstr_lb vs i).
    Qed.

    Lemma depvars_rprogram_ub vs p :
      VS.subset (depvars_rprogram vs p) (VS.union vs (vars_program p)).
    Proof.
      move: p vs. apply: last_ind => [| p i IH] vs //=.
      - exact: VSLemmas.union_subset_1.
      - rewrite depvars_rprogram_rcons. rewrite vars_program_rcons.
        rewrite (VSLemmas.P.union_sym (vars_program p)). rewrite -VSLemmas.P.union_assoc.
        apply: (VSLemmas.subset_trans (IH _)).
        apply: VSLemmas.union_subsets; last exact: VSLemmas.subset_refl.
        exact: (depvars_rinstr_ub vs i).
    Qed.

    Lemma depvars_epre_eprogram_lb vs e p :
      VS.subset vs (depvars_epre_eprogram vs e p).
    Proof.
      rewrite /depvars_epre_eprogram.
      apply: (VSLemmas.subset_trans _ (depvars_ebexp_lb _ e)).
      exact: (depvars_eprogram_lb vs p).
    Qed.

    Lemma depvars_epre_eprogram_ub vs e p :
      VS.subset (depvars_epre_eprogram vs e p)
                (VS.union vs (VS.union (vars_ebexp e) (vars_program p))).
    Proof.
      rewrite /depvars_epre_eprogram.
      apply: (VSLemmas.subset_trans (depvars_ebexp_ub _ e)).
      apply: VSLemmas.subset_union3; last by VSLemmas.dp_subset.
      apply: (VSLemmas.subset_trans (depvars_eprogram_ub vs p)).
      by VSLemmas.dp_subset.
    Qed.

    Lemma depvars_rpre_rprogram_lb vs e p :
      VS.subset vs (depvars_rpre_rprogram vs e p).
    Proof.
      rewrite /depvars_rpre_rprogram.
      apply: (VSLemmas.subset_trans _ (depvars_rbexp_lb _ e)).
      exact: (depvars_rprogram_lb vs p).
    Qed.

    Lemma depvars_rpre_rprogram_ub vs e p :
      VS.subset (depvars_rpre_rprogram vs e p)
                (VS.union vs (VS.union (vars_rbexp e) (vars_program p))).
    Proof.
      rewrite /depvars_rpre_rprogram.
      apply: (VSLemmas.subset_trans (depvars_rbexp_ub _ e)).
      apply: VSLemmas.subset_union3; last by VSLemmas.dp_subset.
      apply: (VSLemmas.subset_trans (depvars_rprogram_ub vs p)).
      by VSLemmas.dp_subset.
    Qed.


    Lemma depvars_ebexp_cardinal_sat vs e :
      VS.cardinal (depvars_ebexp vs e) <= VS.cardinal vs ->
      VS.Equal (depvars_ebexp vs e) vs.
    Proof.
      move=> Hc. move: (depvars_ebexp_lb vs e) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_ebexp vs e).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_ebexp vs e)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.

    Lemma depvars_rbexp_cardinal_sat vs e :
      VS.cardinal (depvars_rbexp vs e) <= VS.cardinal vs ->
      VS.Equal (depvars_rbexp vs e) vs.
    Proof.
      move=> Hc. move: (depvars_rbexp_lb vs e) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_rbexp vs e).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_rbexp vs e)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.

    Lemma depvars_einstr_cardinal_sat vs i :
      VS.cardinal (depvars_einstr vs i) <= VS.cardinal vs ->
      VS.Equal (depvars_einstr vs i) vs.
    Proof.
      move=> Hc. move: (depvars_einstr_lb vs i) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_einstr vs i).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_einstr vs i)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.

    Lemma depvars_rinstr_cardinal_sat vs i :
      VS.cardinal (depvars_rinstr vs i) <= VS.cardinal vs ->
      VS.Equal (depvars_rinstr vs i) vs.
    Proof.
      move=> Hc. move: (depvars_rinstr_lb vs i) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_rinstr vs i).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_rinstr vs i)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.

    Lemma depvars_eprogram_cardinal_sat vs p :
      VS.cardinal (depvars_eprogram vs p) <= VS.cardinal vs ->
      VS.Equal (depvars_eprogram vs p) vs.
    Proof.
      move=> Hc. move: (depvars_eprogram_lb vs p) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_eprogram vs p).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_eprogram vs p)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.

    Lemma depvars_rprogram_cardinal_sat vs p :
      VS.cardinal (depvars_rprogram vs p) <= VS.cardinal vs ->
      VS.Equal (depvars_rprogram vs p) vs.
    Proof.
      move=> Hc. move: (depvars_rprogram_lb vs p) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_rprogram vs p).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_rprogram vs p)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.

    Lemma depvars_epre_eprogram_cardinal_sat vs e p :
      VS.cardinal (depvars_epre_eprogram vs e p) <= VS.cardinal vs ->
      VS.Equal (depvars_epre_eprogram vs e p) vs.
    Proof.
      move=> Hc. move: (depvars_epre_eprogram_lb vs e p) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_epre_eprogram vs e p).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_epre_eprogram vs e p)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.

    Lemma depvars_rpre_rprogram_cardinal_sat vs e p :
      VS.cardinal (depvars_rpre_rprogram vs e p) <= VS.cardinal vs ->
      VS.Equal (depvars_rpre_rprogram vs e p) vs.
    Proof.
      move=> Hc. move: (depvars_rpre_rprogram_lb vs e p) => Hsub.
      have Heq: VS.cardinal vs = VS.cardinal (depvars_rpre_rprogram vs e p).
      { move: (VSLemmas.subset_cardinal Hsub) Hc => {Hsub}.
        move: (VS.cardinal vs) (VS.cardinal (depvars_rpre_rprogram vs e p)) => n m H1 H2.
        move: (eqn_leq n m). rewrite H1 H2 /=. by move/eqP. }
      apply: VSLemmas.P.equal_sym. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_cardinal_equal Hsub Heq).
    Qed.


    Lemma depvars_ebexp_subset_sat vs e :
      VS.subset (depvars_ebexp vs e) vs -> VS.Equal (depvars_ebexp vs e) vs.
    Proof.
      move=> Hsub. apply: depvars_ebexp_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_rbexp_subset_sat vs e :
      VS.subset (depvars_rbexp vs e) vs -> VS.Equal (depvars_rbexp vs e) vs.
    Proof.
      move=> Hsub. apply: depvars_rbexp_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_einstr_subset_sat vs i :
      VS.subset (depvars_einstr vs i) vs -> VS.Equal (depvars_einstr vs i) vs.
    Proof.
      move=> Hsub. apply: depvars_einstr_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_rinstr_subset_sat vs i :
      VS.subset (depvars_rinstr vs i) vs -> VS.Equal (depvars_rinstr vs i) vs.
    Proof.
      move=> Hsub. apply: depvars_rinstr_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_eprogram_subset_sat vs p :
      VS.subset (depvars_eprogram vs p) vs -> VS.Equal (depvars_eprogram vs p) vs.
    Proof.
      move=> Hsub. apply: depvars_eprogram_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_rprogram_subset_sat vs p :
      VS.subset (depvars_rprogram vs p) vs -> VS.Equal (depvars_rprogram vs p) vs.
    Proof.
      move=> Hsub. apply: depvars_rprogram_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_epre_eprogram_subset_sat vs e p :
      VS.subset (depvars_epre_eprogram vs e p) vs ->
      VS.Equal (depvars_epre_eprogram vs e p) vs.
    Proof.
      move=> Hsub. apply: depvars_epre_eprogram_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_rpre_rprogram_subset_sat vs e p :
      VS.subset (depvars_rpre_rprogram vs e p) vs ->
      VS.Equal (depvars_rpre_rprogram vs e p) vs.
    Proof.
      move=> Hsub. apply: depvars_rpre_rprogram_cardinal_sat.
      exact: (VSLemmas.subset_cardinal Hsub).
    Qed.

    Lemma depvars_eprogram_ind_sat1 vs p i :
      VS.subset (depvars_eprogram (depvars_einstr vs i) p) vs ->
      VS.Equal (depvars_einstr vs i) vs.
    Proof.
      move=> Hsub. move: (depvars_einstr_lb vs i) => Hsub1.
      move: (VSLemmas.subset_trans (depvars_eprogram_lb (depvars_einstr vs i) p) Hsub) => Hsub2.
      apply/VSLemmas.equalP. exact: (VSLemmas.subset_antisym Hsub2 Hsub1).
    Qed.

    Lemma depvars_eprogram_ind_sat2 vs p i :
      VS.subset (depvars_eprogram (depvars_einstr vs i) p) vs ->
      VS.Equal (depvars_eprogram (depvars_einstr vs i) p) vs.
    Proof.
      move=> Hsub. move: (depvars_eprogram_ind_sat1 Hsub) => H.
      rewrite H in Hsub *. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_antisym Hsub (depvars_eprogram_lb vs p)).
    Qed.

    Lemma depvars_rprogram_ind_sat1 vs p i :
      VS.subset (depvars_rprogram (depvars_rinstr vs i) p) vs ->
      VS.Equal (depvars_rinstr vs i) vs.
    Proof.
      move=> Hsub. move: (depvars_rinstr_lb vs i) => Hsub1.
      move: (VSLemmas.subset_trans (depvars_rprogram_lb (depvars_rinstr vs i) p) Hsub) => Hsub2.
      apply/VSLemmas.equalP. exact: (VSLemmas.subset_antisym Hsub2 Hsub1).
    Qed.

    Lemma depvars_rprogram_ind_sat2 vs p i :
      VS.subset (depvars_rprogram (depvars_rinstr vs i) p) vs ->
      VS.Equal (depvars_rprogram (depvars_rinstr vs i) p) vs.
    Proof.
      move=> Hsub. move: (depvars_rprogram_ind_sat1 Hsub) => H.
      rewrite H in Hsub *. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_antisym Hsub (depvars_rprogram_lb vs p)).
    Qed.

    Lemma depvars_epre_eprogram_ind_sat1 vs e p :
      VS.subset (depvars_ebexp (depvars_eprogram vs p) e) vs ->
      VS.Equal (depvars_eprogram vs p) vs.
    Proof.
      move=> Hsub. move: (depvars_eprogram_lb vs p) => Hsub1.
      move: (VSLemmas.subset_trans (depvars_ebexp_lb (depvars_eprogram vs p) e) Hsub) => Hsub2.
      apply/VSLemmas.equalP. exact: (VSLemmas.subset_antisym Hsub2 Hsub1).
    Qed.

    Lemma depvars_epre_eprogram_ind_sat2 vs e p :
      VS.subset (depvars_ebexp (depvars_eprogram vs p) e) vs ->
      VS.Equal (depvars_ebexp (depvars_eprogram vs p) e) vs.
    Proof.
      move=> Hsub. move: (depvars_epre_eprogram_ind_sat1 Hsub) => H.
      rewrite H in Hsub *. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_antisym Hsub (depvars_ebexp_lb vs e)).
    Qed.

    Lemma depvars_rpre_rprogram_ind_sat1 vs e p :
      VS.subset (depvars_rbexp (depvars_rprogram vs p) e) vs ->
      VS.Equal (depvars_rprogram vs p) vs.
    Proof.
      move=> Hsub. move: (depvars_rprogram_lb vs p) => Hsub1.
      move: (VSLemmas.subset_trans (depvars_rbexp_lb (depvars_rprogram vs p) e) Hsub) => Hsub2.
      apply/VSLemmas.equalP. exact: (VSLemmas.subset_antisym Hsub2 Hsub1).
    Qed.

    Lemma depvars_rpre_rprogram_ind_sat2 vs e p :
      VS.subset (depvars_rbexp (depvars_rprogram vs p) e) vs ->
      VS.Equal (depvars_rbexp (depvars_rprogram vs p) e) vs.
    Proof.
      move=> Hsub. move: (depvars_rpre_rprogram_ind_sat1 Hsub) => H.
      rewrite H in Hsub *. apply/VSLemmas.equalP.
      exact: (VSLemmas.subset_antisym Hsub (depvars_rbexp_lb vs e)).
    Qed.


    Fixpoint ebexp_partition vs e :=
      match e with
      | Eand e1 e2 => ebexp_partition vs e1 /\ ebexp_partition vs e2
      | _ => VSLemmas.disjoint (vars_ebexp e) vs \/ VS.subset (vars_ebexp e) vs
      end.

    Fixpoint rbexp_partition vs e :=
      match e with
      | Rand e1 e2 => rbexp_partition vs e1 /\ rbexp_partition vs e2
      | _ => VSLemmas.disjoint (vars_rbexp e) vs \/ VS.subset (vars_rbexp e) vs
      end.

    Definition einstr_partition vs i :=
      match i with
      | Iassume (e, r) => ebexp_partition vs e
      | _ => VSLemmas.disjoint (lvs_instr i) vs \/ VS.subset (vars_instr i) vs
      end.

    Definition rinstr_partition vs i :=
      match i with
      | Iassume (e, r) => rbexp_partition vs r
      | _ => VSLemmas.disjoint (lvs_instr i) vs \/ VS.subset (vars_instr i) vs
      end.

    Fixpoint eprogram_partition vs p :=
      match p with
      | [::] => True
      | hd::tl => einstr_partition vs hd /\ eprogram_partition vs tl
      end.

    Fixpoint rprogram_partition vs p :=
      match p with
      | [::] => True
      | hd::tl => rinstr_partition vs hd /\ rprogram_partition vs tl
      end.

    Definition espec_partition vs s :=
      ebexp_partition vs (eqn_bexp (espre s)) /\ eprogram_partition vs (esprog s).

    Definition rspec_partition vs s :=
      rbexp_partition vs (rspre s) /\ rprogram_partition vs (rsprog s).


    Lemma eprogram_partition_rcons vs p i :
      eprogram_partition vs (rcons p i) <-> eprogram_partition vs p /\ einstr_partition vs i.
    Proof.
      elim: p i vs => [| i p IH] j vs //=.
      - tauto.
      - move: (IH j vs). tauto.
    Qed.

    Lemma rprogram_partition_rcons vs p i :
      rprogram_partition vs (rcons p i) <-> rprogram_partition vs p /\ rinstr_partition vs i.
    Proof.
      elim: p i vs => [| i p IH] j vs //=.
      - tauto.
      - move: (IH j vs). tauto.
    Qed.
    Ltac mytac ::=
      match goal with
      | H : VSLemmas.disjoint ?vs1 ?vs2 = true |-
          is_true (VSLemmas.disjoint ?vs2 ?vs1) \/ _ =>
          left; rewrite VSLemmas.disjoint_sym; assumption
      | H : is_true (VS.subset (VS.union _ ?vs2) ?vs1) |-
          _ \/ is_true (VS.subset ?vs2 ?vs1) =>
          right; exact: (VSLemmas.subset_union5 H)
      end.

    Ltac mytac ::=
      match goal with
      | H : VSLemmas.disjoint ?vs1 ?vs2 = true |-
          is_true (VSLemmas.disjoint ?vs2 ?vs1) \/ _ =>
          left; rewrite VSLemmas.disjoint_sym; assumption
      | H : is_true (VS.subset (VS.union _ ?vs2) ?vs1) |-
          _ \/ is_true (VS.subset ?vs2 ?vs1) =>
          right; exact: (VSLemmas.subset_union5 H)
      | H0 : VSLemmas.disjoint ?vs (VS.singleton ?t) = false,
          H : VSLemmas.disjoint ?vs (VS.add ?t _) = true |- _ =>
          (rewrite VSLemmas.disjoint_singleton in H0);
          (rewrite VSLemmas.disjoint_add H0 /= in H);
          discriminate
      end.

    Lemma depvars_ebexp_partition vs e :
      VS.subset (depvars_ebexp vs e) vs -> ebexp_partition vs e.
    Proof.
      elim: e vs => /=.
      - move=> vs _. right. exact: VSLemmas.subset_empty.
      - move=> e1 e2 vs. rewrite /depvars_ebexp /=. case_if; by mytac.
      - move=> e1 e2 ms vs. rewrite /depvars_ebexp /=. case_if; by mytac.
      - move=> e1 IH1 e2 IH2 vs. rewrite depvars_eand => Hsub.
        move: (VSLemmas.subset_trans (depvars_ebexp_lb (depvars_ebexp vs e1) e2) Hsub) => Hsub1.
        split; first exact: (IH1 _ Hsub1). apply: IH2.
        move: (depvars_ebexp_subset_sat Hsub1) => Heq.
        rewrite Heq in Hsub. assumption.
    Qed.

    Lemma depvars_rbexp_partition vs e :
      VS.subset (depvars_rbexp vs e) vs -> rbexp_partition vs e.
    Proof.
      elim: e vs => /=.
      - move=> vs _. right. exact: VSLemmas.subset_empty.
      - move=> n e1 e2 vs. rewrite /depvars_rbexp /=. case_if; by mytac.
      - move=> n op e1 e2 vs. rewrite /depvars_rbexp /=. case_if; by mytac.
      - move=> e IH vs. rewrite /depvars_rbexp /=. case_if; by mytac.
      - move=> e1 IH1 e2 IH2 vs. rewrite depvars_rand => Hsub.
        move: (VSLemmas.subset_trans (depvars_rbexp_lb (depvars_rbexp vs e1) e2) Hsub) => Hsub1.
        split; first exact: (IH1 _ Hsub1). apply: IH2.
        move: (depvars_rbexp_subset_sat Hsub1) => Heq.
        rewrite Heq in Hsub. assumption.
      - move=> e1 IH1 e2 IH2 vs. rewrite /depvars_rbexp /=. case_if; by mytac.
    Qed.

    Lemma depvars_einstr_partition vs i :
      VS.subset (depvars_einstr vs i) vs -> einstr_partition vs i.
    Proof.
      case: i => //=; intros; case_if'; case_match_atom; try mytac.
      move: H; case_if'. exact: depvars_ebexp_partition.
    Qed.

    Lemma depvars_rinstr_partition vs i :
      VS.subset (depvars_rinstr vs i) vs -> rinstr_partition vs i.
    Proof.
      case: i => //=; intros; case_if'; case_match_atom; try mytac.
      move: H; case_if'. exact: depvars_rbexp_partition.
    Qed.

    Lemma depvars_eprogram_partition vs p :
      VS.subset (depvars_eprogram vs p) vs -> eprogram_partition vs p.
    Proof.
      move: p vs. apply: last_ind => [| p i IH] vs //=.
      rewrite depvars_eprogram_rcons => Hsub. rewrite eprogram_partition_rcons.
      move: (depvars_eprogram_ind_sat1 Hsub) => Hi.
      move: (depvars_eprogram_ind_sat2 Hsub) => Hp. rewrite Hi in Hp. split.
      - apply: IH. rewrite Hp. exact: VSLemmas.subset_refl.
      - apply: depvars_einstr_partition. rewrite Hi. exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_rprogram_partition vs p :
      VS.subset (depvars_rprogram vs p) vs -> rprogram_partition vs p.
    Proof.
      move: p vs. apply: last_ind => [| p i IH] vs //=.
      rewrite depvars_rprogram_rcons => Hsub. rewrite rprogram_partition_rcons.
      move: (depvars_rprogram_ind_sat1 Hsub) => Hi.
      move: (depvars_rprogram_ind_sat2 Hsub) => Hp. rewrite Hi in Hp. split.
      - apply: IH. rewrite Hp. exact: VSLemmas.subset_refl.
      - apply: depvars_rinstr_partition. rewrite Hi. exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_epre_eprogram_partition1 vs e p :
      VS.subset (depvars_epre_eprogram vs e p) vs -> ebexp_partition vs e.
    Proof.
      rewrite /depvars_epre_eprogram => Hsub.
      move: (depvars_epre_eprogram_ind_sat1 Hsub) => Hp.
      move: (depvars_epre_eprogram_ind_sat2 Hsub) => He.
      apply: depvars_ebexp_partition. rewrite Hp in He. rewrite He.
      exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_epre_eprogram_partition2 vs e p :
      VS.subset (depvars_epre_eprogram vs e p) vs -> eprogram_partition vs p.
    Proof.
      rewrite /depvars_epre_eprogram => Hsub.
      move: (depvars_epre_eprogram_ind_sat1 Hsub) => Hp.
      apply: depvars_eprogram_partition. rewrite Hp.
      exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_rpre_rprogram_partition1 vs e p :
      VS.subset (depvars_rpre_rprogram vs e p) vs -> rbexp_partition vs e.
    Proof.
      rewrite /depvars_rpre_rprogram => Hsub.
      move: (depvars_rpre_rprogram_ind_sat1 Hsub) => Hp.
      move: (depvars_rpre_rprogram_ind_sat2 Hsub) => He.
      apply: depvars_rbexp_partition. rewrite Hp in He. rewrite He.
      exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_rpre_rprogram_partition2 vs e p :
      VS.subset (depvars_rpre_rprogram vs e p) vs -> rprogram_partition vs p.
    Proof.
      rewrite /depvars_rpre_rprogram => Hsub.
      move: (depvars_rpre_rprogram_ind_sat1 Hsub) => Hp.
      apply: depvars_rprogram_partition. rewrite Hp.
      exact: VSLemmas.subset_refl.
    Qed.


    Section AddRelevantVarsRec.

      Variable e : ebexp.
      Variable r : rbexp.
      Variable p : program.

      Definition evsize vs :=
        let vsall := VS.union vs (VS.union (vars_ebexp e) (vars_program p)) in
        VS.cardinal vsall - VS.cardinal vs.

      Definition rvsize vs :=
        let vsall := VS.union vs (VS.union (vars_rbexp r) (vars_program p)) in
        VS.cardinal vsall - VS.cardinal vs.

      From Coq Require Import Recdef.

      Function depvars_epre_eprogram_sat vs
               {measure evsize vs} :=
        let vs' := depvars_epre_eprogram vs e p in
        match VS.cardinal vs' > VS.cardinal vs with
        | true => depvars_epre_eprogram_sat vs'
        | false => vs'
        end.
      Proof.
        move=> vs H. rewrite /evsize.
        have Hsub1:
          (VS.subset
             (VS.union (depvars_epre_eprogram vs e p)
                       (VS.union (vars_ebexp e) (vars_program p)))
             (VS.union vs (VS.union (vars_ebexp e) (vars_program p)))).
        { apply: VSLemmas.subset_union3.
          - exact: depvars_epre_eprogram_ub.
          - by VSLemmas.dp_subset. }
        have Hsub2:
          (VS.subset
             (VS.union vs (VS.union (vars_ebexp e) (vars_program p)))
             (VS.union (depvars_epre_eprogram vs e p)
                       (VS.union (vars_ebexp e) (vars_program p)))).
        { apply: VSLemmas.union_subsets; last exact: VSLemmas.subset_refl.
          exact: depvars_epre_eprogram_lb. }
        move: (VSLemmas.subset_antisym Hsub1 Hsub2) => {Hsub1 Hsub2} /VSLemmas.equalP Heq.
        rewrite Heq. apply: ltn_lt. apply: ltn_sub2l.
        - apply: (ltn_leq_trans H). apply: VSLemmas.subset_cardinal.
          exact: depvars_epre_eprogram_ub.
        - exact: H.
      Qed.

      Function depvars_rpre_rprogram_sat vs
               {measure rvsize vs} :=
        let vs' := depvars_rpre_rprogram vs r p in
        match VS.cardinal vs' > VS.cardinal vs with
        | true => depvars_rpre_rprogram_sat vs'
        | false => vs'
        end.
      Proof.
        move=> vs H. rewrite /rvsize.
        have Hsub1:
          (VS.subset
             (VS.union (depvars_rpre_rprogram vs r p)
                       (VS.union (vars_rbexp r) (vars_program p)))
             (VS.union vs (VS.union (vars_rbexp r) (vars_program p)))).
        { apply: VSLemmas.subset_union3.
          - exact: depvars_rpre_rprogram_ub.
          - by VSLemmas.dp_subset. }
        have Hsub2:
          (VS.subset
             (VS.union vs (VS.union (vars_rbexp r) (vars_program p)))
             (VS.union (depvars_rpre_rprogram vs r p)
                       (VS.union (vars_rbexp r) (vars_program p)))).
        { apply: VSLemmas.union_subsets; last exact: VSLemmas.subset_refl.
          exact: depvars_rpre_rprogram_lb. }
        move: (VSLemmas.subset_antisym Hsub1 Hsub2) => {Hsub1 Hsub2} /VSLemmas.equalP Heq.
        rewrite Heq. apply: ltn_lt. apply: ltn_sub2l.
        - apply: (ltn_leq_trans H). apply: VSLemmas.subset_cardinal.
          exact: depvars_rpre_rprogram_ub.
        - exact: H.
      Qed.

      Lemma depvars_epre_eprogram_sat_lb vs :
        VS.subset vs (depvars_epre_eprogram_sat vs).
      Proof.
        apply: (@depvars_epre_eprogram_sat_ind (fun vs vs' => VS.subset vs vs')).
        - move=> {}vs vs' Hc Hsub.
          apply: (VSLemmas.subset_trans (depvars_epre_eprogram_lb vs e p)).
          exact: Hsub.
        - move=> {}vs vs' Hc. exact: (depvars_epre_eprogram_lb vs e p).
      Qed.

      Lemma depvars_epre_eprogram_sat_ub vs :
        VS.subset (depvars_epre_eprogram_sat vs)
                  (VS.union vs (VS.union (vars_ebexp e) (vars_program p))).
      Proof.
        apply: (@depvars_epre_eprogram_sat_ind
                  (fun vs vs' =>
                     VS.subset vs' (VS.union vs (VS.union (vars_ebexp e) (vars_program p))))).
        - move=> {}vs vs' Hc Hsub. apply: (VSLemmas.subset_trans Hsub).
          apply: (VSLemmas.subset_union3 (depvars_epre_eprogram_ub vs e p)).
          by VSLemmas.dp_subset.
        - move=> {}vs vs' Hc. exact: (depvars_epre_eprogram_ub vs e p).
      Qed.

      Lemma depvars_rpre_rprogram_sat_lb vs :
        VS.subset vs (depvars_rpre_rprogram_sat vs).
      Proof.
        apply: (@depvars_rpre_rprogram_sat_ind (fun vs vs' => VS.subset vs vs')).
        - move=> {}vs vs' Hc Hsub.
          apply: (VSLemmas.subset_trans (depvars_rpre_rprogram_lb vs r p)).
          exact: Hsub.
        - move=> {}vs vs' Hc. exact: (depvars_rpre_rprogram_lb vs r p).
      Qed.

      Lemma depvars_rpre_rprogram_sat_ub vs :
        VS.subset (depvars_rpre_rprogram_sat vs)
                  (VS.union vs (VS.union (vars_rbexp r) (vars_program p))).
      Proof.
        apply: (@depvars_rpre_rprogram_sat_ind
                  (fun vs vs' =>
                     VS.subset vs' (VS.union vs (VS.union (vars_rbexp r) (vars_program p))))).
        - move=> {}vs vs' Hc Hsub. apply: (VSLemmas.subset_trans Hsub).
          apply: (VSLemmas.subset_union3 (depvars_rpre_rprogram_ub vs r p)).
          by VSLemmas.dp_subset.
        - move=> {}vs vs' Hc. exact: (depvars_rpre_rprogram_ub vs r p).
      Qed.


      Lemma depvars_epre_eprogram_sat_partition1 vs :
        ebexp_partition (depvars_epre_eprogram_sat vs) e.
      Proof.
        apply: (@depvars_epre_eprogram_sat_ind
                  (fun vs vs' => ebexp_partition vs' e)).
        - move=> {}vs vs' Hc Hp. assumption.
        - move=> {}vs vs' Hc. move/idP/negP: Hc => Hc. rewrite -leqNgt in Hc.
          move: (depvars_epre_eprogram_cardinal_sat Hc) => Heq.
          apply: (depvars_epre_eprogram_partition1 (p := p)). rewrite /vs'.
          rewrite !Heq. exact: VSLemmas.subset_refl.
      Qed.

      Lemma depvars_epre_eprogram_sat_partition2 vs :
        eprogram_partition (depvars_epre_eprogram_sat vs) p.
      Proof.
        apply: (@depvars_epre_eprogram_sat_ind
                  (fun vs vs' => eprogram_partition vs' p)).
        - move=> {}vs vs' Hc Hp. assumption.
        - move=> {}vs vs' Hc. move/idP/negP: Hc => Hc. rewrite -leqNgt in Hc.
          move: (depvars_epre_eprogram_cardinal_sat Hc) => Heq.
          apply: (depvars_epre_eprogram_partition2 (e := e)). rewrite /vs'.
          rewrite !Heq. exact: VSLemmas.subset_refl.
      Qed.

      Lemma depvars_rpre_rprogram_sat_partition1 vs :
        rbexp_partition (depvars_rpre_rprogram_sat vs) r.
      Proof.
        apply: (@depvars_rpre_rprogram_sat_ind
                  (fun vs vs' => rbexp_partition vs' r)).
        - move=> {}vs vs' Hc Hp. assumption.
        - move=> {}vs vs' Hc. move/idP/negP: Hc => Hc. rewrite -leqNgt in Hc.
          move: (depvars_rpre_rprogram_cardinal_sat Hc) => Heq.
          apply: (depvars_rpre_rprogram_partition1 (p := p)). rewrite /vs'.
          rewrite !Heq. exact: VSLemmas.subset_refl.
      Qed.

      Lemma depvars_rpre_rprogram_sat_partition2 vs :
        rprogram_partition (depvars_rpre_rprogram_sat vs) p.
      Proof.
        apply: (@depvars_rpre_rprogram_sat_ind
                  (fun vs vs' => rprogram_partition vs' p)).
        - move=> {}vs vs' Hc Hp. assumption.
        - move=> {}vs vs' Hc. move/idP/negP: Hc => Hc. rewrite -leqNgt in Hc.
          move: (depvars_rpre_rprogram_cardinal_sat Hc) => Heq.
          apply: (depvars_rpre_rprogram_partition2 (e := r)). rewrite /vs'.
          rewrite !Heq. exact: VSLemmas.subset_refl.
      Qed.

    End AddRelevantVarsRec.

    Lemma depvars_epre_eprogram_sat_partition_espec s :
      espec_partition (depvars_epre_eprogram_sat
                         (eqn_bexp (espre s)) (esprog s) (vars_ebexp (espost s))) s.
    Proof.
      split.
      - exact: depvars_epre_eprogram_sat_partition1.
      - exact: depvars_epre_eprogram_sat_partition2.
    Qed.

    Lemma depvars_rpre_rprogram_sat_partition_rspec s :
      rspec_partition (depvars_rpre_rprogram_sat
                         (rspre s) (rsprog s) (vars_rbexp (rspost s))) s.
    Proof.
      split.
      - exact: depvars_rpre_rprogram_sat_partition1.
      - exact: depvars_rpre_rprogram_sat_partition2.
    Qed.


    Local Notation mem1 v vs i := (if VS.mem v vs then Some i
                                   else None) (only parsing).
    Local Notation mem2 v1 v2 vs i := (if VS.mem v1 vs || VS.mem v2 vs then Some i
                                       else None) (only parsing).

    Fixpoint slice_ebexp vs e :=
      match e with
      | Etrue => e
      | Eeq e1 e2 =>
          if VSLemmas.disjoint vs (vars_eexp e1)
             && VSLemmas.disjoint vs (vars_eexp e2) then etrue
          else e
      | Eeqmod e1 e2 ms =>
          if VSLemmas.disjoint vs (vars_eexp e1)
             && VSLemmas.disjoint vs (vars_eexp e2)
             && VSLemmas.disjoint vs (vars_eexps ms) then etrue
          else e
      | Eand e1 e2 =>
          match slice_ebexp vs e1, slice_ebexp vs e2 with
          | e1, Etrue => e1
          | Etrue, e2 => e2
          | e1, e2 => Eand e1 e2
          end
      end.

    Fixpoint slice_rbexp vs e :=
      match e with
      | Rtrue => e
      | Req _ e1 e2 =>
          if VSLemmas.disjoint vs (vars_rexp e1)
             && VSLemmas.disjoint vs (vars_rexp e2) then rtrue
          else e
      | Rcmp _ _ e1 e2 =>
          if VSLemmas.disjoint vs (vars_rexp e1)
             && VSLemmas.disjoint vs (vars_rexp e2) then rtrue
          else e
      | Rneg e' => if VSLemmas.disjoint vs (vars_rbexp e') then rtrue
                   else e
      | Rand e1 e2 =>
        match slice_rbexp vs e1, slice_rbexp vs e2 with
        | e1, Rtrue => e1
        | Rtrue, e2 => e2
        | e1, e2 => Rand e1 e2
        end
      | Ror e1 e2 =>
        if VSLemmas.disjoint vs (vars_rbexp e1)
           && VSLemmas.disjoint vs (vars_rbexp e2) then rtrue
        else e
      end.

    Definition slice_einstr vs i :=
      match i with
      | Iassume (e, _) => Some (Iassume (slice_ebexp vs e, rtrue))
      | _ => if VSLemmas.disjoint (lvs_instr i) vs then None else Some i
    end.

    Definition slice_rinstr vs i :=
      match i with
      | Iassume (_, r) => Some (Iassume (etrue, slice_rbexp vs r))
      | _ => if VSLemmas.disjoint (lvs_instr i) vs then None else Some i
    end.

    Fixpoint slice_eprogram vs p :=
      match p with
      | [::] => [::]
      | hd::tl => match slice_einstr vs hd with
                  | None => slice_eprogram vs tl
                  | Some i => i::slice_eprogram vs tl
                  end
      end.

    Fixpoint slice_rprogram vs p :=
      match p with
      | [::] => [::]
      | hd::tl => match slice_rinstr vs hd with
                  | None => slice_rprogram vs tl
                  | Some i => i::slice_rprogram vs tl
                  end
      end.

    Definition slice_espec (s : espec) :=
      let vs := depvars_epre_eprogram_sat
                  (eqn_bexp (espre s)) (esprog s) (vars_ebexp (espost s)) in
      {| esinputs := esinputs s;
         espre := (slice_ebexp vs (eqn_bexp (espre s)), rng_bexp (espre s));
         esprog := slice_eprogram vs (esprog s);
         espost := espost s |}.

    Definition slice_rspec (s : rspec) :=
      let vs := depvars_rpre_rprogram_sat
                  (rspre s) (rsprog s) (vars_rbexp (rspost s)) in
      {| rsinputs := rsinputs s;
         rspre := slice_rbexp vs (rspre s);
         rsprog := slice_rprogram vs (rsprog s);
         rspost := rspost s |}.


    Lemma slice_eprogram_rcons_none vs p i :
      slice_einstr vs i = None ->
      slice_eprogram vs (rcons p i) = slice_eprogram vs p.
    Proof.
      elim: p vs i => [| i p IH] vs i' /= Hsi.
      - rewrite Hsi. reflexivity.
      - rewrite !(IH _ _ Hsi). reflexivity.
    Qed.

    Lemma slice_rprogram_rcons_none vs p i :
      slice_rinstr vs i = None ->
      slice_rprogram vs (rcons p i) = slice_rprogram vs p.
    Proof.
      elim: p vs i => [| i p IH] vs i' /= Hsi.
      - rewrite Hsi. reflexivity.
      - rewrite !(IH _ _ Hsi). reflexivity.
    Qed.

    Lemma slice_eprogram_rcons_some vs p i i' :
      slice_einstr vs i = Some i' ->
      slice_eprogram vs (rcons p i) = rcons (slice_eprogram vs p) i'.
    Proof.
      elim: p vs i i' => [| i p IH] vs i1 i2 /= Hsi1.
      - rewrite Hsi1. reflexivity.
      - rewrite !(IH _ _ _ Hsi1). case Hsi: (slice_einstr vs i).
        + rewrite rcons_cons. reflexivity.
        + reflexivity.
    Qed.

    Lemma slice_rprogram_rcons_some vs p i i' :
      slice_rinstr vs i = Some i' ->
      slice_rprogram vs (rcons p i) = rcons (slice_rprogram vs p) i'.
    Proof.
      elim: p vs i i' => [| i p IH] vs i1 i2 /= Hsi1.
      - rewrite Hsi1. reflexivity.
      - rewrite !(IH _ _ _ Hsi1). case Hsi: (slice_rinstr vs i).
        + rewrite rcons_cons. reflexivity.
        + reflexivity.
    Qed.


    Global Instance add_proper_slice_ebexp_set :
      Proper (VS.Equal ==> eq ==> eq) slice_ebexp.
    Proof.
      move=> s1 s2 Hs e1 e2 ?; subst. (elim: e2 => //=);
                                      intros; try rewrite !Hs /=; try reflexivity.
      rewrite H H0. reflexivity.
    Qed.

    Global Instance add_proper_slice_rbexp_set :
      Proper (VS.Equal ==> eq ==> eq) slice_rbexp.
    Proof.
      move=> s1 s2 Hs e1 e2 ?; subst. (elim: e2 => //=);
                                      intros; try rewrite !Hs /=; try reflexivity.
      rewrite H H0. reflexivity.
    Qed.

    Global Instance add_proper_slice_einstr_set :
      Proper (VS.Equal ==> eq ==> eq) slice_einstr.
    Proof.
      move=> s1 s2 Hs i1 i2 ?; subst. (case: i2 => //=);
                                      intros; try rewrite !Hs /=; try reflexivity.
      case: b => [e _] /=. rewrite Hs. reflexivity.
    Qed.

    Global Instance add_proper_slice_rinstr_set :
      Proper (VS.Equal ==> eq ==> eq) slice_rinstr.
    Proof.
      move=> s1 s2 Hs i1 i2 ?; subst. (case: i2 => //=);
                                      intros; try rewrite !Hs /=; try reflexivity.
      case: b => [_ r] /=. rewrite Hs. reflexivity.
    Qed.

    Global Instance add_proper_slice_eprogram_set :
      Proper (VS.Equal ==> eq ==> eq) slice_eprogram.
    Proof.
      move=> s1 s2 Hs p1 p2 ?; subst. (elim: p2 => //=);
                                      intros; try rewrite !Hs /=; try reflexivity.
      rewrite H Hs. reflexivity.
    Qed.

    Global Instance add_proper_slice_rprogram_set :
      Proper (VS.Equal ==> eq ==> eq) slice_rprogram.
    Proof.
      move=> s1 s2 Hs p1 p2 ?; subst. (elim: p2 => //=);
                                      intros; try rewrite !Hs /=; try reflexivity.
      rewrite H Hs. reflexivity.
    Qed.

    Lemma slice_rinstr_rng_instr vs i i' :
      slice_rinstr vs i = Some i' -> is_rng_instr i'.
    Proof.
      case: i => //=; intros; case_if; try discriminate; try case_option; subst; try done.
      case: b H => [e r] /=. case=> ?; subst. done.
    Qed.

    Lemma slice_rprogram_rng_program vs p : is_rng_program (slice_rprogram vs p).
    Proof.
      elim: p => [| i p IH] //=. case Hs: (slice_rinstr vs i).
      - simpl. rewrite (slice_rinstr_rng_instr Hs) /=. exact: IH.
      - assumption.
    Qed.

    Lemma slice_rspec_rng_spec s : is_rng_rspec (slice_rspec s).
    Proof. exact: slice_rprogram_rng_program. Qed.


    Ltac mytac ::=
      (repeat
         match goal with
         | H : is_true (_ && _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             move/andP: H => [H1 H2]
         | H : None = Some _ |- _ => discriminate
         | H : Some _ = None |- _ => discriminate
         | H : Some _ = Some _ |- _ => case: H => H; subst; simpl
         | |- is_true (VS.subset VS.empty _) => exact: VSLemmas.subset_empty
         | H : _ \/ is_true (VS.subset ?vs1 ?vs2) |- is_true (VS.subset ?vs1 ?vs2) =>
             case: H; [intros | by apply]
         | H : is_true (VSLemmas.disjoint (VS.union _ _) _) |- _ =>
             rewrite VSLemmas.disjoint_sym in H
         | H : is_true (VSLemmas.disjoint _ (VS.union _ _)) |- _ =>
             let Hdisj1 := fresh in
             let Hdisj2 := fresh in
             rewrite VSLemmas.disjoint_union in H; move/andP: H => [Hdisj1 Hdisj2]
         | H1 : is_true (VSLemmas.disjoint ?vs1 ?vs2),
             H2 : context c [VSLemmas.disjoint ?vs1 ?vs2]
           |- _ =>
             rewrite H1 /= in H2
         | H1 : is_true (VSLemmas.disjoint ?vs1 ?vs2),
             H2 : context c [VSLemmas.disjoint ?vs2 ?vs1]
           |- _ =>
             rewrite VSLemmas.disjoint_sym H1 /= in H2
         | H : true = false |- _ => discriminate
         | H1 : is_true (VS.subset (vars_ebexp (slice_ebexp ?vs ?e)) _),
             H2 : slice_ebexp ?vs ?e = _ |- _ =>
             rewrite H2 /= in H1
         | H1 : is_true (VS.subset (vars_rbexp (slice_rbexp ?vs ?e)) _),
             H2 : slice_rbexp ?vs ?e = _ |- _ =>
             rewrite H2 /= in H1
         | |- context c [vars_ebexp _] => rewrite /vars_ebexp /=
         | |- context c [vars_rbexp _] => rewrite /vars_rbexp /=
         end); try VSLemmas.dp_subset.

    Lemma ebexp_partition_slice_subset vs e :
      ebexp_partition vs e -> VS.subset (vars_ebexp (slice_ebexp vs e)) vs.
    Proof.
      elim: e vs => /=.
      - intros; by mytac.
      - intros; case_if; by mytac.
      - intros; case_if; by mytac.
      - move=> e1 IH1 e2 IH2 vs [Hpart1 Hpart2].
        move: (IH1 _ Hpart1) (IH2 _ Hpart2) => Hsub1 Hsub2.
        case Hs1: (slice_ebexp vs e1); case Hs2: (slice_ebexp vs e2); simpl; by mytac.
    Qed.

    Lemma rbexp_partition_slice_subset vs e :
      rbexp_partition vs e -> VS.subset (vars_rbexp (slice_rbexp vs e)) vs.
    Proof.
      elim: e vs => /=.
      - intros; by mytac.
      - intros; case_if; by mytac.
      - intros; case_if; by mytac.
      - intros; case_if; by mytac.
      - move=> e1 IH1 e2 IH2 vs [Hpart1 Hpart2].
        move: (IH1 _ Hpart1) (IH2 _ Hpart2) => Hsub1 Hsub2.
        case Hs1: (slice_rbexp vs e1); case Hs2: (slice_rbexp vs e2); simpl; by mytac.
      - intros; case_if; by mytac.
    Qed.

    Lemma einstr_partition_slice_subset vs i i' :
      slice_einstr vs i = Some i' ->
      einstr_partition vs i -> VS.subset (vars_instr i') vs.
    Proof.
      case: i => //=; intros; case_if'; try by mytac.
      case: b H H0 => [e r] /=. intros; mytac. rewrite /vars_bexp /=.
      rewrite VSLemmas.union_emptyr. exact: (ebexp_partition_slice_subset H0).
    Qed.

    Lemma rinstr_partition_slice_subset vs i i' :
      slice_rinstr vs i = Some i' ->
      rinstr_partition vs i -> VS.subset (vars_instr i') vs.
    Proof.
      case: i => //=; intros; case_if'; try by mytac.
      case: b H H0 => [e r] /=. intros; mytac. rewrite /vars_bexp /=.
      rewrite VSLemmas.union_emptyl. exact: (rbexp_partition_slice_subset H0).
    Qed.

    Lemma eprogram_partition_slice_subset vs p :
      eprogram_partition vs p -> VS.subset (vars_program (slice_eprogram vs p)) vs.
    Proof.
      elim: p vs => [| i p IH] vs /=.
      - intros; by mytac.
      - move=> [Hpi Hpp]. case Hsi: (slice_einstr vs i) => /=.
        + apply: (VSLemmas.subset_union3 (einstr_partition_slice_subset Hsi Hpi)).
          exact: (IH _ Hpp).
        + exact: (IH _ Hpp).
    Qed.

    Lemma rprogram_partition_slice_subset vs p :
      rprogram_partition vs p -> VS.subset (vars_program (slice_rprogram vs p)) vs.
    Proof.
      elim: p vs => [| i p IH] vs /=.
      - intros; by mytac.
      - move=> [Hpi Hpp]. case Hsi: (slice_rinstr vs i) => /=.
        + apply: (VSLemmas.subset_union3 (rinstr_partition_slice_subset Hsi Hpi)).
          exact: (IH _ Hpp).
        + exact: (IH _ Hpp).
    Qed.


    Ltac mytac ::=
      repeat match goal with
             | H : context f [if ?e then _ else _] |- _ =>
                 (move: H); (dcase e); case; intros
             | |- context f [if ?e then _ else _] =>
                 dcase e; case; intros
             | H : Some _ = None |- _ => discriminate
             | H : None = Some _ |- _ => discriminate
             | H : Some _ = Some _ |- _ => case: H; intros; subst
             | H : _ && _ = true |- _ =>
                 let H1 := fresh in
                 let H2 := fresh in
                 move/andP: H => [H1 H2]
             | H1 : slice_ebexp ?vs ?e = _,
                 H2 : context f [slice_ebexp ?vs ?e] |- _ => rewrite /= H1 in H2
             | H1 : slice_rbexp ?vs ?e = _,
                 H2 : context f [slice_rbexp ?vs ?e] |- _ => rewrite /= H1 in H2
             end.

    Lemma slice_ebexp_vars_subset vs e :
      VS.subset (vars_ebexp (slice_ebexp vs e)) (vars_ebexp e).
    Proof.
      elim: e => //=.
      - by VSLemmas.dp_subset.
      - intros; mytac; simpl; by VSLemmas.dp_subset.
      - intros; mytac; simpl; by VSLemmas.dp_subset.
      - move=> e1 IH1 e2 IH2. case Hs1: (slice_ebexp vs e1); case Hs2: (slice_ebexp vs e2);
          mytac; simpl; by VSLemmas.dp_subset.
    Qed.

    Lemma slice_rbexp_vars_subset vs e :
      VS.subset (vars_rbexp (slice_rbexp vs e)) (vars_rbexp e).
    Proof.
      elim: e => //=.
      - by VSLemmas.dp_subset.
      - intros; mytac; simpl; by VSLemmas.dp_subset.
      - intros; mytac; simpl; by VSLemmas.dp_subset.
      - intros; mytac; simpl; by VSLemmas.dp_subset.
      - move=> e1 IH1 e2 IH2. case Hs1: (slice_rbexp vs e1); case Hs2: (slice_rbexp vs e2);
          mytac; simpl; by VSLemmas.dp_subset.
      - move=> e1 IH1 e2 IH2; mytac; simpl; by VSLemmas.dp_subset.
    Qed.

    Lemma slice_einstr_lvs_equal vs i i' :
      slice_einstr vs i = Some i' -> VS.Equal (lvs_instr i') (lvs_instr i).
    Proof.
      case: i => //=; intros; case_if; case_option; subst; simpl; try reflexivity.
      move: b H => [e r] /= [] ?; subst. simpl. reflexivity.
    Qed.

    Lemma slice_rinstr_lvs_equal vs i i' :
      slice_rinstr vs i = Some i' -> VS.Equal (lvs_instr i') (lvs_instr i).
    Proof.
      case: i => //=; intros; case_if; case_option; subst; simpl; try reflexivity.
      move: b H => [e r] /= [] ?; subst. simpl. reflexivity.
    Qed.

    Lemma slice_einstr_vars_subset vs i i' :
      slice_einstr vs i = Some i' -> VS.subset (vars_instr i') (vars_instr i).
    Proof.
      case: i => //=; intros; mytac; simpl; try VSLemmas.dp_subset.
      move: H; case: b; intros; mytac; simpl. rewrite /vars_bexp /=.
      apply: VSLemmas.union_subsets.
      - exact: slice_ebexp_vars_subset.
      - exact: VSLemmas.subset_empty.
    Qed.

    Lemma slice_rinstr_vars_subset vs i i' :
      slice_rinstr vs i = Some i' -> VS.subset (vars_instr i') (vars_instr i).
    Proof.
      case: i => //=; intros; mytac; simpl; try VSLemmas.dp_subset.
      move: H; case: b; intros; mytac; simpl. rewrite /vars_bexp /=.
      apply: VSLemmas.union_subsets.
      - exact: VSLemmas.subset_empty.
      - exact: slice_rbexp_vars_subset.
    Qed.

    Lemma slice_eprogram_vars_subset vs p :
      VS.subset (vars_program (slice_eprogram vs p)) (vars_program p).
    Proof.
      elim: p => [| i p IH] //=.
      - by VSLemmas.dp_subset.
      - case Hi: (slice_einstr vs i) => /=.
        + move: (slice_einstr_vars_subset Hi) => Hsub. by VSLemmas.dp_subset.
        + apply: VSLemmas.subset_union2. assumption.
    Qed.

    Lemma slice_rprogram_vars_subset vs p :
      VS.subset (vars_program (slice_rprogram vs p)) (vars_program p).
    Proof.
      elim: p => [| i p IH] //=.
      - by VSLemmas.dp_subset.
      - case Hi: (slice_rinstr vs i) => /=.
        + move: (slice_rinstr_vars_subset Hi) => Hsub. by VSLemmas.dp_subset.
        + apply: VSLemmas.subset_union2. assumption.
    Qed.

    Lemma depvars_epre_eprogram_slice_subset f p vs :
      VS.cardinal vs < VS.cardinal (depvars_epre_eprogram vs f p) = false ->
      VS.subset (vars_program (slice_eprogram (depvars_epre_eprogram vs f p) p))
                (depvars_epre_eprogram vs f p).
    Proof.
      move=> H. move/idP/negP: H. rewrite -leqNgt => Hc.
      move: (depvars_epre_eprogram_cardinal_sat Hc) => Heq.
      rewrite Heq. apply: eprogram_partition_slice_subset.
      apply: (depvars_epre_eprogram_partition2 (e:=f)).
      rewrite Heq. exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_rpre_rprogram_slice_subset f p vs :
      VS.cardinal vs < VS.cardinal (depvars_rpre_rprogram vs f p) = false ->
      VS.subset (vars_program (slice_rprogram (depvars_rpre_rprogram vs f p) p))
                (depvars_rpre_rprogram vs f p).
    Proof.
      move=> H. move/idP/negP: H. rewrite -leqNgt => Hc.
      move: (depvars_rpre_rprogram_cardinal_sat Hc) => Heq.
      rewrite Heq. apply: rprogram_partition_slice_subset.
      apply: (depvars_rpre_rprogram_partition2 (e:=f)).
      rewrite Heq. exact: VSLemmas.subset_refl.
    Qed.

    Lemma depvars_epre_eprogram_sat_slice_subset f p vs :
      VS.subset (vars_program (slice_eprogram (depvars_epre_eprogram_sat f p vs) p))
                (depvars_epre_eprogram_sat f p vs).
    Proof.
      apply: eprogram_partition_slice_subset.
      exact: depvars_epre_eprogram_sat_partition2.
    Qed.

    Lemma depvars_rpre_rprogram_sat_slice_subset f p vs :
      VS.subset (vars_program (slice_rprogram (depvars_rpre_rprogram_sat f p vs) p))
                (depvars_rpre_rprogram_sat f p vs).
    Proof.
      apply: rprogram_partition_slice_subset.
      exact: depvars_rpre_rprogram_sat_partition2.
    Qed.


    Ltac mytac ::=
      (repeat match goal with
         | |- True => trivial
         | H : ?e |- ?e => assumption
         | |- is_true (?e == ?e) => exact: eqxx
         | H : is_true false \/ _ |- _ =>
             (case: H => H); [discriminate | idtac]
         | H : context f [if ?e then _ else _] |- _ =>
             (move: H); (dcase e); case; intros
         | |- context f [if ?e then _ else _] =>
             dcase e; case; intros
         | H : Some _ = None |- _ => discriminate
         | H : None = Some _ |- _ => discriminate
         | H : Some _ = Some _ |- _ => case: H; intros; subst
         | H : VSLemmas.disjoint (VS.singleton ?v) ?vs = true |- _ =>
             rewrite VSLemmas.disjoint_sym in H
         | H : VSLemmas.disjoint ?vs (VS.singleton ?v) = true |- _ =>
             rewrite VSLemmas.disjoint_singleton in H
         | H : is_true (VSLemmas.disjoint ?vs (VS.singleton ?v)) |- _ =>
             rewrite VSLemmas.disjoint_singleton in H
         | H : VSLemmas.disjoint (VS.add _ (VS.singleton _)) _ = true |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             (rewrite VSLemmas.disjoint_sym VSLemmas.disjoint_add in H); (move/andP: H => [H1 H2])
         | H : is_true (VS.subset (VS.add _ _) _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             (rewrite VSLemmas.subset_add6 in H); (case/andP: H); (move=> H1 H2)
         | H : is_true (VS.subset (VS.union _ _) _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             (rewrite VSLemmas.subset_union6 in H); (case/andP: H); (move=> H1 H2)
         | H : context f [vars_bexp (?e, ?r)] |- _ =>
             rewrite /vars_bexp /= in H
         | H : eval_bexp (?e, ?r) ?E ?s |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             (rewrite /eval_bexp /= in H); (case: H => H1 H2)
         | |- eval_bexp (?e, ?r) ?E ?s =>
             rewrite /eval_bexp /=; split
         | Hag : MA.agree ?vs ?E1 ?E2, Hsub : is_true (VS.subset (vars_atom ?a) ?vs) |-
             context c [atyp ?a ?E1] =>
             rewrite (agree_atyp (MA.subset_set_agree Hsub Hag))
         | H : ~~ VS.mem ?t ?vs = true |-
             MA.agree ?vs (TE.add ?t _ _) _ =>
             apply: (MA.not_mem_add_map_l); [assumption |]
         | H : is_true (~~ VS.mem ?t ?vs) |-
             MA.agree ?vs (TE.add ?t _ _) _ =>
             apply: (MA.not_mem_add_map_l); [assumption |]
         | |- MA.agree _ (TE.add ?x ?v _) (TE.add ?x ?v _) => apply: MA.agree_add_map2
         | |- MA.agree _ ?E ?E => exact: MA.agree_refl
         end).

    Lemma slice_einstr_none_agree vs E i :
      slice_einstr vs i = None ->
      MA.agree vs (instr_succ_typenv i E) E.
    Proof. case: i => //=; intros; by mytac. Qed.

    Lemma slice_rinstr_none_agree vs E i :
      slice_rinstr vs i = None ->
      MA.agree vs (instr_succ_typenv i E) E.
    Proof. case: i => //=; intros; by mytac. Qed.

    Lemma slice_einstr_some_succ_typenv E vs i i' :
      slice_einstr vs i = Some i' ->
      instr_succ_typenv i E = instr_succ_typenv i' E.
    Proof.
      case: i => //=; intros; mytac; simpl; try reflexivity.
      move: H; case: b => [e r]. case=> <- /=. reflexivity.
    Qed.

    Lemma slice_rinstr_some_succ_typenv E vs i i' :
      slice_rinstr vs i = Some i' ->
      instr_succ_typenv i E = instr_succ_typenv i' E.
    Proof.
      case: i => //=; intros; mytac; simpl; try reflexivity.
      move: H; case: b => [e r]. case=> <- /=. reflexivity.
    Qed.

    Lemma slice_eprogram_succ_typenv E vs p :
      eprogram_partition vs p ->
      MA.agree vs (program_succ_typenv p E) (program_succ_typenv (slice_eprogram vs p) E).
    Proof.
      elim: p E vs => [| i p IH] E vs /=.
      - move=> _. exact: MA.agree_refl.
      - move=> [Hpi Hpp]. case Hsi: (slice_einstr vs i); simpl.
        + rewrite (slice_einstr_some_succ_typenv _ Hsi). exact: IH.
        + apply: (MA.agree_trans (IH (instr_succ_typenv i E) vs Hpp)).
          apply: agree_program_succ_typenv.
          * exact: (slice_einstr_none_agree E Hsi).
          * apply: (MA.subset_set_agree (eprogram_partition_slice_subset Hpp)).
            exact: (slice_einstr_none_agree _ Hsi).
    Qed.

    Lemma slice_rprogram_succ_typenv E vs p :
      rprogram_partition vs p ->
      MA.agree vs (program_succ_typenv p E) (program_succ_typenv (slice_rprogram vs p) E).
    Proof.
      elim: p E vs => [| i p IH] E vs /=.
      - move=> _. exact: MA.agree_refl.
      - move=> [Hpi Hpp]. case Hsi: (slice_rinstr vs i); simpl.
        + rewrite (slice_rinstr_some_succ_typenv _ Hsi). exact: IH.
        + apply: (MA.agree_trans (IH (instr_succ_typenv i E) vs Hpp)).
          apply: agree_program_succ_typenv.
          * exact: (slice_rinstr_none_agree E Hsi).
          * apply: (MA.subset_set_agree (rprogram_partition_slice_subset Hpp)).
            exact: (slice_rinstr_none_agree _ Hsi).
    Qed.

    Lemma slice_einstr_some_succ_typenv2 vs E1 E2 i i' :
      MA.agree vs E1 E2 ->
      slice_einstr vs i = Some i' ->
      einstr_partition vs i ->
      MA.agree vs (instr_succ_typenv i E1) (instr_succ_typenv i E2).
    Proof.
      move=> Hag. rewrite /slice_einstr /einstr_partition.
      case: i => //=; intros; case_if; case_option; subst; simpl; by mytac.
    Qed.

    Lemma slice_rinstr_some_succ_typenv2 vs E1 E2 i i' :
      MA.agree vs E1 E2 ->
      slice_rinstr vs i = Some i' ->
      rinstr_partition vs i ->
      MA.agree vs (instr_succ_typenv i E1) (instr_succ_typenv i E2).
    Proof.
      move=> Hag. rewrite /slice_rinstr /rinstr_partition.
      case: i => //=; intros; case_if; case_option; subst; simpl; by mytac.
    Qed.


    Lemma slice_ebexp_eval E vs e s :
      eval_ebexp e E s -> eval_ebexp (slice_ebexp vs e) E s.
    Proof.
      elim: e => //=.
      - move=> e1 e2 H. by case_if.
      - move=> e1 e2 ms H. by case_if.
      - move=> e1 IH1 e2 IH2 [H1 H2].
        case Hs1: (slice_ebexp vs e1) => //=; rewrite Hs1 /= in IH1.
        + (case Hs2: (slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; tauto.
        + (case Hs2: (slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; tauto.
        + (case Hs2: (slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; tauto.
        + (case Hs2: (slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; tauto.
    Qed.

    Ltac myauto :=
      repeat match goal with
             | H : is_true (_ == _) |- _ => move/eqP: H => H
             | |- is_true (_ == _) => apply/eqP
             | H : is_true (_ && _) |- _ =>
                 let H1 := fresh in
                 let H2 := fresh in
                 move/andP: H => [H1 H2]
             | |- is_true (_ && _) => apply/andP
             | |- _ /\ _ => split
             end.

    Lemma slice_rbexp_eval vs e s :
      eval_rbexp e s -> eval_rbexp (slice_rbexp vs e) s.
    Proof.
      elim: e => //=.
      - move=> n e1 e2. by case_if.
      - move=> n op e1 e2 H. by case_if.
      - move=> e1 IH. by case_if.
      - move=> e1 IH1 e2 IH2 /andP [H1 H2].
        case Hs1: (slice_rbexp vs e1) => //=; rewrite Hs1 /= in IH1.
        + (case Hs2: (slice_rbexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; tauto.
        + (case Hs2: (slice_rbexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; intros; myauto; tauto.
        + (case Hs2: (slice_rbexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; intros; myauto; tauto.
        + (case Hs2: (slice_rbexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; intros; myauto; tauto.
        + (case Hs2: (slice_rbexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; intros; myauto; tauto.
        + (case Hs2: (slice_rbexp vs e2) => //=); (rewrite Hs2 /= in IH2);
          move: (IH1 H1) (IH2 H2) => /=; intros; myauto; tauto.
      - move=> e1 IH1 e2 IH2 /orP [] H.
        + case: (VSLemmas.disjoint vs (vars_rbexp e1) && VSLemmas.disjoint vs (vars_rbexp e2))
              => //=. by rewrite H orTb.
        + case: (VSLemmas.disjoint vs (vars_rbexp e1) && VSLemmas.disjoint vs (vars_rbexp e2))
              => //=. by rewrite H orbT.
    Qed.

    Ltac mytac ::=
      (repeat match goal with
              | H : context f [if ?e then _ else _] |- _ =>
                  (move: H); (dcase e); case; intros
              | |- context f [if ?e then _ else _] =>
                  dcase e; case; intros
              | H : eval_instr _ _ _ _,
                  Heqm : TSEQM.state_eqmod _ _ _ |- _ =>
                  (move: Heqm); (inversion_clear H); intros
              | H : Some _ = None |- _ => discriminate
              | H : VSLemmas.disjoint (VS.singleton ?v) ?vs = true |- _ =>
                  rewrite VSLemmas.disjoint_sym in H
              | H : VSLemmas.disjoint (VS.add _ (VS.singleton _)) _ = true |- _ =>
                  rewrite VSLemmas.disjoint_sym in H
              | H : VSLemmas.disjoint ?vs (VS.singleton ?v) = true |- _ =>
                  rewrite VSLemmas.disjoint_singleton in H
              | H : is_true (VSLemmas.disjoint ?vs (VS.singleton ?v)) |- _ =>
                  rewrite VSLemmas.disjoint_singleton in H
              | H : VSLemmas.disjoint _ (VS.add _ (VS.singleton _)) = true |- _ =>
                  let H1 := fresh in let H2 := fresh in
                  (rewrite VSLemmas.disjoint_add in H); (move/andP: H => [H1 H2])
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hnotin : ~~ VS.mem ?v ?vs = true,
                    Hupd : S.Upd ?v _ ?s1 ?s2
                |- TSEQM.state_eqmod ?vs ?s2 ?s1' =>
                  exact: (TSEQM.state_eqmod_Upd_notin_l Heqm Hnotin Hupd)
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hupd2 : S.Upd2 ?v2 _ ?v1 _ ?s1 ?s2,
                    Hnotin1 : is_true (~~ VS.mem ?v1 ?vs),
                      Hnotin2 : is_true (~~ VS.mem ?v2 ?vs)
                |- TSEQM.state_eqmod ?vs ?s2 ?s1' =>
                  exact: (TSEQM.state_eqmod_Upd2_notin_l Heqm Hnotin2 Hnotin1 Hupd2)
              | H : ?e |- ?e => assumption
              end).

    Lemma slice_einstr_none_eval E vs i s1 s2 s1' :
      slice_einstr vs i = None ->
      eval_instr E i s1 s2 -> TSEQM.state_eqmod vs s1 s1' ->
      TSEQM.state_eqmod vs s1' s2.
    Proof. case: i => //=; intros; apply: TSEQM.state_eqmod_sym; by mytac. Qed.

    Lemma slice_rinstr_none_eval E vs i s1 s2 s1' :
      slice_rinstr vs i = None ->
      eval_instr E i s1 s2 -> TSEQM.state_eqmod vs s1 s1' ->
      TSEQM.state_eqmod vs s1' s2.
    Proof. case: i => //=; intros; apply: TSEQM.state_eqmod_sym; by mytac. Qed.

    Ltac mytac ::=
      (repeat match goal with
              | |- True => trivial
              | H : ?e |- ?e => assumption
              | |- is_true (?e == ?e) => exact: eqxx
              | H : context f [if ?e then _ else _] |- _ =>
                  (move: H); (dcase e); case; intros
              | |- context f [if ?e then _ else _] =>
                  dcase e; case; intros
              | H : Some _ = None |- _ => discriminate
              | H : None = Some _ |- _ => discriminate
              | H : Some _ = Some _ |- _ => case: H; intros; subst
              | H : eval_instr _ _ _ _,
                  Hsub : is_true (VS.subset (vars_instr _) _),
                  Heqm : TSEQM.state_eqmod _ _ _ |- _ =>
                  (move: Heqm Hsub); (inversion_clear H); simpl; intros
              | H : VSLemmas.disjoint ?vs (VS.singleton ?v) = true |- _ =>
                  rewrite VSLemmas.disjoint_singleton in H
              | H : is_true (VSLemmas.disjoint ?vs (VS.singleton ?v)) |- _ =>
                  rewrite VSLemmas.disjoint_singleton in H
              | H : VSLemmas.disjoint _ (VS.add _ (VS.singleton _)) = true |- _ =>
                  let H1 := fresh in
                  let H2 := fresh in
                  (rewrite VSLemmas.disjoint_add in H); (move/andP: H => [H1 H2])
              | H : is_true (VS.subset (VS.add _ _) _) |- _ =>
                  let H1 := fresh in
                  let H2 := fresh in
                  (rewrite VSLemmas.subset_add6 in H); (case/andP: H); (move=> H1 H2)
              | H : is_true (VS.subset (VS.union _ _) _) |- _ =>
                  let H1 := fresh in
                  let H2 := fresh in
                  (rewrite VSLemmas.subset_union6 in H); (case/andP: H); (move=> H1 H2)
              | Hupd : S.Upd ?x ?v ?s1 ?s2,
                  Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1'
                |- exists s2' : state, (TSEQM.state_eqmod ?vs ?s2 ?s2' /\ _) =>
                  exists (S.upd x v s1'); split
              | Hupd2 : S.Upd2 ?x ?v ?y ?u ?s1 ?s2,
                  Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1'
                |- exists s2' : state, TSEQM.state_eqmod ?vs ?s2 ?s2' /\ _ =>
                  exists (S.upd2 x v y u s1'); split
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hsub : is_true (VS.subset (vars_atom ?a) ?vs)
                |- context f [eval_atom ?a ?s1] =>
                  rewrite (state_eqmod_eval_atom Heqm Hsub)
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hsub : is_true (VS.subset (vars_atom ?a) ?vs),
                    H : context f [eval_atom ?a ?s1] |- _ =>
                  rewrite (state_eqmod_eval_atom Heqm Hsub) in H
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hsub : is_true (VS.subset (vars_rexp ?a) ?vs)
                |- context f [eval_rexp ?a ?s1] =>
                  rewrite (state_eqmod_eval_rexp Heqm Hsub)
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hsub : is_true (VS.subset (vars_rexp ?a) ?vs),
                    H : context f [eval_rexp ?a ?s1] |- _ =>
                  rewrite (state_eqmod_eval_rexp Heqm Hsub) in H
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hsub : is_true (VS.subset (vars_rbexp ?a) ?vs)
                |- context f [eval_rbexp ?a ?s1] =>
                  rewrite (state_eqmod_eval_rbexp Heqm Hsub)
              | Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1',
                  Hsub : is_true (VS.subset (vars_rbexp ?a) ?vs),
                    H : context f [eval_rbexp ?a ?s1] |- _ =>
                  rewrite (state_eqmod_eval_rbexp Heqm Hsub) in H
              | Hupd : S.Upd ?x ?v ?s1 ?s2,
                  Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1'
                |- TSEQM.state_eqmod ?vs ?s2 (S.upd ?x ?v ?s1') =>
                  apply: (TSEQM.state_eqmod_Upd Hupd _ Heqm);
                  exact: S.Upd_upd
              | Hupd2 : S.Upd2 ?x ?v ?y ?u ?s1 ?s2,
                  Heqm : TSEQM.state_eqmod ?vs ?s1 ?s1'
                |- TSEQM.state_eqmod ?vs ?s2 (S.upd2 ?x ?v ?y ?u ?s1') =>
                  apply: (TSEQM.state_eqmod_Upd2 Hupd2 _ Heqm);
                  exact: S.Upd2_upd2
              | Heqm : TSEQM.state_eqmod ?vs ?s2 ?s1'
                |- exists s2' : state, TSEQM.state_eqmod ?vs ?s2 s2' /\ eval_instr ?E Inop ?s1' ?s2' =>
                  exists s1'; split; [assumption | exact: EInop]
              | H : context f [vars_bexp (?e, ?r)] |- _ =>
                  rewrite /vars_bexp /= in H
              | H : eval_bexp (?e, ?r) ?E ?s |- _ =>
                  let H1 := fresh in
                  let H2 := fresh in
                  (rewrite /eval_bexp /= in H); (case: H => H1 H2)
              | |- eval_bexp (?e, ?r) ?E ?s =>
                  rewrite /eval_bexp /=; split
              | |- exists s2' : state,
                  TSEQM.state_eqmod ?vs ?s2 ?s2' /\ eval_instr ?E (Iassume _) ?s1' ?s2' =>
                  exists s1'; split
              | |- eval_instr ?E (Iassume _) ?s ?s => apply: EIassume
              end).

    Lemma slice_einstr_some_eval E vs i i' s1 s2 s1' :
      slice_einstr vs i = Some i' -> VS.subset (vars_instr i') vs ->
      eval_instr E i s1 s2 -> TSEQM.state_eqmod vs s1 s1' ->
      exists s2', TSEQM.state_eqmod vs s2 s2' /\ eval_instr E i' s1' s2'.
    Proof.
      case: i => //=; intros; mytac.
      - apply: EImov; exact: S.Upd_upd.
      - apply: EIshl; exact: S.Upd_upd.
      - apply: EIcshl; exact: S.Upd2_upd2.
      - apply: (EInondet _ H0); exact: S.Upd_upd.
      - apply: (EIcmovT _ _ H0); exact: S.Upd_upd.
      - apply: (EIcmovF _ _ H0); exact: S.Upd_upd.
      - apply: EInot; exact: S.Upd_upd.
      - apply: EIadd; exact: S.Upd_upd.
      - apply: EIadds; exact: S.Upd2_upd2.
      - apply: EIadc; exact: S.Upd_upd.
      - apply: EIadcs; exact: S.Upd2_upd2.
      - apply: EIsub; exact: S.Upd_upd.
      - apply: EIsubc; exact: S.Upd2_upd2.
      - apply: EIsubb; exact: S.Upd2_upd2.
      - apply: EIsbc; exact: S.Upd_upd.
      - apply: EIsbcs; exact: S.Upd2_upd2.
      - apply: EIsbb; exact: S.Upd_upd.
      - apply: EIsbbs; exact: S.Upd2_upd2.
      - apply: EImul; exact: S.Upd_upd.
      - apply: (EImullU H0). exact: S.Upd2_upd2.
      - apply: (EImullS H0); exact: S.Upd2_upd2.
      - apply: (EImuljU H0); exact: S.Upd_upd.
      - apply: (EImuljS H0); exact: S.Upd_upd.
      - apply: (EIsplitU H0); exact: S.Upd2_upd2.
      - apply: (EIsplitS H0); exact: S.Upd2_upd2.
      - apply: EIand; exact: S.Upd_upd.
      - apply: EIor; exact: S.Upd_upd.
      - apply: EIxor; exact: S.Upd_upd.
      - apply: EIcast; exact: S.Upd_upd.
      - apply: EIvpc; exact: S.Upd_upd.
      - apply: EIjoin; exact: S.Upd_upd.
      - move: H H0. case: b => [e r]. case=> ?; subst. simpl in H1.
        intros; mytac.
        + apply/(state_eqmod_eval_ebexp E H2 H). apply: slice_ebexp_eval. assumption.
        + reflexivity.
    Qed.

    Lemma slice_rinstr_some_eval E vs i i' s1 s2 s1' :
      slice_rinstr vs i = Some i' -> VS.subset (vars_instr i') vs ->
      eval_instr E i s1 s2 -> TSEQM.state_eqmod vs s1 s1' ->
      exists s2', TSEQM.state_eqmod vs s2 s2' /\ eval_instr E i' s1' s2'.
    Proof.
      case: i => //=; intros; mytac.
      - apply: EImov; exact: S.Upd_upd.
      - apply: EIshl; exact: S.Upd_upd.
      - apply: EIcshl; exact: S.Upd2_upd2.
      - apply: (EInondet _ H0); exact: S.Upd_upd.
      - apply: (EIcmovT _ _ H0); exact: S.Upd_upd.
      - apply: (EIcmovF _ _ H0); exact: S.Upd_upd.
      - apply: EInot; exact: S.Upd_upd.
      - apply: EIadd; exact: S.Upd_upd.
      - apply: EIadds; exact: S.Upd2_upd2.
      - apply: EIadc; exact: S.Upd_upd.
      - apply: EIadcs; exact: S.Upd2_upd2.
      - apply: EIsub; exact: S.Upd_upd.
      - apply: EIsubc; exact: S.Upd2_upd2.
      - apply: EIsubb; exact: S.Upd2_upd2.
      - apply: EIsbc; exact: S.Upd_upd.
      - apply: EIsbcs; exact: S.Upd2_upd2.
      - apply: EIsbb; exact: S.Upd_upd.
      - apply: EIsbbs; exact: S.Upd2_upd2.
      - apply: EImul; exact: S.Upd_upd.
      - apply: (EImullU H0). exact: S.Upd2_upd2.
      - apply: (EImullS H0); exact: S.Upd2_upd2.
      - apply: (EImuljU H0); exact: S.Upd_upd.
      - apply: (EImuljS H0); exact: S.Upd_upd.
      - apply: (EIsplitU H0); exact: S.Upd2_upd2.
      - apply: (EIsplitS H0); exact: S.Upd2_upd2.
      - apply: EIand; exact: S.Upd_upd.
      - apply: EIor; exact: S.Upd_upd.
      - apply: EIxor; exact: S.Upd_upd.
      - apply: EIcast; exact: S.Upd_upd.
      - apply: EIvpc; exact: S.Upd_upd.
      - apply: EIjoin; exact: S.Upd_upd.
      - move: H H0. case: b => [e r]. case=> ?; subst. simpl in H1.
        intros; mytac. rewrite -(state_eqmod_eval_rbexp H2 H3).
        apply: slice_rbexp_eval. assumption.
    Qed.

    Lemma slice_eprogram_eval E vs p s1 s2 s1' :
      VS.subset (vars_program (slice_eprogram vs p)) vs ->
      eval_program E p s1 s2 -> TSEQM.state_eqmod vs s1 s1' ->
      exists s2', TSEQM.state_eqmod vs s2 s2' /\ eval_program E (slice_eprogram vs p) s1' s2'.
    Proof.
      elim: p E vs s1 s2 s1' => [| i p IH] E vs s1 s2 s1' /=.
      - move=> _ Hev; inversion_clear Hev. move=> Heqm. exists s1'.
        split; first assumption. exact: Enil.
      - case Hsi: (slice_einstr vs i) => /=.
        + rewrite VSLemmas.subset_union6. move/andP=> [Hsubi Hsubp].
          move=> Hev; inversion_clear Hev. move=> Heqm.
          move: (slice_einstr_some_eval Hsi Hsubi H Heqm) => [t' [Heqm' Hevi']].
          move: (IH _ _ _ _ _ Hsubp H0 Heqm') => [s2' [Heqm'' Hevp']].
          exists s2'. split; first assumption. apply: (Econs Hevi').
          rewrite -(slice_einstr_some_succ_typenv E Hsi). exact: Hevp'.
        + move=> Hsub Hev. inversion_clear Hev. move=> Heqm.
          move: (slice_einstr_none_eval Hsi H Heqm) => /TSEQM.state_eqmod_sym Heqm'.
          move: (IH _ _ _ _ _ Hsub H0 Heqm') => [s2' [Heqm'' Hev']].
          exists s2'. split; first exact: Heqm''. apply: (agree_eval_program Hev').
          apply: (MA.subset_set_agree Hsub). exact: (slice_einstr_none_agree E Hsi).
    Qed.

    Lemma slice_rprogram_eval E vs p s1 s2 s1' :
      VS.subset (vars_program (slice_rprogram vs p)) vs ->
      eval_program E p s1 s2 -> TSEQM.state_eqmod vs s1 s1' ->
      exists s2', TSEQM.state_eqmod vs s2 s2' /\ eval_program E (slice_rprogram vs p) s1' s2'.
    Proof.
      elim: p E vs s1 s2 s1' => [| i p IH] E vs s1 s2 s1' /=.
      - move=> _ Hev; inversion_clear Hev. move=> Heqm. exists s1'.
        split; first assumption. exact: Enil.
      - case Hsi: (slice_rinstr vs i) => /=.
        + rewrite VSLemmas.subset_union6. move/andP=> [Hsubi Hsubp].
          move=> Hev; inversion_clear Hev. move=> Heqm.
          move: (slice_rinstr_some_eval Hsi Hsubi H Heqm) => [t' [Heqm' Hevi']].
          move: (IH _ _ _ _ _ Hsubp H0 Heqm') => [s2' [Heqm'' Hevp']].
          exists s2'. split; first assumption. apply: (Econs Hevi').
          rewrite -(slice_rinstr_some_succ_typenv E Hsi). exact: Hevp'.
        + move=> Hsub Hev. inversion_clear Hev. move=> Heqm.
          move: (slice_rinstr_none_eval Hsi H Heqm) => /TSEQM.state_eqmod_sym Heqm'.
          move: (IH _ _ _ _ _ Hsub H0 Heqm') => [s2' [Heqm'' Hev']].
          exists s2'. split; first exact: Heqm''. apply: (agree_eval_program Hev').
          apply: (MA.subset_set_agree Hsub). exact: (slice_rinstr_none_agree E Hsi).
    Qed.

    (* Soundness of slicing *)

    Theorem slice_espec_sound s :
      valid_espec (slice_espec s) -> valid_espec s.
    Proof.
      case: s => E f p g. rewrite /valid_espec /=.
      move=> H s1 s2 Hco [Hevfe Hevfr] Hevp.
      set vs := (depvars_epre_eprogram_sat (eqn_bexp f) p (vars_ebexp g)).
      move: (depvars_epre_eprogram_sat_slice_subset (eqn_bexp f) p (vars_ebexp g)) => Hsub.
      move: (@TSEQM.state_eqmod_refl vs s1) => Heqms1.
      move: (slice_eprogram_eval Hsub Hevp Heqms1) => [s2' [Heqms2' Hevs2']].
      move: (slice_ebexp_eval vs Hevfe) => Hevfes.
      move: (H s1 s2' Hco (conj Hevfes Hevfr) Hevs2') => Hevgs2'.
      apply/(state_eqmod_eval_ebexp _ Heqms2' (depvars_epre_eprogram_sat_lb _ _ _)).
      apply/(agree_eval_ebexp
               (E2 := (program_succ_typenv (slice_eprogram vs p) E))); last assumption.
      apply: (MA.subset_set_agree
                (depvars_epre_eprogram_sat_lb (eqn_bexp f) p (vars_ebexp g))).
      exact: (slice_eprogram_succ_typenv _
                (depvars_epre_eprogram_sat_partition2 (eqn_bexp f) p (vars_ebexp g))).
    Qed.

    Theorem slice_rspec_sound s :
      valid_rspec (slice_rspec s) -> valid_rspec s.
    Proof.
      case: s => E f p g. rewrite /valid_rspec /=.
      move=> H s1 s2 Hco Hevfr Hevp.
      set vs := (depvars_rpre_rprogram_sat f p (vars_rbexp g)).
      move: (depvars_rpre_rprogram_sat_slice_subset f p (vars_rbexp g)) => Hsub.
      move: (@TSEQM.state_eqmod_refl vs s1) => Heqms1.
      move: (slice_rprogram_eval Hsub Hevp Heqms1) => [s2' [Heqms2' Hevs2']].
      move: (slice_rbexp_eval vs Hevfr) => Hevfrs.
      move: (H s1 s2' Hco Hevfrs Hevs2') => Hevgs2'.
      rewrite (state_eqmod_eval_rbexp Heqms2' (depvars_rpre_rprogram_sat_lb _ _ _)).
      exact: Hevgs2'.
    Qed.


    (* Well-formedness of slicing *)

    Lemma well_typed_ebexp_slice_ebexp E vs e :
      well_typed_ebexp E e -> well_typed_ebexp E (slice_ebexp vs e).
    Proof.
      elim: e => //=; intros; case_if; try done. move/andP: H1 => [H1 H2].
      move: (H H1) => {}H. move: (H0 H2) => {}H0.
      case: (slice_ebexp vs e) H; case: (slice_ebexp vs e0) H0; (move => //=); intros; by t_auto.
    Qed.

    Lemma well_typed_rbexp_slice_rbexp E vs e :
      well_typed_rbexp E e -> well_typed_rbexp E (slice_rbexp vs e).
    Proof.
      elim: e => //=; intros; case_if; try done. move/andP: H1 => [H1 H2].
      move: (H H1) => {}H. move: (H0 H2) => {}H0.
      case: (slice_rbexp vs r) H; case: (slice_rbexp vs r0) H0; (move => //=); intros; by t_auto.
    Qed.

    Lemma well_formed_ebexp_slice_ebexp E vs e :
      well_formed_ebexp E e -> well_formed_ebexp E (slice_ebexp vs e).
    Proof.
      rewrite /well_formed_ebexp. move/andP=> [Hdef Hwt].
      rewrite (are_defined_subset (slice_ebexp_vars_subset vs e) Hdef) /=.
      exact: (well_typed_ebexp_slice_ebexp _ Hwt).
    Qed.

    Lemma well_formed_rbexp_slice_rbexp E vs e :
      well_formed_rbexp E e -> well_formed_rbexp E (slice_rbexp vs e).
    Proof.
      rewrite /well_formed_rbexp. move/andP=> [Hdef Hwt].
      rewrite (are_defined_subset (slice_rbexp_vars_subset vs e) Hdef) /=.
      exact: (well_typed_rbexp_slice_rbexp _ Hwt).
    Qed.

    Lemma instr_slice_einstr_well_formed E vs i i' :
      well_formed_instr E i -> slice_einstr vs i = Some i' -> well_formed_instr E i'.
    Proof.
      case: i => //=; intros; case_if; case_option; subst; try assumption.
      case: b H H0 => [e r] /=. move=> Hwf [] ?; subst.
      rewrite /well_formed_instr /= in Hwf *. move/andP: Hwf => [Hdef Hwt].
      rewrite /vars_bexp !are_defined_union /= in Hdef *.
      rewrite are_defined_empty andbT. move/andP: Hdef => [Hdefe Hdefr].
      rewrite (are_defined_subset (slice_ebexp_vars_subset vs e) Hdefe) /=.
      rewrite /well_typed_bexp andbT /=. move/andP: Hwt => [Hwte Hwtr].
      exact: (well_typed_ebexp_slice_ebexp _ Hwte).
    Qed.

    Lemma instr_slice_rinstr_well_formed E vs i i' :
      well_formed_instr E i -> slice_rinstr vs i = Some i' -> well_formed_instr E i'.
    Proof.
      case: i => //=; intros; case_if; case_option; subst; try assumption.
      case: b H H0 => [e r] /=. move=> Hwf [] ?; subst.
      rewrite /well_formed_instr /= in Hwf *. move/andP: Hwf => [Hdef Hwt].
      rewrite /vars_bexp !are_defined_union /= in Hdef *.
      rewrite are_defined_empty /=. move/andP: Hdef => [Hdefe Hdefr].
      rewrite (are_defined_subset (slice_rbexp_vars_subset vs r) Hdefr) /=.
      rewrite /well_typed_bexp /=. move/andP: Hwt => [Hwte Hwtr].
      exact: (well_typed_rbexp_slice_rbexp _ Hwtr).
    Qed.

    Lemma well_formed_instr_slice_einstr E1 E2 vs i i' :
      MA.agree vs E1 E2 -> einstr_partition vs i ->
      well_formed_instr E1 i -> slice_einstr vs i = Some i' -> well_formed_instr E2 i'.
    Proof.
      move=> Hag. (case: i => //=); intros; case_if; case_option; subst; simpl;
                  repeat
                    match goal with
                    | H : ?e |- ?e => assumption
                    | H : is_true false \/ _ |- _ => (case: H => H); [discriminate | idtac]
                    | H : is_true (well_formed_instr ?E1 ?i) |-
                        is_true (well_formed_instr ?E2 ?i) =>
                        rewrite (@agree_well_formed_instr E2 E1)
                    | |- MA.agree (vars_instr _) _ _ => simpl
                    | Hag : MA.agree ?vs ?E1 ?E2 |- MA.agree _ ?E2 ?E1 =>
                        apply: (MA.subset_set_agree _ (MA.agree_sym Hag))
                    end.
      case: b H H0 H1 => [e r] /= Hpat Hwf [] ?; subst.
      move: Hwf. rewrite /well_formed_instr /=.
      rewrite /vars_bexp !are_defined_union are_defined_empty andbT /=.
      rewrite /well_typed_bexp andbT /=.
      move/andP=> [/andP [Hdefe Hdefr] /andP [Hwte Hwtr]].
      move: (MA.subset_set_agree (ebexp_partition_slice_subset Hpat) Hag) => Hage.
      rewrite -(agree_are_defined Hage) -(agree_well_typed_ebexp Hage).
      rewrite (are_defined_subset (slice_ebexp_vars_subset vs e) Hdefe).
      rewrite (well_typed_ebexp_slice_ebexp vs Hwte). reflexivity.
    Qed.

    Lemma well_formed_instr_slice_rinstr E1 E2 vs i i' :
      MA.agree vs E1 E2 -> rinstr_partition vs i ->
      well_formed_instr E1 i -> slice_rinstr vs i = Some i' -> well_formed_instr E2 i'.
    Proof.
      move=> Hag. (case: i => //=); intros; case_if; case_option; subst; simpl;
                  repeat
                    match goal with
                    | H : ?e |- ?e => assumption
                    | H : is_true false \/ _ |- _ => (case: H => H); [discriminate | idtac]
                    | H : is_true (well_formed_instr ?E1 ?i) |-
                        is_true (well_formed_instr ?E2 ?i) =>
                        rewrite (@agree_well_formed_instr E2 E1)
                    | |- MA.agree (vars_instr _) _ _ => simpl
                    | Hag : MA.agree ?vs ?E1 ?E2 |- MA.agree _ ?E2 ?E1 =>
                        apply: (MA.subset_set_agree _ (MA.agree_sym Hag))
                    end.
      case: b H H0 H1 => [e r] /= Hpat Hwf [] ?; subst.
      move: Hwf. rewrite /well_formed_instr /=.
      rewrite /vars_bexp !are_defined_union are_defined_empty /=.
      rewrite /well_typed_bexp /=.
      move/andP=> [/andP [Hdefe Hdefr] /andP [Hwte Hwtr]].
      move: (MA.subset_set_agree (rbexp_partition_slice_subset Hpat) Hag) => Hagr.
      rewrite -(agree_are_defined Hagr) -(agree_well_typed_rbexp Hagr).
      rewrite (are_defined_subset (slice_rbexp_vars_subset vs r) Hdefr).
      rewrite (well_typed_rbexp_slice_rbexp vs Hwtr). reflexivity.
    Qed.

    Lemma well_formed_program_slice_eprogram E1 E2 vs p :
      MA.agree vs E1 E2 -> eprogram_partition vs p ->
      well_formed_program E1 p -> well_formed_program E2 (slice_eprogram vs p).
    Proof.
      elim: p E1 E2 => [| i p IH] E1 E2 //=. move=> Hag [Hpai Hpap].
      move/andP=> [Hwfi Hwfp]. case Hs: (slice_einstr vs i) => /=.
      - apply/andP; split.
        + exact: (well_formed_instr_slice_einstr Hag Hpai Hwfi Hs).
        + apply: (IH _ _ _ Hpap Hwfp).
          rewrite -(slice_einstr_some_succ_typenv _ Hs).
          exact: (slice_einstr_some_succ_typenv2 Hag Hs Hpai).
      - apply: (IH (instr_succ_typenv i E1) _ _ Hpap Hwfp).
        apply: (MA.agree_trans (slice_einstr_none_agree E1 Hs)). exact: Hag.
    Qed.

    Lemma well_formed_program_slice_rprogram E1 E2 vs p :
      MA.agree vs E1 E2 -> rprogram_partition vs p ->
      well_formed_program E1 p -> well_formed_program E2 (slice_rprogram vs p).
    Proof.
      elim: p E1 E2 => [| i p IH] E1 E2 //=. move=> Hag [Hpai Hpap].
      move/andP=> [Hwfi Hwfp]. case Hs: (slice_rinstr vs i) => /=.
      - apply/andP; split.
        + exact: (well_formed_instr_slice_rinstr Hag Hpai Hwfi Hs).
        + apply: (IH _ _ _ Hpap Hwfp).
          rewrite -(slice_rinstr_some_succ_typenv _ Hs).
          exact: (slice_rinstr_some_succ_typenv2 Hag Hs Hpai).
      - apply: (IH (instr_succ_typenv i E1) _ _ Hpap Hwfp).
        apply: (MA.agree_trans (slice_rinstr_none_agree E1 Hs)). exact: Hag.
    Qed.

    Lemma well_formed_espec_slice_espec s :
      well_formed_espec s -> well_formed_espec (slice_espec s).
    Proof.
      case: s => [E [ef rf] p g]. rewrite /well_formed_espec /=.
      move=> /andP [/andP [Hf Hp] Hg]. rewrite !well_formed_bexp_split /= in Hf *.
      move/andP: Hf => [Hef Hrf]. rewrite (well_formed_ebexp_slice_ebexp _ Hef) Hrf /=.
      apply/andP; split.
      - apply: (well_formed_program_slice_eprogram (MA.agree_refl _) _ Hp).
        exact: depvars_epre_eprogram_sat_partition2.
      - move: (slice_eprogram_succ_typenv
                 E (depvars_epre_eprogram_sat_partition2 ef p (vars_ebexp g))) => Hag.
        move: (depvars_epre_eprogram_sat_lb ef p (vars_ebexp g)) => Hsub.
        move: (MA.subset_set_agree Hsub Hag) => {}Hag.
        rewrite -(agree_well_formed_ebexp Hag). exact: Hg.
    Qed.

    Lemma well_formed_rspec_slice_rspec s :
      well_formed_rspec s -> well_formed_rspec (slice_rspec s).
    Proof.
      case: s => [E f p g]. rewrite /well_formed_rspec /=.
      move=> /andP [/andP [Hf Hp] Hg]. rewrite (well_formed_rbexp_slice_rbexp _ Hf) /=.
      apply/andP; split.
      - apply: (well_formed_program_slice_rprogram (MA.agree_refl _) _ Hp).
        exact: depvars_rpre_rprogram_sat_partition2.
      - move: (slice_rprogram_succ_typenv
                 E (depvars_rpre_rprogram_sat_partition2 f p (vars_rbexp g))) => Hag.
        move: (depvars_rpre_rprogram_sat_lb f p (vars_rbexp g)) => Hsub.
        move: (MA.subset_set_agree Hsub Hag) => {}Hag.
        rewrite -(agree_well_formed_rbexp Hag). exact: Hg.
    Qed.


    (* vars of slice_espec and slice_rspec *)

    Lemma slice_espec_subset_espec s : VS.subset (vars_espec (slice_espec s)) (vars_espec s).
    Proof.
      case: s => [E f p g]. rewrite /vars_espec /slice_espec /=. rewrite /vars_bexp /=.
      move: (slice_ebexp_vars_subset
               ((depvars_epre_eprogram_sat (eqn_bexp f) p (vars_ebexp g))) (eqn_bexp f)) => ?.
      move: (slice_eprogram_vars_subset
               (depvars_epre_eprogram_sat (eqn_bexp f) p (vars_ebexp g)) p) => ?.
      by VSLemmas.dp_subset.
    Qed.

    Lemma slice_rspec_subset_rspec s : VS.subset (vars_rspec (slice_rspec s)) (vars_rspec s).
    Proof.
      case: s => [E f p g]. rewrite /vars_rspec /slice_rspec /=.
      move: (slice_rbexp_vars_subset
               ((depvars_rpre_rprogram_sat f) p (vars_rbexp g)) f) => ?.
      move: (slice_rprogram_vars_subset
               (depvars_rpre_rprogram_sat f p (vars_rbexp g)) p) => ?.
      by VSLemmas.dp_subset.
    Qed.

    Lemma slice_espec_subset s :
      VS.subset (vars_espec (slice_espec s))
        (VS.union (vars_rbexp (rng_bexp (espre s)))
           (depvars_epre_eprogram_sat
              (eqn_bexp (espre s)) (esprog s) (vars_ebexp (espost s)))).
    Proof.
      case: s => [E f p g]. rewrite /vars_espec /slice_espec /vars_bexp /=.
      move: (eprogram_partition_slice_subset
               (depvars_epre_eprogram_sat_partition2 (eqn_bexp f) p (vars_ebexp g))) => ?.
      move: (ebexp_partition_slice_subset
               (depvars_epre_eprogram_sat_partition1 (eqn_bexp f) p (vars_ebexp g))) => ?.
      move: (depvars_epre_eprogram_sat_lb (eqn_bexp f) p (vars_ebexp g)) => ?.
      by VSLemmas.dp_subset.
    Qed.

    Lemma slice_rspec_subset s :
      VS.subset (vars_rspec (slice_rspec s))
        (depvars_rpre_rprogram_sat
           (rspre s) (rsprog s) (vars_rbexp (rspost s))).
    Proof.
      case: s => [E f p g]. rewrite /vars_rspec /slice_rspec /=.
      move: (rprogram_partition_slice_subset
               (depvars_rpre_rprogram_sat_partition2 f p (vars_rbexp g))) => ?.
      move: (rbexp_partition_slice_subset
               (depvars_rpre_rprogram_sat_partition1 f p (vars_rbexp g))) => ?.
      move: (depvars_rpre_rprogram_sat_lb f p (vars_rbexp g)) => ?.
      by VSLemmas.dp_subset.
    Qed.


    (* TELemmas.sbumap *)

    (* TODO: Check if this lemma is used *)
    Lemma slice_einstr_submap E1 E2 vs i i' :
      slice_einstr vs i = Some i' ->
      well_defined_instr E1 i' ->
      TELemmas.submap E1 E2 ->
      TELemmas.submap (instr_succ_typenv i' E1) (instr_succ_typenv i E2).
    Proof.
      case: i => //=; intros; case_if; case_option; subst; simpl; hyps_splitb;
      repeat
        match goal with
        | H : is_true (well_defined_instr _ _) |- _ => simpl in H; hyps_splitb
        | Hsub : TELemmas.submap ?E1 ?E2,
            Hdef : is_true (are_defined (vars_atom ?a) ?E1)
          |- context f [atyp ?a ?E2] =>
            rewrite -(atyp_submap Hsub Hdef)
        | Hsub : TELemmas.submap ?E1 ?E2,
            Hdef : is_true (are_defined (vars_atom ?a) ?E1),
              H : context f [atyp ?a ?E2] |- _ =>
            rewrite -(atyp_submap Hsub Hdef) in H
        | |- TELemmas.submap (TE.add ?x ?t _) (TE.add ?x ?t _) => apply: submap_add
        | |- TELemmas.submap ?e ?e => exact: TELemmas.submap_refl
        | H : ?p |- ?p => assumption
        end.
      case: b H H0 => [e r] /=. case=> <-. move=> _ /=. assumption.
    Qed.

    (* TODO: remove this lemma or prove it *)
    Lemma slice_eprogram_submap E1 E2 vs p :
      well_formed_program E1 (slice_eprogram vs p) ->
      TELemmas.submap E1 E2 ->
      TELemmas.submap (program_succ_typenv (slice_eprogram vs p) E1)
                      (program_succ_typenv p E2).
    Proof.
      elim: p E1 E2 => [| i p IH] E1 E2 //=. case Hs: (slice_einstr vs i) => /=.
      - move/andP => [Hwfi Hwfp] Hsub. apply: (IH _ _ Hwfp).
        apply: (slice_einstr_submap Hs _ Hsub). exact: (well_formed_instr_well_defined Hwfi).
      - move=> Hwfp Hsub. apply: (IH _ _ Hwfp).
    Abort.

  End Slicing.

End MakeDSL.

Module VarOrderPrinter <: Printer with Definition t := var.
  Definition t := VarOrder.t.
  Definition to_string (v : VarOrder.t) :=
    ("v" ++ string_of_N v)%string.
End VarOrderPrinter.

Module DSL := MakeDSL VarOrder VarOrderPrinter VS VM TE Store.
