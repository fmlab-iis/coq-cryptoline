
(** Typed CryptoLine. *)

From Coq Require Import List Ascii ZArith OrderedType String.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State BBCommon.
From ssrlib Require Import Var SsrOrder ZAriths Store FSets FMaps Tactics Seqs Nats Strings.
From Cryptoline Require Import Options.
From Cryptoline Require Export DSLRaw.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


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
  Module TELemmas := TypEnvLemmas TE.
  Local Hint Immediate S.Upd_upd S.Upd2_upd2 : dsl.

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

  Global Instance add_proper_size_of_rexp :
    Proper (eq ==> TE.Equal ==> eq) size_of_rexp.
  Proof.
    move=> e1 e2 ? E1 E2 Heq; subst. case: e2 => //=.
    move=> x. rewrite -> Heq. reflexivity.
  Qed.


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
    let '(e1, r1) := e1 in
    let '(e2, r2) := e2 in
    (if e1 == etrue then e2
     else if e2 == etrue then e1
          else eand e1 e2,
      if r1 == rtrue then r2
      else if r2 == rtrue then r1
           else rand r1 r2).

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

  Lemma bands_singleton e : bands [:: e] = e.
  Proof. by case: e => //=. Qed.


  (* Atoms *)

  Definition avar := @Avar V.T.
  Definition aconst := @Aconst V.T.
  Definition atom := @atom V.T.

  Definition atyp (a : atom) (te : TE.env) : typ :=
    match a with
    | Avar v => TE.vtyp v te
    | Aconst ty _ => ty
    end.

  Definition asize (a : atom) (te : TE.env) : nat := sizeof_typ (atyp a te).

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

  Global Instance add_proper_atyp : Proper (eq ==> TE.Equal ==> eq) atyp.
  Proof.
    move=> a1 a2 ? E1 E2 Heq; subst. rewrite /atyp. case: a2 => //=.
    move=> x. move: (Heq x). case H2: (TE.find x E2) => H1.
    - rewrite (TE.find_some_vtyp H1) (TE.find_some_vtyp H2). reflexivity.
    - rewrite (TE.find_none_vtyp H1) (TE.find_none_vtyp H2). reflexivity.
  Qed.

  Global Instance add_proper_asize : Proper (eq ==> TE.Equal ==> eq) asize.
  Proof.
    move=> a1 a2 ? E1 E2 Heq; subst. rewrite /asize. rewrite Heq. reflexivity.
  Qed.


  (* Instructions and programs *)

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
  | Icut : bexp -> instr
  | Iassert : bexp -> instr
  | Iassume : bexp -> instr.

  Definition program := seq instr.


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
    | Icut a1, Icut b1 => (a1 == b1)
    | Iassert a1, Iassert b1 => (a1 == b1)
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
    | Icut e
    | Iassert e
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
    | Icut _
    | Iassert _
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
    | Icut e
    | Iassert e
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

  Lemma instr_mem_lvs i p :
    i \in p -> VS.subset (lvs_instr i) (lvs_program p).
  Proof.
    elim: p => [| j p IH] //=. rewrite in_cons. case/orP.
    - move/eqP=> ?; subst. by VSLemmas.dp_subset.
    - move=> Hin. move: (IH Hin) => ?. by VSLemmas.dp_subset.
  Qed.

  Lemma instr_mem_rvs i p :
    i \in p -> VS.subset (rvs_instr i) (rvs_program p).
  Proof.
    elim: p => [| j p IH] //=. rewrite in_cons. case/orP.
    - move/eqP=> ?; subst. by VSLemmas.dp_subset.
    - move=> Hin. move: (IH Hin) => ?. by VSLemmas.dp_subset.
  Qed.

  Lemma instr_mem_vars i p :
    i \in p -> VS.subset (vars_instr i) (vars_program p).
  Proof.
    elim: p => [| j p IH] //=. rewrite in_cons. case/orP.
    - move/eqP=> ?; subst. by VSLemmas.dp_subset.
    - move=> Hin. move: (IH Hin) => ?. by VSLemmas.dp_subset.
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

  Lemma vars_program_rev p :
    VS.Equal (vars_program (rev p)) (vars_program p).
  Proof.
    elim: p => [| i p IH] //=. rewrite rev_cons vars_program_rcons IH VSLemmas.P.union_sym.
    reflexivity.
  Qed.

  Lemma lvs_program_rev p :
    VS.Equal (lvs_program (rev p)) (lvs_program p).
  Proof.
    elim: p => [| i p IH] //=. rewrite rev_cons lvs_program_rcons IH VSLemmas.P.union_sym.
    reflexivity.
  Qed.


  (* Specifications *)

  Record spec : Type :=
    mkSpec { sinputs : TE.env;
             spre : bexp;
             sprog : program;
             spost : bexp }.


  Definition vars_spec (s : spec) : VS.t :=
    VS.union
      (vars_bexp (spre s))
      (VS.union
         (vars_program (sprog s))
         (vars_bexp (spost s))).


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
      | Icut e => "cut " ++ string_of_bexp e
      | Iassert e => "assert " ++ string_of_bexp e
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

  End StringOutputs.


  (* Conversion from bits to integer *)

  Definition bv2z (t : typ) (bs : bits) : Z :=
    match t with
    | Tuint _ => to_Zpos bs
    | Tsint _ => to_Z bs
    end.

  Definition acc2z (E : TE.env) (v : V.t) (s : S.t) : Z :=
    bv2z (TE.vtyp v E) (S.acc v s).

  Global Instance add_proper_acc2z_env :
    Proper (TE.Equal ==> eq ==> eq ==> eq) acc2z.
  Proof.
    move=> E1 E2 Heq v1 v2 ? s1 s2 ?; subst. rewrite /acc2z.
    move: (Heq v2) => Hf. rewrite (TELemmas.find_same_vtyp Hf). reflexivity.
  Qed.

  Global Instance add_proper_acc2z_store :
    Proper (eq ==> eq ==> S.Equal ==> eq) acc2z.
  Proof.
    move=> E1 E2 ? v1 v2 ? s1 s2 Heq; subst. rewrite /acc2z.
    rewrite (S.add_proper_acc (erefl v2) Heq). reflexivity.
  Qed.

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


  (* Update of typing environments *)

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
    | Icut _
    | Iassert _
    | Iassume _ => te
    end.

  Definition program_succ_typenv (p : program) (te : TE.env) : TE.env :=
    foldl (fun te i => instr_succ_typenv i te) te p.

  Global Instance add_proper_instr_succ_typenv :
    Proper (eq ==> TE.Equal ==> TE.Equal) instr_succ_typenv.
  Proof.
    move=> i1 i2 ? E1 E2 Heq; subst. case: i2 => //=; intros; rewrite Heq; reflexivity.
  Qed.

  Global Instance add_proper_program_succ_typenv :
    Proper (eq ==> TE.Equal ==> TE.Equal) program_succ_typenv.
  Proof.
    move=> p1 p2 ? E1 E2 Heq; subst. elim: p2 E1 E2 Heq => [| i p IH] E1 E2 Heq //=.
    apply: (IH (instr_succ_typenv i E1) (instr_succ_typenv i E2)).
    rewrite Heq. reflexivity.
  Qed.

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

  Local Notation state := (state S.t).
  Local Notation ERR := (ERR S.t).

  Inductive eval_instr (te : TE.env) : instr -> state -> state -> Prop :=
  | Eerr : forall i, eval_instr te i ERR ERR
  | EImov v a s t :
      S.Upd v (eval_atom a s) s t ->
      eval_instr te (Imov v a) (OK s) (OK t)
  | EIshl v a i s t :
      S.Upd v (shlB i (eval_atom a s)) s t ->
      eval_instr te (Ishl v a i) (OK s) (OK t)
  | EIcshl vh vl a1 a2 i s t :
      S.Upd2 vl (shrB i
                      (low (size (eval_atom a2 s))
                           (shlB i
                                 (cat (eval_atom a2 s) (eval_atom a1 s)))))
             vh (high (size (eval_atom a1 s))
                      (shlB i
                            (cat (eval_atom a2 s) (eval_atom a1 s))))
             s t ->
      eval_instr te (Icshl vh vl a1 a2 i) (OK s) (OK t)
  | EInondet v ty s t n :
      size n = sizeof_typ ty ->
      S.Upd v n s t ->
      eval_instr te (Inondet v ty) (OK s) (OK t)
  | EIcmovT v c a1 a2 s t :
      to_bool (eval_atom c s) ->
      S.Upd v (eval_atom a1 s) s t ->
      eval_instr te (Icmov v c a1 a2) (OK s) (OK t)
  | EIcmovF v c a1 a2 s t :
      ~~ to_bool (eval_atom c s) ->
      S.Upd v (eval_atom a2 s) s t ->
      eval_instr te (Icmov v c a1 a2) (OK s) (OK t)
  | EInop s t : S.Equal s t -> eval_instr te Inop (OK s) (OK t)
  | EInot v ty a s t :
      S.Upd v (invB (eval_atom a s)) s t ->
      eval_instr te (Inot v ty a) (OK s) (OK t)
  | EIadd v a1 a2 s t :
      S.Upd v (addB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Iadd v a1 a2) (OK s) (OK t)
  | EIadds c v a1 a2 s t :
      S.Upd2 v (addB (eval_atom a1 s) (eval_atom a2 s))
             c (1-bits of bool
                       (carry_addB (eval_atom a1 s) (eval_atom a2 s)))
             s t ->
      eval_instr te (Iadds c v a1 a2) (OK s) (OK t)
  | EIadc v a1 a2 y s t :
      S.Upd v (adcB (to_bool (eval_atom y s))
                    (eval_atom a1 s)
                    (eval_atom a2 s)).2
            s t ->
      eval_instr te (Iadc v a1 a2 y) (OK s) (OK t)
  | EIadcs c v a1 a2 y s t :
      S.Upd2 v (adcB (to_bool (eval_atom y s))
                     (eval_atom a1 s)
                     (eval_atom a2 s)).2
             c (1-bits of bool
                       ((adcB (to_bool (eval_atom y s))
                             (eval_atom a1 s)
                             (eval_atom a2 s)).1))
             s t ->
      eval_instr te (Iadcs c v a1 a2 y) (OK s) (OK t)
  | EIsub v a1 a2 s t :
      S.Upd v (subB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Isub v a1 a2) (OK s) (OK t)
  | EIsubc c v a1 a2 s t :
      S.Upd2 v ((adcB true (eval_atom a1 s) (invB (eval_atom a2 s))).2)
             c (1-bits of bool
                       ((adcB true (eval_atom a1 s) (invB (eval_atom a2 s))).1))
             s t ->
      eval_instr te (Isubc c v a1 a2) (OK s) (OK t)
  | EIsubb b v a1 a2 s t :
      S.Upd2 v (subB (eval_atom a1 s) (eval_atom a2 s))
             b (1-bits of bool
                       (borrow_subB (eval_atom a1 s) (eval_atom a2 s)))
             s t ->
      eval_instr te (Isubb b v a1 a2) (OK s) (OK t)
  | EIsbc v a1 a2 y s t :
      S.Upd v (adcB (to_bool (eval_atom y s))
                    (eval_atom a1 s)
                    (invB (eval_atom a2 s))).2
            s t ->
      eval_instr te (Isbc v a1 a2 y) (OK s) (OK t)
  | EIsbcs c v a1 a2 y s t :
      S.Upd2 v (adcB (to_bool (eval_atom y s))
                     (eval_atom a1 s)
                     (invB (eval_atom a2 s))).2
             c (1-bits of bool
                       ((adcB (to_bool (eval_atom y s))
                             (eval_atom a1 s)
                             (invB (eval_atom a2 s))).1))
             s t ->
      eval_instr te (Isbcs c v a1 a2 y) (OK s) (OK t)
  | EIsbb v a1 a2 y s t :
      S.Upd v (sbbB (to_bool (eval_atom y s))
                    (eval_atom a1 s)
                    (eval_atom a2 s)).2
            s t ->
      eval_instr te (Isbb v a1 a2 y) (OK s) (OK t)
  | EIsbbs b v a1 a2 y s t :
      S.Upd2 v (sbbB (to_bool (eval_atom y s))
                     (eval_atom a1 s)
                     (eval_atom a2 s)).2
             b (1-bits of bool
                       ((sbbB (to_bool (eval_atom y s))
                             (eval_atom a1 s)
                             (eval_atom a2 s)).1))
             s t ->
      eval_instr te (Isbbs b v a1 a2 y) (OK s) (OK t)
  | EImul v a1 a2 s t :
      S.Upd v (mulB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Imul v a1 a2) (OK s) (OK t)
  | EImullU vh vl a1 a2 s t :
      is_unsigned (atyp a1 te) ->
      S.Upd2 vl (low (size (eval_atom a2 s))
                     (mulB (zext (size (eval_atom a1 s)) (eval_atom a1 s))
                           (zext (size (eval_atom a1 s)) (eval_atom a2 s))))
             vh (high (size (eval_atom a1 s))
                      (mulB (zext (size (eval_atom a1 s)) (eval_atom a1 s))
                            (zext (size (eval_atom a1 s)) (eval_atom a2 s))))
             s t ->
      eval_instr te (Imull vh vl a1 a2) (OK s) (OK t)
  | EImullS vh vl a1 a2 s t :
      is_signed (atyp a1 te) ->
      S.Upd2 vl (low (size (eval_atom a2 s))
                     (mulB (sext (size (eval_atom a1 s)) (eval_atom a1 s))
                           (sext (size (eval_atom a1 s)) (eval_atom a2 s))))
             vh (high (size (eval_atom a1 s))
                      (mulB (sext (size (eval_atom a1 s)) (eval_atom a1 s))
                            (sext (size (eval_atom a1 s)) (eval_atom a2 s))))
             s t ->
      eval_instr te (Imull vh vl a1 a2) (OK s) (OK t)
  | EImuljU v a1 a2 s t :
      is_unsigned (atyp a1 te) ->
      S.Upd v (mulB (zext (size (eval_atom a1 s)) (eval_atom a1 s))
                    (zext (size (eval_atom a1 s)) (eval_atom a2 s)))
            s t ->
      eval_instr te (Imulj v a1 a2) (OK s) (OK t)
  | EImuljS v a1 a2 s t :
      is_signed (atyp a1 te) ->
      S.Upd v (mulB (sext (size (eval_atom a1 s)) (eval_atom a1 s))
                    (sext (size (eval_atom a1 s)) (eval_atom a2 s)))
            s t ->
      eval_instr te (Imulj v a1 a2) (OK s) (OK t)
  | EIsplitU vh vl a n s t :
      is_unsigned (atyp a te) ->
      S.Upd2 vl (shrB ((size (eval_atom a s)) - n) (shlB ((size (eval_atom a s)) - n) (eval_atom a s)))
             vh (shrB n (eval_atom a s))
             s t ->
      eval_instr te (Isplit vh vl a n) (OK s) (OK t)
  | EIsplitS vh vl a n s t :
      is_signed (atyp a te) ->
      S.Upd2 vl (shrB ((size (eval_atom a s)) - n) (shlB ((size (eval_atom a s)) - n) (eval_atom a s)))
             vh (sarB n (eval_atom a s))
             s t ->
      eval_instr te (Isplit vh vl a n) (OK s) (OK t)
  | EIand v ty a1 a2 s t :
      S.Upd v (andB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Iand v ty a1 a2) (OK s) (OK t)
  | EIor v ty a1 a2 s t :
      S.Upd v (orB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Ior v ty a1 a2) (OK s) (OK t)
  | EIxor v ty a1 a2 s t :
      S.Upd v (xorB (eval_atom a1 s) (eval_atom a2 s)) s t ->
      eval_instr te (Ixor v ty a1 a2) (OK s) (OK t)
  | EIcast v ty a s t :
      S.Upd v (tcast (eval_atom a s) (atyp a te) ty) s t ->
      eval_instr te (Icast v ty a) (OK s) (OK t)
  | EIvpc v ty a s t :
      S.Upd v (tcast (eval_atom a s) (atyp a te) ty) s t ->
      eval_instr te (Ivpc v ty a) (OK s) (OK t)
  | EIjoin v ah al s t :
      S.Upd v (cat (eval_atom al s) (eval_atom ah s)) s t ->
      eval_instr te (Ijoin v ah al) (OK s) (OK t)
  | EIcutOK e s t :
    S.Equal s t ->
    eval_bexp e te s -> eval_instr te (Icut e) (OK s) (OK t)
  | EIcutERR e s :
    (~ eval_bexp e te s) -> eval_instr te (Icut e) (OK s) ERR
  | EIassertOK e s t :
    S.Equal s t ->
    eval_bexp e te s -> eval_instr te (Iassert e) (OK s) (OK t)
  | EIassertERR e s :
    (~ eval_bexp e te s) -> eval_instr te (Iassert e) (OK s) ERR
  | EIassume e s t :
    S.Equal s t ->
    eval_bexp e te s -> eval_instr te (Iassume e) (OK s) (OK t)
  .

  Local Hint Constructors eval_instr : dsl.

  Local Hint Immediate Eerr : dsl.

  Definition state_equal (s t : state) : Prop :=
    match s, t with
    | OK s, OK t => S.Equal s t
    | State.ERR, State.ERR => True
    | _, _ => False
    end.

  Lemma state_equal_refl s : state_equal s s.
  Proof. case: s => //=. move=> s; reflexivity. Qed.

  Lemma state_equal_sym s t : state_equal s t -> state_equal t s.
  Proof.
    case: s; case: t => //=. move=> s t Heq. apply: S.Equal_sym. assumption.
  Qed.

  Lemma state_equal_trans s t u : state_equal s t -> state_equal t u -> state_equal s u.
  Proof.
    case: s; case: t; case: u => //=. move=> s t u H1 H2.
    exact: (S.Equal_trans H1 H2).
  Qed.

  Global Instance state_equal_equivalence : Equivalence state_equal :=
    {| Equivalence_Reflexive := state_equal_refl;
      Equivalence_Symmetric := state_equal_sym;
      Equivalence_Transitive := state_equal_trans |}.

  Lemma Equal_state_equal s t : S.Equal s t -> state_equal (OK s) (OK t).
  Proof. rewrite /=. by apply. Qed.


  Inductive eval_instrs (te : TE.env) : seq instr -> state -> state -> Prop :=
  | Enil s t : state_equal s t -> eval_instrs te [::] s t
  | Econs hd tl s t u : eval_instr te hd s t ->
                  eval_instrs (instr_succ_typenv hd te) tl t u ->
                  eval_instrs te (hd::tl) s u.

  Definition eval_program (te : TE.env) p s t : Prop := eval_instrs te p s t.


  Ltac eval_instr_elim :=
    match goal with
    | H : eval_instr _ _ _ _ |- _ => inversion_clear H
    end.

  Ltac eval_instr_intro :=
    match goal with
    | |- eval_instr _ _ ERR ERR => apply: Eerr
    | |- eval_instr _ (Imov _ _) _ _ => apply: EImov
    | |- eval_instr _ (Ishl _ _ _) _ _ => apply: EIshl
    | |- eval_instr _ (Icshl _ _ _ _ _) _ _ => apply: EIcshl
    | |- eval_instr _ (Inondet _ _) _ _ => apply: EInondet
    | H : is_true (to_bool (eval_atom ?c ?s)) |- eval_instr _ (Icmov _ ?c _ _) (OK ?s) _ => apply: (EIcmovT _ _ H)
    | H : to_bool (eval_atom ?c ?s) = true |- eval_instr _ (Icmov _ ?c _ _) (OK ?s) _ => apply: (EIcmovT _ _ H)
    | H : is_true (~~ (to_bool (eval_atom ?c ?s))) |- eval_instr _ (Icmov _ ?c _ _) (OK ?s) _ => apply: (EIcmovF _ _ H)
    | |- eval_instr _ Inop _ _ => apply: EInop
    | |- eval_instr _ (Inot _ _ _) _ _ => apply: EInot
    | |- eval_instr _ (Iadd _ _ _) _ _ => apply: EIadd
    | |- eval_instr _ (Iadds _ _ _ _) _ _ => apply: EIadds
    | |- eval_instr _ (Iadc _ _ _ _) _ _ => apply: EIadc
    | |- eval_instr _ (Iadcs _ _ _ _ _) _ _ => apply: EIadcs
    | |- eval_instr _ (Isub _ _ _) _ _ => apply: EIsub
    | |- eval_instr _ (Isubc _ _ _ _) _ _ => apply: EIsubc
    | |- eval_instr _ (Isubb _ _ _ _) _ _ => apply: EIsubb
    | |- eval_instr _ (Isbc _ _ _ _) _ _ => apply: EIsbc
    | |- eval_instr _ (Isbcs _ _ _ _ _) _ _ => apply: EIsbcs
    | |- eval_instr _ (Isbb _ _ _ _) _ _ => apply: EIsbb
    | |- eval_instr _ (Isbbs _ _ _ _ _) _ _ => apply: EIsbbs
    | |- eval_instr _ (Imul _ _ _) _ _ => apply: EImul
    | H : is_true (is_unsigned (atyp ?a ?E)) |- eval_instr ?E (Imull _ _ ?a _) _ _ => apply: (EImullU H)
    | H : is_unsigned (atyp ?a ?E) = true |- eval_instr ?E (Imull _ _ ?a _) _ _ => apply: (EImullU H)
    | H : is_true (is_signed (atyp ?a ?E)) |- eval_instr ?E (Imull _ _ ?a _) _ _ => apply: (EImullS H)
    | H : is_signed (atyp ?a ?E) = true |- eval_instr ?E (Imull _ _ ?a _) _ _ => apply: (EImullS H)
    | H : is_true (is_unsigned (atyp ?a ?E)) |- eval_instr ?E (Imulj _ ?a _) _ _ => apply: (EImuljU H)
    | H : is_unsigned (atyp ?a ?E) = true |- eval_instr ?E (Imulj _ ?a _) _ _ => apply: (EImuljU H)
    | H : is_true (is_signed (atyp ?a ?E)) |- eval_instr ?E (Imulj _ ?a _) _ _ => apply: (EImuljS H)
    | H : is_signed (atyp ?a ?E) = true |- eval_instr ?E (Imulj _ ?a _) _ _ => apply: (EImuljS H)
    | H : is_true (is_unsigned (atyp ?a ?E)) |- eval_instr ?E (Isplit _ _ ?a _) _ _ => apply: (EIsplitU H)
    | H : is_unsigned (atyp ?a ?E) = true |- eval_instr ?E (Isplit _ _ ?a _) _ _ => apply: (EIsplitU H)
    | H : is_true (is_signed (atyp ?a ?E)) |- eval_instr ?E (Isplit _ _ ?a _) _ _ => apply: (EIsplitS H)
    | H : is_signed (atyp ?a ?E) = true |- eval_instr ?E (Isplit _ _ ?a _) _ _ => apply: (EIsplitS H)
    | |- eval_instr _ (Iand _ _ _ _) _ _ => apply: EIand
    | |- eval_instr _ (Ior _ _ _ _) _ _ => apply: EIor
    | |- eval_instr _ (Ixor _ _ _ _) _ _ => apply: EIxor
    | |- eval_instr _ (Icast _ _ _) _ _ => apply: EIcast
    | |- eval_instr _ (Ivpc _ _ _) _ _ => apply: EIvpc
    | |- eval_instr _ (Ijoin _ _ _) _ _ => apply: EIjoin
    | |- eval_instr _ (Icut ?e) (OK _) (OK _) => apply: EIcutOK
    | |- eval_instr _ (Icut ?e) (OK _) ERR => apply: EIcutERR
    | |- eval_instr _ (Iassert ?e) (OK _) (OK _) => apply: EIassertOK
    | |- eval_instr _ (Iassert ?e) (OK _) ERR => apply: EIassertERR
    | |- eval_instr _ (Iassume _) _ _ => apply: EIassume
    end.

  Global Instance add_proper_eval_eexp_env :
    Proper (eq ==> TE.Equal ==> eq ==> eq) eval_eexp.
  Proof.
    move=> e1 e2 ? E1 E2 Heq s1 s2 ?; subst. elim: e2 => //=.
    - move=> x. rewrite Heq. reflexivity.
    - move=> op e IH. rewrite IH. reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> e IH n. rewrite IH. reflexivity.
  Qed.

  Global Instance add_proper_eval_eexp_store :
    Proper (eq ==> eq ==> S.Equal ==> eq) eval_eexp.
  Proof.
    move=> e1 e2 ? E1 E2 ? s1 s2 Heq; subst. elim: e2 => //=.
    - move=> x. rewrite -> Heq. reflexivity.
    - move=> op e IH. rewrite IH. reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> e IH n. rewrite IH. reflexivity.
  Qed.

  Global Instance add_proper_eval_eexps_env :
    Proper (eq ==> TE.Equal ==> eq ==> eq) eval_eexps.
  Proof.
    move=> es1 es2 ? E1 E2 Heq s1 s2 ?; subst.
    elim: es2 => [| e es IH] //=. f_equal.
    - by rewrite Heq.
    - exact: IH.
  Qed.

  Global Instance add_proper_eval_eexps_store :
    Proper (eq ==> eq ==> S.Equal ==> eq) eval_eexps.
  Proof.
    move=> es1 es2 ? E1 E2 ? s1 s2 Heq; subst.
    elim: es2 => [| e es IH] //=. f_equal.
    - by rewrite -> Heq.
    - exact: IH.
  Qed.

  Global Instance add_proper_eval_rexp_store :
    Proper (eq ==> S.Equal ==> eq) eval_rexp.
  Proof.
    move=> e1 e2 ? s1 s2 Heq; subst. elim: e2 => //=.
    - move=> x. rewrite -> Heq. reflexivity.
    - move=> _ op e IH. rewrite IH. reflexivity.
    - move=> _ op e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> _ e IH n. rewrite IH. reflexivity.
    - move=> _ e IH n. rewrite IH. reflexivity.
  Qed.

  Global Instance add_proper_eval_ebexp_env :
    Proper (eq ==> TE.Equal ==> eq ==> iff) eval_ebexp.
  Proof.
    move=> e1 e2 ? E1 E2 Heq s1 s2 ?; subst. elim: e2 => //=.
    - move=> e1 e2. by rewrite Heq.
    - move=> e1 e2 ms. by rewrite Heq.
    - move=> e1 IH1 e2 IH2. by rewrite IH1 IH2.
  Qed.

  Global Instance add_proper_eval_ebexp_store :
    Proper (eq ==> eq ==> S.Equal ==> iff) eval_ebexp.
  Proof.
    move=> e1 e2 ? E1 E2 ? s1 s2 Heq; subst. elim: e2 => //=.
    - move=> e1 e2. by rewrite -> Heq.
    - move=> e1 e2 ms. by rewrite -> Heq.
    - move=> e1 IH1 e2 IH2. by rewrite IH1 IH2.
  Qed.

  Global Instance add_proper_eval_rbexp_store :
    Proper (eq ==> S.Equal ==> eq) eval_rbexp.
  Proof.
    move=> e1 e2 ? s1 s2 Heq; subst. elim: e2 => //=.
    - move=> _ e1 e2. rewrite -> Heq. reflexivity.
    - move=> _ op e1 e2. rewrite -> Heq. reflexivity.
    - move=> e IH. rewrite IH. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
  Qed.

  Global Instance add_proper_eval_bexp_env :
    Proper (eq ==> TE.Equal ==> eq ==> iff) eval_bexp.
  Proof.
    move=> e1 e2 ? E1 E2 Heq s1 s2 ?; subst.
    rewrite /eval_bexp. by rewrite Heq.
  Qed.

  Global Instance add_proper_eval_bexp_store :
    Proper (eq ==> eq ==> S.Equal ==> iff) eval_bexp.
  Proof.
    move=> e1 e2 ? E1 E2 ? s1 s2 Heq; subst.
    rewrite /eval_bexp. by rewrite -> Heq.
  Qed.

  Global Instance add_proper_valid :
    Proper (eq ==> TE.Equal ==> iff) valid.
  Proof.
    move=> e1 e2 ? E1 E2 Heq; subst. split.
    - move=> H s Hco. move/(S.add_proper_conform_env (erefl s) Heq): Hco => Hco.
      move: (H _ Hco). rewrite Heq. by apply.
    - move=> H s Hco. move/(S.add_proper_conform_env (erefl s) Heq): Hco => Hco.
      move: (H _ Hco). rewrite Heq. by apply.
  Qed.

  Global Instance add_proper_entails :
    Proper (eq ==> eq ==> TE.Equal ==> iff) entails.
  Proof.
    move=> f1 f2 ? g1 g2 ? E1 E2 Heq; subst. rewrite /entails. split.
    - move=> H s Hco Hev. move/(S.add_proper_conform_env (erefl s) Heq): Hco => Hco.
      move: (H _ Hco). rewrite Heq. by apply.
    - move=> H s Hco Hev. move/(S.add_proper_conform_env (erefl s) Heq): Hco => Hco.
      move: (H _ Hco). rewrite -Heq. by apply.
  Qed.

  Global Instance add_proper_eval_atom :
    Proper (eq ==> S.Equal ==> eq) eval_atom.
  Proof.
    move=> a1 a2 ? s1 s2 Heq; subst. rewrite /eval_atom. case: a2 => //=.
    move=> x. rewrite -> Heq. reflexivity.
  Qed.

  Global Instance add_proper_eval_instr_env :
    Proper (TE.Equal ==> eq ==> eq ==> eq ==> iff) eval_instr.
  Proof.
    move=> E1 E2 Heq i1 i2 ? s1 s2 ? s3 s4 ?; subst.
    (case: i2 => //=); intros; split; intros; eval_instr_elim;
    repeat match goal with
      | H1 : TE.Equal ?E1 ?E2, H2 : context c [atyp _ ?E1] |- context c [eval_instr ?E2 _ _ _] =>
          rewrite (add_proper_atyp (erefl _) H1) in H2
      | H1 : TE.Equal ?E1 ?E2, H2 : context c [asize _ ?E1] |- context c [eval_instr ?E2 _ _ _] =>
          rewrite (add_proper_asize (erefl _) H1) in H2
      | H1 : TE.Equal ?E1 ?E2, H2 : context c [atyp _ ?E2] |- context c [eval_instr ?E1 _ _ _] =>
          rewrite -(add_proper_atyp (erefl _) H1) in H2
      | H1 : TE.Equal ?E1 ?E2, H2 : context c [asize _ ?E2] |- context c [eval_instr ?E1 _ _ _] =>
          rewrite -(add_proper_asize (erefl _) H1) in H2
      end;
    try eval_instr_intro; eauto.
    all: (match goal with
          | H1 : TE.Equal ?E1 ?E2, H2 : context [eval_bexp _ ?E1 _] |- _ =>
              rewrite -> H1 in H2
          | H1 : TE.Equal ?E1 ?E2 |- context [eval_bexp _ ?E1 _] =>
              rewrite -> H1
          end); assumption.
  Qed.

  Global Instance add_proper_eval_instr_store1 :
    Proper (eq ==> eq ==> state_equal ==> eq ==> iff) eval_instr.
  Proof.
    move=> E1 E2 ? i1 i2 ? s1 s2 Heq s3 s4 ?; subst. case: s1 Heq; case: s2 => //=.
    move=> s1 s2 Heq.
    (case: i2 => //=); intros; split; intros; eval_instr_elim;
    repeat
      match goal with
      | H1 : S.Equal ?s1 ?s2, H2 : context c [eval_atom ?a ?s1] |- context c [eval_instr _ _ (OK ?s2) _] =>
          rewrite -> (add_proper_eval_atom (erefl a) H1) in H2
      | H1 : S.Equal ?s1 ?s2, H2 : context c [eval_atom ?a ?s2] |- context c [eval_instr _ _ (OK ?s1) _] =>
          rewrite <- (add_proper_eval_atom (erefl a) H1) in H2
      | H1 : S.Equal ?s1 ?s2, H2 : S.Upd _ _ ?s1 _ |- context c [eval_instr _ _ (OK ?s2)] =>
          rewrite -> (S.add_proper_Upd1 (erefl _) (erefl _) H1 (erefl _)) in H2
      | H1 : S.Equal ?s1 ?s2, H2 : S.Upd _ _ ?s2 _ |- context c [eval_instr _ _ (OK ?s1)] =>
          rewrite <- (S.add_proper_Upd1 (erefl _) (erefl _) H1 (erefl _)) in H2
      | H1 : S.Equal ?s1 ?s2, H2 : S.Upd2 _ _ _ _ ?s1 _ |- context c [eval_instr _ _ (OK ?s2)] =>
          rewrite -> (S.add_proper_Upd2_1 (erefl _) (erefl _) (erefl _) (erefl _) H1 (erefl _)) in H2
      | H1 : S.Equal ?s1 ?s2, H2 : S.Upd2 _ _ _ _ ?s2 _ |- context c [eval_instr _ _ (OK ?s1)] =>
          rewrite <- (S.add_proper_Upd2_1 (erefl _) (erefl _) (erefl _) (erefl _) H1 (erefl _)) in H2
      end;
    try (by eval_instr_intro; eauto).
    all:
      eval_instr_intro;
      repeat
        match goal with
        | H1 : S.Equal ?s1 ?s2, H2 : S.Equal ?s1 ?s3 |- S.Equal ?s2 ?s3 =>
            rewrite <- H1; rewrite <- H2; reflexivity
        | H1 : S.Equal ?s1 ?s2, H2 : S.Equal ?s3 ?s1 |- S.Equal ?s3 ?s2 =>
            rewrite <- H1; rewrite -> H2; reflexivity
        | H1 : S.Equal ?s1 ?s2, H2 : context [eval_bexp ?b ?E ?s1]  |-
            context [eval_bexp ?b ?E ?s2] =>
            rewrite <- H1; assumption
        | H1 : S.Equal ?s1 ?s2, H2 : context [eval_bexp ?b ?E ?s2]  |-
            context [eval_bexp ?b ?E ?s1] =>
            rewrite -> H1; assumption
        end.
    all: reflexivity.
  Qed.

  Global Instance add_proper_eval_instr_store2 :
    Proper (eq ==> eq ==> eq ==> state_equal ==> iff) eval_instr.
  Proof.
    move=> E1 E2 ? i1 i2 ? s1 s2 ? s3 s4 Heq; subst.
    case: s2 Heq; case: s3; case: s4 => //=.
    2: by move=> s1 s2 Heq; split => H; inversion_clear H.
    (case: i2 => //=); intros; split; intros; eval_instr_elim;
    try eval_instr_intro;
    repeat match goal with
           | H1 : S.Equal ?s1 ?s2, H2 : S.Upd _ _ _ ?s1 |- context c [S.Upd _ _ _ ?s2] =>
               rewrite -(S.add_proper_Upd2 (erefl _) (erefl _) (erefl _) H1)
           | H1 : S.Equal ?s1 ?s2, H2 : S.Upd _ _ _ ?s2 |- context c [S.Upd _ _ _ ?s1] =>
               rewrite (S.add_proper_Upd2 (erefl _) (erefl _) (erefl _) H1)
           | H1 : S.Equal ?s1 ?s2, H2 : S.Upd2 _ _ _ _ _ ?s1 |- context c [S.Upd2 _ _ _ _ _ ?s2] =>
               rewrite -(S.add_proper_Upd2_2 (erefl _) (erefl _) (erefl _) (erefl _) (erefl _) H1)
           | H1 : S.Equal ?s1 ?s2, H2 : S.Upd2 _ _ _ _ _ ?s2 |- context c [S.Upd2 _ _ _ _ _ ?s1] =>
               rewrite (S.add_proper_Upd2_2 (erefl _) (erefl _) (erefl _) (erefl _) (erefl _) H1)
           end; eauto.
    all: by (repeat match goal with
                    | H1 : S.Equal ?s1 ?s2, H2 : context [?s1] |- _ => rewrite -> H1 in H2
                    | H1 : S.Equal ?s1 ?s2 |- context [?s1] => rewrite -> H1
                    | |- S.Equal ?s ?s => reflexivity
                    end).
  Qed.

  Global Instance add_proper_eval_program_env :
    Proper (TE.Equal ==> eq ==> eq ==> eq ==> iff) eval_program.
  Proof.
    move=> E1 E2 Heq p1 p2 ? s1 s2 ? t1 t2 ?; subst.
    elim: p2 E1 E2 s2 t2 Heq => [| i p IH] E1 E2 s t Heq.
    - split; inversion_clear 1; exact: (Enil _ H0).
    - have Heqsucc: TE.Equal (instr_succ_typenv i E1) (instr_succ_typenv i E2) by rewrite Heq.
      split; inversion_clear 1.
      + apply: Econs.
        * rewrite <- Heq. exact: H0.
        * by apply/(IH _ _ _ _ Heqsucc).
      + apply: Econs.
        * rewrite -> Heq. exact: H0.
        * by apply/(IH _ _ _ _ Heqsucc).
  Qed.

  Global Instance add_proper_eval_program_store1 :
    Proper (eq ==> eq ==> state_equal ==> eq ==> iff) eval_program.
  Proof.
    move=> E1 E2 ? p1 p2 ? s1 s2 Heq t1 t2 ?; subst.
    case: p2 => [| i p].
    - split; inversion_clear 1.
      + apply: Enil. rewrite <- Heq; assumption.
      + apply: Enil. rewrite -> Heq; assumption.
    - split; inversion_clear 1.
      + rewrite -> Heq in H0. apply: (Econs H0). assumption.
      + rewrite <- Heq in H0. apply: (Econs H0). assumption.
  Qed.

  Global Instance add_proper_eval_program_store2 :
    Proper (eq ==> eq ==> eq ==> state_equal ==> iff) eval_program.
  Proof.
    move=> E1 E2 ? p1 p2 ? s1 s2 ? t1 t2 Heq; subst.
    elim: p2 E2 s2 t1 t2 Heq => [| i p IH] E s t1 t2 Heq.
    - split; inversion_clear 1.
      + apply: Enil. by rewrite <- Heq.
      + apply: Enil. by rewrite -> Heq.
    -  split; inversion_clear 1.
      + apply: (Econs H0). apply/(IH _ _ _ _ Heq). assumption.
      + apply: (Econs H0). apply/(IH _ _ _ _ Heq). assumption.
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

  Lemma eval_bexp_band E s e1 e2 :
    eval_bexp (band e1 e2) E s <-> eval_bexp e1 E s /\ eval_bexp e2 E s.
  Proof.
    rewrite /band. case: e1 => [e1 r1]; case: e2 => [e2 r2] //=.
    by case_if; repeat match goal with
                       | H : (_ == _) = true |- _ => move/eqP: H => ?; subst
                       | |- _ <-> _ => split; move=> ?
                       | |- _ /\ _ => split
                       | |- eval_bexp _ _ _ => rewrite /eval_bexp /=
                       | H : eval_bexp _ _ _ |- _ => rewrite /eval_bexp /= in H
                       | H : _ /\ _ |- _ => case: H => ? ?
                       | H : is_true (_ && _) |- _ => move/andP: H => [? ?]
                       | |- is_true (_ && _) => apply/andP; split
                       | |- True => done
                       | |- is_true true => exact: is_true_true
                       | H : ?e |- ?e => assumption
                       end.
  Qed.

  Lemma eval_bexp_bands_nil E s : eval_bexp (bands [::]) E s.
  Proof. by rewrite /eval_bexp /=. Qed.

  Lemma eval_bexp_bands_cons E s e es :
    eval_bexp (bands (e::es)) E s <-> eval_bexp e E s /\ eval_bexp (bands es) E s.
  Proof.
    move: es e. apply: last_ind => [| es e IH] f //=.
    - rewrite bands_singleton /bands /=. move: (eval_bexp_bands_nil E s). tauto.
    - rewrite /bands. rewrite -rcons_cons. rewrite !foldl_rcons.
      rewrite -/(bands (f::es)) -/(bands es). split => H.
      + move/eval_bexp_band : H => [Hfes He]. move/IH: Hfes => [Hf Hes].
        split; [assumption |]. apply/eval_bexp_band. tauto.
      + move: H => [Hf /eval_bexp_band [Hes He]]. apply/eval_bexp_band.
        split; [| assumption]. apply/IH. tauto.
  Qed.

  Lemma eval_bexp_bands_rcons E s es e :
    eval_bexp (bands (rcons es e)) E s <-> eval_bexp (bands es) E s /\ eval_bexp e E s.
  Proof.
    rewrite /bands foldl_rcons. rewrite -/(bands es). split; [move=> H | move=> [H1 H2]].
    - move/eval_bexp_band : H. tauto.
    - apply/eval_bexp_band. tauto.
  Qed.

  Lemma eval_bexp_bands_cat E s es1 es2 :
    eval_bexp (bands (es1 ++ es2)) E s <-> eval_bexp (bands es1) E s /\ eval_bexp (bands es2) E s.
  Proof.
    elim: es1 es2 => [| e1 es1 IH] es2 //=.
    - move: (eval_bexp_bands_nil E s). tauto.
    - split => [/eval_bexp_bands_cons [H1 /IH [H2 H3]] | [/eval_bexp_bands_cons [H1 H2] H3]].
      + split; [apply/eval_bexp_bands_cons |]; tauto.
      + apply/eval_bexp_bands_cons. split; [| apply/IH]; tauto.
  Qed.


  Lemma eval_program_singleton i te1 s1 s2:
    eval_program te1 ([:: i]) s1 s2 -> eval_instr te1 i s1 s2.
  Proof.
    move=> H. inversion_clear H. inversion_clear H1. rewrite <- H. assumption.
  Qed.

  Lemma eval_program_cons_exists E hd tl s1 s3 :
    eval_program E (hd :: tl) s1 s3 ->
    exists s2, eval_instr E hd s1 s2 /\
               eval_program (instr_succ_typenv hd E) tl s2 s3.
  Proof.
    move => Hev.
    inversion_clear Hev.
    exists t => //.
  Qed.

  Lemma eval_program_rcons_exists E p i s1 s3 :
    eval_program E (rcons p i) s1 s3 ->
    exists s2, eval_program E p s1 s2 /\
               eval_instr (program_succ_typenv p E) i s2 s3.
  Proof.
    elim: p E s1 s3 => [| hd tl IH] E s1 s3 Hev /=.
    - inversion_clear Hev. move: H. inversion_clear H0. move=> Hev.
      exists s1. rewrite <- H. split; [exact: (Enil _ (state_equal_refl s1)) | exact: Hev].
    - move: (eval_program_cons_exists Hev) => [s2 [Hev_hd Hev_tli]].
      move: (IH _ _ _ Hev_tli) => [s4 [Hev_tl Hev_i]].
      exists s4. split.
      + exact: (Econs Hev_hd Hev_tl).
      + exact: Hev_i.
  Qed.

  Lemma eval_program_rcons E p i s1 s2 s3 :
    eval_program E p s1 s2 ->
    eval_instr (program_succ_typenv p E) i s2 s3 ->
    eval_program E (rcons p i) s1 s3.
  Proof.
    elim: p E i s1 s2 s3 => [| i p IH1] E j s1 s2 s3 //=.
    - inversion_clear 1. rewrite H0. move=> H. apply: (Econs H). apply: Enil. reflexivity.
    - move=> Hev1 Hev2. inversion_clear Hev1. apply: (Econs H).
      apply: (IH1 _ _ _ _ _ H0). assumption.
  Qed.

  Lemma eval_program_cat_exists E p1 p2 s1 s3 :
    eval_program E (p1 ++ p2) s1 s3 ->
    exists s2, eval_program E p1 s1 s2 /\
               eval_program (program_succ_typenv p1 E) p2 s2 s3.
  Proof.
    elim: p1 p2 E s1 s3 => [| i1 p1 IH] p2 E s1 s3 Hev /=.
    - rewrite cat0s in Hev. exists s1. split; [exact: (Enil _ (state_equal_refl s1)) | exact: Hev].
    - rewrite cat_cons in Hev. move: (eval_program_cons_exists Hev) => [s4 [Hev_i1 Hev_cat]].
      move: (IH _ _ _ _ Hev_cat) => [s5 [Hev_p1 Hev_p2]]. exists s5. split.
      + exact: (Econs Hev_i1 Hev_p1).
      + exact: Hev_p2.
  Qed.

  Lemma eval_program_cat E p1 p2 s1 s2 s3 :
    eval_program E p1 s1 s2 ->
    eval_program (program_succ_typenv p1 E) p2 s2 s3 ->
    eval_program E (p1 ++ p2) s1 s3.
  Proof.
    elim: p1 E p2 s1 s2 s3 => [| i1 p1 IH1] E p2 s1 s2 s3 //=.
    - inversion_clear 1. rewrite -> H0. by apply.
    - move=> Hev1 Hev2. inversion_clear Hev1. apply: (Econs H).
      apply: (IH1 _ _ _ _ _ H0). assumption.
  Qed.

  Lemma eval_instr_err E i s : eval_instr E i ERR s -> s = ERR.
  Proof. move=> H; inversion_clear H. reflexivity. Qed.

  Lemma eval_program_err E p s : eval_program E p ERR s -> s = ERR.
  Proof.
    elim: p E s => [| i p IH] E s //=.
    - inversion_clear 1. by case: s H0.
    - inversion_clear 1. move: (eval_instr_err H0) => ?; subst.
      exact: (IH _ _ H1).
  Qed.

  Lemma eval_instr_err_err E i : eval_instr E i ERR ERR.
  Proof. exact: Eerr. Qed.

  Lemma eval_program_err_err E p : eval_program E p ERR ERR.
  Proof.
    elim: p E => [| i p IH] E //=.
    - apply: Enil. reflexivity.
    - apply: (Econs (eval_instr_err_err _ _)). exact: IH.
  Qed.

  Lemma eval_program_err_ok E p s : ~ eval_program E p ERR (OK s).
  Proof. move=> H. move: (eval_program_err H). discriminate. Qed.

  Lemma eval_instr_ok_err E i s :
    eval_instr E i (OK s) ERR -> exists e, (i = Icut e \/ i = Iassert e) /\ ~ eval_bexp e E s.
  Proof.
    inversion_clear 1.
    - exists e. split; [left; reflexivity | assumption].
    - exists e. split; [right; reflexivity | assumption].
  Qed.

  Lemma eval_program_cons_ok E i p s1 s3 :
    eval_program E (i :: p) (OK s1) (OK s3) ->
    exists s2, eval_instr E i (OK s1) (OK s2) /\
               eval_program (instr_succ_typenv i E) p (OK s2) (OK s3).
  Proof.
    move=> H. inversion_clear H. case: t H0 H1 => /=.
    - move=> t Hevi Hevp. exists t. tauto.
    - move=> _ H. apply: False_ind. exact: (eval_program_err_ok H).
  Qed.

  Lemma eval_program_rcons_ok E p i s1 s3 :
    eval_program E (rcons p i) (OK s1) (OK s3) ->
    exists s2, eval_program E p (OK s1) (OK s2) /\
               eval_instr (program_succ_typenv p E) i (OK s2) (OK s3).
  Proof.
    move=> H. move: (eval_program_rcons_exists H) => [s2 [Hevp Hevi]].
    case: s2 Hevp Hevi => /=.
    - move=> t Hevp Hevi. exists t. tauto.
    - move=> _ {}H. apply: False_ind. by inversion_clear H.
  Qed.

  Lemma eval_program_cat_ok E p1 p2 s1 s3 :
    eval_program E (p1 ++ p2) (OK s1) (OK s3) ->
    exists s2, eval_program E p1 (OK s1) (OK s2) /\
               eval_program (program_succ_typenv p1 E) p2 (OK s2) (OK s3).
  Proof.
    move=> Hev. move: (eval_program_cat_exists Hev) => [s2 [Hev1 Hev2]].
    case: s2 Hev1 Hev2 => /=.
    - move=> t Hev1 Hev2. exists t. tauto.
    - move=> _ H. apply: False_ind. exact: (eval_program_err_ok H).
  Qed.

  Lemma eval_program_cons_ok_err E i p s :
    eval_program E (i :: p) (OK s) ERR ->
    (exists t, eval_instr E i (OK s) (OK t) /\
                 eval_program (instr_succ_typenv i E) p (OK t) ERR) \/
      (eval_instr E i (OK s) ERR).
  Proof.
    move=> H. inversion_clear H. case: t H0 H1 => /=.
    - move=> t Hevi Hevp. left; exists t; tauto.
    - move=> Hevi Hevp; by right.
  Qed.

  Lemma eval_program_rcons_ok_err E p i s :
    eval_program E (rcons p i) (OK s) ERR ->
    (exists t, eval_program E p (OK s) (OK t) /\
                 eval_instr (program_succ_typenv p E) i (OK t) ERR) \/
      (eval_program E p (OK s) ERR).
  Proof.
    move=> H. move: (eval_program_rcons_exists H) => [s2 [Hevp Hevi]].
    case: s2 Hevp Hevi => /=.
    - move=> t Hevp Hevi. left; exists t; tauto.
    - move=> ? ?; by right.
  Qed.

  Lemma eval_program_cat_ok_err E p1 p2 s :
    eval_program E (p1 ++ p2) (OK s) ERR ->
    (exists t, eval_program E p1 (OK s) (OK t) /\
                 eval_program (program_succ_typenv p1 E) p2 (OK t) ERR) \/
      (eval_program E p1 (OK s) ERR).
  Proof.
    move=> H. move: (eval_program_cat_exists H) => [s2 [Hev1 Hev2]].
    case: s2 Hev1 Hev2 => /=.
    - move=> t Hev1 Hev2. left; exists t; tauto.
    - move=> ? ?; by right.
  Qed.


  (* Partial correctness *)

  Definition valid_spec_ok (s : spec) : Prop :=
    forall s1 s2,
      S.conform s1 (sinputs s) ->
      eval_bexp (spre s) (sinputs s) s1 ->
      eval_program (sinputs s) (sprog s) (OK s1) (OK s2) ->
      eval_bexp (spost s) (program_succ_typenv (sprog s) (sinputs s)) s2.

  Definition valid_spec_err (s : spec) : Prop :=
    forall s1,
      S.conform s1 (sinputs s) ->
      eval_bexp (spre s) (sinputs s) s1 ->
      ~ eval_program (sinputs s) (sprog s) (OK s1) ERR.

  Definition valid_spec (s : spec) : Prop :=
    valid_spec_ok s /\ valid_spec_err s.


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
    | Icut e
    | Iassert e
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

  Global Instance add_proper_well_typed_eexp :
    Proper (TE.Equal ==> eq ==> eq) well_typed_eexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. elim: e2 => //=.
    move=> op e1 IH1 e2 IH2. by rewrite IH1 IH2.
  Qed.

  Global Instance add_proper_well_typed_eexps :
    Proper (TE.Equal ==> eq ==> eq) well_typed_eexps.
  Proof.
    move=> E1 E2 Heq es1 es2 ?; subst. elim: es2 => [| e es IH] //=.
    by rewrite {1}Heq IH.
  Qed.

  Global Instance add_proper_well_typed_rexp :
    Proper (TE.Equal ==> eq ==> eq) well_typed_rexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. (elim: e2 => //=).
    - move=> x. by rewrite Heq.
    - move=> n _ e IH. by rewrite IH Heq.
    - move=> n _ e1 IH1 e2 IH2. by rewrite IH1 IH2 Heq.
    - move=> n e IH _. by rewrite IH Heq.
    - move=> n e IH _. by rewrite IH Heq.
  Qed.

  Global Instance add_proper_well_typed_ebexp :
    Proper (TE.Equal ==> eq ==> eq) well_typed_ebexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. elim: e2 => //=.
    - move=> e1 e2. by rewrite Heq.
    - move=> e1 e2 ms. by rewrite Heq.
    - move=> e1 IH1 e2 IH2. by rewrite IH1 IH2.
  Qed.

  Global Instance add_proper_well_typed_rbexp :
    Proper (TE.Equal ==> eq ==> eq) well_typed_rbexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. elim: e2 => //=.
    - move=> n e1 e2. by rewrite Heq.
    - move=> n _ e1 e2. by rewrite Heq.
    - move=> e1 IH1 e2 IH2. by rewrite IH1 IH2.
    - move=> e1 IH1 e2 IH2. by rewrite IH1 IH2.
  Qed.

  Global Instance add_proper_well_typed_bexp :
    Proper (TE.Equal ==> eq ==> eq) well_typed_bexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. case: e2 => [e r].
    rewrite /well_typed_bexp /=. by rewrite Heq.
  Qed.

  Global Instance add_proper_well_sized_atom :
    Proper (TE.Equal ==> eq ==> eq) well_sized_atom.
  Proof.
    move=> E1 E2 Heq a1 a2 ?; subst. case: a2 => //=.
    move=> v. rewrite /well_sized_atom /=. by repeat rewrite -> Heq.
  Qed.

  Global Instance add_proper_well_typed_atom :
    Proper (TE.Equal ==> eq ==> eq) well_typed_atom.
  Proof.
    move=> E1 E2 Heq a1 a2 ?; subst. case: a2 => //=.
    move=> v. rewrite /well_typed_atom /=. by rewrite -> Heq.
  Qed.

  Global Instance add_proper_well_typed_instr :
    Proper (TE.Equal ==> eq ==> eq) well_typed_instr.
  Proof.
    move=> E1 E2 Heq i1 i2 ?; subst. (case: i2 => //=);
    intros; by repeat rewrite -> Heq.
  Qed.


  (* Well-defined instructions *)

  Module TEKS := MapKeySet V TE VS.

  (* the set of defined variables *)
  Definition vars_env (te : TE.env) := TEKS.key_set te.

  (* Note: Use TE.mem v te to determine if v is defined *)
  Definition is_defined (v : var) (te : TE.env) : bool :=
    TE.mem v te.

  Definition are_defined (vs : VS.t) (te : TE.env) : bool :=
    VS.for_all (is_defined^~ te) vs.

  Lemma is_defined_compat_bool E : compat_bool VS.SE.eq (is_defined^~ E).
  Proof. move=> x y Hxy. rewrite Hxy. reflexivity. Qed.

  Global Instance add_proper_vars_env :
    Proper (TE.Equal ==> VS.Equal) vars_env.
  Proof.
    move=> E1 E2 Heq. rewrite /vars_env. rewrite -> Heq. reflexivity.
  Qed.

  Global Instance add_proper_is_defined :
    Proper (eq ==> TE.Equal ==> eq) is_defined.
  Proof.
    move=> x1 x2 ? E1 E2 Heq; subst. rewrite /is_defined. rewrite Heq. reflexivity.
  Qed.

  Global Instance add_proper_are_defined_vars :
    Proper (VS.Equal ==> eq ==> eq) are_defined.
  Proof.
    move=> vs1 vs2 H E1 E2 ?; subst. rewrite /are_defined.
    case H2: (VS.for_all (is_defined^~ E2) vs2).
    - apply: (VS.for_all_1 (is_defined_compat_bool _)). move=> x Hin.
      move: (VS.for_all_2 (is_defined_compat_bool _) H2). apply. rewrite -H. assumption.
    - apply/negP => H1. move/negP: H2; apply.
      apply: (VS.for_all_1 (is_defined_compat_bool _)). move=> x Hin.
      move: (VS.for_all_2 (is_defined_compat_bool _) H1). apply. rewrite H. assumption.
  Qed.

  Global Instance add_proper_are_defined_env :
    Proper (eq ==> TE.Equal ==> eq) are_defined.
  Proof.
    move=> vs1 vs2 ? E1 E2 Heq; subst. rewrite /are_defined.
    case H2: (VS.for_all (is_defined^~ E2) vs2).
    - apply: (VS.for_all_1 (is_defined_compat_bool _)). move=> x Hin.
      move: (VS.for_all_2 (is_defined_compat_bool _) H2). rewrite Heq.
      apply. assumption.
    - apply/negP => H1. move/negP: H2; apply.
      apply: (VS.for_all_1 (is_defined_compat_bool _)). move=> x Hin.
      move: (VS.for_all_2 (is_defined_compat_bool _) H1). rewrite -Heq.
      apply. assumption.
  Qed.

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
    | Icut e
    | Iassert e
    | Iassume e => are_defined (vars_bexp e) te
    end.

  Global Instance add_proper_well_defined_instr :
    Proper (TE.Equal ==> eq ==> eq) well_defined_instr.
  Proof.
    move=> E1 E2 Heq i1 i2 ?; subst.
    case: i2 => //=; intros; by repeat rewrite -> Heq.
  Qed.


  (* Well-formedness *)

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

  Definition well_formed_spec (s : spec) : bool :=
    well_formed_bexp (sinputs s) (spre s) &&
    well_formed_program (sinputs s) (sprog s) &&
    well_formed_bexp (program_succ_typenv (sprog s) (sinputs s)) (spost s).


  Global Instance add_proper_well_formed_eexp :
    Proper (TE.Equal ==> eq ==> eq) well_formed_eexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. rewrite /well_formed_eexp. by rewrite Heq.
  Qed.

  Global Instance add_proper_well_formed_eexps :
    Proper (TE.Equal ==> eq ==> eq) well_formed_eexps.
  Proof.
    move=> E1 E2 Heq es1 es2 ?; subst. elim: es2 => [| e es IH] //=.
    by rewrite IH Heq.
  Qed.

  Global Instance add_proper_well_formed_rexp :
    Proper (TE.Equal ==> eq ==> eq) well_formed_rexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. rewrite /well_formed_rexp. by rewrite Heq.
  Qed.

  Global Instance add_proper_well_formed_ebexp :
    Proper (TE.Equal ==> eq ==> eq) well_formed_ebexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. rewrite /well_formed_ebexp. by rewrite Heq.
  Qed.

  Global Instance add_proper_well_formed_rbexp :
    Proper (TE.Equal ==> eq ==> eq) well_formed_rbexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. rewrite /well_formed_rbexp. by rewrite Heq.
  Qed.

  Global Instance add_proper_well_formed_bexp :
    Proper (TE.Equal ==> eq ==> eq) well_formed_bexp.
  Proof.
    move=> E1 E2 Heq e1 e2 ?; subst. rewrite /well_formed_bexp. by rewrite Heq.
  Qed.

  Global Instance add_proper_well_formed_instr :
    Proper (TE.Equal ==> eq ==> eq) well_formed_instr.
  Proof.
    move=> E1 E2 Heq i1 i2 ?; subst. rewrite /well_formed_instr. by rewrite Heq.
  Qed.

  Global Instance add_proper_well_formed_program :
    Proper (TE.Equal ==> eq ==> eq) well_formed_program.
  Proof.
    move=> E1 E2 Heq p1 p2 ?; subst. elim: p2 E1 E2 Heq => [| i p IH] E1 E2 Heq //=.
    rewrite {1}Heq. rewrite (IH (instr_succ_typenv i E1)  (instr_succ_typenv i E2));
      [reflexivity | by rewrite Heq].
  Qed.


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

  Lemma well_formed_instr_cut E e :
    well_formed_instr E (Icut e) = well_formed_bexp E e.
  Proof.
    rewrite /well_formed_instr /well_formed_bexp /=. reflexivity.
  Qed.

  Lemma well_formed_instr_assert E e :
    well_formed_instr E (Iassert e) = well_formed_bexp E e.
  Proof.
    rewrite /well_formed_instr /well_formed_bexp /=. reflexivity.
  Qed.

  Lemma well_formed_instr_assume E e :
    well_formed_instr E (Iassume e) = well_formed_bexp E e.
  Proof.
    rewrite /well_formed_instr /well_formed_bexp /=. reflexivity.
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
    - exact: (well_typed_bexp_submap H0 Hwd Hwt).
    - exact: (well_typed_bexp_submap H0 Hwd Hwt).
    - exact: (well_typed_bexp_submap H0 Hwd Hwt).
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

  Lemma submap_instr_succ_typenv i te1 te2:
    well_formed_instr te1 i ->
    TELemmas.submap te1 te2 ->
    TELemmas.submap (instr_succ_typenv i te1) (instr_succ_typenv i te2).
  Proof.
    (elim: i te1 te2 => //=); intros;
    repeat match goal with
      | H : ?a |- ?a => assumption
      | H : ?l \/ ?r |- _ => case: H => H
      | |- ?l /\ ?r => split
      | |- is_true (_ && _) => apply /andP
      | H : is_true(well_formed_instr ?te ?i) |- _  =>
          let Hwd := fresh "Hwd" in
          let Hwt := fresh "Hwt" in
          move/andP: H => [Hwd Hwt]
      | Hwd: is_true (well_defined_instr ?te ?i) |- _ =>
          (rewrite /= in Hwd)
      | H : is_true(well_typed_instr ?te ?i) |- _  =>
          (rewrite /= in H)
      | H : is_true (_ && _) |- _ =>
          let H1 := fresh in let H2 := fresh in move/andP: H => [H1 H2]
      | Hsub: TELemmas.submap ?te1 ?te2, Hwd: is_true (are_defined ?vs ?te1)
        |- is_true (are_defined ?vs ?te2) =>
          exact: (are_defined_submap Hsub Hwd)
      | Hsub: TELemmas.submap ?te1 ?te2,
          Hwd: is_true (are_defined (vars_atom ?a) ?te1)
        |- context [atyp ?a ?te2] =>
          rewrite -(atyp_submap Hsub Hwd)
      | |- TELemmas.submap (TE.add ?x ?v ?E1) (TE.add ?x ?v ?E2) =>
          apply: TELemmas.submap_add
      end; done.
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

  Lemma well_formed_program_subset_rvs E p :
    well_formed_program E p ->
    VS.subset (rvs_program p) (VS.union (vars_env E) (lvs_program p)).
  Proof.
    elim: p E => [| i p IH] E /=.
    - move=> _. exact: VSLemmas.subset_empty.
    - move/andP=> [Hwfi Hwfp]. move: (IH _ Hwfp) => Hsubp.
      rewrite vars_env_instr_succ_typenv in Hsubp.
      move: (well_formed_instr_subset_rvs Hwfi) => Hsubi.
      apply: VSLemmas.subset_union3.
      + by VSLemmas.dp_subset.
      + rewrite -VSLemmas.P.union_assoc. assumption.
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

  Lemma well_formed_eexp_vars_subset E e :
    well_formed_eexp E e -> VS.subset (vars_eexp e) (vars_env E).
  Proof.
    rewrite /well_formed_eexp. move/andP=> [H _]. rewrite are_defined_subset_env in H.
    assumption.
  Qed.

  Lemma well_formed_ebexp_vars_subset E e :
    well_formed_ebexp E e -> VS.subset (vars_ebexp e) (vars_env E).
  Proof.
    rewrite /well_formed_ebexp. move/andP=> [H _]. rewrite are_defined_subset_env in H.
    assumption.
  Qed.

  Lemma well_formed_rexp_vars_subset E e :
    well_formed_rexp E e -> VS.subset (vars_rexp e) (vars_env E).
  Proof.
    rewrite /well_formed_rexp. move/andP=> [H _]. rewrite are_defined_subset_env in H.
    assumption.
  Qed.

  Lemma well_formed_rbexp_vars_subset E e :
    well_formed_rbexp E e -> VS.subset (vars_rbexp e) (vars_env E).
  Proof.
    rewrite /well_formed_rbexp. move/andP=> [H _]. rewrite are_defined_subset_env in H.
    assumption.
  Qed.

  Lemma well_formed_bexp_vars_subset E e :
    well_formed_bexp E e -> VS.subset (vars_bexp e) (vars_env E).
  Proof.
    rewrite /well_formed_bexp. move/andP=> [H _]. rewrite are_defined_subset_env in H.
    assumption.
  Qed.

  Lemma well_formed_program_vars_subset E p :
    well_formed_program E p ->
    VS.subset (vars_program p) (VS.union (vars_env E) (lvs_program p)).
  Proof.
    elim: p E => [| i p IH] E //=.
    - move=> _. exact: VSLemmas.subset_empty.
    - move/andP=> [Hwfi Hwfp]. move: (IH _ Hwfp) => Hsub.
      rewrite vars_env_instr_succ_typenv in Hsub.
      move: (well_formed_instr_subset_rvs Hwfi) => Hrvs.
      rewrite vars_instr_split.
      rewrite VSLemmas.P.union_assoc in Hsub.
      by VSLemmas.dp_subset.
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

  Lemma well_formed_spec_pre s :
    well_formed_spec s -> well_formed_bexp (sinputs s) (spre s).
  Proof. by move/andP=> [/andP [H1 H2] H3]. Qed.

  Lemma well_formed_spec_prog s :
    well_formed_spec s -> well_formed_program (sinputs s) (sprog s).
  Proof. by move/andP=> [/andP [H1 H2] H3]. Qed.

  Lemma well_formed_spec_post s :
    well_formed_spec s -> well_formed_bexp (program_succ_typenv (sprog s) (sinputs s)) (spost s).
  Proof. by move/andP=> [/andP [H1 H2] H3]. Qed.

  Lemma well_defined_instr_instr_succ_typenv E i j :
    well_defined_instr E i ->
    well_defined_instr (instr_succ_typenv j E) i.
  Proof.
    (case: i => //=); intros;
      by repeat
           match goal with
           | H : is_true (are_defined ?vs ?E) |-
               is_true (are_defined ?vs (instr_succ_typenv _ ?E)) =>
               exact: (are_defined_instr_succ_typenv _ H)
           | H : is_true (_ && _) |- _ =>
               let H1 := fresh in
               let H2 := fresh in
               move/andP: H => [H1 H2]
           | |- is_true (_ && _) => apply/andP; split
           | H : ?e |- ?e => assumption
           end.
  Qed.

  Lemma well_defined_instr_program_succ_typenv E i p :
    well_defined_instr E i ->
    well_defined_instr (program_succ_typenv p E) i.
  Proof.
    elim: p E => [| j p IH] E Hdefi //=. apply: IH.
    exact: (well_defined_instr_instr_succ_typenv _ Hdefi).
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
    - apply: (EIcutOK H1). apply/(submap_eval_bexp Hsub H). assumption.
    - apply: EIcutERR. move=> H3. apply: H1. apply/(submap_eval_bexp Hsub H). assumption.
    - apply: (EIcutOK H1). apply/(submap_eval_bexp Hsub H). assumption.
    - apply: EIcutERR. move=> H3; apply: H1. apply/(submap_eval_bexp Hsub H). assumption.
    - apply: (EIassertOK H1). apply/(submap_eval_bexp Hsub H). assumption.
    - apply: EIassertERR. move=> H3; apply: H1. apply/(submap_eval_bexp Hsub H). assumption.
    - apply: (EIassertOK H1). apply/(submap_eval_bexp Hsub H). assumption.
    - apply: EIassertERR. move=> H3; apply: H1. apply/(submap_eval_bexp Hsub H). assumption.
    - apply: (EIassume H1). apply/(submap_eval_bexp Hsub H). assumption.
    - apply: (EIassume H1). apply/(submap_eval_bexp Hsub H). assumption.
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

  Lemma vtyp_instr_succ_typenv_not_mem_lvs E x i :
    ~~ VS.mem x (lvs_instr i) ->
    TE.vtyp x (instr_succ_typenv i E) = TE.vtyp x E.
  Proof.
    (case: i => //=); intros;
      by repeat match goal with
                | H : is_true (~~ VS.mem _ (VS.singleton _)) |- _ =>
                    move: (VSLemmas.not_mem_singleton1 H) => /= {}H
                | H : is_true (~~ VS.mem _ (VS.add _ _)) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    move: (VSLemmas.not_mem_add1 H) => {H} [H1 H2]
                | H : ~ VS.SE.eq _ _ |- _ =>
                    move/negP: H => H
                | H : is_true (?x != ?t) |- context [TE.vtyp ?x (TE.add ?t _ _)] =>
                    rewrite (TE.vtyp_add_neq H)
                | |- ?e = ?e => reflexivity
                end.
  Qed.

  Lemma atyp_instr_succ_typenv_disjoint_lvs E a i :
    VSLemmas.disjoint (vars_atom a) (lvs_instr i) ->
    atyp a (instr_succ_typenv i E) = atyp a E.
  Proof.
    case: a => //=. move=> x. rewrite VSLemmas.disjoint_sym VSLemmas.disjoint_singleton.
    exact: vtyp_instr_succ_typenv_not_mem_lvs.
  Qed.

  Lemma vtyp_program_succ_typenv_not_mem_lvs E x p :
    ~~ VS.mem x (lvs_program p) ->
    TE.vtyp x (program_succ_typenv p E) = TE.vtyp x E.
  Proof.
    elim: p E => [| i p IH] E //= H. move: (VSLemmas.not_mem_union1 H) => {H} [H1 H2].
    rewrite (IH _ H2). exact: (vtyp_instr_succ_typenv_not_mem_lvs _ H1).
  Qed.

  Lemma atyp_program_succ_typenv_disjoint_lvs E a p :
    VSLemmas.disjoint (vars_atom a) (lvs_program p) ->
    atyp a (program_succ_typenv p E) = atyp a E.
  Proof.
    elim: p E => [| i p IH] E //= H. rewrite VSLemmas.disjoint_union in H.
    move/andP: H => [H1 H2]. rewrite (IH _ H2).
    exact: (atyp_instr_succ_typenv_disjoint_lvs _ H1).
  Qed.

  Lemma instr_succ_typenv_add_comm E v t i :
    ~~ VS.mem v (vars_instr i) ->
    TE.Equal (TE.add v t (instr_succ_typenv i E)) (instr_succ_typenv i (TE.add v t E)).
  Proof.
    (case: i => //=); intros;
      by repeat match goal with
                | |- TE.Equal ?e ?e => reflexivity
                | H : is_true (~~ VS.mem _ (VS.add _ _)) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    move: (VSLemmas.not_mem_add1 H) => {H} [H1 H2]
                | H : is_true (~~ VS.mem _ (VS.union _ _)) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    move: (VSLemmas.not_mem_union1 H) => {H} [H1 H2]
                | H : is_true (~~ VS.mem _ (VS.singleton _)) |- _ =>
                    move: (VSLemmas.not_mem_singleton1 H) => {}H
                | H : is_true (~~ VS.mem ?x (vars_atom ?a)) |-
                    context [atyp ?a (TE.add ?x ?t ?E)] =>
                    rewrite (atyp_add_not_mem _ _ H)
                | |- TE.Equal (TE.add _ _ (TE.add ?y ?ty _))
                              (TE.add ?y ?ty (TE.add _ _ _)) =>
                    rewrite TELemmas.add_comm
                | |- TE.Equal (TE.add ?x ?v _) (TE.add ?x ?v _) =>
                    apply: TELemmas.add2_equal; first reflexivity
                | H : ~ VS.SE.eq ?x ?y |- ~ TE.SE.eq ?x ?y =>
                    assumption
                | H : (~ VS.SE.eq ?x ?y) |- (~ TE.SE.eq ?y ?x) =>
                    let Heq := fresh in
                    (intro Heq); (apply H); (apply: VS.SE.eq_sym); assumption
             end.
  Qed.

  Lemma instr_succ_typenv_disjoint_comm E i j :
    VSLemmas.disjoint (vars_instr i) (vars_instr j) ->
    TE.Equal (instr_succ_typenv i (instr_succ_typenv j E))
             (instr_succ_typenv j (instr_succ_typenv i E)).
  Proof.
    case: i => //=; intros;
    repeat match goal with
           | |- TE.Equal ?e ?e => reflexivity
           | H : is_true (VSLemmas.disjoint (VS.add _ _) _) |- _ =>
               let H1 := fresh in
               let H2 := fresh in
               rewrite VSLemmas.disjoint_add_l in H;
               move/andP: H => [H1 H2]
           | H : is_true (VSLemmas.disjoint (VS.union _ _) _) |- _ =>
               let H1 := fresh in
               let H2 := fresh in
               rewrite VSLemmas.disjoint_union_l in H;
               move/andP: H => [H1 H2]
           | H : is_true (VSLemmas.disjoint (VS.singleton _) _) |- _ =>
               rewrite VSLemmas.disjoint_singleton_l in H
           | H : is_true (VSLemmas.disjoint (vars_atom ?a) (vars_instr ?i)) |-
               context [atyp ?a (instr_succ_typenv ?i ?E)] =>
               rewrite (atyp_instr_succ_typenv_disjoint_lvs _ )
           | H : is_true (~~ VS.mem ?v (vars_instr ?i)) |-
               context [TE.add ?v ?t (instr_succ_typenv ?i ?E)] =>
               rewrite (instr_succ_typenv_add_comm _ _ H)
           | H : is_true (VSLemmas.disjoint (vars_atom ?a) (vars_instr ?j)) |-
               is_true (VSLemmas.disjoint (vars_atom ?a) (lvs_instr ?j)) =>
               exact: (VSLemmas.disjoint_subset_r H (lvs_instr_subset _))
           end.
  Qed.

  Lemma well_defined_instr_not_mem_add E i x v :
    well_defined_instr E i ->
    ~~ VS.mem x (vars_instr i) ->
    well_defined_instr (TE.add x v E) i.
  Proof.
    (case: i => //=); intros;
      by repeat match goal with
                | H : is_true (are_defined ?vs ?E) |- is_true (are_defined ?vs (TE.add _ _ ?E)) =>
                    apply: are_defined_addr
                | H : is_true (_ && _) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    move/andP: H => [H1 H2]
                | |- is_true (_ && _) =>
                    apply/andP; split
                | H : ?e |- ?e => assumption
                end.
  Qed.

  Lemma Upd_disjoint_eval_atom x v s1 s2 a :
    S.Upd x v s1 s2 -> VSLemmas.disjoint (VS.singleton x) (vars_atom a) ->
    eval_atom a s2 = eval_atom a s1.
  Proof.
    case: a => [y | t bs] /= Hupd Hdisj.
    - rewrite VSLemmas.disjoint_singleton in Hdisj. move: (VSLemmas.not_mem_singleton1 Hdisj).
      move/negP => Hne. rewrite (S.acc_Upd_neq Hne Hupd). reflexivity.
    - reflexivity.
  Qed.

  Lemma Upd2_disjoint_eval_atom x1 v1 x2 v2 s1 s2 a :
    S.Upd2 x1 v1 x2 v2 s1 s2 ->
    VSLemmas.disjoint (VS.singleton x1) (vars_atom a) ->
    VSLemmas.disjoint (VS.singleton x2) (vars_atom a) ->
    eval_atom a s2 = eval_atom a s1.
  Proof.
    case: a => [y | t bs] /= Hupd Hdisj1 Hdisj2.
    - rewrite !VSLemmas.disjoint_singleton in Hdisj1 Hdisj2.
      move: (VSLemmas.not_mem_singleton1 Hdisj1); move/negP => {Hdisj1} Hne1.
      move: (VSLemmas.not_mem_singleton1 Hdisj2); move/negP => {Hdisj2} Hne2.
      rewrite (S.acc_Upd2_neq Hne1 Hne2 Hupd). reflexivity.
    - reflexivity.
  Qed.


  (* Infer input variables *)

  Fixpoint inputs_program_rec (defined : VS.t) (p : program) : VS.t :=
    match p with
    | [::] => VS.empty
    | i::p => VS.union (VS.diff (rvs_instr i) defined)
                       (inputs_program_rec (VS.union (lvs_instr i) defined) p)
    end.

  Definition inputs_program (p : program) : VS.t :=
    inputs_program_rec VS.empty p.


  Global Instance add_proper_inputs_program_rec :
    Proper (VS.Equal ==> eq ==> VS.Equal) inputs_program_rec.
  Proof.
    move=> d1 d2 Heq p1 p2 ?; subst. elim: p2 d1 d2 Heq => [| i p IH] d1 d2 Heq //=.
    have Heq': VS.Equal (VS.union (lvs_instr i) d1) (VS.union (lvs_instr i) d2) by rewrite Heq; reflexivity.
    rewrite (IH _ _ Heq') Heq. reflexivity.
  Qed.

  Lemma inputs_program_cons i p :
    VS.Equal (inputs_program (i::p))
             (VS.union (rvs_instr i)
                       (inputs_program_rec (lvs_instr i) p)).
  Proof.
    rewrite /inputs_program /=. rewrite VSLemmas.diff_empty_r.
    rewrite VSLemmas.union_emptyr. reflexivity.
  Qed.

  Lemma inputs_program_rec_rcons defined p i :
    VS.Equal (inputs_program_rec defined (rcons p i))
             (VS.union (inputs_program_rec defined p)
                       (VS.diff (rvs_instr i) (VS.union (lvs_program p) defined))).
  Proof.
    elim: p defined => [| j p IH] defined //=.
    - rewrite !VSLemmas.union_emptyl !VSLemmas.union_emptyr. reflexivity.
    - rewrite IH. set ins := (inputs_program_rec (VS.union (lvs_instr j) defined) p).
      set s1 := VS.diff (rvs_instr j) defined.
      rewrite VSLemmas.P.union_assoc.
      rewrite (VSLemmas.P.union_sym (lvs_instr j) (lvs_program p)).
      rewrite VSLemmas.P.union_assoc. reflexivity.
  Qed.

  Lemma input_program_rcons p i :
    VS.Equal (inputs_program (rcons p i))
             (VS.union (inputs_program p) (VS.diff (rvs_instr i) (lvs_program p))).
  Proof.
    rewrite -(VSLemmas.union_emptyr (lvs_program p)). exact: inputs_program_rec_rcons.
  Qed.

  Lemma inputs_program_rec_cat defined p1 p2 :
    VS.Equal (inputs_program_rec defined (p1 ++ p2))
             (VS.union (inputs_program_rec defined p1)
                       (inputs_program_rec (VS.union (lvs_program p1) defined) p2)).
  Proof.
    elim: p1 p2 defined => [| i1 p1 IH1] p2 defined //=.
    - rewrite !VSLemmas.union_emptyl. reflexivity.
    - rewrite IH1. set s1 := (inputs_program_rec (VS.union (lvs_instr i1) defined) p1).
      rewrite (VSLemmas.P.union_sym (lvs_instr i1) (lvs_program p1)).
      rewrite !VSLemmas.P.union_assoc. reflexivity.
  Qed.

  Lemma inputs_program_cat p1 p2 :
    VS.Equal (inputs_program (p1 ++ p2))
             (VS.union (inputs_program p1)
                       (inputs_program_rec (lvs_program p1) p2)).
  Proof.
    rewrite -(VSLemmas.union_emptyr (lvs_program p1)).
    exact: inputs_program_rec_cat.
  Qed.

  Lemma inputs_program_rec_subset defined p :
    VS.subset (inputs_program_rec defined p) (VS.diff (rvs_program p) defined).
  Proof.
    elim: p defined => [| i p IH] defined //=.
    - exact: VSLemmas.subset_empty.
    - move: (IH (VS.union (lvs_instr i) defined)) => {IH}.
      set s1 := (inputs_program_rec (VS.union (lvs_instr i) defined) p).
      move=> Hsub. apply: VSLemmas.subset_union3.
      + apply: VSLemmas.subset_diff_same. by VSLemmas.dp_subset.
      + apply: (VSLemmas.subset_trans Hsub). apply: VSLemmas.subset_diff; by VSLemmas.dp_subset.
  Qed.

  Lemma inputs_program_subset p :
    VS.subset (inputs_program p) (rvs_program p).
  Proof.
    rewrite -(VSLemmas.diff_empty_r (rvs_program p)).
    exact: inputs_program_rec_subset.
  Qed.


  (* Non-blocking *)

  Definition is_nondet (i : instr) : bool :=
    match i with
    | Inondet _ _ => true
    | _ => false
    end.

  Definition is_cut (i : instr) : bool :=
    match i with
    | Icut _ => true
    | _ => false
    end.

  Definition is_assert (i : instr) : bool :=
    match i with
    | Iassert _ => true
    | _ => false
    end.

  Definition is_assume (i : instr) : bool :=
    match i with
    | Iassume _ => true
    | _ => false
    end.

  (* Given a store, the evaluation of every instruction except assert and assume
     should result in a store *)
  Lemma instr_nonblocking (te : TE.env) (i : instr) (s : S.t) :
    ~~ is_cut i ->
    ~~ is_assert i ->
    ~~ is_assume i ->
    exists (t : S.t), eval_instr te i (OK s) (OK t).
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
    - (* Inop *) move=> _. exists s. exact: (EInop _ (S.Equal_refl s)).
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
    eval_instr te (Imov t a) (OK s1) (OK s2) ->
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
    eval_instr te (Ishl t a n) (OK s1) (OK s2) ->
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
    eval_instr te (Icshl t t0 a a0 n) (OK s1) (OK s2) ->
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
    eval_instr te (Inondet t t0) (OK s1) (OK s2) ->
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
    eval_instr te (Icmov t a a0 a1) (OK s1) (OK s2) ->
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
    eval_instr te Inop (OK s1) (OK s2) ->
    S.conform s2 (instr_succ_typenv Inop te) .
  Proof .
    move => Hcon _ _ Hev. inversion_clear Hev.
    rewrite -(S.add_proper_conform_store H (erefl _)). assumption.
  Qed.

  Lemma conform_eval_succ_typenv_Inot te t t0 a s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Inot t t0 a) ->
    well_typed_instr te (Inot t t0 a) ->
    eval_instr te (Inot t t0 a) (OK s1) (OK s2) ->
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
    eval_instr te (Iadd t a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Iadds t t0 a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Iadc t a a0 a1) (OK s1) (OK s2) ->
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
    eval_instr te (Iadcs t t0 a a0 a1) (OK s1) (OK s2) ->
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
    eval_instr te (Isub t a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Isubc t t0 a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Isubb t t0 a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Isbc t a a0 a1) (OK s1) (OK s2) ->
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
    eval_instr te (Isbcs t t0 a a0 a1) (OK s1) (OK s2) ->
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
    eval_instr te (Isbb t a a0 a1) (OK s1) (OK s2) ->
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
    eval_instr te (Isbbs t t0 a a0 a1) (OK s1) (OK s2) ->
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
    eval_instr te (Imul t a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Imull t t0 a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Imulj t a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Isplit t t0 a n) (OK s1) (OK s2) ->
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
    eval_instr te (Iand t t0 a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Ior t t0 a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Ixor t t0 a a0) (OK s1) (OK s2) ->
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
    eval_instr te (Icast t t0 a) (OK s1) (OK s2) ->
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
    eval_instr te (Ivpc t t0 a) (OK s1) (OK s2) ->
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
    eval_instr te (Ijoin t a a0) (OK s1) (OK s2) ->
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

  Lemma conform_eval_succ_typenv_Icut te b s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Icut b) ->
    well_typed_instr te (Icut b) ->
    eval_instr te (Icut b) (OK s1) (OK s2) ->
    S.conform s2 (instr_succ_typenv (Icut b) te) .
  Proof .
    move => Hcon Hdef _ Hev. inversion_clear Hev.
    rewrite -(S.add_proper_conform_store H (erefl _)). assumption.
  Qed.

  Lemma conform_eval_succ_typenv_Iassert te b s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iassert b) ->
    well_typed_instr te (Iassert b) ->
    eval_instr te (Iassert b) (OK s1) (OK s2) ->
    S.conform s2 (instr_succ_typenv (Iassert b) te) .
  Proof .
    move => Hcon Hdef _ Hev. inversion_clear Hev.
    rewrite -(S.add_proper_conform_store H (erefl _)). assumption.
  Qed.

  Lemma conform_eval_succ_typenv_Iassume te b s1 s2 :
    S.conform s1 te ->
    well_defined_instr te (Iassume b) ->
    well_typed_instr te (Iassume b) ->
    eval_instr te (Iassume b) (OK s1) (OK s2) ->
    S.conform s2 (instr_succ_typenv (Iassume b) te) .
  Proof .
    move => Hcon Hdef _ Hev. inversion_clear Hev.
    rewrite -(S.add_proper_conform_store H (erefl _)). assumption.
  Qed.

  Lemma conform_instr_succ_typenv te i s1 s2 :
    well_formed_instr te i ->
    S.conform s1 te ->
    eval_instr te i (OK s1) (OK s2) ->
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
    - move => b; apply conform_eval_succ_typenv_Icut .
    - move => b; apply conform_eval_succ_typenv_Iassert .
    - move => b; apply conform_eval_succ_typenv_Iassume .
  Qed .

  Lemma conform_program_succ_typenv E p s1 s2 :
    well_formed_program E p ->
    S.conform s1 E ->
    eval_program E p (OK s1) (OK s2) ->
    S.conform s2 (program_succ_typenv p E).
  Proof.
    elim: p E s1 s2 => [| i p IH] E s1 s2 Hwf Hco Hep /=.
    - move: Hco. inversion_clear Hep. simpl in H. rewrite -> H. by apply.
    - inversion_clear Hep. rewrite well_formed_program_cons in Hwf.
      move/andP: Hwf => [Hwf_i Hwf_p]. case: t H H0 => //=.
      + move=> t H H0. apply: (IH _ _ _ Hwf_p _ H0).
        exact: (conform_instr_succ_typenv Hwf_i Hco H).
      + move=> H1 H2. apply: False_ind. exact: (eval_program_err_ok H2).
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

    Global Instance bvs_equivalence E : Equivalence (bvs_eqi E).
    Proof.
      repeat split.
      - exact: bvs_eqi_sym.
      - exact: bvs_eqi_trans.
    Qed.

    Global Instance add_proper_bvs_eqi_env :
      Proper (TE.Equal ==> eq ==> eq ==> iff) bvs_eqi.
    Proof.
      move=> E1 E2 He s1 s2 ? t1 t2 ?; subst; split.
      - move=> Heq x Hmem. rewrite <- He in Hmem. exact: (Heq _ Hmem).
      - move=> Heq x Hmem. rewrite -> He in Hmem. exact: (Heq _ Hmem).
    Qed.

    Global Instance add_proper_bvs_eqi_store1 :
      Proper (eq ==> S.Equal ==> S.Equal ==> iff) bvs_eqi.
    Proof.
      move=> E1 E2 ? s1 s2 Hs t1 t2 Ht; subst; split.
      - move=> Heq x Hmem. rewrite <- Hs. rewrite <- Ht. exact: (Heq _ Hmem).
      - move=> Heq x Hmem. rewrite -> Hs. rewrite -> Ht. exact: (Heq _ Hmem).
    Qed.

    Global Instance add_proper_bvs_eqi_store2 :
      Proper (eq ==> S.Equal ==> eq ==> iff) bvs_eqi.
    Proof.
      move=> E1 E2 ? s1 s2 Hs t1 t2 ?; subst; split.
      - move=> Heq x Hmem. rewrite <- Hs. exact: (Heq _ Hmem).
      - move=> Heq x Hmem. rewrite -> Hs. exact: (Heq _ Hmem).
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
          Hev : eval_instr _ _ (OK ?s1) _ |- _ =>
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
      well_defined_instr E i -> bvs_eqi E s1 t1 -> eval_instr E i (OK s1) (OK s2) ->
      exists t2, eval_instr E i (OK t1) (OK t2) /\ bvs_eqi (instr_succ_typenv i E) s2 t2.
    Proof.
      case: i => /=; try (move=> *; mytac; by eauto with dsl).
      (* Inop *)
      move=> _ Heqi Hev; inversion_clear Hev. rewrite -> H in Heqi. exists t1.
      split; last assumption. exact: (EInop _ (S.Equal_refl t1)).
      (* Icut *)
      move=> e Hdef Heqi Hev. move: Heqi. inversion_clear Hev => Heqi.
      exists t1. rewrite <- H. split; last assumption. apply: (EIcutOK (S.Equal_refl t1)).
      apply/(bvs_eqi_eval_bexp Hdef Heqi). assumption.
      (* Iassert *)
      move=> e Hdef Heqi Hev. move: Heqi. inversion_clear Hev => Heqi.
      exists t1. rewrite <- H. split; last assumption. apply: (EIassertOK (S.Equal_refl t1)).
      apply/(bvs_eqi_eval_bexp Hdef Heqi). assumption.
      (* Iassume *)
      move=> e Hdef Heqi Hev. move: Heqi. inversion_clear Hev => Heqi.
      exists t1. rewrite <- H. split; last assumption. apply: (EIassume (S.Equal_refl t1)).
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

    Global Instance add_proper_force_conform_vars_env :
      Proper (TE.Equal ==> eq ==> eq ==> eq) force_conform_vars.
    Proof.
      move=> E1 E2 Heq vs1 vs2 ? s1 s2 ?; subst. elim: vs2 => [| v vs IH] //=.
      rewrite IH. rewrite -> Heq. reflexivity.
    Qed.

    Global Instance add_proper_force_conform_vars_store :
      Proper (eq ==> eq ==> S.Equal ==> S.Equal) force_conform_vars.
    Proof.
      move=> E1 E2 ? vs1 vs2 ? s1 s2 Heq; subst. elim: vs2 => [| v vs IH] //=.
      apply: S.Equal_upd_Equal. assumption.
    Qed.

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

    Global Instance add_proper_force_conform_env1 :
      Proper (TE.Equal ==> eq ==> eq ==> S.Equal) force_conform.
    Proof.
      move=> E1 E2 Heq F1 F2 ? s1 s2 ?; subst. rewrite /force_conform.
      have Hdiff: VS.Equal (VS.diff (vars_env F2) (vars_env E1))
                    (VS.diff (vars_env F2) (vars_env E2)) by rewrite Heq.
     exact: (force_conform_vars_set_equal F2 s2 Hdiff).
    Qed.

    Global Instance add_proper_force_conform_env2 :
      Proper (eq ==> TE.Equal ==> eq ==> S.Equal) force_conform.
    Proof.
      move=> E1 E2 ? F1 F2 Heq s1 s2 ?; subst. rewrite /force_conform.
      rewrite {1}Heq. apply: force_conform_vars_set_equal.
      by rewrite Heq.
    Qed.

    Global Instance add_proper_force_conform_store :
      Proper (eq ==> eq ==> S.Equal ==> S.Equal) force_conform.
    Proof.
      move=> E1 E2 ? F1 F2 ? s1 s2 Heq; subst. rewrite /force_conform.
      rewrite Heq. reflexivity.
    Qed.

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

  Module MA := TypEnvAgree V TE VS.

  Section Agree.

    Lemma agree_atyp a E1 E2 :
      MA.agree (vars_atom a) E1 E2 -> atyp a E1 = atyp a E2.
    Proof. case: a => //=. move=> v Ha. exact: (MA.agree_vtyp_singleton Ha). Qed.

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
      - move=> v Ha. rewrite /acc2z. rewrite (MA.agree_vtyp_singleton Ha). reflexivity.
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

    Lemma agree_lvs_instr_succ_typenv i E1 E2 :
      MA.agree (rvs_instr i) E1 E2 ->
      MA.agree (lvs_instr i) (instr_succ_typenv i E1) (instr_succ_typenv i E2).
    Proof.
      (case: i => //=); intros; dec_atom_typ; MA.dp_agree;
        by repeat match goal with
                  | |- context [TE.find ?x (TE.add ?x ?t ?E)] =>
                      rewrite (TELemmas.find_add_eq (eqxx x))
                  | H : (?x == ?y) = true |- context [TE.find ?x (TE.add ?y ?t ?E)] =>
                      rewrite (TELemmas.find_add_eq H)
                  | H : ~ (is_true (?x == ?y)) |- context [TE.find ?x (TE.add ?y ?t ?E)] =>
                      rewrite (TELemmas.find_add_neq H)
                  | |- context [TE.find ?x (TE.add ?y ?t ?E)] =>
                      let H := fresh in
                      dcase (x == y); case; move=> H; [| move/negP: H => H]
                  | |- ?e = ?e => reflexivity
                  end.
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
      case: s1; case: s2 => //=.
      - move=> s1 s2. case: i => //=; intros; inversion_eval_instr.
        + apply: EImov; assumption.
        + apply: EIshl; assumption.
        + apply: EIcshl; assumption.
        + apply: (EInondet _ H1); assumption.
        + apply: (EIcmovT _ _ H1); assumption.
        + apply: (EIcmovF _ _ H1); assumption.
        + exact: EInop.
        + apply: EInot; assumption.
        + apply: EIadd; assumption.
        + apply: EIadds; assumption.
        + apply: EIadc; assumption.
        + apply: EIadcs; assumption.
        + apply: EIsub; assumption.
        + apply: EIsubc; assumption.
        + apply: EIsubb; assumption.
        + apply: EIsbc; assumption.
        + apply: EIsbcs; assumption.
        + apply: EIsbb; assumption.
        + apply: EIsbbs; assumption.
        + apply: EImul; assumption.
        + apply: EImullU; by dec_atom_typ.
        + apply: EImullS; by dec_atom_typ.
        + apply: EImuljU; by dec_atom_typ.
        + apply: EImuljS; by dec_atom_typ.
        + apply: EIsplitU; by dec_atom_typ.
        + apply: EIsplitS; by dec_atom_typ.
        + apply: EIand; assumption.
        + apply: EIor; assumption.
        + apply: EIxor; assumption.
        + apply: EIcast; by dec_atom_typ.
        + apply: EIvpc; by dec_atom_typ.
        + apply: EIjoin; assumption.
        + apply: (EIcutOK H1). apply/agree_eval_bexp; last exact: H2.
          apply: MA.agree_sym. apply: (MA.subset_set_agree _ H0) => {H0 H1 H2}.
          case: b => [e r] /=. rewrite /vars_bexp /=. exact: VSLemmas.union_subset_1.
        + apply: (EIassertOK H1). apply/agree_eval_bexp; last exact: H2.
          apply: MA.agree_sym. apply: (MA.subset_set_agree _ H0) => {H0 H1 H2}.
          case: b => [e r] /=. rewrite /vars_bexp /=. exact: VSLemmas.union_subset_1.
        + apply: (EIassume H1). apply/agree_eval_bexp; last exact: H2.
          apply: MA.agree_sym. apply: (MA.subset_set_agree _ H0) => {H0 H1 H2}.
          case: b => [e r] /=. rewrite /vars_bexp /=. exact: VSLemmas.union_subset_1.
      - move=> s Hev Hag. move: (eval_instr_ok_err Hev) => [e [Hi Hee]].
        case: Hi => Hi; subst.
        + apply: EIcutERR. move=> H; apply: Hee.
          apply/(agree_eval_bexp _ (MA.subset_set_agree (vars_ebexp_subset _) Hag)).
          exact: H.
        + apply: EIassertERR. move=> H; apply: Hee.
          apply/(agree_eval_bexp _ (MA.subset_set_agree (vars_ebexp_subset _) Hag)).
          exact: H.
      - move=> s. by inversion_clear 1.
      - move=> *; exact: Eerr.
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
    Proof. case: e => //=. move=> x Hag. exact: (MA.agree_vsize_singleton Hag). Qed.

    Lemma agree_well_typed_rexp E1 E2 e :
      MA.agree (vars_rexp e) E1 E2 -> well_typed_rexp E1 e = well_typed_rexp E2 e.
    Proof.
      elim: e => //=.
      - move=> x Hag. rewrite (MA.agree_vsize_singleton Hag). reflexivity.
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
      rewrite /atyp /asize /=. rewrite (MA.agree_vtyp_singleton Hag). reflexivity.
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
      MA.agree (rvs_instr i) E1 E2 -> well_formed_instr E1 i = well_formed_instr E2 i.
    Proof.
      case: i => //=; rewrite /well_formed_instr /=; intros; MA.simpl_agree;
                   by (agree_rewrite_well_formed; reflexivity).
    Qed.

    Lemma agree_well_formed_program E1 E2 p :
      MA.agree (inputs_program p) E1 E2 -> well_formed_program E1 p = well_formed_program E2 p.
    Proof.
      rewrite /inputs_program. move: (MA.agree_empty_set E1 E2).
      move: VS.empty. elim: p E1 E2 => [| i p IH] E1 E2 defined //= Hagd Hag.
      move/MA.agree_union_set: Hag => [Hag1 Hag2].
      (* *)
      move: (MA.agree_union_sets Hag1 Hagd) => {Hag1} H.
      move: (MA.subset_set_agree (VSLemmas.subset_union_diff3 _ _) H) => {H} Hagi.
      rewrite (agree_well_formed_instr Hagi).
      (* *)
      move: (agree_rvs_instr_succ_typenv Hagd Hagi) => {Hagd} Hagd_succ.
      move: (agree_lvs_instr_succ_typenv Hagi) => Haglvs_succ.
      move: (MA.agree_union_sets Haglvs_succ Hagd_succ) => {Hagd_succ Haglvs_succ} Haglvsd_succ.
      (* *)
      rewrite (IH (instr_succ_typenv i E1) (instr_succ_typenv i E2) (VS.union (lvs_instr i) defined)
                  Haglvsd_succ (agree_rvs_instr_succ_typenv Hag2 Hagi)).
      reflexivity.
    Qed.

    (* A less precise version *)
    Lemma agree_vars_well_formed_instr E1 E2 i :
      MA.agree (vars_instr i) E1 E2 -> well_formed_instr E1 i = well_formed_instr E2 i.
    Proof.
      case: i => //=; rewrite /well_formed_instr /=; intros; MA.simpl_agree;
                   by (agree_rewrite_well_formed; reflexivity).
    Qed.

    (* A less precise version *)
    Lemma agree_vars_well_formed_program' E1 E2 p :
      MA.agree (vars_program p) E1 E2 -> well_formed_program E1 p = well_formed_program E2 p.
    Proof.
      elim: p E1 E2 => [| i p IH] E1 E2 //=. move/MA.agree_union_set => [Hagi Hagp].
      rewrite (agree_well_formed_instr (MA.subset_set_agree (rvs_instr_subset i) Hagi)).
      rewrite (IH (instr_succ_typenv i E1)  (instr_succ_typenv i E2)); first reflexivity.
      exact: (agree_instr_succ_typenv Hagp Hagi).
    Qed.

    Lemma agree_instr_succ_typenv_l E1 E2 vs i :
      VSLemmas.disjoint vs (lvs_instr i) ->
      MA.agree vs E1 E2 ->
      MA.agree vs (instr_succ_typenv i E1) E2.
    Proof.
      (case: i => //=); intros;
      by repeat match goal with
                | H : ?e |- ?e => assumption
                | |- MA.agree _ ?E ?E => reflexivity
                | H : is_true (VSLemmas.disjoint _ (VS.singleton _)) |- _ =>
                    rewrite VSLemmas.disjoint_singleton_r in H
                | H : is_true (VSLemmas.disjoint _ (VS.add _ _)) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    rewrite VSLemmas.disjoint_add_r in H;
                    move/andP: H => [H1 H2]
                | |- MA.agree _ (TE.add _ _ _) _ =>
                    apply: MA.not_mem_add_map_l
                end.
    Qed.

    Lemma agree_instr_succ_typenv_l1 E vs i :
      VSLemmas.disjoint vs (lvs_instr i) ->
      MA.agree vs (instr_succ_typenv i E) E.
    Proof.
      move=> Hdisj. exact: (agree_instr_succ_typenv_l Hdisj (MA.agree_refl _)).
    Qed.

    Lemma agree_instr_succ_typenv_r E1 E2 vs i :
      VSLemmas.disjoint vs (lvs_instr i) ->
      MA.agree vs E1 E2 ->
      MA.agree vs E1 (instr_succ_typenv i E2).
    Proof.
      move=> Hdisj /MA.agree_sym Hag. apply: MA.agree_sym.
      exact: agree_instr_succ_typenv_l.
    Qed.

    Lemma agree_instr_succ_typenv_r1 E vs i :
      VSLemmas.disjoint vs (lvs_instr i) ->
      MA.agree vs E (instr_succ_typenv i E).
    Proof.
      move=> H. apply: MA.agree_sym. exact: agree_instr_succ_typenv_l1.
    Qed.

    Lemma agree_program_succ_typenv_l E1 E2 vs p :
      VSLemmas.disjoint vs (lvs_program p) ->
      MA.agree vs E1 E2 ->
      MA.agree vs (program_succ_typenv p E1) E2.
    Proof.
      elim: p E1 E2 => [| i p IH] E1 E2 //=.
      rewrite VSLemmas.disjoint_union_r. move/andP=> [Hi Hp] Hag.
      apply: (MA.agree_trans _ (agree_instr_succ_typenv_l Hi Hag)).
      exact: (IH _ _ Hp (MA.agree_refl _)).
    Qed.

    Lemma agree_program_succ_typenv_l1 E vs p :
      VSLemmas.disjoint vs (lvs_program p) ->
      MA.agree vs (program_succ_typenv p E) E.
    Proof.
      elim: p E => [| i p IH] E //=.
      rewrite VSLemmas.disjoint_union_r. move/andP=> [Hi Hp].
      apply: (MA.agree_trans _ (agree_instr_succ_typenv_l1 _ Hi)).
      exact: (IH _ Hp).
    Qed.

    Lemma agree_program_succ_typenv_r E1 E2 vs p :
      VSLemmas.disjoint vs (lvs_program p) ->
      MA.agree vs E1 E2 ->
      MA.agree vs E1 (program_succ_typenv p E2).
    Proof.
      move=> Hdisj /MA.agree_sym Hag. apply: MA.agree_sym.
      exact: agree_program_succ_typenv_l.
    Qed.

    Lemma agree_program_succ_typenv_r1 E vs p :
      VSLemmas.disjoint vs (lvs_program p) ->
      MA.agree vs E (program_succ_typenv p E).
    Proof.
      move=> H. apply: MA.agree_sym. exact: agree_program_succ_typenv_l1.
    Qed.

  End Agree.


  (** Split a specification at cuts *)

  Section SplitCuts.

    (* compositional reasoning *)

    Lemma compose_spec_valid E f p1 m p2 g :
      well_formed_program E p1 ->
      valid_spec {| sinputs := E; spre := f; sprog := p1; spost := m |} ->
      valid_spec {| sinputs := program_succ_typenv p1 E; spre := m; sprog := p2; spost := g |} ->
      valid_spec {| sinputs := E; spre := f; sprog := p1 ++ Icut m :: p2; spost := g |}.
    Proof.
      rewrite /valid_spec /=. rewrite /valid_spec_ok /valid_spec_err /=.
      move=> Hwfp1 [H1ok H1err] [H2ok H2err]. split.
      - move=> s1 s2 Hco Hevf Hev.
        move: (eval_program_cat_ok Hev) => {Hev} [t1 [Hevp1 Hevcp2]].
        move: (eval_program_cons_ok Hevcp2) => {Hevcp2} [t2 [Hevc Hevp2]].
        inversion_clear Hevc. simpl in Hevp2. move: H H0 => Heq Hevm.
        rewrite <- (Equal_state_equal Heq) in Hevp2.
        rewrite program_succ_typenv_cat /=.
        exact: (H2ok _ _ (conform_program_succ_typenv Hwfp1 Hco Hevp1) Hevm Hevp2).
      - move=> s Hco Hevf Hev. case: (eval_program_cat_ok_err Hev) => {Hev} /=.
        + move=> [t1 [Hevp1 Hevcp2]]. case: (eval_program_cons_ok_err Hevcp2) => {Hevcp2} /=.
          * move=> [t2 [Hevc Hevp2]]. inversion_clear Hevc. move: H H0 => Heq Hevm.
            rewrite <- (Equal_state_equal Heq) in Hevp2.
            exact: (H2err _ (conform_program_succ_typenv Hwfp1 Hco Hevp1) Hevm Hevp2).
          * inversion 1; subst. apply: H1. exact: (H1ok _ _ Hco Hevf Hevp1).
        + exact: (H1err _ Hco Hevf).
    Qed.

    Lemma compose_spec_assert_valid E f p1 m p2 g :
      valid_spec {| sinputs := E; spre := f; sprog := p1; spost := m |} ->
      valid_spec {| sinputs := E; spre := f; sprog := p1 ++ p2; spost := g |} ->
      valid_spec {| sinputs := E; spre := f; sprog := p1 ++ Iassert m :: p2; spost := g |}.
    Proof.
      rewrite /valid_spec /=. rewrite /valid_spec_ok /valid_spec_err /=.
      move=> [H1ok H1err] [H2ok H2err]. split.
      - move=> s1 s2 Hco Hevf Hev.
        move: (eval_program_cat_ok Hev) => {Hev} [t1 [Hevp1 Hevcp2]].
        move: (eval_program_cons_ok Hevcp2) => {Hevcp2} [t2 [Hevc Hevp2]].
        simpl in *. inversion_clear Hevc. move: H H0 => Heq Hevm.
        rewrite -(Equal_state_equal Heq) in Hevp2.
        rewrite program_succ_typenv_cat /=.
        rewrite -program_succ_typenv_cat. apply: (H2ok _ _ Hco Hevf).
        exact: (eval_program_cat Hevp1 Hevp2).
      - move=> s Hco Hevf Hev. case: (eval_program_cat_ok_err Hev) => {Hev} /=.
        + move=> [t1 [Hevp1 Hevcp2]]. case: (eval_program_cons_ok_err Hevcp2) => {Hevcp2} /=.
          * move=> [t2 [Hevc Hevp2]]. inversion_clear Hevc. move: H H0 => Heq Hevm.
            rewrite -(Equal_state_equal Heq) in Hevp2. apply: (H2err _ Hco Hevf).
            exact: (eval_program_cat Hevp1 Hevp2).
          * inversion 1; subst. apply: H1. exact: (H1ok _ _ Hco Hevf Hevp1).
        + exact: (H1err _ Hco Hevf).
    Qed.


    (* a procedure that splits a specification at cuts *)

    Fixpoint cut_spec_rec visited_rev E f p g : seq spec :=
      match p with
      | [::] => [:: {| sinputs := E; spre := f; sprog := rev visited_rev; spost := g |}]
      | i::p => match i with
                | Icut e =>
                    let visited := rev visited_rev in
                    {| sinputs := E; spre := f; sprog := visited; spost := e |}
                      :: cut_spec_rec [::] (program_succ_typenv visited E) e p g
                | _ => cut_spec_rec (i::visited_rev) E f p g
                end
      end.

    Definition cut_spec (s : spec) : seq spec :=
      cut_spec_rec [::] (sinputs s) (spre s) (sprog s) (spost s).

    Definition compose_spec (s1 s2 : spec) : spec :=
      {| sinputs := sinputs s1;
         spre := spre s1;
         sprog := sprog s1 ++ Icut (spost s1) :: sprog s2;
         spost := spost s2 |}.

    Definition program_has_no_cut (p : program) : bool :=
      ~~ has is_cut p.

    Definition spec_has_no_cut (s : spec) : bool :=
      program_has_no_cut (sprog s).


    Lemma program_has_no_cut_cons i p :
      program_has_no_cut (i::p) = (~~ is_cut i) && (program_has_no_cut p).
    Proof. rewrite /program_has_no_cut /=. rewrite negb_or. reflexivity. Qed.

    Lemma program_has_no_cut_rcons p i :
      program_has_no_cut (rcons p i) = (program_has_no_cut p) && (~~ is_cut i).
    Proof.
      elim: p => [| j p IH] //=.
      - rewrite /program_has_no_cut /=. rewrite orbF. reflexivity.
      - rewrite !program_has_no_cut_cons IH. rewrite andbA. reflexivity.
    Qed.

    Lemma program_has_no_cut_cat p1 p2 :
      program_has_no_cut (p1 ++ p2) = (program_has_no_cut p1) && (program_has_no_cut p2).
    Proof.
      elim: p1 => [| i1 p1 IH1] //=. rewrite !program_has_no_cut_cons IH1.
      rewrite andbA. reflexivity.
    Qed.

    Lemma cut_spec_has_no_cut s :
      all spec_has_no_cut (cut_spec s).
    Proof.
      rewrite /spec_has_no_cut /program_has_no_cut /cut_spec.
      case: s => E f p g /=.
      have: (~~ has is_cut [::]) by done.
      move: [::]. elim: p E f g => [| i p IH] E f g //=.
      - move=> visited_rev Hncv. rewrite andbT. by rewrite has_rev.
      - move=> visited_rev Hncv. case: i => //=; try (intros; apply: IH; simpl; assumption).
        move=> e. rewrite has_rev Hncv /=. exact: IH.
    Qed.

    Lemma cut_spec_has_no_cut_in s c :
      In c (cut_spec s) ->
      spec_has_no_cut c.
    Proof.
      move=> Hin. move/all_forall: (cut_spec_has_no_cut s).
      apply; assumption.
    Qed.

    Lemma cut_spec_rec_hd_pre visited_rev E f p g s ss :
      cut_spec_rec visited_rev E f p g = [:: s & ss] ->
      spre s = f.
    Proof.
      elim: p visited_rev E f g s ss => [| i p IH] visited_rev E f g s ss /=.
      - case => <- _ /=. reflexivity.
      - case: i; try by (intros; apply: (IH _ _ _ _ _ _ H)).
        move=> e [] <- _. reflexivity.
    Qed.

    Lemma cut_spec_rec_hd_typenv visited_rev E f p g s ss :
      cut_spec_rec visited_rev E f p g = [:: s & ss] ->
      sinputs s = E.
    Proof.
      elim: p visited_rev E f g s ss => [| i p IH] visited_rev E f g s ss /=.
      - case => <- _ /=. reflexivity.
      - case: i; try by (intros; apply: (IH _ _ _ _ _ _ H)).
        move=> e [] <- _. reflexivity.
    Qed.

    Lemma cut_spec_rec_pre_post visited_rev E f p g s1 s2 ss :
      cut_spec_rec visited_rev E f p g = [:: s1, s2 & ss] -> spre s2 = spost s1.
    Proof.
      elim: p visited_rev E f g s1 s2 ss => [| i p IH] visited_rev E f g s1 s2 ss //=.
      case: i; try by (intros; apply: IH; exact: H).
      move=> e. case => <- Hss /=. exact: (cut_spec_rec_hd_pre Hss).
    Qed.

    Lemma cut_spec_rec_typenv visited_rev E f p g s1 s2 ss :
      cut_spec_rec visited_rev E f p g = [:: s1, s2 & ss] -> sinputs s2 = program_succ_typenv (sprog s1) E.
    Proof.
      elim: p visited_rev E f g s1 s2 ss => [| i p IH] visited_rev E f g s1 s2 ss //=.
      case: i; try by (intros; apply: IH; exact: H).
      move=> e. case => <- Hss /=. exact: (cut_spec_rec_hd_typenv Hss).
    Qed.

    Lemma cut_spec_sound s :
      well_formed_program (sinputs s) (sprog s) ->
      Forall valid_spec (cut_spec s) -> valid_spec s.
    Proof.
      rewrite /cut_spec. case: s => E f p g /=. rewrite -{1 3}(cat0s p).
      have {2}->: [::] = rev [::] by reflexivity.
      move: [::]. elim: p E f g => [| i p IH] E f g visited //=.
      - rewrite revK cats0. move=> Hwf. inversion_clear 1. assumption.
      - (case: i => //=);
        try by (intros; rewrite -cat_rcons; apply: IH;
                [ rewrite cat_rcons; assumption
                | rewrite rev_rcons; assumption ]).
        move=> e Hwf Hall. inversion_clear Hall. move: H H0 => Hv Hall.
        apply: compose_spec_valid.
        + exact: (well_formed_program_cat1 Hwf).
        + rewrite revK in Hv. assumption.
        + rewrite -(cat0s p). apply: IH.
          * exact: (well_formed_program_cons2 (well_formed_program_cat2 Hwf)).
          * rewrite revK in Hall; assumption.
    Qed.

    Lemma cut_spec_well_formed s :
      well_formed_spec s -> all well_formed_spec (cut_spec s).
    Proof.
      rewrite /cut_spec /well_formed_spec. case: s => E f p g /=.
      rewrite -{1 2}(cat0s p). have {3}->: [::] = rev [::] by reflexivity.
      move: [::]. elim: p E f g => [| i p IH] E f g visited //=.
      - rewrite cats0. move=> /andP [/andP [Hwff Hwfp] Hwfg].
        by rewrite revK Hwff Hwfp Hwfg.
      - move=> /andP [/andP [Hwff Hwfp] Hwfg].
        rewrite -cat_rcons in Hwfp.
        rewrite well_formed_program_cat in Hwfp. move/andP: Hwfp => [Hwfvi Hwfp].
        case: i Hwfvi Hwfp Hwfg;
          try by
          (intros; rewrite -rev_rcons; apply: IH;
           rewrite Hwff; rewrite well_formed_program_cat; rewrite Hwfvi Hwfp; rewrite cat_rcons Hwfg).
        move=> e Hwfvi Hwfp Hwfg. rewrite well_formed_program_rcons /= in Hwfvi.
        move/andP: Hwfvi => [Hwfv Hwfi]. rewrite /well_formed_instr /= in Hwfi.
        simpl. rewrite revK Hwff /=. rewrite Hwfv /=.
        rewrite {1}/well_formed_bexp Hwfi /=.
        have ->: [::] = rev [::] by reflexivity. apply: IH.
        rewrite program_succ_typenv_rcons /= in Hwfp. rewrite cat0s Hwfp andbT.
        rewrite program_succ_typenv_cat /= in Hwfg. rewrite Hwfg andbT.
        exact: Hwfi.
    Qed.

    Lemma cut_spec_well_formed_in s c :
      In c (cut_spec s) ->
      well_formed_spec s -> well_formed_spec c.
    Proof.
      move=> Hin Hwf. move: (cut_spec_well_formed Hwf). move/all_forall.
      apply. assumption.
    Qed.

  End SplitCuts.


  (* Construct specifications to verify assertions and the postcondition. *)

  Section CutAsserts.

    Fixpoint cut_asserts_rec visited_rev E f p g : seq spec :=
      match p with
      | [::] => [:: {| sinputs := E; spre := f; sprog := rev visited_rev; spost := g |}]
      | i::p => match i with
                | Iassert e => {| sinputs := E; spre := f; sprog := rev visited_rev; spost := e |}
                                 :: cut_asserts_rec visited_rev E f p g
                | _ => cut_asserts_rec (i::visited_rev) E f p g
                end
      end.

    Definition cut_asserts (s : spec) : seq spec :=
      cut_asserts_rec [::] (sinputs s) (spre s) (sprog s) (spost s).

    Definition program_has_no_assert (p : program) : bool :=
      ~~ has is_assert p.

    Definition spec_has_no_assert (s : spec) : bool :=
      program_has_no_assert (sprog s).


    Lemma program_has_no_assert_singleton i :
      program_has_no_assert [:: i] = (~~ is_assert i).
    Proof. rewrite/program_has_no_assert /=. rewrite orbF. reflexivity. Qed.

    Lemma program_has_no_assert_cons i p :
      program_has_no_assert (i::p) = (~~ is_assert i) && (program_has_no_assert p).
    Proof.
      rewrite /program_has_no_assert /=. rewrite negb_or. reflexivity.
    Qed.

    Lemma program_has_no_assert_rcons p i :
      program_has_no_assert (rcons p i) = (program_has_no_assert p) && (~~ is_assert i).
    Proof.
      elim: p => [| j p IH] //=.
      - exact: program_has_no_assert_singleton.
      - rewrite !program_has_no_assert_cons IH. rewrite andbA. reflexivity.
    Qed.

    Lemma program_has_no_assert_cat p1 p2 :
      program_has_no_assert (p1 ++ p2) = (program_has_no_assert p1) && (program_has_no_assert p2).
    Proof.
      elim: p1 p2 => [| i1 p1 IH1] p2 //=.
      rewrite !program_has_no_assert_cons IH1. rewrite andbA. reflexivity.
    Qed.

    Lemma cut_asserts_has_no_assert s :
      all spec_has_no_assert (cut_asserts s).
    Proof.
      rewrite /spec_has_no_assert /program_has_no_assert /cut_asserts. case: s => E f p g /=.
      have: (~~ has is_assert [::]) by done.
      move: [::]. elim: p E f g => [| i p IH] E f g //=.
      - move=> visited_rev Hncv. rewrite andbT. by rewrite has_rev.
      - move=> visited_rev Hncv. case: i => //=; try (intros; apply: IH; simpl; assumption).
        move=> e. rewrite has_rev Hncv /=. exact: IH.
    Qed.

    Lemma cut_asserts_rec_hd_pre visited_rev E f p g s ss :
      cut_asserts_rec visited_rev E f p g = [:: s & ss] ->
      spre s = f.
    Proof.
      elim: p visited_rev E f g s ss => [| i p IH] visited_rev E f g s ss /=.
      - case => <- _ /=. reflexivity.
      - case: i; try by (intros; apply: (IH _ _ _ _ _ _ H)).
        move=> e [] <- _. reflexivity.
    Qed.

    Lemma cut_asserts_rec_hd_typenv visited_rev E f p g s ss :
      cut_asserts_rec visited_rev E f p g = [:: s & ss] ->
      sinputs s = E.
    Proof.
      elim: p visited_rev E f g s ss => [| i p IH] visited_rev E f g s ss /=.
      - case => <- _ /=. reflexivity.
      - case: i; try by (intros; apply: (IH _ _ _ _ _ _ H)).
        move=> e [] <- _. reflexivity.
    Qed.

    Lemma cut_asserts_sound s :
      Forall valid_spec (cut_asserts s) -> valid_spec s.
    Proof.
      rewrite /cut_asserts. case: s => E f p g /=. rewrite -{2}(cat0s p).
      have {1}->: [::] = rev [::] by reflexivity.
      move: [::]. elim: p E f g => [| i p IH] E f g visited //=.
      - rewrite revK cats0. inversion_clear 1. assumption.
      - (case: i => //=);
        try by (intros; rewrite -cat_rcons; apply: IH;
                rewrite rev_rcons; assumption).
        move=> e Hall. inversion_clear Hall. move: H H0 => Hv Hall.
        rewrite revK in Hv. apply: (compose_spec_assert_valid Hv).
        exact: (IH _ _ _ _ Hall).
    Qed.

    Lemma cut_asserts_well_formed s :
      well_formed_spec s -> Forall well_formed_spec (cut_asserts s).
    Proof.
      rewrite /cut_asserts /well_formed_spec. case: s => E f p g /=.
      rewrite -{1 2}(cat0s p). have {3}->: [::] = rev [::] by reflexivity.
      move: [::]. elim: p E f g => [| i p IH] E f g visited //=.
      - rewrite cats0. move=> /andP [/andP [Hwff Hwfp] Hwfg]. apply: Forall_cons => //=.
        by rewrite revK Hwff Hwfp Hwfg.
      - move=> /andP [/andP [Hwff Hwfp] Hwfg]. rewrite -cat_rcons in Hwfp.
        rewrite well_formed_program_cat in Hwfp. move/andP: Hwfp => [Hwfvi Hwfp].
        case: i Hwfvi Hwfp Hwfg;
          try by
          (intros; rewrite -rev_rcons; apply: IH;
           rewrite Hwff; rewrite well_formed_program_cat; rewrite Hwfvi Hwfp; rewrite cat_rcons Hwfg).
        move=> e Hwfvi Hwfp Hwfg. rewrite well_formed_program_rcons /= in Hwfvi.
        move/andP: Hwfvi => [Hwfv Hwfi]. rewrite /well_formed_instr /= in Hwfi.
        apply: Forall_cons.
        + simpl. rewrite revK Hwff /=. rewrite Hwfv /=. exact: Hwfi.
        + apply: IH. rewrite program_succ_typenv_rcons /= in Hwfp.
          rewrite program_succ_typenv_cat /= -program_succ_typenv_cat in Hwfg.
          rewrite well_formed_program_cat. by rewrite Hwff Hwfv Hwfp Hwfg.
    Qed.

  End CutAsserts.


  (* Construct specifications to verify assertions. *)

  Section ExtractAsserts.

    Fixpoint extract_asserts_rec visited_rev E f p : seq spec :=
      match p with
      | [::] => [::]
      | i::p => match i with
                | Iassert e => {| sinputs := E; spre := f; sprog := rev visited_rev; spost := e |}
                                 :: extract_asserts_rec visited_rev E f p
                | _ => extract_asserts_rec (i::visited_rev) E f p
                end
      end.

    Definition extract_asserts (s : spec) : seq spec :=
      extract_asserts_rec [::] (sinputs s) (spre s) (sprog s).

    Definition remove_asserts_program (p : program) : program :=
      filter (fun i => ~~ is_assert i) p.

    Definition remove_asserts (s : spec) : spec :=
      {| sinputs := sinputs s;
         spre := spre s;
         sprog := remove_asserts_program (sprog s);
         spost := spost s |}.


    Lemma extract_asserts_rec_inputs visited_rev E f p a :
      In a (extract_asserts_rec visited_rev E f p) -> sinputs a = E.
    Proof.
      elim: p visited_rev => [| i p IH] visited_rev //=.
      case: i; intros; try exact: (IH _ H).
      case: (in_inv H) => {}H.
      - subst; simpl. reflexivity.
      - exact: (IH _ H).
    Qed.

    Lemma extract_asserts_inputs s a :
      In a (extract_asserts s) -> sinputs a = sinputs s.
    Proof. exact: extract_asserts_rec_inputs. Qed.

    Lemma extract_asserts_rec_pre visited_rev E f p a :
      In a (extract_asserts_rec visited_rev E f p) -> spre a = f.
    Proof.
      elim: p visited_rev => [| i p IH] visited_rev //=.
      case: i; intros; try exact: (IH _ H).
      case: (in_inv H) => {}H.
      - subst; simpl. reflexivity.
      - exact: (IH _ H).
    Qed.

    Lemma extract_asserts_pre s a :
      In a (extract_asserts s) -> spre a = spre s.
    Proof. exact: extract_asserts_rec_pre. Qed.

    Lemma extract_asserts_has_no_assert s :
      all spec_has_no_assert (extract_asserts s).
    Proof.
      rewrite /spec_has_no_assert /program_has_no_assert /extract_asserts.
      case: s => E f p g /=.
      have: (~~ has is_assert [::]) by done.
      move: [::]. elim: p E f => [| i p IH] E f //=.
      move=> visited_rev Hncv. case: i => //=; try (intros; apply: IH; simpl; assumption).
      move=> e. rewrite has_rev Hncv /=. exact: IH.
    Qed.

    Lemma extract_asserts_rec_hd_pre visited_rev E f p s ss :
      extract_asserts_rec visited_rev E f p = [:: s & ss] ->
      spre s = f.
    Proof.
      elim: p visited_rev E f s ss => [| i p IH] visited_rev E f s ss /=.
      - discriminate.
      - case: i; try by (intros; apply: (IH _ _ _ _ _ H)).
        move=> e [] <- _. reflexivity.
    Qed.

    Lemma extract_asserts_rec_hd_typenv visited_rev E f p s ss :
      extract_asserts_rec visited_rev E f p = [:: s & ss] ->
      sinputs s = E.
    Proof.
      elim: p visited_rev E f s ss => [| i p IH] visited_rev E f s ss /=.
      - discriminate.
      - case: i; try by (intros; apply: (IH _ _ _ _ _ H)).
        move=> e [] <- _. reflexivity.
    Qed.

    Lemma remove_asserts_program_cons1 i p :
      is_assert i ->
      remove_asserts_program (i::p) = remove_asserts_program p.
    Proof. by case: i => //=. Qed.

    Lemma remove_asserts_program_cons2 i p :
      ~~ is_assert i ->
      remove_asserts_program (i::p) = i::remove_asserts_program p.
    Proof. by case: i => //=. Qed.

    Lemma remove_asserts_program_rcons1 p i :
      is_assert i ->
      remove_asserts_program (rcons p i) = remove_asserts_program p.
    Proof.
      elim: p => [| j p IH] //=.
      - move=> -> /=. reflexivity.
      - move=> Hi. rewrite (IH Hi). reflexivity.
    Qed.

    Lemma remove_asserts_program_cat p1 p2 :
      remove_asserts_program (p1 ++ p2) = remove_asserts_program p1 ++ remove_asserts_program p2.
    Proof.
      elim: p1 p2 => [| i1 p1 IH1] p2 //=. rewrite IH1.
      by case: (is_assert i1) => //=.
    Qed.

    Lemma remove_asserts_program_has_no_assert p :
      program_has_no_assert (remove_asserts_program p).
    Proof.
      elim: p => [| i p IH] //=. by case: i => //=.
    Qed.

    Lemma remove_asserts_has_no_assert s :
      spec_has_no_assert (remove_asserts s).
    Proof. exact: remove_asserts_program_has_no_assert. Qed.

    Lemma remove_asserts_program_succ_typenv E p :
      program_succ_typenv (remove_asserts_program p) E = program_succ_typenv p E.
    Proof.
      elim: p E => [| i p IH] E //=. by case: i => //=.
    Qed.

    Lemma remove_asserts_succ_typenv s :
      program_succ_typenv (sprog (remove_asserts s)) (sinputs (remove_asserts s)) =
        program_succ_typenv (sprog s) (sinputs s).
    Proof. case: s => E f p g. exact: remove_asserts_program_succ_typenv. Qed.

    Lemma no_asserts_remove_asserts p :
      program_has_no_assert p -> remove_asserts_program p = p.
    Proof.
      rewrite /program_has_no_assert. elim: p => [| i p IH] //=.
      case: (is_assert i) => //=. move=> Hp.
      rewrite (IH Hp). reflexivity.
    Qed.

    Lemma remove_asserts_program_vars_subset p :
      VS.subset (vars_program (remove_asserts_program p)) (vars_program p).
    Proof.
      elim: p => [| i p IH] //=.
      - exact: VSLemmas.subset_refl.
      - case_if; simpl; by VSLemmas.dp_subset.
    Qed.

    Lemma remove_asserts_vars_subset s :
      VS.subset (vars_spec (remove_asserts s)) (vars_spec s).
    Proof.
      rewrite /vars_spec /remove_asserts. case: s => E f p g /=.
      move: (remove_asserts_program_vars_subset p) => H.
      by VSLemmas.dp_subset.
    Qed.

    Lemma extract_asserts_vars_subset s a :
      In a (extract_asserts s) ->
      VS.subset (vars_spec a) (vars_spec s).
    Proof.
      rewrite /extract_asserts /vars_spec. case: s => E f p g /=.
      rewrite -{2}(cat0s p). have {1}->: [::] = rev [::] by reflexivity.
      move: [::]. elim: p a E f g => [| i p IH] a E f g visited //=.
      (case: i => //=); intros;
      try by (rewrite -cat_rcons; apply: IH; rewrite rev_rcons; exact: H).
      (* Iassert *)
      case: H => H.
      - subst; simpl. rewrite revK. rewrite vars_program_cat /=.
        by VSLemmas.dp_subset.
      - move: (IH _ _ _ g _ H). rewrite !vars_program_cat /=.
        move=> Hsub. apply: (VSLemmas.subset_trans Hsub).
        by VSLemmas.dp_subset.
    Qed.


    Lemma extract_asserts_sound s :
      valid_spec (remove_asserts s) ->
      Forall valid_spec (extract_asserts s) ->
      valid_spec s.
    Proof.
      rewrite /remove_asserts /extract_asserts.
      case: s => E f p g /=. rewrite -{1 3}(cat0s p).
      have {2}->: [::] = rev [::] by reflexivity.
      have: ~~ has is_assert [::] by done.
      move: [::]. elim: p E f g => [| i p IH] E f g visited Hnav //=.
      - rewrite cats0. rewrite (no_asserts_remove_asserts Hnav).
        move=> Hs _. assumption.
      - rewrite revK. (case: i => /=); try by
                        (intros;
                         rewrite -cat_rcons in H *; apply: IH;
                         [ rewrite has_rcons /=; assumption
                         | assumption
                         | rewrite rev_rcons; assumption ]).
        move=> e Hvg Hall. inversion_clear Hall. move: H H0 => Hva Hall.
        apply: (compose_spec_assert_valid Hva). apply: (IH _ _ _ _ Hnav _ Hall).
        rewrite remove_asserts_program_cat /= in Hvg.
        rewrite remove_asserts_program_cat. assumption.
    Qed.

    Lemma extract_asserts_well_formed s :
      well_formed_spec s -> Forall well_formed_spec (extract_asserts s).
    Proof.
      rewrite /extract_asserts /well_formed_spec. case: s => E f p g /=.
      move/andP => [H _]; move: H. clear g.
      rewrite -{1}(cat0s p). have {2}->: [::] = rev [::] by reflexivity.
      move: [::]. elim: p E f => [| i p IH] E f visited //=.
      move=> /andP [Hwff Hwfp]. rewrite -cat_rcons in Hwfp.
      rewrite well_formed_program_cat in Hwfp. move/andP: Hwfp => [Hwfvi Hwfp].
      case: i Hwfvi Hwfp; try by
        (intros; rewrite -rev_rcons; apply: IH;
         rewrite Hwff; rewrite well_formed_program_cat; rewrite Hwfvi Hwfp).
      (* Iassert *)
      move=> e Hwfvi Hwfp. rewrite well_formed_program_rcons /= in Hwfvi.
      move/andP: Hwfvi => [Hwfv Hwfi]. rewrite /well_formed_instr /= in Hwfi.
      apply: Forall_cons.
      - simpl. rewrite revK Hwff /=. rewrite Hwfv /=. exact: Hwfi.
      - apply: IH. rewrite program_succ_typenv_rcons /= in Hwfp.
        rewrite well_formed_program_cat. by rewrite Hwff Hwfv Hwfp.
    Qed.

    Lemma extract_asserts_well_formed_in s a :
      In a (extract_asserts s) ->
      well_formed_spec s -> well_formed_spec a.
    Proof.
      move=> Hin Hwf. move: (extract_asserts_well_formed Hwf).
      move/Forall_forall; apply. assumption.
    Qed.

    Lemma remove_asserts_program_well_formed E p :
      well_formed_program E p ->
      well_formed_program E (remove_asserts_program p).
    Proof.
      elim: p E => [| i p IH] E //=.
      case: i; intros; split_andb_hyps; simpl in *;
        by repeat match goal with
                  | H : is_true ?e |- context [?e] => rewrite H /=
                  | H : is_true (well_formed_program ?E ?p) |-
                      context [well_formed_program ?E (remove_asserts_program ?p)] =>
                      rewrite (IH _ H) /=
                  end.
    Qed.

    Lemma remove_asserts_well_formed s :
      well_formed_spec s -> well_formed_spec (remove_asserts s).
    Proof.
      rewrite /well_formed_spec /remove_asserts. case: s => E f p g /=.
      move/andP => [/andP [Hwff Hwfp] Hwfg]. rewrite Hwff /=.
      rewrite (remove_asserts_program_well_formed Hwfp) /=.
      rewrite remove_asserts_program_succ_typenv Hwfg /=. reflexivity.
    Qed.


    (* Preserving of having no cuts *)

    Lemma remove_asserts_program_preserve_no_cut p :
      program_has_no_cut (remove_asserts_program p) = program_has_no_cut p.
    Proof.
      rewrite /program_has_no_cut. elim: p => [| i p IH] //=.
      case_if => /=; rewrite !negb_or; rewrite IH //.
      by case: i H.
    Qed.

    Lemma remove_asserts_preserve_no_cut s :
      spec_has_no_cut (remove_asserts s) = spec_has_no_cut s.
    Proof.
      rewrite /spec_has_no_cut /program_has_no_cut.
      case: s => E f p g /=. exact: remove_asserts_program_preserve_no_cut.
    Qed.

    Lemma extract_asserts_preserve_no_cut s :
      spec_has_no_cut s ->
      all spec_has_no_cut (extract_asserts s).
    Proof.
      rewrite /spec_has_no_cut /program_has_no_cut /extract_asserts.
      case: s => E f p g /=.
      have: ~~ has is_cut [::] by done.
      move: [::]. clear g. elim: p E f => [| i p IH] E f visited_rev Hvi //=.
      case: i => //=; try (intros; rewrite IH; done).
      (* Icut *)
      move=> _ Hp. rewrite has_rev Hvi /=.
      exact: IH.
    Qed.

  End ExtractAsserts.


End MakeDSL.

Module DSL := MakeDSL VarOrder VarOrderPrinter VS VM TE Store.
