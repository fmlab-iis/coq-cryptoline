
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Tactics .
From BitBlasting Require Import State QFBV.
From Cryptoline Require Import DSL SSA SSA2ZSSA.
From nbits Require Import NBits.

(** Conversion from range specifications and safety conditions to QFBV expressions *)

Import SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition qfbv_atomic a :=
  match a with
  | SSA.Avar v => QFBV.Evar v
  | SSA.Aconst ty n => QFBV.Econst n
  end .

Definition qfbv_true := QFBV.Btrue .

Definition qfbv_false := QFBV.Bfalse .

Definition qfbv_var v := QFBV.Evar v .

Definition qfbv_const n := QFBV.Econst (NBitsDef.from_nat n n) .

Definition qfbv_zero w := QFBV.Econst (NBitsDef.from_nat w 0) .

Definition qfbv_one w := QFBV.Econst (NBitsDef.from_nat w 1) .

Definition qfbv_not qe := QFBV.Eunop QFBV.Unot qe .

Definition qfbv_neg qe := QFBV.Eunop QFBV.Uneg qe .

Definition qfbv_extr i j qe := QFBV.Eunop (QFBV.Uextr i j) qe .

Definition qfbv_high n qe := QFBV.Eunop (QFBV.Uhigh n) qe .

Definition qfbv_low n qe := QFBV.Eunop (QFBV.Ulow n) qe .

Definition qfbv_zext n qe := QFBV.Eunop (QFBV.Uzext n) qe .

Definition qfbv_sext n qe := QFBV.Eunop (QFBV.Usext n) qe .

Definition qfbv_and qe0 qe1 := QFBV.Ebinop QFBV.Band qe0 qe1 .

Definition qfbv_or qe0 qe1 := QFBV.Ebinop QFBV.Bor qe0 qe1 .

Definition qfbv_xor qe0 qe1 := QFBV.Ebinop QFBV.Bxor qe0 qe1 .

Definition qfbv_add qe0 qe1 := QFBV.Ebinop QFBV.Badd qe0 qe1 .

Definition qfbv_sub qe0 qe1 := QFBV.Ebinop QFBV.Bsub qe0 qe1 .

Definition qfbv_mul qe0 qe1 := QFBV.Ebinop QFBV.Bmul qe0 qe1 .

Definition qfbv_mod qe0 qe1 := QFBV.Ebinop QFBV.Bmod qe0 qe1 .

Definition qfbv_srem qe0 qe1 := QFBV.Ebinop QFBV.Bsrem qe0 qe1 .

Definition qfbv_smod qe0 qe1 := QFBV.Ebinop QFBV.Bsmod qe0 qe1 .

Definition qfbv_shl qe0 qe1 := QFBV.Ebinop QFBV.Bshl qe0 qe1 .

Definition qfbv_lshr qe0 qe1 := QFBV.Ebinop QFBV.Blshr qe0 qe1 .

Definition qfbv_ashr qe0 qe1 := QFBV.Ebinop QFBV.Bashr qe0 qe1 .

Definition qfbv_concat qe0 qe1 := QFBV.Ebinop QFBV.Bconcat qe0 qe1 .

Definition qfbv_eq qe0 qe1 := QFBV.Bbinop QFBV.Beq qe0 qe1 .

Definition qfbv_ult qe0 qe1 := QFBV.Bbinop QFBV.Bult qe0 qe1 .

Definition qfbv_ule qe0 qe1 := QFBV.Bbinop QFBV.Bule qe0 qe1 .

Definition qfbv_ugt qe0 qe1 := QFBV.Bbinop QFBV.Bugt qe0 qe1 .

Definition qfbv_uge qe0 qe1 := QFBV.Bbinop QFBV.Buge qe0 qe1 .

Definition qfbv_slt qe0 qe1 := QFBV.Bbinop QFBV.Bslt qe0 qe1 .

Definition qfbv_sle qe0 qe1 := QFBV.Bbinop QFBV.Bsle qe0 qe1 .

Definition qfbv_sgt qe0 qe1 := QFBV.Bbinop QFBV.Bsgt qe0 qe1 .

Definition qfbv_sge qe0 qe1 := QFBV.Bbinop QFBV.Bsge qe0 qe1 .

Definition qfbv_uaddo qe0 qe1 := QFBV.Bbinop QFBV.Buaddo qe0 qe1 .

Definition qfbv_usubo qe0 qe1 := QFBV.Bbinop QFBV.Busubo qe0 qe1 .

Definition qfbv_umulo qe0 qe1 := QFBV.Bbinop QFBV.Bumulo qe0 qe1 .

Definition qfbv_saddo qe0 qe1 := QFBV.Bbinop QFBV.Bsaddo qe0 qe1 .

Definition qfbv_ssubo qe0 qe1 := QFBV.Bbinop QFBV.Bssubo qe0 qe1 .

Definition qfbv_smulo qe0 qe1 := QFBV.Bbinop QFBV.Bsmulo qe0 qe1 .

Definition qfbv_lneg qb := QFBV.Blneg qb .

Definition qfbv_conj qb0 qb1 := QFBV.Bconj qb0 qb1 .

Definition qfbv_disj qb0 qb1 := QFBV.Bdisj qb0 qb1 .

Fixpoint exp_rexp (e : SSA.rexp) : QFBV.exp :=
  match e with
  | Rvar v => qfbv_var v
  | Rconst _ n => QFBV.Econst n
  | Runop w op e =>
    match op with
    | Rnegb => qfbv_neg (exp_rexp e)
    | Rnotb => qfbv_not (exp_rexp e)
    end
  | Rbinop _ op e1 e2 =>
    match op with
    | Radd => qfbv_add (exp_rexp e1) (exp_rexp e2)
    | Rsub => qfbv_sub (exp_rexp e1) (exp_rexp e2)
    | Rmul => qfbv_mul (exp_rexp e1) (exp_rexp e2)
    | Rumod => qfbv_mod (exp_rexp e1) (exp_rexp e2)
    | Rsrem => qfbv_srem (exp_rexp e1) (exp_rexp e2)
    | Rsmod => qfbv_smod (exp_rexp e1) (exp_rexp e2)
    | Randb => qfbv_and (exp_rexp e1) (exp_rexp e2)
    | Rorb => qfbv_or (exp_rexp e1) (exp_rexp e2)
    | Rxorb => qfbv_xor (exp_rexp e1) (exp_rexp e2)
    end
  | Ruext _ e n => qfbv_zext n (exp_rexp e)
  | Rsext _ e n => qfbv_sext n (exp_rexp e)
  end .

Fixpoint bexp_rbexp (e : SSA.rbexp) : QFBV.bexp :=
  match e with
  | Rtrue => QFBV.Btrue
  | Req _ e1 e2 =>
    qfbv_eq (exp_rexp e1) (exp_rexp e2)
  | Rcmp _ op e1 e2 =>
    match op with
    | Rult => qfbv_ult (exp_rexp e1) (exp_rexp e2)
    | Rule => qfbv_ule (exp_rexp e1) (exp_rexp e2)
    | Rugt => qfbv_ugt (exp_rexp e1) (exp_rexp e2)
    | Ruge => qfbv_uge (exp_rexp e1) (exp_rexp e2)
    | Rslt => qfbv_slt (exp_rexp e1) (exp_rexp e2)
    | Rsle => qfbv_sle (exp_rexp e1) (exp_rexp e2)
    | Rsgt => qfbv_sgt (exp_rexp e1) (exp_rexp e2)
    | Rsge => qfbv_sge (exp_rexp e1) (exp_rexp e2)
    end 
  | Rneg e => qfbv_lneg (bexp_rbexp e)
  | Rand e1 e2 =>
    qfbv_conj (bexp_rbexp e1) (bexp_rbexp e2)
  | Ror e1 e2 =>
    qfbv_disj (bexp_rbexp e1) (bexp_rbexp e2)
  end .

(* properties of conversion *)

Lemma eval_exp_var v s :
  QFBV.eval_exp (qfbv_var v) s = SSAStore.acc v s.
Proof.
  reflexivity.
Qed.

Lemma eval_exp_atomic a s :
  QFBV.eval_exp (qfbv_atomic a) s = eval_atomic a s.
Proof.
  case: a => /=; reflexivity.
Qed.

Lemma eval_exp_rexp (e : SSA.rexp) s:
  QFBV.eval_exp (exp_rexp e) s = eval_rexp e s.
Admitted .
(* TODO: wait for the mod, smod, srem
Proof .
  elim: e => /=.
  - reflexivity.
  - reflexivity.
  - move=> w op e IH;
             case : op; rewrite /= IH; reflexivity .
  - move=> w op e0 IH0 e1 IH1 .
    case : op; rewrite /=; rewrite IH0 IH1 // .
  - move => w e IH n; rewrite /= IH // .
  - move => w e IH n; rewrite /= IH // .
    
Qed.
 *)

Lemma eval_bexp_rbexp e s:
  QFBV.eval_bexp (bexp_rbexp e) s <-> eval_rbexp e s .
Proof .
  elim : e => /= .
  - done .
  - move => w e0 e1; split .
    + move => /eqP Heq; rewrite -!eval_exp_rexp Heq // .
    + move => Heq; rewrite !eval_exp_rexp Heq // .
  - move => w op e0 e1;
      elim : op => /=; rewrite -!eval_exp_rexp // .
  - move => e; elim => Hleft Hright; split .
    + move => /negP Hneg .
      red; move => Heval .
      move : (Hright Heval); done .
    + move => Heval .
      apply /negP; red; move => Hneg .
      move : (Hleft Hneg); done .
  - move => e0 IH0 e1 IH1; split .
    + move => /andP [Heval0 Heval1] .
      tauto .
    + move => [Heval0 Heval1] .
      elim IH0 => {IH0} _ IH0; elim IH1 => {IH1} _ IH1 .
      rewrite (IH0 Heval0) (IH1 Heval1) // .
  - move => e0 IH0 e1 IH1; split .
    + move => /orP Hor .
      tauto .
    + move => Hor .
      elim IH0 => {IH0} _ IH0; elim IH1 => {IH1} _ IH1 .
      elim Hor; move => He; apply /orP; tauto .
Qed .

Lemma eval_bexp_rbexp1 e s:
  QFBV.eval_bexp (bexp_rbexp e) s -> eval_rbexp e s.
Proof.
  move: (eval_bexp_rbexp e s) => [H1 H2]. exact: H1.
Qed.

Lemma eval_bexp_rbexp2 e s:
  eval_rbexp e s -> QFBV.eval_bexp (bexp_rbexp e) s.
Proof.
  move: (eval_bexp_rbexp e s) => [H1 H2]. exact: H2.
Qed.

Definition bexp_instr (te : TypEnv.SSATE.env) (i : SSA.instr) : QFBV.bexp :=
  match i with
  (* Inondet (v, t): v = a nondeterministic value of type t *)
  | SSA.Inondet _ _
  (* Inop: do nothing *)
  | SSA.Inop => QFBV.Btrue
  (* Imov (v, a): v = a *)
  | SSA.Imov v a =>
    qfbv_eq (qfbv_var v) (qfbv_atomic a)
  (* Icmov (v, c, a1, a2): if c then v = a1 else v = a2 *)
  | SSA.Icmov v c a1 a2 =>
    let 'qec := qfbv_eq (qfbv_const 1) (qfbv_atomic c) in
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    qfbv_eq (qfbv_var v) (QFBV.Eite qec qe1 qe2)
  (* Iadd (v, a1, a2): v = a1 + a2, overflow is forbidden *)
  | SSA.Iadd v a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    qfbv_eq (qfbv_var v) (qfbv_add qe1 qe2)
  (* Iadds (c, v, a1, a2): v = a1 + a2, c = carry flag *)
  | SSA.Iadds c v a1 a2 =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext 1 (qfbv_atomic a2) in
    let 'qerext := qfbv_add qe1ext qe2ext in
    qfbv_conj
      (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
      (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
  (* Iadc (v, a1, a2, y): v = a1 + a2 + y, overflow is forbidden *)
  | SSA.Iadc v a1 a2 y =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    qfbv_eq (qfbv_var v)
            (qfbv_low a_size (qfbv_add (qfbv_add qeyext qe1ext) qe2ext))
  (* Iadcs (c, v, a1, a2, y): v = a1 + a2 + y, c = carry flag *)
  | SSA.Iadcs c v a1 a2 y =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    let 'qerext := qfbv_add (qfbv_add qeyext qe1ext) qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
  (* Isub (v, a1, a2): v = a1 - a2, overflow is forbidden *)
  | SSA.Isub v a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    qfbv_eq (qfbv_var v) (qfbv_sub qe1 qe2)
  (* Isubb (b, v, a1, a2): v = a1 - a2, b = borrow flag *)
  | SSA.Isubb b v a1 a2 =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext 1 (qfbv_atomic a2) in
    let 'qerext := qfbv_sub qe1ext qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v)
                       (qfbv_low a_size qerext))
  (* Isubc (c, v, a1, a2): v = a1 + not(a2) + 1, c = carry flag *)
  | SSA.Isubc c v a1 a2 =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2negext := qfbv_sext 1 (qfbv_neg (qfbv_atomic a2)) in
    let 'qerext := qfbv_add qe1ext qe2negext in
    qfbv_conj (qfbv_eq (qfbv_var c)
                       (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v)
                       (qfbv_low a_size qerext))
  (* Isbb (v, a1, a2, y): v = a1 - a2 - y *)
  | SSA.Isbb v a1 a2 y =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    qfbv_eq (qfbv_var v)
            (qfbv_low a_size (qfbv_sub (qfbv_sub qe1ext qe2ext) qeyext))
  (* Isbbs (b, v, a1, a2, y): v = a1 - a2 - y, b = borrow flag *)
  | SSA.Isbbs b v a1 a2 y =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    let 'qerext := qfbv_sub (qfbv_sub qe1ext qe2ext) qeyext in
    qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
  (* Isbc (v, a1, a2, y): v = a1 + not(a2) + y *)
  | SSA.Isbc v a1 a2 y =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2notext := qfbv_sext 1 (qfbv_not (qfbv_atomic a2)) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    qfbv_eq (qfbv_var v)
            (qfbv_low a_size (qfbv_add (qfbv_add qeyext qe1ext) qe2notext))
  (* Isbcs (c, v, a1, a2, y): v = a1 + not(a2) + y, c = carry flag *)
  | SSA.Isbcs c v a1 a2 y =>
    let 'a_size := asize a1 te in
    let 'qe1ext := qfbv_sext 1 (qfbv_atomic a1) in
    let 'qe2notext := qfbv_sext 1 (qfbv_not (qfbv_atomic a2)) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    let 'qerext := qfbv_add (qfbv_add qeyext qe1ext) qe2notext in
    qfbv_conj (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
  (* Imul (v, a1, a2): v = a1 * a2, overflow is forbidden *)
  | SSA.Imul v a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    qfbv_eq (qfbv_var v) (qfbv_mul qe1 qe2)
  (* Imull (vh, vl, a1, a2): vh and vl are respectively the high part and
     the low part of the full multiplication a1 * a2 *)
  | SSA.Imull vh vl a1 a2 =>
    let 'a1_size := asize a1 te in
    let 'a2_size := asize a2 te in
    let 'qe1ext := qfbv_sext a1_size (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext a1_size (qfbv_atomic a2) in
    let 'qerext := qfbv_mul qe1ext qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var vh)
                       (qfbv_high a1_size qerext))
              (qfbv_eq (qfbv_var vl)
                       (qfbv_low a2_size qerext))
  (* Iumulj (v, a1, a2): v = the full multiplication of a1 * a2, which is equivalent
     to Iumull (vh, vl, a1, a2); Join (r, vh, vl) *)
  | SSA.Imulj v a1 a2 =>
    let 'a_size := asize a1 te  in
    let 'qe1ext := qfbv_sext a_size (qfbv_atomic a1) in
    let 'qe2ext := qfbv_sext a_size (qfbv_atomic a2) in
    let 'qerext := qfbv_mul qe1ext qe2ext in
    qfbv_eq (qfbv_var v) qerext
  (* Ishl (v, a, n): v = a * 2^n, overflow is forbidden *)
  (* need a better size for NBitsDef.from_nat *)
  | SSA.Ishl v a n =>
    let 'qea := qfbv_atomic a in
    let 'qen := qfbv_const n in
    qfbv_eq (qfbv_var v) (qfbv_shl qea qen)
  (* Ijoin (v, ah, al): v = ah * 2^w + al where w is the bit-width of al *)
  | SSA.Ijoin v ah al =>
    let 'qeh := qfbv_atomic ah in
    let 'qel := qfbv_atomic al in
    qfbv_eq (qfbv_var v) (qfbv_concat qeh qel)
  (* Isplit (vh, vl, a, n): vh is the high (w - n) bits (signed extended to w bits)
     of a and vl is the low n bits (zero extended to w bits) of a where w is the
     bit-width of a *)
  | SSA.Isplit vh vl a n =>
    let 'a_size := asize a te in
    let 'qen := qfbv_const n in
    let 'qeamn := qfbv_const (a_size - n) in
    let 'qea := qfbv_atomic a in
    let 'qel := qfbv_lshr (qfbv_shl qea qeamn) qeamn in
    if Typ.is_unsigned (atyp a te) then
      qfbv_conj (qfbv_eq (qfbv_var vh)
                         (qfbv_lshr qea qen))
                (qfbv_eq (qfbv_var vl) qel)
    else
      qfbv_conj (qfbv_eq (qfbv_var vh)
                         (qfbv_ashr qea qen))
                (qfbv_eq (qfbv_var vl) qel)
  (* Icshl (vh, vl, a1, a2, n) *)
  | SSA.Icshl vh vl a1 a2 n =>
    let 'a1_size := asize a1 te in
    let 'a2_size := asize a2 te in
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qer := qfbv_shl (qfbv_concat qe1 qe2) (qfbv_const n) in
    let 'qel := qfbv_low a2_size qer in
    let 'qeh := qfbv_extr a2_size (a2_size + a1_size - 1) qer in
    qfbv_conj (qfbv_eq (qfbv_var vh) qeh)
              (qfbv_eq (qfbv_var vl) (qfbv_lshr qel (qfbv_const n)))
  (* Inot (v, t, a): v = not(a), the one's complement of a, v is of type t *)
  | SSA.Inot v t a =>
    let 'qea := qfbv_atomic a in
    qfbv_eq (qfbv_var v) (qfbv_not qea)
  (* Iand (v, t, a1, a2): v = the bitwise AND of a1 and a2, v is of type t *)
  | SSA.Iand v t a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qer := qfbv_and qe1 qe2 in
    qfbv_eq (qfbv_var v) qer
  (* Ior (v, t, a1, a2): v = the bitwise OR of a1 and a2, v is of type t *)
  | SSA.Ior v t a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qer := qfbv_or qe1 qe2 in
    qfbv_eq (qfbv_var v) qer
  (* Ixor (v, t, a1, a2): v = the bitwise XOR of a1 and a2, v is of type t *)
  | SSA.Ixor v t a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qer := qfbv_xor qe1 qe2 in
    qfbv_eq (qfbv_var v) qer
  (* == Instructions that cannot be translated to polynomials == *)
  (* == Type conversions == *)
  (* Icast (v, t, a): v = the value of a represented by the type t of v *)
  (* Ivpc (v, t, a): v = a, value preserved casting to type t *)
  | SSA.Icast v t a
  | SSA.Ivpc v t a =>
    let 'a_typ := atyp a te in
    let 'a_size := Typ.sizeof_typ a_typ in
    let 't_size := Typ.sizeof_typ t in
    let 'qea := qfbv_atomic a in
    qfbv_eq (qfbv_var v)
            (if Typ.is_unsigned a_typ then
               (if t_size == a_size then qea
                else if t_size < a_size then qfbv_low t_size qea
                else qfbv_zext (t_size - a_size) qea)
             else
               (if t_size == a_size then qea
                else if t_size < a_size then qfbv_low t_size qea
                else qfbv_sext (t_size - a_size) qea))
  (* Specifications *)
  | SSA.Iassume (_, rbexp) => bexp_rbexp rbexp
  end .

Fixpoint bexp_program te (p : program) : seq QFBV.bexp :=
  match p with
  | [::] => [::]
  | hd::tl =>
    let 'te_succ := instr_succ_typenv hd te in
    (bexp_instr te_succ hd)::(bexp_program te_succ tl)
  end .

Record bexp_spec : Type :=
  mkQFBVSpec { bpre : QFBV.bexp;
               bprog : seq QFBV.bexp;
               bpost : QFBV.bexp } .

Definition bexp_of_rspec te (s : rspec) : bexp_spec :=
  {| bpre := bexp_rbexp (rspre s);
     bprog := bexp_program te (rsprog s);
     bpost := bexp_rbexp (rspost s) |}.

Ltac rewrite_eval_exp_atomic :=
  repeat rewrite -> eval_exp_atomic in *.

Lemma eval_bexp_instr te i p s1 s2 :
  SSA.ssa_vars_unchanged_program (SSA.vars_instr i) p ->
  eval_program te p s1 s2 ->
  QFBV.eval_bexp (bexp_instr te i) s1 ->
  QFBV.eval_bexp (bexp_instr te i) s2 .
Proof .
  case : i => /=; intros; rewrite_eval_exp_atomic;
  (let rec tac :=
     match goal with
     | H : is_true (ssa_vars_unchanged_program (SSAVS.add _ _) ?p) |- _ =>
       let H1 := fresh in
       let H2 := fresh in
       move: (ssa_unchanged_program_add1 H) => {H} [H1 H2]; tac
     | H : is_true (ssa_vars_unchanged_program (SSAVS.union _ _) ?p) |- _ =>
       let H1 := fresh in
       let H2 := fresh in
       move: (ssa_unchanged_program_union1 H) => {H} [H1 H2]; tac
     | H1 : eval_program _ ?p ?s1 ?s2,
       H2 : is_true (ssa_unchanged_program_var ?p ?v) |-
       context f [SSAStore.acc ?v ?s2] =>
       (* convert (SSAState.acc v s2) to (SSAState.acc v s1) *)
       rewrite -(acc_unchanged_program H2 H1); tac
     | H1 : eval_program _ ?p ?s1 ?s2,
       H2 : is_true (ssa_vars_unchanged_program (vars_atomic ?a) ?p) |-
       context f [eval_atomic ?a ?s2] =>
       (* convert (eval_atomic a s2) to (eval_atomic a s1) *)
       rewrite -(ssa_unchanged_program_eval_atomic H2 H1); tac
     | _ => by assumption
     end in tac || idtac) .
  - (* split *)
    move : H1; case (Typ.is_unsigned (atyp a te)) => /=;
    move: (ssa_unchanged_program_add1 H) => {H} [H1 H2];
    move: (ssa_unchanged_program_add1 H2) => {H2} [H2 H3];
    rewrite -!(acc_unchanged_program H2 H0)
            -!(acc_unchanged_program H1 H0);
    rewrite_eval_exp_atomic;
    rewrite -(ssa_unchanged_program_eval_atomic H3 H0);
    move => /andP [Hhi Hlo];
              apply /andP; split; done .
  - (* cast *)
    move : H1;
      case (Typ.is_unsigned (atyp a te)) => /=;
      case (Typ.sizeof_typ t0 == Typ.sizeof_typ (atyp a te)) => /=;
      [ idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a te)) => /=
      | idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a te)) => /= ];
      move: (ssa_unchanged_program_add1 H) => {H} [H H1];
      rewrite -!(acc_unchanged_program H H0);
      rewrite_eval_exp_atomic;
      rewrite -(ssa_unchanged_program_eval_atomic H1 H0) // .
  - (* vpc *)
    move : H1;
      case (Typ.is_unsigned (atyp a te)) => /=;
      case (Typ.sizeof_typ t0 == Typ.sizeof_typ (atyp a te)) => /=;
      [ idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a te)) => /=
      | idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a te)) => /= ];
      move: (ssa_unchanged_program_add1 H) => {H} [H H1];
      rewrite -!(acc_unchanged_program H H0);
      rewrite_eval_exp_atomic;
      rewrite -(ssa_unchanged_program_eval_atomic H1 H0) // .
  - (* assume *)
    case : b H H1 => eb rb .
    rewrite /vars_bexp /= => Hun .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} Hun .
    rewrite (eval_bexp_rbexp rb s1) (eval_bexp_rbexp rb s2) => Hs1 .
    elim Hun => {Hun} _ Hun .
    elim : (ssa_unchanged_program_eval_rbexp Hun H0) => Hs1s2 _ .
    by apply : Hs1s2 .
Qed .

(* auxiliary lemmas *)

Lemma from_nat_simple :
  forall n, to_nat (from_nat n n) = n .
Admitted .

Lemma high_extract :
  forall l bs,
    high l bs = extract (size bs - l) (size bs - 1) bs .
Admitted .

Lemma SSAVS_mem_vars_env_SSATE_mem :
  forall te v, SSAVS.mem v (vars_env te) ->
               TypEnv.SSATE.mem v te .
Admitted .  

Lemma conform_size_eval_atomic :
  forall te s a,
    SSAVS.subset (vars_atomic a) (vars_env te) ->
    SSAStore.conform s te ->
    size (eval_atomic a s) == Typ.sizeof_typ (atyp a te) .
Proof .
  move => te s; case .
  - move => v /= .
    rewrite SSAVS.S.Lemmas.subset_singleton => Hmem Hcon .
    case : (Hcon v (SSAVS_mem_vars_env_SSATE_mem Hmem)) => <- .
    done .
  - move => t b _ _ .
    rewrite /atyp /= .
    (* size of (Aconst t b) = b but
       Typ.sizeof_typ (atyp (Aconst t b)) = t,
       why is b = t?
     *)
Admitted .

Lemma to_bool_is_true :
  forall a s,
    to_bool (eval_atomic a s) ->
    [:: true] == eval_atomic a s .
Admitted .

Lemma not_to_bool_is_false :
  forall a s,
    ~~ to_bool (eval_atomic a s) ->
    [:: false] == eval_atomic a s .
Admitted .  

Lemma adc_sext_add_high b bs0 bs1 :
  size bs0 = size bs1 ->
  from_bool 1 (adcB (to_bool b) bs0 bs1).1 ==
  high 1 ((zext (size bs0) b) +# (sext 1 bs0) +# (sext 1 bs1))%bits .
Admitted .

Lemma adc_sext_add_low b bs0 bs1 :
  size bs0 = size bs1 ->
  (adcB (to_bool b) bs0 bs1).2 ==
  low (size bs0) ((zext (size bs0) b) +# (sext 1 bs0) +# (sext 1 bs1))%bits .
Admitted .

  
Lemma adc_false_sext_add_high bs0 bs1 :
  size bs0 = size bs1 ->
  from_bool 1 (adcB false bs0 bs1).1 ==
  high 1 ((sext 1 bs0) +# (sext 1 bs1))%bits .
Proof .
  move => Hsize .
  move : (adc_sext_add_high [::false] Hsize) .
  have : (to_bool [:: false] = false) .
  { rewrite /to_bool // . }
  move => Hbool .
  rewrite Hbool => {Hbool} Heq .
  rewrite (eqP Heq) .
Admitted .  

Lemma adc_false_sext_add_low bs0 bs1 :
  size bs0 = size bs1 ->
  (adcB false bs0 bs1).2 ==
  low (size bs0) ((sext 1 bs0) +# (sext 1 bs1))%bits .
Proof .
  move => Hsize .
  move : (adc_sext_add_low [::false] Hsize) .
  have : (to_bool [:: false] = false) .
  { rewrite /to_bool // . }
  move => Hbool .
  rewrite Hbool => {Hbool} Heq .
  rewrite (eqP Heq) .
Admitted .  

Lemma sbb_sext_sub_high b bs0 bs1 :
  size bs0 = size bs1 ->
  from_bool 1 (sbbB (to_bool b) bs0 bs1).1 ==
  high 1 ((sext 1 bs0) -# (sext 1 bs1) -# (zext (size bs0) b))%bits .
Admitted .

Lemma sbb_sext_sub_low b bs0 bs1 :
  size bs0 = size bs1 ->
  (sbbB (to_bool b) bs0 bs1).2 ==
  low (size bs0) ((sext 1 bs0) -# (sext 1 bs1) -# (zext (size bs0) b))%bits .
Admitted .

Lemma sbb_false_sext_sub_high bs0 bs1 :
  size bs0 = size bs1 ->
  from_bool 1 (sbbB false bs0 bs1).1 ==
  high 1 ((sext 1 bs0) -# (sext 1 bs1))%bits .
Proof .
  move => Hsize .
  move : (sbb_sext_sub_high [::false] Hsize) .
  have : (to_bool [:: false] = false) .
  { rewrite /to_bool // . }
  move => Hbool .
  rewrite Hbool => {Hbool} Heq .
  rewrite (eqP Heq) .
Admitted .
  
Lemma sbb_false_sext_sub_low bs0 bs1 :
  size bs0 = size bs1 ->
  (sbbB false bs0 bs1).2 ==
  low (size bs0) ((sext 1 bs0) -# (sext 1 bs1))%bits .
Proof .
  move => Hsize .
  move : (sbb_sext_sub_low [::false] Hsize) .
  have : (to_bool [:: false] = false) .
  { rewrite /to_bool // . }
  move => Hbool .
  rewrite Hbool => {Hbool} Heq .
  rewrite (eqP Heq) .
Admitted .

Lemma mul_sext bs0 bs1 :
  full_mul bs0 bs1 ==
  ((sext (size bs0) bs0) *# (sext (size bs0) bs1))%bits .
Admitted .

Lemma vtyp_var_add_eq te v tv :
  TypEnv.SSATE.vtyp v (TypEnv.SSATE.add v tv te) = tv .
Proof .
  rewrite /asize /= /TypEnv.SSATE.vtyp .
  rewrite SSAVM.Lemmas.add_eq_o // .
Qed .

Lemma vtyp_var_add_neq te v u tu :
  v != u ->
  TypEnv.SSATE.vtyp v (TypEnv.SSATE.add u tu te) =
  TypEnv.SSATE.vtyp v te .
Proof .
  move => Hneq .
  rewrite !/asize /= /TypEnv.SSATE.vtyp .
  rewrite SSAVM.Lemmas.add_neq_o // .
  rewrite /SSAVM.M.SE.eq eq_sym .
  apply/negP : Hneq .
Qed .

Lemma eval_exp_if s b qfbv0 qfbv1 :
  QFBV.eval_exp (if b then qfbv0 else qfbv1) s =
  if b then QFBV.eval_exp qfbv0 s else QFBV.eval_exp qfbv1 s .
Proof .
  case b => /=; done .
Qed .

Lemma eval_bexp_if s b qfbv0 qfbv1 :
  QFBV.eval_bexp (if b then qfbv0 else qfbv1) s =
  if b then QFBV.eval_bexp qfbv0 s else QFBV.eval_bexp qfbv1 s .
Proof .
  case b => /=; done .
Qed .

Lemma size_inv_same bs :
  size bs = size (~~# bs)%bits .
Proof .
  elim : bs; first done .
  move => b bs IH .
  rewrite /= IH // .
Qed .

Lemma size_neg_same bs :
  size bs = size (-# bs)%bits .
Proof .
  elim : bs; first done .
  move => b bs IH .
  rewrite /negB /= .
  case b; rewrite /= ?size_succB size_inv_same // .
Qed .

Lemma size_sbbB b bs0 bs1 : 
  size (sbbB b bs0 bs1).2 = minn (size bs0) (size bs1) .
Proof .
  rewrite /sbbB /adcB /full_adder /= .
  dcase (full_adder_zip (~~ b) (zip bs0 (~~# bs1)%bits)) => [[c res] Hadder] => /= .
  have : res = (c, res).2 => // .
  rewrite -Hadder; case => -> .
  rewrite size_full_adder_zip -size_inv_same // .
Qed .

Lemma size_ucast bs n :
  size (ucastB bs n) = n .
Proof .
  rewrite /ucastB /= .
  case Heq : (n == size bs) .
  - rewrite (eqP Heq) // .
  - case Hlt : (n < size bs) {Heq} .
    + rewrite size_low // .
    + rewrite size_zext addnBA; first auto with * .
      rewrite leqNgt Hlt // .
Qed .

Lemma size_scast bs n :
  size (scastB bs n) = n .
Proof .
  rewrite /scastB /= .
  case Heq : (n == size bs) .
  - rewrite (eqP Heq) // .
  - case Hlt : (n < size bs) {Heq} .
    + rewrite size_low // .
    + rewrite size_sext addnBA; first auto with * .
      rewrite leqNgt Hlt // .
Qed .

Lemma size_tcast bs s t :
  size (Typ.tcast bs s t) = Typ.sizeof_typ t .
Proof .
  rewrite /Typ.tcast; case s => _;
    [rewrite size_ucast // | rewrite size_scast //] .
Qed .
  
Lemma size_unsigned_same ty :
  Typ.sizeof_typ (Typ.unsigned_typ ty) = Typ.sizeof_typ ty .
Proof .
  case ty; done .
Qed .
  
Lemma size_eval_atomic_asize te a s :
  SSAVS.subset (vars_atomic a) (vars_env te) ->
  SSAStore.conform s te ->
  size (eval_atomic a s) = asize a te .
Proof .
  move => Hsub Hcon .
  rewrite (eqP (conform_size_eval_atomic Hsub Hcon)) /asize // .
Qed .

Lemma asize_add_same te a v :
  asize a (TypEnv.SSATE.add v (atyp a te) te) = (asize a te) .
Proof .
  case : a .
  - move => va; case Heq : (va == v) .
    + rewrite (eqP Heq) /asize /= .
      rewrite /TypEnv.SSATE.vtyp /= .
      rewrite SSAVM.Lemmas.find_add_eq // .
    + rewrite /asize /= .
      rewrite /TypEnv.SSATE.vtyp /= .
      rewrite SSAVM.Lemmas.find_add_neq // .
      rewrite /SSAVM.M.SE.eq Heq // .
  - move => t b /= .
    rewrite /asize /atyp // .
Qed .      

Lemma size_eval_atomic_same te s a0 a1 :
  SSAStore.conform s te ->
  SSAVS.subset (vars_atomic a0) (vars_env te) ->
  SSAVS.subset (vars_atomic a1) (vars_env te) ->
  atyp a0 te = atyp a1 te ->
  size (eval_atomic a0 s) = size (eval_atomic a1 s) .
Proof .
  move => Hcon Hsub0 Hsub1 Hatypeq .
  move : (conform_size_eval_atomic Hsub0 Hcon)
           (conform_size_eval_atomic Hsub1 Hcon) .
  rewrite Hatypeq eq_sym .
  case => /eqP -> .
  case => /eqP -> // .
Qed .

Lemma mem_subset_singleton x s :
  SSAVS.mem x s ->
  SSAVS.subset (SSAVS.singleton x) s .
Proof .
  apply SSAVS.Lemmas.subset_singleton2 .
Qed .

Lemma not_mem_add x y s :
  ~~ SSAVS.mem x (SSAVS.add y s) ->
  x != y /\ ~~ SSAVS.mem x s .
Proof .
  move => Hnmem; split .
  - apply /negP => Heq .
    move : (SSAVS.Lemmas.mem_add2 s Heq) => Hmem .
    rewrite Hmem in Hnmem .
    done .
  - apply /negP => Hmem .
    move : (SSAVS.Lemmas.mem_add3 y Hmem) => {Hmem} Hmem .
    rewrite Hmem in Hnmem .
    done .
Qed .

Ltac unchanged_instr_subset :=
  match goal with
  | Hsub : is_true (SSAVS.subset (SSAVS.singleton ?v) (SSAVS.union ?vs0 ?vs1))
    |- _ =>
    move : (SSAVS.Lemmas.subset_singleton1 Hsub) => {Hsub};
    rewrite VSLemmas.OP.P.Dec.F.union_b;
    case /orP => Hsub;
    move : (SSAVS.Lemmas.subset_singleton2 Hsub) => {Hsub} Hsub; unchanged_instr_subset
  | Hsub0 : is_true (SSAVS.subset ?vs0 ?vs1),
    Hsub1 : is_true (SSAVS.subset ?vs1 ?vs2)
    |- _ =>
    let H := fresh in
    move : (SSAVS.Lemmas.subset_trans Hsub0 Hsub1) => {Hsub0} H; unchanged_instr_subset
  | Hsub : is_true (SSAVS.subset (SSAVS.singleton ?v) ?vs),
    Hun : is_true (ssa_vars_unchanged_instr ?vs ?i)
    |- _ =>
    move : (ssa_unchanged_instr_subset Hun Hsub) => {Hun} Hun; unchanged_instr_subset
  | Hun : is_true (ssa_vars_unchanged_instr (SSAVS.singleton ?v) ?i)
    |- _ =>
    let H0 := fresh in
    move : (ssa_unchanged_instr_singleton1 Hun) => {Hun};
    rewrite /ssa_var_unchanged_instr /lvs_instr => H0
  end .

Ltac not_mem_rewrite_vtyp :=
  match goal with
  | Hnmem : is_true (~~ SSAVS.mem ?v (SSAVS.singleton ?u))
    |- _ =>
    move : (SSAVS.Lemmas.not_mem_singleton1 Hnmem) => {Hnmem} /negP Hnmem;
    rewrite !vtyp_var_add_neq //
  | Hnmem : is_true (~~ SSAVS.mem ?v (SSAVS.add ?u (SSAVS.singleton ?w)))
    |- _ =>
    let Hneq := fresh in
    let H := fresh in
    move : (not_mem_add Hnmem) => {Hnmem} [Hneq H];
    move : (SSAVS.Lemmas.not_mem_singleton1 H) => {H} /negP H;
    rewrite !vtyp_var_add_neq //
  | _ => idtac
  end .

Lemma atyp_well_defined_unchanged te i a :
  well_defined_instr te i ->
  ssa_vars_unchanged_instr (vars_env te) i ->
  SSAVS.subset (vars_atomic a) (rvs_instr i) ->
  atyp a (instr_succ_typenv i te) = atyp a te .
Proof .
  elim a; last (case i => /=; done) .
  move => v; case i => /= .
  - move => u a0 .
    move => /are_defined_subset Ha0te Hun Hva0 .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 n .
    move => /are_defined_subset Ha0te Hun Hva0 .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => vh vl a0 a1 n .
    move => /andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hun Hva0a1 .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - done .
  - move => u ac a0 a1 .
    rewrite /are_defined => /andP [/andP [/are_defined_subset Hdefc /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hun Hvaca0a1 .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - done .
  - move => u t a0 .
    move => /are_defined_subset Hdef Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1 .
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 .
    move => /andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1 ac .
    move => /andP [/andP [/are_defined_subset Hdefc /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 ac .
    move => /andP [/andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] /are_defined_subset Hdefc] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1 .
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 .
    move => /andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 .
    move => /andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1 ac .
    move => /andP [/andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /are_defined_subset Hdefc] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 ac .
    move => /andP [/andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] /are_defined_subset Hdefc] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1 ac .
    move => /andP [/andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /are_defined_subset Hdefc] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 ac .
    move => /andP [/andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] /are_defined_subset Hdefc] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1 .
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 .
    move => /andP [/andP [_ /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1 .
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 n .
    move => /andP [Hneq /are_defined_subset Hdef] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u w a0 a1 .
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u t a0 a1 .
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u t a0 a1 .
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u t a0 .
    move => /are_defined_subset Hdef Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u t a0 .
    move => /are_defined_subset Hdef Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - move => u a0 a1.
    move => /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hun Hsub .
    unchanged_instr_subset; not_mem_rewrite_vtyp .
  - done .
Qed .

  
Lemma asize_well_defined_unchanged te i a :
  well_defined_instr te i ->
  ssa_vars_unchanged_instr (vars_env te) i ->
  SSAVS.subset (vars_atomic a) (rvs_instr i) ->
  asize a (instr_succ_typenv i te) = asize a te .
Proof .
  elim a; last (case i => /=; done) .
  move => v Hdef Hun Hsub .
  rewrite /asize .
  rewrite atyp_well_defined_unchanged // .
Qed .    

Ltac well_defined_to_vs_subset :=
  match goal with
  | Hdef : is_true (well_defined_instr _ ?i) |- _ =>
    move : Hdef; rewrite /well_defined_instr;
    [ let H := fresh in
      let H0 := fresh in
      let H1 := fresh in
      let H2 := fresh in
      move => /andP [/andP [/andP [H /are_defined_subset H0] /are_defined_subset H1] /are_defined_subset H2]
   || let H := fresh in
      let H0 := fresh in
      let H1 := fresh in
      move => /andP [/andP [/are_defined_subset H /are_defined_subset H0] /are_defined_subset H1]
   || let H := fresh in
      let H0 := fresh in
      let H1 := fresh in
      move => /andP [/andP [H /are_defined_subset H0] /are_defined_subset H1]
   || let H := fresh in
      move => /andP [/are_defined_subset H /are_defined_subset Hdef]
   || let H := fresh in
      move => /andP [H /are_defined_subset Hdef]
   || move => /are_defined_subset Hdef
    ]
  | Hdef : is_true (SSAVS.subset _ _ && SSAVS.subset _ _) |- _ =>
    let Hsub1 := fresh in
    let Hsub2 := fresh in
    move : Hdef => /andP [Hsub1 Hsub2]
  | Hdef : is_true (_ && SSAVS.subset _ _) |- _ =>
    let Hprev := fresh in
    let Hsub := fresh in
    move : Hdef => /andP [Hprev Hsub]
(*
  | Hdef : is_true (_ && SSAVS.subset _ _ && SSAVS.subset _ _) |- _ =>
    let Hneq := fresh in
    let Hsub1 := fresh in
    let Hsub2 := fresh in
    move : Hdef => /andP [/andP [Hneq Hsub1] Hsub2]
*)
  end .

Ltac eval_exp_exp_atomic_to_pred_state :=
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) _),
    Hun : is_true (ssa_vars_unchanged_instr _ ?i),
    Hinst : eval_instr _ ?i _ ?s2
    |-
    context f [QFBV.eval_exp (qfbv_atomic ?a) ?s2]   =>
    rewrite eval_exp_atomic
            -(ssa_unchanged_instr_eval_atomic
                (ssa_unchanged_instr_subset Hun Hsub)
                Hinst)
  end .

Ltac qfbv_store_acc :=
  match goal with
  | HUpd : SSAStore.Upd _ _ _ ?s2 |- context f [SSAStore.acc _ ?s2] =>
    rewrite (SSAStore.acc_Upd_eq _ HUpd) //
  | Hneq : is_true (?u != ?v),
    HUpd : SSAStore.Upd2 ?v _ ?u _ _ ?s2 |- context f [SSAStore.acc ?v ?s2] =>
    move /negP : Hneq; rewrite eq_sym => /negP Hneq;
    rewrite (SSAStore.acc_Upd2_eq1 _ Hneq HUpd) //
  | HUpd : SSAStore.Upd2 _ _ ?v _ _ ?s2 |- context f [SSAStore.acc ?v ?s2] =>
    rewrite (SSAStore.acc_Upd2_eq2 _ HUpd) //
  end .



Lemma bexp_instr_eval te i s1 s2 :
  well_formed_instr te i ->
  SSAStore.conform s1 te ->
  ssa_vars_unchanged_instr (vars_env te) i ->
  eval_instr te i s1 s2 ->
  QFBV.eval_bexp (bexp_instr (instr_succ_typenv i te) i) s2 .
Proof .
  case: i => /= .
  - (* Imov *)
    move => v a /andP [Hdef _] _ Hun Hinst .
    well_defined_to_vs_subset .    
    eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst .
    qfbv_store_acc .
  - (* Ishl *)
    move => v a n /andP [Hdef _] _ Hun Hinst .
    well_defined_to_vs_subset .
    eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst .
    qfbv_store_acc .
    rewrite from_nat_simple // .
  - (* Icshl *)
    move => vh vl ah al n /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 //
      | rewrite SSAVS.Lemmas.union_subset_2 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst .
    repeat qfbv_store_acc .
    rewrite from_nat_simple high_extract .
    rewrite !size_shlB !size_cat !addnK .
    rewrite !(eqP (conform_size_eval_atomic H3 Hcon))
            !(eqP (conform_size_eval_atomic H Hcon)) /= .
    apply /andP; split; done .
  - (* Inondet *)
    done .
  - (* Icmov *)
    move => v c a0 a1 /andP [Hdef Hty ] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    rewrite /joinlsb /= .
    move : Hty => /andP [ Htyc _ ] .
    inversion_clear Hinst; repeat qfbv_store_acc .
    + rewrite (to_bool_is_true H1) // .
    + move : (not_to_bool_is_false H1) .
      case => /eqP <- // .
  - (* Inop *)
    done .
  - (* Inot *)
    move => v t a /andP [Hdef _] _ Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Iadd *)
    move => v a0 a1 /andP [Hdef _] _ Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Iadds *)
    move => c v a0 a1 /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite /carry_addB .
    rewrite /well_typed_instr in Hty .
    move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize .
    rewrite (adc_false_sext_add_high Hsize) /= .
    rewrite {1}/addB .
    rewrite (eqP (adc_false_sext_add_low Hsize)) .
    move /negP : H1; rewrite eq_sym; move /negP => H1 .
    rewrite (size_eval_atomic_asize H3 Hcon) // .
  - (* Iadc *)
    move => v a0 a1 c /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite /well_typed_instr in Hty .
    move : Hty => /andP [Hty _] .
    move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize .
    rewrite (eqP (adc_sext_add_low (eval_atomic c s1) Hsize)) .
    rewrite (size_eval_atomic_asize H3 Hcon) // .
  - (* Iadcs *)
    move => c v a0 a1 ac /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun) ;
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite /well_typed_instr in Hty .
    move : Hty => /andP [Hty _] .
    move : (size_eval_atomic_same Hcon H0 H1 (eqP Hty)) => Hsize .
    rewrite (eqP (adc_sext_add_high (eval_atomic ac s1) Hsize)) .
    rewrite (eqP (adc_sext_add_low (eval_atomic ac s1) Hsize)) .
    rewrite (size_eval_atomic_asize _ Hcon) // .
    apply /andP; split; done .
  - (* Isub *)
    move => v a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Isubc *)
    move => c v a0 a1 /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun) ;
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite /carry_addB .
    rewrite /well_typed_instr in Hty .
    move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize .
    rewrite (size_neg_same (eval_atomic a1 s1)) in Hsize .
    rewrite (eqP (adc_false_sext_add_high Hsize)) .
    rewrite {3}/addB .
    rewrite (eqP (adc_false_sext_add_low Hsize)) .
    rewrite (size_eval_atomic_asize H3 Hcon) /= .
    apply /andP; split; done .
  - (* Isubb *)
    move => c v a0 a1 /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun) ;
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite /borrow_subB .
    rewrite /well_typed_instr in Hty .
    move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize .
    rewrite (sbb_false_sext_sub_high Hsize) /= .
    rewrite /subB .
    rewrite (eqP (sbb_false_sext_sub_low Hsize)) .
    rewrite (size_eval_atomic_asize _ Hcon) // .
  - (* Isbc *)
    move => v a0 a1 ac /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    move : Hty; rewrite /well_typed_instr => /andP [Hty _] .
    move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize .
    rewrite (size_inv_same (eval_atomic a1 s1)) in Hsize .
    rewrite (eqP (adc_sext_add_low (eval_atomic ac s1) Hsize)) .
    rewrite (size_eval_atomic_asize _ Hcon) // .
  - (* Isbcs *)
    move => c v a0 a1 ac /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    move : Hty .
    rewrite /well_typed_instr => /andP [Hty _] .
    move : (size_eval_atomic_same Hcon H0 H1 (eqP Hty)) => Hsize .
    rewrite (size_inv_same (eval_atomic a1 s1)) in Hsize .
    rewrite (eqP (adc_sext_add_high (eval_atomic ac s1) Hsize)) .
    rewrite (eqP (adc_sext_add_low (eval_atomic ac s1) Hsize)) .
    rewrite !(size_eval_atomic_asize H0 Hcon) /= .
    apply /andP; split; done .
  - (* Isbb *)
    move => v a0 a1 ac /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    move : Hty .
    rewrite /well_typed_instr => /andP [Hty _] .
    move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize .
    rewrite (eqP (sbb_sext_sub_low (eval_atomic ac s1) Hsize)) .
    rewrite !(size_eval_atomic_asize H3 Hcon) // .
  - (* Isbbs *)
    move => c v a0 a1 ac /andP [Hdef Hty] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    move : Hty .
    rewrite /well_typed_instr => /andP [Hty _] .
    move : (size_eval_atomic_same Hcon H0 H1 (eqP Hty)) => Hsize .
    rewrite (eqP (sbb_sext_sub_high (eval_atomic ac s1) Hsize)) .
    rewrite (eqP (sbb_sext_sub_low (eval_atomic ac s1) Hsize)) .
    rewrite !(size_eval_atomic_asize H0 Hcon) .
    apply /andP; split; done .
  - (* Imul *)
    move => v a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Imull *)
    move => vh vl a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_2 //
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite (eqP (mul_sext (eval_atomic a0 s1) (eval_atomic a1 s1))) .
    rewrite (size_eval_atomic_asize H3 Hcon)
            (size_eval_atomic_asize H Hcon) /= .
    apply /andP; split; done .
  - (* Imulj *)
    move => v a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.union_subset_1 // ] .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite (eqP (mul_sext (eval_atomic a0 s1) (eval_atomic a1 s1))) .
    rewrite (size_eval_atomic_asize H0 Hcon) // .
  - (* Isplit *)
    move => vh vl a n /andP [Hdef _] Hcon Hun Hinst .
    rewrite !(asize_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.subset_refl // ] .
    rewrite !(atyp_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.subset_refl // ] .
    repeat well_defined_to_vs_subset .
    inversion Hinst => {H H0 H2 H3 H4 H5};
    [ rewrite H6 /= | rewrite -Typ.not_signed_is_unsigned H6 /= ];
    repeat eval_exp_exp_atomic_to_pred_state;
    repeat qfbv_store_acc;
    rewrite !(size_eval_atomic_asize Hdef Hcon)
            !from_nat_simple;
    apply /andP; split; done .
  - (* Iand *)
    move => v t a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Ior *)
    move => v t a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Ixor *)
    move => v t a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Icast *)
    move => v t a /andP [Hdef _] Hcon Hun Hinst .
    rewrite !(atyp_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.subset_refl // ] .
    repeat well_defined_to_vs_subset .
    rewrite !eval_exp_if .
    rewrite /qfbv_low /= .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite /Typ.tcast /ucastB /scastB /=
            !(size_eval_atomic_asize Hdef Hcon) !/asize .
    case (atyp a te) => // .
  - (* Ivpc *)
    move => v t a /andP [Hdef _] Hcon Hun Hinst .
    rewrite !(atyp_well_defined_unchanged Hdef Hun);
      [ idtac
      | rewrite SSAVS.Lemmas.subset_refl // ] .
    repeat well_defined_to_vs_subset .
    rewrite !eval_exp_if .
    rewrite /qfbv_low /= .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
    rewrite /Typ.tcast /ucastB /scastB /=
            !(size_eval_atomic_asize Hdef Hcon) !/asize .
    case (atyp a te) => // .
  - (* Ijoin *)
    move => v a0 a1 /andP [Hdef _] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    repeat eval_exp_exp_atomic_to_pred_state .
    inversion_clear Hinst; repeat qfbv_store_acc .
  - (* Iassume *)
    move => b /andP [Hdef _] Hcon Hun Hinst .
    repeat well_defined_to_vs_subset .
    inversion_clear Hinst; repeat qfbv_store_acc .
    case H; case b => /= ebexp rbexp _ Hrbexp .
    case (eval_bexp_rbexp rbexp s2) => _ Hqfbv .
    apply : Hqfbv => // .
Qed .    

(* Connect premises by conjunction. *)

Fixpoint eval_bexps_conj (es : seq QFBV.bexp) (s : SSAStore.t) : Prop :=
  match es with
  | [::] => True
  | hd::tl => QFBV.eval_bexp hd s /\ eval_bexps_conj tl s
  end .

Lemma eval_program_cons te hd tl s1 s3 :
  eval_program te (hd :: tl) s1 s3 ->
  exists s2, eval_instr te hd s1 s2 /\
             eval_program (instr_succ_typenv hd te) tl s2 s3 .
Proof .
  move => Hev .
  inversion_clear Hev .
  exists t => // .
Qed .

Lemma mem_add_neq elt te x y (ty : elt) :
  x != y ->
  TypEnv.SSATE.mem x (TypEnv.SSATE.add y ty te) ->
  TypEnv.SSATE.mem x te .
Proof .
  move => Hneq .
  rewrite TypEnv.SSATE.Lemmas.mem_add_neq // .
  move : Hneq => /negP // .
Qed .

Lemma eqb_false_neqb (T : eqType) (x : T) y :
  (x == y) = false -> x != y .
Proof .
  move => Heqf .
  apply contraFneq with (x == y); last done .
  case => -> // .
Qed .  

Lemma conform_Upd te s1 s2 ty x v :
  Typ.sizeof_typ ty = size v ->
  SSAStore.conform s1 te ->
  SSAStore.Upd x v s1 s2 ->
  SSAStore.conform s2 (TypEnv.SSATE.add x ty te) .
Proof .
  move => Hszeq Hcon HUpd y Hmem .
  case Heq : (y == x) .
  - rewrite (TypEnv.SSATE.vsize_add_eq Heq)
            (SSAStore.acc_Upd_eq Heq HUpd) // .
  - move : (eqb_false_neqb Heq) => {Heq} Hneq .
    rewrite TypEnv.SSATE.vsize_add_neq // .
    move : (mem_add_neq Hneq Hmem) => {Hmem} Hmem .
    rewrite (SSAStore.acc_Upd_neq Hneq HUpd) .
    rewrite Hcon // .
Qed .

Lemma conform_Upd2 te s1 s2 ty1 ty2 x1 x2 v1 v2 :
  x1 != x2 ->
  Typ.sizeof_typ ty1 = size v1 ->
  Typ.sizeof_typ ty2 = size v2 ->
  SSAStore.conform s1 te ->
  SSAStore.Upd2 x2 v2 x1 v1 s1 s2 ->
  SSAStore.conform s2
    (TypEnv.SSATE.add x1 ty1
      (TypEnv.SSATE.add x2 ty2 te)) .
Proof .
  move => Hneq Hty1 Hty2 Hcon HUpd2 y Hmem .
  case Heq1 : (y == x1); case Heq2 : (y == x2) .
  - rewrite -(eqP Heq1) -(eqP Heq2) in Hneq .
    move : Hneq => /eqP // .
  - rewrite (SSAStore.acc_Upd2_eq2 Heq1 HUpd2)
            (TypEnv.SSATE.vsize_add_eq Heq1) // .
  - move : (eqb_false_neqb Heq1) => {Heq1} Hneq1 .
    rewrite (SSAStore.acc_Upd2_eq1 Heq2 Hneq1 HUpd2)
            (TypEnv.SSATE.vsize_add_neq Hneq1)
            (TypEnv.SSATE.vsize_add_eq Heq2) // .
  - move : (eqb_false_neqb Heq1) => {Heq1} Hneq1 .
    move : (eqb_false_neqb Heq2) => {Heq2} Hneq2 .
    rewrite (SSAStore.acc_Upd2_neq Hneq2 Hneq1 HUpd2)
            (TypEnv.SSATE.vsize_add_neq Hneq1)
            (TypEnv.SSATE.vsize_add_neq Hneq2) Hcon // .
    exact : (mem_add_neq Hneq2 (mem_add_neq Hneq1 Hmem)) .
Qed .
    
Lemma conform_eval_succ_typenv te i s1 s2 :
  well_formed_instr te i ->
  SSAStore.conform s1 te ->
  eval_instr te i s1 s2 ->
  SSAStore.conform s2 (instr_succ_typenv i te) .
Proof .
  move => /andP [Hdef Hty] Hcon .
  case : i Hdef Hty => /= .
  - (* Imov *)
    move => v a /are_defined_subset Hdef _ Hev .
    inversion_clear Hev .
    apply : (conform_Upd _ Hcon H) .
    rewrite (size_eval_atomic_asize Hdef) // .
  - (* Ishl *)
    move => v a n /are_defined_subset Hdef _ Hev .
    inversion_clear Hev .
    apply : (conform_Upd _ Hcon H) .
    rewrite size_shlB (size_eval_atomic_asize Hdef) // .
  - (* Icshl *)
    move => vh vl a0 a1 n /andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] _ Hev .
    inversion_clear Hev .
    apply : (conform_Upd2 Hneq _ _ Hcon H) .
    + rewrite size_high (size_eval_atomic_asize Hdef0) // .
    + rewrite size_shrB size_low (size_eval_atomic_asize Hdef1) // .
  - (* Inondet *)
    move => v t _ _ Hev .
    inversion_clear Hev .
    apply : (conform_Upd _ Hcon H0) => // .
  - (* Icmov *)
    move => v ac a0 a1 /andP [/andP [/are_defined_subset Hdefc /are_defined_subset Hdef0] /are_defined_subset Hdef1] /andP [_ Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H0);
    [ rewrite (size_eval_atomic_asize Hdef0) //
    | rewrite (size_eval_atomic_asize Hdef1) //;
      rewrite (eqP Hty) // ] .
  - (* Inop *)
    move => _ _ Hev .
    inversion Hev .
    rewrite -H1 // .
  - (* Inot *)
    move => v t a /are_defined_subset Hdef Hty Hev .
    rewrite /Typ.compatible in Hty .
    inversion_clear Hev .
    apply : (conform_Upd _ Hcon H) => // .
    rewrite -size_inv_same (eqP Hty)
            (size_eval_atomic_asize Hdef) // .
  - (* Iadd *)
    move => v a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_addB (size_eval_atomic_asize Hdef0) // .
    rewrite (size_eval_atomic_asize Hdef1) // .
    rewrite /asize !(eqP Hty) minnE subKn // .
  - (* Iadds *)
    move => u v a0 a1 /andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H) .
    + done .
    + rewrite size_addB (size_eval_atomic_asize Hdef0) //;
      rewrite (size_eval_atomic_asize Hdef1) //;
      rewrite /asize !(eqP Hty) minnE subKn // .
  - (* Iadc *)
    move => v a0 a1 ac /andP [/andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /are_defined_subset Hdefc]
              /andP [Hty Htyc] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite /adcB /full_adder size_full_adder_zip
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize !(eqP Hty) minnE subKn // .
  - (* Iadcs *)
    move => u v a0 a1 ac /andP [/andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] /are_defined_subset Hdefc] /andP [Hty Htyc] Hev .    
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H) .      
    + done .
    + rewrite /adcB /full_adder size_full_adder_zip
              (size_eval_atomic_asize Hdef0) //
              (size_eval_atomic_asize Hdef1) //
              /asize !(eqP Hty) minnE subKn // .
  - (* Isub *)
    move => u a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_subB (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize !(eqP Hty) minnE subKn // .
  - (* Isubc *)
    move => u v a0 a1 /andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H) .
    + done .
    + rewrite size_addB -size_neg_same
              (size_eval_atomic_asize Hdef0) //
              (size_eval_atomic_asize Hdef1) //
              /asize !(eqP Hty) minnE subKn // .
  - (* Isubb *)
    move => u v a0 a1 /andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H) .
    + done .
    + rewrite size_subB
              (size_eval_atomic_asize Hdef0) //
              (size_eval_atomic_asize Hdef1) //
              /asize !(eqP Hty) minnE subKn // .
  - (* Isbc *)
    move => v a0 a1 ac /andP [/andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /are_defined_subset Hdefc]
              /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite /adcB /full_adder size_full_adder_zip
            -size_inv_same 
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize !(eqP Hty) minnE subKn // .
  - (* Isbcs *)
    move => u v a0 a1 ac /andP [/andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] /are_defined_subset Hdefc] /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H) .
    + done .
    + rewrite /adcB /full_adder size_full_adder_zip
              -size_inv_same
              (size_eval_atomic_asize Hdef0) //
              (size_eval_atomic_asize Hdef1) //
              /asize !(eqP Hty) minnE subKn // .
  - (* Isbb *)
    move => v a0 a1 ac /andP [/andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /are_defined_subset Hdefc]
              /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_sbbB
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize !(eqP Hty) minnE subKn // .
  - (* Isbbs *)
    move => u v a0 a1 ac /andP [/andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] /are_defined_subset Hdefc]
              /andP [Hty _] Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H); first done .
    rewrite size_sbbB
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize !(eqP Hty) minnE subKn // .
  - (* Imul *)
    move => v a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_mulB
            (size_eval_atomic_asize Hdef0) // .
  - (* Imull *)
    move => u v a0 a1 /andP [/andP [Hneq /are_defined_subset Hdef0] /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H);
    [ rewrite size_high 
              (size_eval_atomic_asize Hdef0) //
    | rewrite size_low
              (size_eval_atomic_asize Hdef1) // ] .
    rewrite size_unsigned_same // .
  - (* Imulj *)
    move => v a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] Hty Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_full_mul //
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize -(eqP Hty) .
    rewrite /Typ.double_typ /= .
    case (atyp a0 te) => /= // n;
    rewrite mul2n addnn // .
  - (* Isplit *)
    move => u v a n /andP [Hneq /are_defined_subset Hdef] _ Hev .
    inversion_clear Hev; apply : (conform_Upd2 Hneq _ _ Hcon H0);
    [ rewrite size_shrB (size_eval_atomic_asize Hdef) //
    | rewrite size_shrB size_shlB size_unsigned_same (size_eval_atomic_asize Hdef) //
    | rewrite size_sarB (size_eval_atomic_asize Hdef) //
    |  rewrite size_shrB size_shlB size_unsigned_same (size_eval_atomic_asize Hdef) // ] .
  - (* Iand *)
    move => u v a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /andP [Htyc Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_lift
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize -(eqP Hty) maxnn (eqP Htyc) // .
  - (* Ior *)
    move => u v a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /andP [Htyc Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_lift
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize -(eqP Hty) maxnn (eqP Htyc) // .
  - (* Ixor *)
    move => u v a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /andP [Htyc Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_lift
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize -(eqP Hty) maxnn (eqP Htyc) // .
  - (* Icast *)
    move => v t a /are_defined_subset Hdef _ Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_tcast // .
  - (* Ivpc *)
    move => u v a /are_defined_subset Hdef _ Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_tcast // .
  - (* Ijoin *)
    move => v a0 a1 /andP [/are_defined_subset Hdef0 /are_defined_subset Hdef1] /andP [Hun Hty] Hev .
    inversion_clear Hev; apply : (conform_Upd _ Hcon H) .
    rewrite size_cat
            (size_eval_atomic_asize Hdef0) //
            (size_eval_atomic_asize Hdef1) //
            /asize -(eqP Hty) /Typ.double_typ .
    case (atyp a0 te) => /= n;
    rewrite mul2n addnn // .
  - move => b Hdef _ Hev .
    inversion Hev; rewrite -H2 // .
Qed .
    
Lemma bexp_program_eval te p s1 s2 :
  well_formed_ssa_program te p ->
  SSAStore.conform s1 te ->
  eval_program te p s1 s2 ->
  eval_bexps_conj (bexp_program te p) s2.
Proof .
  elim : p te s1 s2 => /= .
  - done .
  - move=> hd tl IH te s1 s3 Hwfssa Hcon Hep.
    move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
    elim : (eval_program_cons Hep) => s2 [Hehd Hetl] .
    move : (ssa_unchanged_program_cons1 Huc) => [Huchd Huctl] .
    split.
    + move : (well_formed_program_cons1 Hwf) => Hwfhd .
      move : (bexp_instr_eval Hwfhd Hcon Huchd Hehd) .
      move : Hetl .
      move : (well_formed_ssa_vars_unchanged_hd Hwfssa) .
      apply : eval_bexp_instr .
    + apply : (IH _ _ _ (well_formed_ssa_tl Hwfssa) _ Hetl) .
      exact : (conform_eval_succ_typenv
                 (well_formed_program_cons1 Hwf)
                 Hcon Hehd) .
Qed .

Definition valid_bexp_spec_conj (s : bexp_spec) : Prop :=
  forall st : SSAStore.t,
    QFBV.eval_bexp (bpre s) st ->
    eval_bexps_conj (bprog s) st ->
    QFBV.eval_bexp (bpost s) st .

Lemma bexp_spec_sound_conj (s : spec) :
  well_formed_ssa_spec s ->
  valid_bexp_spec_conj (bexp_of_rspec (sinputs s) (rspec_of_spec s)) -> valid_rspec (rspec_of_spec s).
Proof.
  (* Prove this with the new rspec_of_spec *)
  (*
  destruct s as [te p g] .
  rewrite /bexp_of_rspec /valid_bexp_spec_conj /=.
  move=> Hwfssa Hvalid s1 s2 /= Hcon Hf Hp.
  apply: eval_bexp_rbexp1.
  apply: Hvalid.
  - move: Hwfssa => /andP /= [/andP [Hwf Huc] Hssa]. apply: eval_bexp_rbexp2.
    apply: (proj1 (ssa_unchanged_program_eval_rbexp _ Hp) Hf).
    apply: (ssa_unchanged_program_subset Huc).
    move/andP: Hwf => /= [/andP [H _] _].
    move : H => /andP [/are_defined_subset H _] .
    exact: (VSLemmas.subset_union5 H).
  - exact: (bexp_program_eval (well_formed_ssa_spec_program Hwfssa) Hcon Hp).
  *)
Admitted.

(* Connect premises by implication. *)

Fixpoint eval_bexps_imp (es : seq QFBV.bexp) (s : SSAStore.t) (p : Prop) : Prop :=
  match es with
  | [::] => p
  | hd::tl => QFBV.eval_bexp hd s -> eval_bexps_imp tl s p
  end.

Definition valid_bexp_spec_imp (s : bexp_spec) : Prop :=
  forall st : SSAStore.t,
    QFBV.eval_bexp (bpre s) st ->
    eval_bexps_imp (bprog s) st (QFBV.eval_bexp (bpost s) st).

Lemma valid_bexp_spec_conj_imp (s : bexp_spec) :
  valid_bexp_spec_conj s -> valid_bexp_spec_imp s.
Proof.
  destruct s as [f p g].
  move => Hc s /= Hf.
  move: (Hc s Hf) => /= {Hc Hf f} Hc.
  elim: p Hc => /=.
  - by apply.
  - move=> hd tl IH Hc Hhd.
    apply: IH => Htl.
    apply: Hc; split; assumption.
Qed.

Lemma valid_bexp_spec_imp_conj (s : bexp_spec) :
  valid_bexp_spec_imp s -> valid_bexp_spec_conj s.
Proof.
  destruct s as [f p g].
  move => Hi s /= Hf.
  move: (Hi s Hf) => /= {Hi Hf f} Hi.
  elim: p Hi => /=.
  - done.
  - move=> hd tl IH Hi [Hhd Htl].
    exact: (IH (Hi Hhd) Htl).
Qed.

Lemma bexp_spec_sound_imp (s : spec) :
  well_formed_ssa_spec s ->
  valid_bexp_spec_imp (bexp_of_rspec (sinputs s) (rspec_of_spec s)) -> valid_rspec (rspec_of_spec s).
Proof.
  move=> Hw Hv.
  apply: (bexp_spec_sound_conj Hw).
  exact: valid_bexp_spec_imp_conj.
Qed.



(* Soundness *)

Definition valid_bexp_spec := valid_bexp_spec_imp.

Theorem bexp_spec_sound (s : spec) :
  well_formed_ssa_spec s ->
  valid_bexp_spec (bexp_of_rspec (sinputs s) (rspec_of_spec s)) -> valid_rspec (rspec_of_spec s).
Proof.
  exact: bexp_spec_sound_imp.
Qed.




(* Define the safety condition in terms of a QFBV expression *)

(* Convert conditions needed for the conversion from bvSSA to zSSA. *)

Definition bexp_atomic_addB_safe te a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 te in
  if Typ.is_unsigned a_typ then
    qfbv_lneg (qfbv_uaddo (qfbv_atomic a1)
                          (qfbv_atomic a2))
  else
    qfbv_lneg (qfbv_saddo (qfbv_atomic a1)
                          (qfbv_atomic a2)) .

Definition bexp_atomic_adcB_safe te a1 a2 ac : QFBV.bexp :=
  let 'a_typ := atyp a1 te in
  if Typ.is_unsigned a_typ then
    qfbv_conj
      (qfbv_lneg
         (qfbv_uaddo (qfbv_atomic a1)
                     (qfbv_atomic a2)))
      (qfbv_lneg
         (qfbv_uaddo (qfbv_add (qfbv_atomic a1)
                               (qfbv_atomic a2))
                     (qfbv_atomic ac)))
  else
    qfbv_conj
      (qfbv_lneg
         (qfbv_saddo (qfbv_atomic a1)
                     (qfbv_atomic a2)))
      (qfbv_lneg
         (qfbv_saddo (qfbv_add (qfbv_atomic a1)
                               (qfbv_atomic a2))
                     (qfbv_atomic ac))) .

Definition bexp_atomic_subB_safe te a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 te in
  if Typ.is_unsigned a_typ then
    qfbv_lneg (qfbv_usubo (qfbv_atomic a1)
                          (qfbv_atomic a2))
  else
    qfbv_lneg (qfbv_ssubo (qfbv_atomic a1)
                          (qfbv_atomic a2)) .

Definition bexp_atomic_sbbB_safe  te a1 a2 ab : QFBV.bexp :=
  let 'a_typ := atyp a1 te in
  if Typ.is_unsigned a_typ then
    qfbv_conj
      (qfbv_lneg
         (qfbv_usubo (qfbv_atomic a1)
                     (qfbv_atomic a2)))
      (qfbv_lneg
         (qfbv_usubo (qfbv_sub (qfbv_atomic a1)
                               (qfbv_atomic a2))
                     (qfbv_atomic ab)))
  else
    qfbv_conj
      (qfbv_lneg
         (qfbv_ssubo (qfbv_atomic a1)
                     (qfbv_atomic a2)))
      (qfbv_lneg
         (qfbv_ssubo (qfbv_sub (qfbv_atomic a1)
                               (qfbv_atomic a2))
                     (qfbv_atomic ab))) .

Definition bexp_atomic_sbcB_safe  te a1 a2 ac : QFBV.bexp :=
  let 'a_typ := atyp a1 te in
  if Typ.is_unsigned a_typ then
    qfbv_conj
      (qfbv_lneg
         (qfbv_usubo (qfbv_atomic a1)
                     (qfbv_atomic a2)))
      (qfbv_lneg
         (qfbv_usubo (qfbv_sub (qfbv_atomic a1)
                               (qfbv_atomic a2))
                     (qfbv_sub (qfbv_one 1)
                               (qfbv_atomic ac))))
  else
    qfbv_conj
      (qfbv_lneg
         (qfbv_ssubo (qfbv_atomic a1)
                     (qfbv_atomic a2)))
      (qfbv_lneg
         (qfbv_ssubo (qfbv_sub (qfbv_atomic a1)
                               (qfbv_atomic a2))
                     (qfbv_sub (qfbv_one 1)
                               (qfbv_atomic ac)))) .

Definition bexp_atomic_mulB_safe te a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 te in
  if Typ.is_unsigned a_typ then
    qfbv_lneg (qfbv_umulo (qfbv_atomic a1)
                          (qfbv_atomic a2))
  else
    qfbv_lneg (qfbv_smulo (qfbv_atomic a1)
                          (qfbv_atomic a2)) .

Definition bexp_atomic_shlBn_safe te a n : QFBV.bexp :=
  let 'a_size := asize a te in
  qfbv_ult (qfbv_atomic a)
           (qfbv_shl (QFBV.Econst (from_nat 1 1))
                     (QFBV.Econst (from_nat (a_size - n) (a_size - n)))) .

Definition bexp_atomic_concatshl_safe te (a1 : atomic) a2 n  : QFBV.bexp :=
  let 'a_size := asize a2 te in
  qfbv_conj
    (qfbv_ule (qfbv_const n) (qfbv_const a_size))
    (bexp_atomic_shlBn_safe te a2 n) .

Definition bexp_atomic_vpc_safe te t a : QFBV.bexp :=
  let 'a_typ := atyp a te in
  let 'a_size := Typ.sizeof_typ a_typ in
  let 't_size := Typ.sizeof_typ t in
  if Typ.is_unsigned a_typ then
    if Typ.is_unsigned t then
      qfbv_ule (qfbv_const a_size)
               (qfbv_const t_size)
    else
      qfbv_ult (qfbv_const a_size)
               (qfbv_const t_size)
  else
    if Typ.is_unsigned t then
      qfbv_conj
        (qfbv_ule (qfbv_zero 1) (qfbv_atomic a))
        (qfbv_ule (qfbv_const a_size)
                  (qfbv_const (t_size + 1)))
    else
      qfbv_conj
        (qfbv_ule (qfbv_zero 1) (qfbv_atomic a))
        (qfbv_ule (qfbv_const a_size)
                  (qfbv_const t_size)) .
    
Definition bexp_instr_safe te (i : instr) : QFBV.bexp :=
  match i with
  | Iadd _ a1 a2 =>
    bexp_atomic_addB_safe te a1 a2
  | Iadc _ a1 a2 ac =>
    bexp_atomic_adcB_safe te a1 a2 ac
  | Isub _ a1 a2 =>
    bexp_atomic_subB_safe te a1 a2
  | Isbc _ a1 a2 ac =>
    bexp_atomic_sbcB_safe te a1 a2 ac
  | Isbb _ a1 a2 ab =>
    bexp_atomic_sbbB_safe te a1 a2 ab
  | Imul _ a1 a2 =>
    bexp_atomic_mulB_safe te a1 a2
  | Ishl v a n =>
    bexp_atomic_shlBn_safe te a n
  | Icshl h l a1 a2 n =>
    bexp_atomic_concatshl_safe te a1 a2 n
  | Ivpc _ t a =>
    bexp_atomic_vpc_safe te t a
  | Inop
  | Inondet _ _
  | Imov _ _
  | Icmov _ _ _ _
  | Iadds _ _ _ _
  | Iadcs _ _ _ _ _
  | Isubc _ _ _ _
  | Isubb _ _ _ _
  | Isbcs _ _ _ _ _
  | Isbbs _ _ _ _ _
  | Imull _ _ _ _
  | Imulj _ _ _
  | Inot _ _ _
  | Iand _ _ _ _
  | Ior _ _ _ _
  | Ixor _ _ _ _
  | Isplit _ _ _ _ 
  | Ijoin _ _ _
  | Icast _ _ _
  | Iassume _ => qfbv_true
  end .

Fixpoint bexp_program_safe te (p : program) : QFBV.bexp :=
  match p with
  | [::] => qfbv_true
  | hd::tl => qfbv_conj
                (bexp_instr_safe te hd)
                (bexp_program_safe (instr_succ_typenv hd te) tl)
  end .

Definition bexp_program_safe_at te (p : program) s : Prop :=
  eval_bexps_imp (bexp_program te p) s
                 (QFBV.eval_bexp (bexp_program_safe te p) s) .




Lemma eval_bexp_atomic_addB_safe te a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_addB_safe te a1 a2) s <->
  addB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) .
Proof .
  case Ht : (Typ.is_unsigned (atyp a1 te));
    rewrite /bexp_atomic_addB_safe /addB_safe Ht /= .
  - rewrite /uaddB_safe /= !eval_exp_atomic // .
  - rewrite /saddB_safe /= !eval_exp_atomic // .
Qed .

Lemma eval_bexp_atomic_adcB_safe te a1 a2 ac s :
  QFBV.eval_bexp (bexp_atomic_adcB_safe te a1 a2 ac) s <->
  adcB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s) .
Proof .
  case Ht : (Typ.is_unsigned (atyp a1 te));
    rewrite /bexp_atomic_adcB_safe /adcB_safe Ht /= .
  - rewrite /uadcB_safe /= !eval_exp_atomic // .
  - rewrite /sadcB_safe /= !eval_exp_atomic // .
Qed .

Lemma eval_bexp_atomic_subB_safe te a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_subB_safe te a1 a2) s <->
  subB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) .
Proof .
  case Ht : (Typ.is_unsigned (atyp a1 te));
    rewrite /bexp_atomic_subB_safe /subB_safe Ht /= .
  - rewrite /usubB_safe /= !eval_exp_atomic // .
  - rewrite /ssubB_safe /= !eval_exp_atomic // .
Qed .

Lemma eval_bexp_atomic_sbbB_safe te a1 a2 ac s :
  QFBV.eval_bexp (bexp_atomic_sbbB_safe te a1 a2 ac) s <->
  sbbB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s) .
Proof .
  case Ht : (Typ.is_unsigned (atyp a1 te));
    rewrite /bexp_atomic_sbbB_safe /sbbB_safe Ht /= .
  - rewrite /usbbB_safe /= !eval_exp_atomic // .
  - rewrite /ssbbB_safe /= !eval_exp_atomic // .
Qed .

Lemma eval_bexp_atomic_sbcB_safe te a1 a2 ac s :
  QFBV.eval_bexp (bexp_atomic_sbcB_safe te a1 a2 ac) s <->
  sbcB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s) .
Proof .
  case Ht : (Typ.is_unsigned (atyp a1 te));
    rewrite /bexp_atomic_sbcB_safe /sbcB_safe Ht /= .
  - rewrite /usbcB_safe /= !eval_exp_atomic // .
  - rewrite /ssbcB_safe /= !eval_exp_atomic // .
Qed .

Lemma eval_bexp_atomic_mulB_safe te a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_mulB_safe te a1 a2) s <->
  mulB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) .
Proof .
  case Ht : (Typ.is_unsigned (atyp a1 te));
    rewrite /bexp_atomic_mulB_safe /mulB_safe Ht /= .
  - rewrite /umulB_safe /= !eval_exp_atomic // .
  - rewrite /smulB_safe /= !eval_exp_atomic // .
Qed .

Lemma eval_bexp_atomic_shlBn_safe te a n s :
  SSAVS.subset (vars_atomic a) (vars_env te) ->
  SSAStore.conform s te ->
  QFBV.eval_bexp (bexp_atomic_shlBn_safe te a n) s <->
  shlBn_safe (atyp a te) (eval_atomic a s) n .
Proof .
  (*
  rewrite /bexp_atomic_shlBn_safe /shlBn_safe /= => Hsub Hcon .
  rewrite !eval_exp_atomic from_nat_simple // .
  rewrite (eqP (conform_size_eval_atomic Hsub Hcon)) // .
   *)
Admitted.

Lemma eval_bexp_atomic_concatshl_safe te a1 a2 n s :
  SSAVS.subset (vars_atomic a2) (vars_env te) ->
  SSAStore.conform s te ->
  QFBV.eval_bexp (bexp_atomic_concatshl_safe te a1 a2 n) s <->
  cshlBn_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) n .
Proof .
  (*
  rewrite /bexp_atomic_concatshl_safe /concatshl_safe /= => Hsub Hcon .
  rewrite !eval_exp_atomic
          (eqP (conform_size_eval_atomic Hsub Hcon))
          leBNlt ltB_to_nat !from_nat_simple
          -leqNgt // .
   *)
Admitted.

Lemma eval_bexp_atomic_vpc_safe te a t s :
  QFBV.eval_bexp (bexp_atomic_vpc_safe te t a) s <->
  vpc_safe t (atyp a te) (eval_atomic a s) .
Proof .
  (*
  rewrite /bexp_atomic_vpc_safe /vpc_safe  /= .
  case Ha : (Typ.is_unsigned (atyp a te));
  case Ht : (Typ.is_unsigned t) => /=;
  [ done 
  | done
  | rewrite !eval_exp_atomic //
  | rewrite !eval_exp_atomic // ] .
   *)
Admitted.

Lemma eval_bexp_instr_safe te i s :
  well_formed_instr te i ->
  SSAStore.conform s te ->
  (QFBV.eval_bexp (bexp_instr_safe te i) s <->
   ssa_instr_safe_at te i s) .
Proof .
  move => /andP [Hdef _] Hcon .
  move : Hdef; case i => /=; try done .
  - move => v a n /are_defined_subset Hsub .
    apply : (eval_bexp_atomic_shlBn_safe _ Hsub Hcon) .
  - move => h l a1 a2 n /andP [/andP [_ _] /are_defined_subset Hsub] .
    apply : (eval_bexp_atomic_concatshl_safe _ _ Hsub Hcon) .
  - move => v a1 a2 _ .
    apply : eval_bexp_atomic_addB_safe .
  - move => v a1 a2 ac _ .
    apply : eval_bexp_atomic_adcB_safe .
  - move => v a1 a2 _ .
    apply : eval_bexp_atomic_subB_safe .
  - move => v a1 a2 ac _ .
    apply : eval_bexp_atomic_sbcB_safe .
  - move => v a1 a2 ac _ .
    apply : eval_bexp_atomic_sbbB_safe .
  - move => v a1 a2 _ .
    apply : eval_bexp_atomic_mulB_safe .
  - move => v t a _ .    
    apply : eval_bexp_atomic_vpc_safe .
Qed .

Lemma unchanged_instr_eval_instr te i a s1 s2 :
  ssa_vars_unchanged_instr (vars_atomic a) i ->
  eval_instr te i s1 s2 ->
  eval_atomic a s1 = eval_atomic a s2 .
Proof .
  case a => // .
  case i => /=;
  [ move => u b v Hun Hev
  | move => u b n v Hun Hev
  | move => u w b0 b1 n v Hun Hev
  | move => u t v Hun Hev
  | move => u b0 b1 bc v Hun Hev
  | move => v Hun Hev
  | move => u ty b v Hun Hev
  | move => u b0 b1 v Hun Hev
  | move => u w b0 b1 v Hun Hev
  | move => u b0 b1 bc v Hun Hev
  | move => u w b0 b1 bc v Hun Hev
  | move => u b0 b1 v Hun Hev
  | move => u w b0 b1 v Hun Hev
  | move => u w b0 b1 v Hun Hev
  | move => u b0 b1 bc v Hun Hev
  | move => u w b0 b1 bc v Hun Hev
  | move => u b0 b1 bc v Hun Hev
  | move => u w b0 b1 bc v Hun Hev
  | move => u b0 b1 v Hun Hev
  | move => u w b0 b1 v Hun Hev
  | move => u b0 b1 v Hun Hev
  | move => u w b n v Hun Hev
  | move => u w b0 b1 v Hun Hev
  | move => u ty b0 b1 v Hun Hev
  | move => u ty b0 b1 v Hun Hev
  | move => u ty b0 v Hun Hev
  | move => u ty b0 v Hun Hev
  | move => u b0 b1 v Hun Hev
  | move => e u Hun Hev ];
    move : (ssa_unchanged_instr_singleton1 Hun) => {Hun} Hun;
    apply : (acc_unchanged_instr Hun Hev) .
Qed .

Lemma eval_bexp_instr_safe_succ te i s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr i) i ->
  eval_instr te i s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s1 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s2 .
Proof .
  case i => /=; try trivial .
  - move => v a n Hun Hev .
    rewrite !eval_exp_atomic .
    rewrite (unchanged_instr_eval_instr Hun Hev) // .
  - move => u v a0 a1 n Hun Hev .
    rewrite !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [_ Hun] .
    rewrite (unchanged_instr_eval_instr Hun Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite /bexp_atomic_addB_safe .
    rewrite !eval_bexp_if => /= .
    rewrite !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite !(unchanged_instr_eval_instr Hun0 Hev)
            !(unchanged_instr_eval_instr Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite /bexp_atomic_adcB_safe !eval_bexp_if => /= .
    rewrite !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun1 Hunc] .
    rewrite !(unchanged_instr_eval_instr Hun0 Hev)
            !(unchanged_instr_eval_instr Hun1 Hev)
            !(unchanged_instr_eval_instr Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite /bexp_atomic_subB_safe !eval_bexp_if => /= .
    rewrite !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun0 Hun1] .
    rewrite !(unchanged_instr_eval_instr Hun0 Hev)
            !(unchanged_instr_eval_instr Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite /bexp_atomic_sbcB_safe !eval_bexp_if => /= .
    rewrite !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun1 Hunc] .
    rewrite !(unchanged_instr_eval_instr Hun0 Hev)
            !(unchanged_instr_eval_instr Hun1 Hev)
            !(unchanged_instr_eval_instr Hunc Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite /bexp_atomic_sbbB_safe !eval_bexp_if => /= .
    rewrite !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun1 Hunc] .
    rewrite !(unchanged_instr_eval_instr Hun0 Hev)
            !(unchanged_instr_eval_instr Hun1 Hev)
            !(unchanged_instr_eval_instr Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite /bexp_atomic_mulB_safe !eval_bexp_if => /= .
    rewrite !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) =>
    {Hun} [Hun0 Hun1] .
    rewrite !(unchanged_instr_eval_instr Hun0 Hev)
            !(unchanged_instr_eval_instr Hun1 Hev) // .
  - move => v t a Hun Hev .
    rewrite /bexp_atomic_vpc_safe !eval_bexp_if => /= .
    rewrite !eval_exp_atomic .
    rewrite !(unchanged_instr_eval_instr Hun Hev) // .
Qed .

Lemma eval_bexp_instr_safe_succs te i p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr i) p ->
  eval_program te p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s1 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s2 .
Proof .
  case i; rewrite /bexp_instr_safe => // .
  - move => v a n Hun Hev .
    rewrite /= !eval_exp_atomic .
    rewrite (ssa_unchanged_program_eval_atomic Hun Hev) // .
  - move => u v a0 a1 n Hun Hev .
    rewrite /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite (ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v ty a Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    rewrite (ssa_unchanged_program_eval_atomic Hun Hev) // .
Qed .    

Lemma eval_bexp_instr_safe_pred te i s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr i) i ->
  eval_instr te i s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s2 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s1 .
Proof .
  case i => // .
  - move => v a n Hun Hev .
    rewrite /= !eval_exp_atomic .
    rewrite (unchanged_instr_eval_instr Hun Hev) // .
  - move => u v a0 a1 n Hun Hev .
    rewrite /= !eval_exp_atomic .
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite (unchanged_instr_eval_instr Hun1 Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic . 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic . 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev)
            (unchanged_instr_eval_instr Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic . 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic . 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev)
            (unchanged_instr_eval_instr Hunc Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic . 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev)
            (unchanged_instr_eval_instr Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic . 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev) // .
  - move => v ty a Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    rewrite (unchanged_instr_eval_instr Hun Hev) // .
Qed .

Lemma eval_bexp_instr_safe_preds te i p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr i) p ->
  eval_program te p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s2 ->
  QFBV.eval_bexp (bexp_instr_safe te i) s1 .
Proof .
  case i; rewrite /bexp_instr_safe => // .
  - move => v a n Hun Hev .
    rewrite /= !eval_exp_atomic .
    rewrite (ssa_unchanged_program_eval_atomic Hun Hev) // .
  - move => u v a0 a1 n Hun Hev .
    rewrite /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite (ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) // .
  - move => v a0 a1 ac Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun] .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) // .
  - move => v a0 a1 Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1] .
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) // .
  - move => v ty a Hun Hev .
    rewrite !eval_bexp_if /= !eval_exp_atomic .
    rewrite (ssa_unchanged_program_eval_atomic Hun Hev) // .
Qed .

(*

Lemma eval_bexp_program_safe1 te pre p :
  ssa_vars_unchanged_program (vars_rbexp pre) p ->
  well_formed_ssa_program te p ->
  (forall s, SSAStore.conform s te ->
             QFBV.eval_bexp (bexp_rbexp pre) s ->
             eval_bexps_conj (bexp_program te p) s ->
             QFBV.eval_bexp (bexp_program_safe te p) s) ->
  (forall s, SSAStore.conform s te ->
             eval_rbexp pre s ->
             zssa_program_safe_at te p s) .
Proof .
  elim : p te => /= .
  - move => te _ _ H s Hcon Hpre .
    apply zssa_program_safe_at_nil .
  - move => hd tl IH te Hun Hwf H s Hcon Hpre .
    move : (eval_bexp_rbexp2 Hpre) => {Hpre} Hpre .
    move : (ssa_unchanged_program_cons1 Hun) => {Hun} [Hunhd Huntl] .
    move : (well_formed_ssa_tl Hwf) => Hwftl .
    move : (IH _ Huntl Hwftl) => Htl .
    move : (H s Hcon Hpre) => H1 .
    apply : zssa_program_safe_at_cons .
    
    Check (H s) .
  Check (ssa_unchanged_program_eval_rbexp1 Hun) .
 *)

(* TODO: move elsewhere *)
Definition ssa_spec_safe_qfbv sp : Prop :=
  forall s,
    QFBV.eval_bexp (bexp_rbexp (rng_bexp (spre sp))) s ->
    eval_bexps_conj (bexp_program (sinputs sp) (sprog sp)) s ->
    QFBV.eval_bexp (bexp_program_safe (sinputs sp) (sprog sp)) s .
