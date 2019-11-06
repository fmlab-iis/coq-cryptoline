
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var.
From BitBlasting Require Import State QFBV.
From Cryptoline Require Import DSL SSA.
From nbits Require Import NBits. 

Import SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition qfbv_atomic a :=
  match a with
  | SSA.Avar v => QFBV.Evar v
  | SSA.Aconst ty n => QFBV.Econst n
  end .

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
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qerext := qfbv_add qe1ext qe2ext in
    qfbv_conj
      (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
      (qfbv_eq (qfbv_var v) (qfbv_low (SSA.asize a1 te) qerext))
  (* Iadc (v, a1, a2, y): v = a1 + a2 + y, overflow is forbidden *)
  | SSA.Iadc v a1 a2 y =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qeyext := qfbv_zext (SSA.asize a1 te - 1) (qfbv_atomic y) in
    qfbv_eq (qfbv_var v)
            (qfbv_add (qfbv_add qe1 qe2) qeyext)
  (* Iadcs (c, v, a1, a2, y): v = a1 + a2 + y, c = carry flag *)
  | SSA.Iadcs c v a1 a2 y =>
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext (SSA.asize a1 te) (qfbv_atomic y) in
    let 'qerext := qfbv_add (qfbv_add qe1ext qe2ext) qeyext in
    qfbv_conj (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v) (qfbv_low (SSA.asize a1 te) qerext))
  (* Isub (v, a1, a2): v = a1 - a2, overflow is forbidden *)
  | SSA.Isub v a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    qfbv_eq (qfbv_var v) (qfbv_sub qe1 qe2)
  (* Isubb (b, v, a1, a2): v = a1 - a2, b = borrow flag *)
  | SSA.Isubb b v a1 a2 =>
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qerext := qfbv_sub qe1ext qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v)
                       (qfbv_low (SSA.asize a1 te) qerext))
  (* Isubc (c, v, a1, a2): v = a1 + not(a2) + 1, c = carry flag *)
  | SSA.Isubc c v a1 a2 =>
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qerext := qfbv_sub qe1ext qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var c)
                       (qfbv_sub (qfbv_const 1) (qfbv_high 1 qerext)))
              (qfbv_eq (qfbv_var v)
                       (qfbv_low (SSA.asize a1 te) qerext))
  (* Isbb (v, a1, a2, y): v = a1 - a2 - y *)
  | SSA.Isbb v a1 a2 y =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qeyext := qfbv_zext (SSA.asize a1 te - 1) (qfbv_atomic y) in
    qfbv_eq (qfbv_var v) (qfbv_sub (qfbv_sub qe1 qe2) qeyext)
  (* Isbbs (b, v, a1, a2, y): v = a1 - a2 - y, b = borrow flag *)
  | SSA.Isbbs b v a1 a2 y =>
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext (SSA.asize a1 te) (qfbv_atomic y) in
    let 'qerext := qfbv_sub (qfbv_sub qe1ext qe2ext) qeyext in
    qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v) (qfbv_low (SSA.asize a1 te) qerext))
  (* Isbc (v, a1, a2, y): v = a1 + not(a2) + y *)
  | SSA.Isbc v a1 a2 y =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qez := qfbv_sub (qfbv_const 1) (qfbv_atomic y) in
    qfbv_eq (qfbv_var v) (qfbv_sub (qfbv_sub qe1 qe2)
                                    (qfbv_zext (SSA.asize a1 te - 1) qez))
  (* Isbcs (c, v, a1, a2, y): v = a1 + not(a2) + y, c = carry flag *)
  | SSA.Isbcs c v a1 a2 y =>
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qez := qfbv_sub (qfbv_const 1) (qfbv_atomic y) in
    let 'qerext := qfbv_sub (qfbv_sub qe1ext qe2ext)
                            (qfbv_zext (SSA.asize a1 te) qez) in
    qfbv_conj (qfbv_eq (qfbv_var c)
                       (qfbv_sub (qfbv_const 1) (qfbv_high 1 qerext)))
              (qfbv_eq (qfbv_var v) (qfbv_low (SSA.asize a1 te) qerext))
  (* Imul (v, a1, a2): v = a1 * a2, overflow is forbidden *)
  | SSA.Imul v a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    qfbv_eq (qfbv_var v) (qfbv_mul qe1 qe2)
  (* Imull (vh, vl, a1, a2): vh and vl are respectively the high part and
     the low part of the full multiplication a1 * a2 *)
  | SSA.Imull vh vl a1 a2 =>
    let 'qe1ext := qfbv_zext (SSA.asize a1 te) (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext (SSA.asize a1 te) (qfbv_atomic a2) in
    let 'qerext := qfbv_mul qe1ext qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var vh)
                       (qfbv_high (SSA.asize a1 te) qerext))
              (qfbv_eq (qfbv_var vl)
                       (qfbv_low (SSA.asize a1 te) qerext))
  (* Iumulj (v, a1, a2): v = the full multiplication of a1 * a2, which is equivalent
     to Iumull (vh, vl, a1, a2); Join (r, vh, vl) *)
  | SSA.Imulj v a1 a2 =>
    let 'qe1ext := qfbv_zext (SSA.asize a1 te) (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext (SSA.asize a1 te) (qfbv_atomic a2) in
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
    let 'qea := qfbv_atomic a in
    let 'qel := qfbv_low n qea in
    let 'qeh := qfbv_high (SSA.asize a te - n) qea in
    qfbv_conj (qfbv_eq (qfbv_var vh)
                       (qfbv_zext (TypEnv.SSATE.vsize vh te - (SSA.asize a te) + n) qeh))
              (qfbv_eq (qfbv_var vl)
                       (qfbv_zext (TypEnv.SSATE.vsize vl te - n) qel))
  (* Icshl (vh, vl, a1, a2, n) *)
  | SSA.Icshl vh vl a1 a2 n =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qer := qfbv_shl (qfbv_concat qe1 qe2) (qfbv_const n) in
    let 'qel := qfbv_low (TypEnv.SSATE.vsize vl te) qer in
    let 'qeh := qfbv_extr (TypEnv.SSATE.vsize vl te)
                          (TypEnv.SSATE.vsize vl te + TypEnv.SSATE.vsize vh te - 1) qer in
    qfbv_conj (qfbv_eq (qfbv_var vh) qeh)
              (qfbv_eq (qfbv_var vl) qel)
  (* Inot (v, t, a): v = not(a), the one's complement of a, v is of type t *)
  | SSA.Inot v t a =>
    let 'qea := qfbv_atomic a in
    qfbv_eq (qfbv_var v) qea
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
  (*
  (* == Instructions that cannot be translated to polynomials == *)
  (* == Type conversions == *)
  (* Icast (v, t, a): v = the value of a represented by the type t of v *)
  | SSA.Icast v t a
  (* Ivpc (v, t, a): v = a, value preserved casting to type t *)
  | SSA.Ivpc v t a
  (* Specifications *)
  | SSA.Iassume : bexp -> instr
 *)
  | _ => QFBV.Bfalse
  end .

Definition bexp_program te (p : program) : seq QFBV.bexp :=
  map (bexp_instr te) p.

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

Record bexp_spec : Type :=
  mkQFBVSpec { bpre : QFBV.bexp;
               bprog : seq QFBV.bexp;
               bpost : QFBV.bexp } .

Definition bexp_of_rspec te (s : rspec) : bexp_spec :=
  {| bpre := bexp_rbexp (rspre s);
     bprog := bexp_program te (rsprog s);
     bpost := bexp_rbexp (rspost s) |}.

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

(* Define the safety condition in terms of a QFBV expression *)
(* TODO: see bexp_program_safe in certified_qhasm_vcg/mqhasm/bvSSA2QFBV.v *)
Definition bexp_program_safe (p : program) : QFBV.bexp := QFBV.Btrue.


