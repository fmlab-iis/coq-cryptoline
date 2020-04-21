
From Coq Require Import Arith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun prime.
From ssrlib Require Import Var Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv.
From Cryptoline Require Import DSL SSA SSA2ZSSA.
From nbits Require Import NBits.

(** Conversion from range specifications and safety conditions to QFBV expressions *)

Import SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* auxiliary lemmas *)

Lemma from_nat_simple :
  forall n, to_nat (NBitsDef.from_nat (trunc_log 2 n).+1 n) = n.
Proof.
  move => n.
  rewrite to_nat_from_nat_bounded; first done.
  by apply : trunc_log_ltn.
Qed.

Ltac rewrite_from_nat_simple :=
  repeat
  match goal with
  | H : context f [(nat_of_bool (odd ?n) +
                    (to_nat (trunc_log 2 ?n) -bits of (?n./2)).*2)%bits]
    |- _ =>
    let Hn := fresh in
    move: (from_nat_simple n) => Hn; rewrite /= in Hn; rewrite Hn in H; clear Hn
  | |- context f [(nat_of_bool (odd ?n) +
                   (to_nat (trunc_log 2 ?n) -bits of (?n./2)).*2)%bits] =>
    let Hn := fresh in
    move: (from_nat_simple n) => Hn; rewrite /= in Hn; rewrite Hn; clear Hn
  end.

(*
Lemma size0 (bs : bitseq) :
  size bs == 0 -> bs == [::].
Proof.
  case : bs; done.
Qed.
 *)

Lemma to_bool_bit_is_true :
  forall bs,
    size bs = 1 ->
    to_bool bs ->
    [:: true] == bs.
Proof.
  move => bs Hs1.
  move : (size1 Hs1).
  elim => Hbs; rewrite (eqP Hbs); done.
Qed.

Lemma not_to_bool_bit_is_false :
  forall bs,
    size bs = 1 ->
    ~~ to_bool bs ->
    [:: false] == bs.
Proof.
  move => bs Hs1.
  move : (size1 Hs1).
  elim => Hbs; rewrite (eqP Hbs); done.
Qed.

Lemma addB_nat p1 p2 :
  addB p1 p2 =
  from_nat (size (addB p1 p2)) (to_nat p1 + to_nat p2).
Proof.
  by rewrite /addB adcB_nat size_from_nat.
Qed.

Lemma to_nat_zext_bool n bs :
  size bs = 1 -> to_nat (zext n bs) == to_bool bs.
Proof.
  move => Hsz1; elim (size1 Hsz1); case => /eqP -> /=;
    by rewrite to_nat_zeros /=.
Qed.

Lemma from_nat_idem m n0 n1 n2 :
  from_nat m (n0 + n1 + n2) ==
  from_nat m (to_nat (from_nat m (n0 + n1)) + n2).
Proof.
  elim : m n0 n1 n2; first done.
  move => m IH n0 n1 n2.
  rewrite to_nat_from_nat.
  move : (div.divn_eq (n0 + n1) (2 ^ m.+1)) => Hmod.
  rewrite (addnC (div.modn (n0 + n1) (2 ^ m.+1)) n2).
  rewrite (from_nat_wrapMany (m.+1)
                             (div.divn (n0 + n1) (2 ^ m.+1))
                             (n2 + div.modn (n0 + n1) (2 ^ m.+1))).
  rewrite -(addnA n2 _ _) (addnC (div.modn (n0 + n1) (2 ^ m.+1)) _).
  rewrite -Hmod.
  rewrite (addnA n2) (addnC n2).
  rewrite -(addnA n0 n2) (addnC n2) (addnA n0 n1).
  done.
Qed.

Lemma atyp_asize E a0 a1 :
  atyp a0 E = atyp a1 E -> asize a0 E == asize a1 E.
Proof.
  rewrite /asize. by move=> ->.
Qed.


(*
Lemma adcB_addB bsc bs0 bs1 :
  size bsc == 1 ->
  size bs0 == size bs1 ->
  (adcB (to_bool bsc) bs0 bs1).2 ==
  (zext (size bs0) bsc +# bs0 +# bs1)%bits.
Proof.
  move => Hszc Hszeq.
  rewrite adcB_nat addB_nat.
  rewrite !size_addB size_adcB size_zext /=.
  move : (leq_addl (size bsc) (size bs0)) => /minn_idPr ->.
  rewrite addB_nat size_addB size_zext /=.
  move : (leq_addl (size bsc) (size bs0)) => /minn_idPr ->.
  rewrite -!(eqP Hszeq) /=.
  move : (leqnn (size bs0)) => /minn_idPl ->.
  rewrite (eqP (to_nat_zext_bool _ Hszc)).
  apply from_nat_idem.
Qed.
*)

Lemma eval_exp_if s b qfbv0 qfbv1 :
  QFBV.eval_exp (if b then qfbv0 else qfbv1) s =
  if b then QFBV.eval_exp qfbv0 s else QFBV.eval_exp qfbv1 s.
Proof.
  case b => /=; done.
Qed.

Lemma eval_bexp_if s b qfbv0 qfbv1 :
  QFBV.eval_bexp (if b then qfbv0 else qfbv1) s =
  if b then QFBV.eval_bexp qfbv0 s else QFBV.eval_bexp qfbv1 s.
Proof.
  case b => /=; done.
Qed.

Lemma not_mem_add x y s :
  ~~ SSAVS.mem x (SSAVS.add y s) ->
  x != y /\ ~~ SSAVS.mem x s.
Proof.
  move=> H. move: (SSAVS.Lemmas.not_mem_add1 H) => [/negP H1 H2]. done.
Qed.


(* bvs_eqi and QFBV.eval_exp, QFBV.eval_bexp *)

Lemma bvs_eqi_qfbv_eval_exp E e s1 s2 :
  are_defined (QFBV.vars_exp e) E -> bvs_eqi E s1 s2 ->
  QFBV.eval_exp e s1 = QFBV.eval_exp e s2
with
bvs_eqi_qfbv_eval_bexp E e s1 s2 :
  are_defined (QFBV.vars_bexp e) E -> bvs_eqi E s1 s2 ->
  QFBV.eval_bexp e s1 = QFBV.eval_bexp e s2.
Proof.
  (* bvs_eqi_qfbv_eval_eexp *)
  case: e => //=.
  - move=> x Hdef Heqi. rewrite are_defined_singleton in Hdef.
    move/memdefP: Hdef => Hmem. exact: (Heqi x Hmem).
  - move=> op e Hdef Heqi. rewrite (bvs_eqi_qfbv_eval_exp _ _ _ _ Hdef Heqi).
    reflexivity.
  - move=> op e1 e2 Hdef Heqi. rewrite are_defined_union in Hdef.
    move/andP: Hdef=> [Hdef1 Hdef2].
    rewrite (bvs_eqi_qfbv_eval_exp _ _ _ _ Hdef1 Heqi)
            (bvs_eqi_qfbv_eval_exp _ _ _ _ Hdef2 Heqi). reflexivity.
  - move=> c e1 e2 Hdef Heqi. rewrite !are_defined_union in Hdef.
    move/andP: Hdef=> [Hdefc /andP [Hdef1 Hdef2]].
    rewrite (bvs_eqi_qfbv_eval_exp _ _ _ _ Hdef1 Heqi)
            (bvs_eqi_qfbv_eval_exp _ _ _ _ Hdef2 Heqi).
    rewrite (bvs_eqi_qfbv_eval_bexp _ _ _ _ Hdefc Heqi). reflexivity.
  (* bvs_eqi_qfbv_eval_bexp *)
  case: e => //=.
  - move=> op e1 e2 Hdef Heqi. rewrite are_defined_union in Hdef.
    move/andP: Hdef=> [Hdef1 Hdef2].
    rewrite (bvs_eqi_qfbv_eval_exp _ _ _ _ Hdef1 Heqi)
            (bvs_eqi_qfbv_eval_exp _ _ _ _ Hdef2 Heqi). reflexivity.
  - move=> e Hdef Heqi. rewrite (bvs_eqi_qfbv_eval_bexp _ _ _ _ Hdef Heqi).
    reflexivity.
  - move=> e1 e2 Hdef Heqi. rewrite are_defined_union in Hdef.
    move/andP: Hdef=> [Hdef1 Hdef2].
    rewrite (bvs_eqi_qfbv_eval_bexp _ _ _ _ Hdef1 Heqi)
            (bvs_eqi_qfbv_eval_bexp _ _ _ _ Hdef2 Heqi). reflexivity.
  - move=> e1 e2 Hdef Heqi. rewrite are_defined_union in Hdef.
    move/andP: Hdef=> [Hdef1 Hdef2].
    rewrite (bvs_eqi_qfbv_eval_bexp _ _ _ _ Hdef1 Heqi)
            (bvs_eqi_qfbv_eval_bexp _ _ _ _ Hdef2 Heqi). reflexivity.
Qed.


(* Conversion from from rbexp to QFBV.bexp *)

Definition qfbv_atomic a :=
  match a with
  | SSA.Avar v => QFBV.Evar v
  | SSA.Aconst ty n => QFBV.Econst n
  end.

Definition qfbv_true := QFBV.Btrue.

Definition qfbv_false := QFBV.Bfalse.

Definition qfbv_var v := QFBV.Evar v.

Definition qfbv_const n :=
  QFBV.Econst (NBitsDef.from_nat (trunc_log 2 n).+1 n).

Definition qfbv_zero w := QFBV.Econst (NBitsDef.from_nat w 0).

Definition qfbv_one w := QFBV.Econst (NBitsDef.from_nat w 1).

Definition qfbv_not qe := QFBV.Eunop QFBV.Unot qe.

Definition qfbv_neg qe := QFBV.Eunop QFBV.Uneg qe.

Definition qfbv_extr i j qe := QFBV.Eunop (QFBV.Uextr i j) qe.

Definition qfbv_high n qe := QFBV.Eunop (QFBV.Uhigh n) qe.

Definition qfbv_low n qe := QFBV.Eunop (QFBV.Ulow n) qe.

Definition qfbv_zext n qe := QFBV.Eunop (QFBV.Uzext n) qe.

Definition qfbv_sext n qe := QFBV.Eunop (QFBV.Usext n) qe.

Definition qfbv_and qe0 qe1 := QFBV.Ebinop QFBV.Band qe0 qe1.

Definition qfbv_or qe0 qe1 := QFBV.Ebinop QFBV.Bor qe0 qe1.

Definition qfbv_xor qe0 qe1 := QFBV.Ebinop QFBV.Bxor qe0 qe1.

Definition qfbv_add qe0 qe1 := QFBV.Ebinop QFBV.Badd qe0 qe1.

Definition qfbv_sub qe0 qe1 := QFBV.Ebinop QFBV.Bsub qe0 qe1.

Definition qfbv_mul qe0 qe1 := QFBV.Ebinop QFBV.Bmul qe0 qe1.

Definition qfbv_mod qe0 qe1 := QFBV.Ebinop QFBV.Bmod qe0 qe1.

Definition qfbv_srem qe0 qe1 := QFBV.Ebinop QFBV.Bsrem qe0 qe1.

Definition qfbv_smod qe0 qe1 := QFBV.Ebinop QFBV.Bsmod qe0 qe1.

Definition qfbv_shl qe0 qe1 := QFBV.Ebinop QFBV.Bshl qe0 qe1.

Definition qfbv_lshr qe0 qe1 := QFBV.Ebinop QFBV.Blshr qe0 qe1.

Definition qfbv_ashr qe0 qe1 := QFBV.Ebinop QFBV.Bashr qe0 qe1.

Definition qfbv_concat qe0 qe1 := QFBV.Ebinop QFBV.Bconcat qe0 qe1.

Definition qfbv_eq qe0 qe1 := QFBV.Bbinop QFBV.Beq qe0 qe1.

Definition qfbv_ult qe0 qe1 := QFBV.Bbinop QFBV.Bult qe0 qe1.

Definition qfbv_ule qe0 qe1 := QFBV.Bbinop QFBV.Bule qe0 qe1.

Definition qfbv_ugt qe0 qe1 := QFBV.Bbinop QFBV.Bugt qe0 qe1.

Definition qfbv_uge qe0 qe1 := QFBV.Bbinop QFBV.Buge qe0 qe1.

Definition qfbv_slt qe0 qe1 := QFBV.Bbinop QFBV.Bslt qe0 qe1.

Definition qfbv_sle qe0 qe1 := QFBV.Bbinop QFBV.Bsle qe0 qe1.

Definition qfbv_sgt qe0 qe1 := QFBV.Bbinop QFBV.Bsgt qe0 qe1.

Definition qfbv_sge qe0 qe1 := QFBV.Bbinop QFBV.Bsge qe0 qe1.

Definition qfbv_uaddo qe0 qe1 := QFBV.Bbinop QFBV.Buaddo qe0 qe1.

Definition qfbv_usubo qe0 qe1 := QFBV.Bbinop QFBV.Busubo qe0 qe1.

Definition qfbv_umulo qe0 qe1 := QFBV.Bbinop QFBV.Bumulo qe0 qe1.

Definition qfbv_saddo qe0 qe1 := QFBV.Bbinop QFBV.Bsaddo qe0 qe1.

Definition qfbv_ssubo qe0 qe1 := QFBV.Bbinop QFBV.Bssubo qe0 qe1.

Definition qfbv_smulo qe0 qe1 := QFBV.Bbinop QFBV.Bsmulo qe0 qe1.

Definition qfbv_lneg qb := QFBV.Blneg qb.

Definition qfbv_conj qb0 qb1 := QFBV.Bconj qb0 qb1.

Definition qfbv_disj qb0 qb1 := QFBV.Bdisj qb0 qb1.

Definition qfbv_ite qb qe0 qe1 := QFBV.Eite qb qe0 qe1.

Definition qfbv_imp f g := qfbv_disj (qfbv_lneg f) g.

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
  end.

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
  end.


(* Properties of the conversion from rbexp to QFBV.bexp *)

Fixpoint qfbv_conjs es :=
  match es with
  | [::] => QFBV.Btrue
  | hd::tl => qfbv_conj hd (qfbv_conjs tl)
  end.

Lemma eval_qfbv_conjs_rcons es e s :
  QFBV.eval_bexp (qfbv_conjs (rcons es e)) s =
  QFBV.eval_bexp (qfbv_conjs es) s && QFBV.eval_bexp e s.
Proof.
  elim: es => [| h es IH] /=.
  - rewrite andbT. reflexivity.
  - rewrite -(@andbA _ _ (QFBV.eval_bexp e s)). rewrite -IH. reflexivity.
Qed.

Lemma eval_qfbv_conjs_cat es1 es2 s :
  QFBV.eval_bexp (qfbv_conjs (es1 ++ es2)) s =
  QFBV.eval_bexp (qfbv_conjs es1) s && QFBV.eval_bexp (qfbv_conjs es2) s.
Proof.
  elim: es1 es2 => [| e1 es1 IH] es2 //=.
  rewrite -(@andbA _ _ (QFBV.eval_bexp (qfbv_conjs es2) s)).
  rewrite -IH. reflexivity.
Qed.

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

Lemma vars_qfbv_atomic a :
  QFBV.vars_exp (qfbv_atomic a) = vars_atomic a.
Proof. by case: a. Qed.

Lemma eval_exp_rexp (e : SSA.rexp) s:
  QFBV.eval_exp (exp_rexp e) s = eval_rexp e s.
Admitted.
(* TODO: wait for the mod, smod, srem
Proof.
  elim: e => /=.
  - reflexivity.
  - reflexivity.
  - move=> w op e IH;
             case : op; rewrite /= IH; reflexivity.
  - move=> w op e0 IH0 e1 IH1.
    case : op; rewrite /=; rewrite IH0 IH1 //.
  - move => w e IH n; rewrite /= IH //.
  - move => w e IH n; rewrite /= IH //.
    
Qed.
 *)

Lemma eval_bexp_rbexp e s:
  QFBV.eval_bexp (bexp_rbexp e) s <-> eval_rbexp e s.
Proof.
  elim : e => /=.
  - done.
  - move => w e0 e1; split.
    + move => /eqP Heq; rewrite -!eval_exp_rexp Heq //.
    + move => Heq; rewrite !eval_exp_rexp Heq //.
  - move => w op e0 e1;
      elim : op => /=; rewrite -!eval_exp_rexp //.
  - move => e; elim => Hleft Hright; split.
    + move => /negP Hneg.
      red; move => Heval.
      move : (Hright Heval); done.
    + move => Heval.
      apply /negP; red; move => Hneg.
      move : (Hleft Hneg); done.
  - move => e0 IH0 e1 IH1; split.
    + move => /andP [Heval0 Heval1].
      tauto.
    + move => [Heval0 Heval1].
      elim IH0 => {IH0} _ IH0; elim IH1 => {IH1} _ IH1.
      rewrite (IH0 Heval0) (IH1 Heval1) //.
  - move => e0 IH0 e1 IH1; split.
    + move => /orP Hor.
      tauto.
    + move => Hor.
      elim IH0 => {IH0} _ IH0; elim IH1 => {IH1} _ IH1.
      elim Hor; move => He; apply /orP; tauto.
Qed.

Lemma eval_bexp_rbexp1 e s :
  QFBV.eval_bexp (bexp_rbexp e) s -> eval_rbexp e s.
Proof.
  move: (eval_bexp_rbexp e s) => [H1 H2]. exact: H1.
Qed.

Lemma eval_bexp_rbexp2 e s :
  eval_rbexp e s -> QFBV.eval_bexp (bexp_rbexp e) s.
Proof.
  move: (eval_bexp_rbexp e s) => [H1 H2]. exact: H2.
Qed.


(* Conversion from programs to QFBV.bexp *)

Definition bexp_instr (E : SSATE.env) (i : SSA.instr) : QFBV.bexp :=
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
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qerext := qfbv_add qe1ext qe2ext in
    qfbv_conj
      (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
      (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
    (*
    qfbv_conj
      (qfbv_eq (qfbv_var c)
               (qfbv_ite (qfbv_uaddo qe1 qe2) (qfbv_one 1) (qfbv_zero 1)))
      (qfbv_eq (qfbv_var v) (qfbv_add qe1 qe2))
     *)
  (* Iadc (v, a1, a2, y): v = a1 + a2 + y, overflow is forbidden *)
  | SSA.Iadc v a1 a2 y =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    qfbv_eq (qfbv_var v)
            (qfbv_low a_size (qfbv_add (qfbv_add qe1ext qe2ext) qeyext))
  (* Iadcs (c, v, a1, a2, y): v = a1 + a2 + y, c = carry flag *)
  | SSA.Iadcs c v a1 a2 y =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    let 'qerext := qfbv_add (qfbv_add qe1ext qe2ext) qeyext in
    qfbv_conj (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
  (* Isub (v, a1, a2): v = a1 - a2, overflow is forbidden *)
  | SSA.Isub v a1 a2 =>
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    qfbv_eq (qfbv_var v) (qfbv_sub qe1 qe2)
  (* Isubb (b, v, a1, a2): v = a1 - a2, b = borrow flag *)
  | SSA.Isubb b v a1 a2 =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qerext := qfbv_sub qe1ext qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v)
                       (qfbv_low a_size qerext))
  (* Isubc (c, v, a1, a2): v = a1 + not(a2) + 1, c = carry flag *)
  | SSA.Isubc c v a1 a2 =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2negext := qfbv_zext 1 (qfbv_neg (qfbv_atomic a2)) in
    let 'qerext := qfbv_add qe1ext qe2negext in
    qfbv_conj (qfbv_eq (qfbv_var c)
                       (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v)
                       (qfbv_low a_size qerext))
  (* Isbb (v, a1, a2, y): v = a1 - a2 - y *)
  | SSA.Isbb v a1 a2 y =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    qfbv_eq (qfbv_var v)
            (qfbv_low a_size (qfbv_sub (qfbv_sub qe1ext qe2ext) qeyext))
  (* Isbbs (b, v, a1, a2, y): v = a1 - a2 - y, b = borrow flag *)
  | SSA.Isbbs b v a1 a2 y =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2ext := qfbv_zext 1 (qfbv_atomic a2) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    let 'qerext := qfbv_sub (qfbv_sub qe1ext qe2ext) qeyext in
    qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
              (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
  (* Isbc (v, a1, a2, y): v = a1 + not(a2) + y *)
  | SSA.Isbc v a1 a2 y =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2notext := qfbv_zext 1 (qfbv_not (qfbv_atomic a2)) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    qfbv_eq (qfbv_var v)
            (qfbv_low a_size (qfbv_add (qfbv_add qe1ext qe2notext) qeyext))
  (* Isbcs (c, v, a1, a2, y): v = a1 + not(a2) + y, c = carry flag *)
  | SSA.Isbcs c v a1 a2 y =>
    let 'a_size := asize a1 E in
    let 'qe1ext := qfbv_zext 1 (qfbv_atomic a1) in
    let 'qe2notext := qfbv_zext 1 (qfbv_not (qfbv_atomic a2)) in
    let 'qeyext := qfbv_zext a_size (qfbv_atomic y) in
    let 'qerext := qfbv_add (qfbv_add qe1ext qe2notext) qeyext in
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
    let 'a1_size := asize a1 E in
    let 'a2_size := asize a2 E in
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
    let 'a_size := asize a1 E  in
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
    let 'a_size := asize a E in
    let 'qen := qfbv_const n in
    let 'qeamn := qfbv_const (a_size - n) in
    let 'qea := qfbv_atomic a in
    let 'qel := qfbv_lshr (qfbv_shl qea qeamn) qeamn in
    if Typ.is_unsigned (atyp a E) then
      qfbv_conj (qfbv_eq (qfbv_var vh)
                         (qfbv_lshr qea qen))
                (qfbv_eq (qfbv_var vl) qel)
    else
      qfbv_conj (qfbv_eq (qfbv_var vh)
                         (qfbv_ashr qea qen))
                (qfbv_eq (qfbv_var vl) qel)
  (* Icshl (vh, vl, a1, a2, n) *)
  | SSA.Icshl vh vl a1 a2 n =>
    let 'a1_size := asize a1 E in
    let 'a2_size := asize a2 E in
    let 'qe1 := qfbv_atomic a1 in
    let 'qe2 := qfbv_atomic a2 in
    let 'qer := qfbv_shl (qfbv_concat qe1 qe2) (qfbv_const n) in
    let 'qel := qfbv_low a2_size qer in
    let 'qeh := qfbv_high a1_size qer in
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
    let 'a_typ := atyp a E in
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
  end.

Fixpoint bexp_program E (p : program) : seq QFBV.bexp :=
  match p with
  | [::] => [::]
  | hd::tl => (bexp_instr E hd)::(bexp_program (instr_succ_typenv hd E) tl)
  end.

Record bexp_spec : Type :=
  mkQFBVSpec { bpre : QFBV.bexp;
               bprog : seq QFBV.bexp;
               bpost : QFBV.bexp }.

Definition bexp_of_rspec E (s : rspec) : bexp_spec :=
  {| bpre := bexp_rbexp (rspre s);
     bprog := bexp_program E (rsprog s);
     bpost := bexp_rbexp (rspost s) |}.


(* Properties of the conversion from programs to QFBV.bexp *)

Ltac rewrite_eval_exp_atomic :=
  repeat rewrite -> eval_exp_atomic in *.

Lemma bexp_instr_submap E1 E2 i :
  well_defined_instr E1 i -> TELemmas.submap E1 E2 ->
  bexp_instr E1 i = bexp_instr E2 i.
Proof.
    by (case: i => //=); (move=> * );
      repeat (match goal with
              | H : is_true (_ && _) |- _ =>
                let H1 := fresh in
                let H2 := fresh in
                move/andP: H => [H1 H2]
              | H1 : TELemmas.submap ?E1 ?E2,
                     H2 : is_true (are_defined (vars_atomic ?a) ?E1) |-
                context f [asize ?a ?E2] =>
                rewrite -(asize_submap H1 H2)
              | H1 : TELemmas.submap ?E1 ?E2,
                H2 : is_true (are_defined (vars_atomic ?a) ?E1) |-
                context f [atyp ?a ?E2] =>
                rewrite -(atyp_submap H1 H2)
              | |- ?e = ?e => reflexivity
              end).
Qed.

Lemma bexp_program_cons E i p :
  bexp_program E (i::p) = (bexp_instr E i)::(bexp_program (instr_succ_typenv i E) p).
Proof. reflexivity. Qed.

Lemma bexp_program_rcons E p i :
  bexp_program E (rcons p i) =
  rcons (bexp_program E p) (bexp_instr (program_succ_typenv p E) i).
Proof.
  elim: p E => [| hd tl IH] E //=. rewrite -IH. reflexivity.
Qed.

Lemma bexp_program_cat E p1 p2 :
  bexp_program E (p1 ++ p2) =
  bexp_program E p1 ++ bexp_program (program_succ_typenv p1 E) p2.
Proof.
  elim: p1 E p2 => [| hd tl IH] E p2 //=. rewrite -IH. reflexivity.
Qed.

Lemma eval_vars_unchanged_program_bexp_instr E i p s1 s2 :
  SSA.ssa_vars_unchanged_program (SSA.vars_instr i) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr E i) s1 ->
  QFBV.eval_bexp (bexp_instr E i) s2.
Proof.
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
     end in tac || idtac).
  - (* split *)
    move : H1; case (Typ.is_unsigned (atyp a E)) => /=;
    move: (ssa_unchanged_program_add1 H) => {H} [H1 H2];
    move: (ssa_unchanged_program_add1 H2) => {H2} [H2 H3];
    rewrite -!(acc_unchanged_program H2 H0)
            -!(acc_unchanged_program H1 H0);
    rewrite_eval_exp_atomic;
    rewrite -(ssa_unchanged_program_eval_atomic H3 H0);
    move => /andP [Hhi Hlo];
              apply /andP; split; done.
  - (* cast *)
    move : H1;
      case (Typ.is_unsigned (atyp a E)) => /=;
      case (Typ.sizeof_typ t0 == Typ.sizeof_typ (atyp a E)) => /=;
      [ idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /=
      | idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /= ];
      move: (ssa_unchanged_program_add1 H) => {H} [H H1];
      rewrite -!(acc_unchanged_program H H0);
      rewrite_eval_exp_atomic;
      rewrite -(ssa_unchanged_program_eval_atomic H1 H0) //.
  - (* vpc *)
    move : H1;
      case (Typ.is_unsigned (atyp a E)) => /=;
      case (Typ.sizeof_typ t0 == Typ.sizeof_typ (atyp a E)) => /=;
      [ idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /=
      | idtac
      | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /= ];
      move: (ssa_unchanged_program_add1 H) => {H} [H H1];
      rewrite -!(acc_unchanged_program H H0);
      rewrite_eval_exp_atomic;
      rewrite -(ssa_unchanged_program_eval_atomic H1 H0) //.
  - (* assume *)
    case : b H H1 => eb rb.
    rewrite /vars_bexp /= => Hun.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} Hun.
    rewrite (eval_bexp_rbexp rb s1) (eval_bexp_rbexp rb s2) => Hs1.
    elim Hun => {Hun} _ Hun.
    elim : (ssa_unchanged_program_eval_rbexp Hun H0) => Hs1s2 _.
    by apply : Hs1s2.
Qed.

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
  end.

Ltac not_mem_rewrite_vtyp :=
  match goal with
  | Hnmem : is_true (~~ SSAVS.mem ?v (SSAVS.singleton ?u))
    |- _ =>
    move : (SSAVS.Lemmas.not_mem_singleton1 Hnmem) => {Hnmem} /negP Hnmem;
    rewrite !SSATE.vtyp_add_neq //
  | Hnmem : is_true (~~ SSAVS.mem ?v (SSAVS.add ?u (SSAVS.singleton ?w)))
    |- _ =>
    let Hneq := fresh in
    let H := fresh in
    move : (not_mem_add Hnmem) => {Hnmem} [Hneq H];
    move : (SSAVS.Lemmas.not_mem_singleton1 H) => {H} /negP H;
    rewrite !SSATE.vtyp_add_neq //
  | _ => idtac
  end.

Lemma atyp_well_defined_unchanged E i a :
  well_defined_instr E i ->
  ssa_vars_unchanged_instr (vars_env E) i ->
  SSAVS.subset (vars_atomic a) (rvs_instr i) ->
  atyp a (instr_succ_typenv i E) = atyp a E.
Proof.
  elim a; last (case i => /=; done).
  move => v; case i => /=.
  - move => u a0.
    rewrite are_defined_subset_env.
    move => Ha0te Hun Hva0.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 n.
    rewrite are_defined_subset_env.
    move => Ha0te Hun Hva0.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => vh vl a0 a1 n.
    rewrite 2!are_defined_subset_env.
    move => /andP [/andP [_ Hdef0] Hdef1] Hun Hva0a1.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - done.
  - move => u ac a0 a1.
    rewrite 3!are_defined_subset_env.
    move => /andP [/andP [Hdefc Hdef0] Hdef1] Hun Hvaca0a1.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - done.
  - move => u t a0.
    rewrite are_defined_subset_env.
    move => Hdef Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [/andP [_ Hdef0] Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1 ac.
    rewrite 3!are_defined_subset_env.
    move => /andP [/andP [Hdefc Hdef0] Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1 ac.
    rewrite 3!are_defined_subset_env.
    move => /andP [/andP [/andP [_ Hdef0] Hdef1] Hdefc] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [/andP [_ Hdef0] Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [/andP [_ Hdef0] Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1 ac.
    rewrite 3!are_defined_subset_env.
    move => /andP [/andP [Hdef0 Hdef1] Hdefc] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1 ac.
    rewrite 3!are_defined_subset_env.
    move => /andP [/andP [/andP [_ Hdef0] Hdef1] Hdefc] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1 ac.
    rewrite 3!are_defined_subset_env.
    move => /andP [/andP [Hdef0 Hdef1] Hdefc] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1 ac.
    rewrite 3!are_defined_subset_env.
    move => /andP [/andP [/andP [_ Hdef0] Hdef1] Hdefc] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [/andP [_ Hdef0] Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 n.
    rewrite are_defined_subset_env.
    move => /andP [Hneq Hdef] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u w a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u t a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u t a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u t a0.
    rewrite are_defined_subset_env.
    move => Hdef Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u t a0.
    rewrite are_defined_subset_env.
    move => Hdef Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - move => u a0 a1.
    rewrite 2!are_defined_subset_env.
    move => /andP [Hdef0 Hdef1] Hun Hsub.
    unchanged_instr_subset; not_mem_rewrite_vtyp.
  - done.
Qed.

Lemma asize_well_defined_unchanged E i a :
  well_defined_instr E i ->
  ssa_vars_unchanged_instr (vars_env E) i ->
  SSAVS.subset (vars_atomic a) (rvs_instr i) ->
  asize a (instr_succ_typenv i E) = asize a E.
Proof.
  elim a; last (case i => /=; done).
  move => v Hdef Hun Hsub.
  rewrite /asize.
  rewrite atyp_well_defined_unchanged //.
Qed.

Ltac decompose_ssa_vars_unchanged_instr :=
  match goal with
  | Hun : is_true (ssa_vars_unchanged_instr (SSAVS.union _ _) _)
    |- _ =>
    let H0 := fresh in
    let H1 := fresh in
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [H0 H1];
      try decompose_ssa_vars_unchanged_instr
  end.

Ltac well_defined_to_vs_subset :=
  match goal with
  | Hdef : is_true (well_defined_instr _ ?i) |- _ =>
    move : Hdef; rewrite /well_defined_instr;
    rewrite !are_defined_subset_env;
    [ let H := fresh in
      let H0 := fresh in
      let H1 := fresh in
      let H2 := fresh in
      move => /andP [/andP [/andP [H H0] H1] H2]
   || let H := fresh in
      let H0 := fresh in
      let H1 := fresh in
      move => /andP [/andP [H H0] H1]
   || let H := fresh in
      let H0 := fresh in
      let H1 := fresh in
      move => /andP [/andP [H H0] H1]
   || let H := fresh in
      let H0 := fresh in
      move => /andP [H H0]
   || let H := fresh in
      let H0 := fresh in
      move => /andP [H H0]
   || let H := fresh in
      move => H
    ]
  | Hdef : is_true (SSAVS.subset _ _ && SSAVS.subset _ _) |- _ =>
    let Hsub1 := fresh in
    let Hsub2 := fresh in
    move : Hdef => /andP [Hsub1 Hsub2]
  | Hdef : is_true (_ && SSAVS.subset _ _) |- _ =>
    let Hprev := fresh in
    let Hsub := fresh in
    move : Hdef => /andP [Hprev Hsub]
  end.

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
  end.

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
  end.

Lemma bexp_instr_eval_Imov E v a s1 s2 :
  well_formed_instr E (Imov v a) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Imov v a) ->
  eval_instr E (Imov v a) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Imov v a)) s2.
Proof.
  move => /andP [Hdef _] _ Hun Hinst /=.
  well_defined_to_vs_subset.
  eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst.
  by qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Ishl E t a n s1 s2 :
  well_formed_instr E (Ishl t a n) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ishl t a n) ->
  eval_instr E (Ishl t a n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ishl t a n)) s2.
Proof.
  move => /andP [Hdef _] _ Hun Hinst /=.
  well_defined_to_vs_subset.
  eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst.
  qfbv_store_acc.
  rewrite_from_nat_simple. exact: eqxx.
Qed.

Lemma bexp_instr_eval_Icshl E t t0 a a0 n s1 s2 :
  well_formed_instr E (Icshl t t0 a a0 n) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Icshl t t0 a a0 n) ->
  eval_instr E (Icshl t t0 a a0 n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Icshl t t0 a a0 n)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst.
  repeat qfbv_store_acc.
  rewrite_from_nat_simple.
  rewrite !(conform_size_eval_atomic H0 Hcon)
          !(conform_size_eval_atomic H Hcon).
  apply /andP; split; done.
Qed.

Lemma bexp_instr_eval_Inondet E t t0 s1 s2 :
  well_formed_instr E (Inondet t t0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Inondet t t0) ->
  eval_instr E (Inondet t t0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Inondet t t0)) s2.
Proof.
  done.
Qed.

Lemma bexp_instr_eval_Icmov E t a a0 a1 s1 s2 :
  well_formed_instr E (Icmov t a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Icmov t a a0 a1) ->
  eval_instr E (Icmov t a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Icmov t a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty ] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  rewrite /joinlsb /=.
  move : Hty => /andP [ Htyc _ ].
  move : (conform_size_eval_atomic H3 Hcon).
  rewrite (eqP Htyc) /= => Hszc.
  inversion_clear Hinst; repeat qfbv_store_acc.
  + by rewrite (to_bool_bit_is_true Hszc H1) //.
  + move : (not_to_bool_bit_is_false Hszc H1). by case => /eqP <- //.
Qed.

Lemma bexp_instr_eval_Inop E s1 s2 :
  well_formed_instr E Inop ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) Inop ->
  eval_instr E Inop s1 s2 ->
  QFBV.eval_bexp (bexp_instr E Inop) s2.
Proof.
  done.
Qed.

Lemma bexp_instr_eval_Inot E t t0 a s1 s2 :
  well_formed_instr E (Inot t t0 a) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Inot t t0 a) ->
  eval_instr E (Inot t t0 a) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Inot t t0 a)) s2.
Proof.
  move => /andP [Hdef _] _ Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; by repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Iadd E t a a0 s1 s2 :
  well_formed_instr E (Iadd t a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iadd t a a0) ->
  eval_instr E (Iadd t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iadd t a a0)) s2.
Proof.
  move => /andP [Hdef _] _ Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; by repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Iadds E t t0 a a0 s1 s2 :
  well_formed_instr E (Iadds t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iadds t t0 a a0) ->
  eval_instr E (Iadds t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iadds t t0 a a0)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  move : Hty => /= /eqP Hty.
  move : (atyp_asize Hty) => /eqP.
  rewrite /asize -(conform_size_eval_atomic H Hcon)
          -(conform_size_eval_atomic H0 Hcon) => Hss.
  rewrite (addB_zext1_high1 Hss) eqxx andTb.
  rewrite (addB_zext1_lown Hss) eqxx. exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Iadc E t a a0 a1 s1 s2 :
  well_formed_instr E (Iadc t a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iadc t a a0 a1) ->
  eval_instr E (Iadc t a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iadc t a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  move : Hty => /andP [Htyeq Htyb].
  move : (conform_size_eval_atomic H0 Hcon).
  rewrite (eqP Htyb) /= => Hsz1.
  move : (conform_size_eval_atomic H3 Hcon).
  rewrite {1}(eqP Htyeq).
  rewrite -(conform_size_eval_atomic H Hcon) => /eqP Hszeq.
  rewrite /asize -(conform_size_eval_atomic H3 Hcon).
  elim : (size1 Hsz1) => /eqP ->.
  - rewrite (adcB_zext1_lown false (eqP Hszeq)). exact: eqxx.
  - rewrite (adcB_zext1_lown true (eqP Hszeq)). exact: eqxx.
Qed.

Lemma bexp_instr_eval_Iadcs E t t0 a a0 a1 s1 s2 :
  well_formed_instr E (Iadcs t t0 a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iadcs t t0 a a0 a1) ->
  eval_instr E (Iadcs t t0 a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iadcs t t0 a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  rewrite /well_typed_instr in Hty.
  move : Hty => /andP [Hty Htyb].
  move : (size_eval_atomic_same Hcon H0 H1 (eqP Hty)) => /eqP Hsize.
  have Hsz1 : size (eval_atomic a1 s1) = 1.
  { by rewrite (conform_size_eval_atomic H2 Hcon) (eqP Htyb). }
  move : (size1 Hsz1). rewrite /asize -(conform_size_eval_atomic H0 Hcon).
  case=> /eqP ->;
          rewrite (adcB_zext1_high1 _ (eqP Hsize)) eqxx andTb;
           rewrite (adcB_zext1_lown _ (eqP Hsize)) eqxx; exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Isub E t a a0 s1 s2 :
  well_formed_instr E (Isub t a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isub t a a0) ->
  eval_instr E (Isub t a a0) s1 s2 ->
  QFBV.eval_bexp
    (bexp_instr (instr_succ_typenv (Isub t a a0) E)
                (Isub t a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Isubc E t t0 a a0 s1 s2 :
  well_formed_instr E (Isubc t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isubc t t0 a a0) ->
  eval_instr E (Isubc t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isubc t t0 a a0)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.

  move : (size_eval_atomic_same Hcon H H0 (eqP Hty)) => Hsize.
  have Hszneg: (size (eval_atomic a s1) = size (-# eval_atomic a0 s1)%bits).
  { by rewrite size_negB -Hsize. }
  rewrite /asize -(conform_size_eval_atomic H Hcon).
  rewrite (addB_zext1_high1 Hszneg) eqxx andTb.
  rewrite (addB_zext1_lown Hszneg) eqxx. exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Isubb E t t0 a a0 s1 s2 :
  well_formed_instr E (Isubb t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isubb t t0 a a0) ->
  eval_instr E (Isubb t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isubb t t0 a a0)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.

  move : (size_eval_atomic_same Hcon H H0 (eqP Hty)) => Hsize.
  rewrite /asize -(conform_size_eval_atomic H Hcon).
  rewrite (subB_zext1_high1 Hsize) eqxx andTb.
  rewrite (subB_zext1_lown Hsize) eqxx. exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Isbc E t a a0 a1 s1 s2 :
  well_formed_instr E (Isbc t a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isbc t a a0 a1) ->
  eval_instr E (Isbc t a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isbc t a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.

  move : Hty; rewrite /well_typed_instr => /andP [Hty Htyb].
  move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize.
  have Hszinv: (size (eval_atomic a s1) = size (~~# eval_atomic a0 s1)%bits).
  { by rewrite size_invB -Hsize. }
  rewrite /asize -(conform_size_eval_atomic H3 Hcon).
  have Hsz1: (size (eval_atomic a1 s1) = 1).
  { by rewrite (conform_size_eval_atomic H0 Hcon) (eqP Htyb). }
  case (size1 Hsz1) => /eqP ->;
  rewrite (adcB_zext1_lown _ Hszinv) eqxx; exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Isbcs E t t0 a a0 a1 s1 s2 :
  well_formed_instr E (Isbcs t t0 a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isbcs t t0 a a0 a1) ->
  eval_instr E (Isbcs t t0 a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isbcs t t0 a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  move : Hty.
  rewrite /well_typed_instr => /andP [Hty Htyb].
  move : (size_eval_atomic_same Hcon H0 H1 (eqP Hty)) => Hsize.
  have : (size (eval_atomic a1 s1) = 1).
  { by rewrite (conform_size_eval_atomic H2 Hcon) (eqP Htyb). }
  move => Hsz1.
  have : (size (eval_atomic a s1) = size (~~# eval_atomic a0 s1)%bits).
  { by rewrite size_invB -Hsize. }
  move => Hszinv.
  rewrite /asize -(conform_size_eval_atomic H0 Hcon).
  (case (size1 Hsz1) => /eqP ->);
    rewrite (adcB_zext1_lown _ Hszinv) eqxx;
    rewrite (adcB_zext1_high1 _ Hszinv) eqxx; exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Isbb E t a a0 a1 s1 s2 :
  well_formed_instr E (Isbb t a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isbb t a a0 a1) ->
  eval_instr E (Isbb t a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isbb t a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  move : Hty.
  rewrite /well_typed_instr => /andP [Hty Htyb].
  move : (size_eval_atomic_same Hcon H3 H (eqP Hty)) => Hsize.
  have : (size (eval_atomic a1 s1) = 1).
  { by rewrite (conform_size_eval_atomic H0 Hcon) (eqP Htyb). }
  move => Hsz1.
  rewrite /asize -(conform_size_eval_atomic H3 Hcon).
  (case : (size1 Hsz1) => /eqP ->);
    rewrite (sbbB_zext1_lown _ Hsize) eqxx; exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Isbbs E t t0 a a0 a1 s1 s2 :
  well_formed_instr E (Isbbs t t0 a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isbbs t t0 a a0 a1) ->
  eval_instr E (Isbbs t t0 a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isbbs t t0 a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  move : Hty.
  rewrite /well_typed_instr => /andP [Hty Htyb].
  move : (size_eval_atomic_same Hcon H0 H1 (eqP Hty)) => Hsize.
  have : (size (eval_atomic a1 s1) = 1).
  { by rewrite (conform_size_eval_atomic H2 Hcon) (eqP Htyb). }
  move => Hsz1.
  rewrite /asize -(conform_size_eval_atomic H0 Hcon).
  (case : (size1 Hsz1) => /eqP ->);
    rewrite (sbbB_zext1_high1 _ Hsize) (sbbB_zext1_lown _ Hsize) !eqxx;
    exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Imul E t a a0 s1 s2 :
  well_formed_instr E (Imul t a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Imul t a a0) ->
  eval_instr E (Imul t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Imul t a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; by repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Imull E t t0 a a0 s1 s2 :
  well_formed_instr E (Imull t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Imull t t0 a a0) ->
  eval_instr E (Imull t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Imull t t0 a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  rewrite (eqP (mul_sext (eval_atomic a s1) (eval_atomic a0 s1))).
  rewrite (size_eval_atomic_asize H Hcon)
          (size_eval_atomic_asize H0 Hcon) /=.
  apply /andP; split; done.
Qed.

Lemma bexp_instr_eval_Imulj E t a a0 s1 s2 :
  well_formed_instr E (Imulj t a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Imulj t a a0) ->
  eval_instr E (Imulj t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Imulj t a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  rewrite (eqP (mul_sext (eval_atomic a s1) (eval_atomic a0 s1))).
  by rewrite (size_eval_atomic_asize H0 Hcon) //.
Qed.

Lemma bexp_instr_eval_Isplit E t t0 a n s1 s2 :
  well_formed_instr E (Isplit t t0 a n) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isplit t t0 a n) ->
  eval_instr E (Isplit t t0 a n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isplit t t0 a n)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  generalize Hdef.
  repeat well_defined_to_vs_subset.
  move => /andP [_ Hdef].
  inversion Hinst => {H H1 H2 H3 H4 H5};
  [ rewrite H7 /= | rewrite -Typ.not_signed_is_unsigned H7 /= ];
    repeat eval_exp_exp_atomic_to_pred_state;
    repeat qfbv_store_acc;
    rewrite_from_nat_simple;
    rewrite !(size_eval_atomic_asize Hdef Hcon);
    apply /andP; split; done.
Qed.

Lemma bexp_instr_eval_Iand E t t0 a a0 s1 s2 :
  well_formed_instr E (Iand t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iand t t0 a a0) ->
  eval_instr E (Iand t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iand t t0 a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; by repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Ior E t t0 a a0 s1 s2 :
  well_formed_instr E (Ior t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ior t t0 a a0) ->
  eval_instr E (Ior t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ior t t0 a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; by repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Ixor E t t0 a a0 s1 s2 :
  well_formed_instr E (Ixor t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ixor t t0 a a0) ->
  eval_instr E (Ixor t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ixor t t0 a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; by repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Icast E t t0 a s1 s2 :
  well_formed_instr E (Icast t t0 a) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Icast t t0 a) ->
  eval_instr E (Icast t t0 a) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Icast t t0 a)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  generalize Hdef.
  repeat well_defined_to_vs_subset.
  move => Hdef.
  rewrite !eval_exp_if.
  rewrite /qfbv_low /=.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  rewrite /Typ.tcast /ucastB /scastB /=
          !(size_eval_atomic_asize Hdef Hcon) !/asize.
  by case (atyp a E) => //.
Qed.

Lemma bexp_instr_eval_Ivpc E t t0 a s1 s2 :
  well_formed_instr E (Ivpc t t0 a) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ivpc t t0 a) ->
  eval_instr E (Ivpc t t0 a) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ivpc t t0 a)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  generalize Hdef.
  repeat well_defined_to_vs_subset.
  move => Hdef.
  rewrite !eval_exp_if.
  rewrite /qfbv_low /=.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  rewrite /Typ.tcast /ucastB /scastB /=
          !(size_eval_atomic_asize Hdef Hcon) !/asize.
  by case (atyp a E) => //.
Qed.

Lemma bexp_instr_eval_Ijoin E t a a0 s1 s2 :
  well_formed_instr E (Ijoin t a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ijoin t a a0) ->
  eval_instr E (Ijoin t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ijoin t a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  repeat well_defined_to_vs_subset.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; by repeat qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Iassume E b s1 s2 :
  well_formed_instr E (Iassume b) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iassume b) ->
  eval_instr E (Iassume b) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iassume b)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst.
  repeat well_defined_to_vs_subset.
  inversion_clear Hinst; repeat qfbv_store_acc.
  case H; case b => /= ebexp rbexp _ Hrbexp.
  case (eval_bexp_rbexp rbexp s2) => _ Hqfbv.
  by apply: Hqfbv => //.
Qed.

Lemma bexp_instr_eval E i s1 s2 :
  well_formed_instr E i ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) i ->
  eval_instr E i s1 s2 ->
  QFBV.eval_bexp (bexp_instr E i) s2.
Proof.
  case: i.
  - move => v a; exact: bexp_instr_eval_Imov.
  - move => v a n; exact: bexp_instr_eval_Ishl.
  - move => u v a0 a1 n; exact: bexp_instr_eval_Icshl.
  - move => v t; exact: bexp_instr_eval_Inondet.
  - move => v ac a0 a1; exact: bexp_instr_eval_Icmov.
  - exact: bexp_instr_eval_Inop.
  - move => v t a; exact: bexp_instr_eval_Inot.
  - move => v a0 a1; exact: bexp_instr_eval_Iadd.
  - move => c v a0 a1; exact: bexp_instr_eval_Iadds.
  - move => v a0 a1 ac; exact: bexp_instr_eval_Iadc.
  - move => c v a0 a1 ac; exact: bexp_instr_eval_Iadcs.
  - move => v a0 a1; exact: bexp_instr_eval_Isub.
  - move => c v a0 a1; exact: bexp_instr_eval_Isubc.
  - move => b v a0 a1; exact: bexp_instr_eval_Isubb.
  - move => v a0 a1 c; exact: bexp_instr_eval_Isbc.
  - move => c v a0 a1 ac; exact: bexp_instr_eval_Isbcs.
  - move => v a0 a1 ab; exact: bexp_instr_eval_Isbb.
  - move => b v a0 a1 ab; exact: bexp_instr_eval_Isbbs.
  - move => v a0 a1; exact: bexp_instr_eval_Imul.
  - move => u v a0 a1; exact: bexp_instr_eval_Imull.
  - move => v a0 a1; exact: bexp_instr_eval_Imulj.
  - move => u v a n; exact: bexp_instr_eval_Isplit.
  - move => v t a0 a1; exact: bexp_instr_eval_Iand.
  - move => v t a0 a1; exact: bexp_instr_eval_Ior.
  - move => v t a0 a1; exact: bexp_instr_eval_Ixor.
  - move => v t a; exact: bexp_instr_eval_Icast.
  - move => v t a; exact: bexp_instr_eval_Ivpc.
  - move => v a0 a1; exact: bexp_instr_eval_Ijoin.
  - move => b; exact: bexp_instr_eval_Iassume.
Qed.



(* From QFBV to instruction evaluation *)

Lemma ssastore_reupd v s : SSAStore.Upd v (SSAStore.acc v s) s s.
Proof.
  move=> x. case Hxv: (x == v).
  - rewrite (SSAStore.S.acc_upd_eq Hxv). rewrite (eqP Hxv). reflexivity.
  - move/idP/negP: Hxv => Hxv. rewrite (SSAStore.S.acc_upd_neq Hxv). reflexivity.
Qed.

Lemma ssastore_reupd_imp v bs s : bs = SSAStore.acc v s -> SSAStore.Upd v bs s s.
Proof. move=> ->. exact: ssastore_reupd. Qed.

Lemma ssastore_reupd2 vl vh s :
  SSAStore.Upd2 vl (SSAStore.acc vl s) vh (SSAStore.acc vh s) s s.
Proof.
  move=> x. case Hxh: (x == vh).
  - rewrite (SSAStore.S.acc_upd_eq Hxh). rewrite (eqP Hxh). reflexivity.
  - move/idP/negP: Hxh => Hxh. rewrite (SSAStore.S.acc_upd_neq Hxh).
    case Hxl: (x == vl).
    + rewrite (SSAStore.S.acc_upd_eq Hxl). rewrite (eqP Hxl). reflexivity.
    + move/idP/negP: Hxl => Hxl. rewrite (SSAStore.S.acc_upd_neq Hxl).
      reflexivity.
Qed.

Lemma ssastore_reupd2_imp vl vh bsl bsh s :
  bsl = SSAStore.acc vl s ->
  bsh = SSAStore.acc vh s ->
  SSAStore.Upd2 vl bsl vh bsh s s.
Proof. move=> -> ->.  exact: ssastore_reupd2. Qed.


Ltac intro_atomic_size :=
  match goal with
  | Hco : SSAStore.conform ?bs ?E,
    Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)) |- _ =>
    let Hsize := fresh "Hsize" in
    move: (conform_size_eval_atomic Hsub Hco) => Hsize; move: Hsub; intro_atomic_size
  | |- _ => intros
  end.

Ltac to_asize :=
  repeat
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E |-
    context f [size (eval_atomic ?a ?s)] =>
    rewrite (size_eval_atomic_asize Hsub Hco)
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    H : context f [size (eval_atomic ?a ?s)] |- _ =>
    rewrite (size_eval_atomic_asize Hsub Hco) in H
  end.

Ltac of_asize :=
  repeat
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E |-
    context f [asize ?a ?E] =>
    rewrite -(size_eval_atomic_asize Hsub Hco)
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    H : context f [asize ?a ?E] |- _ =>
    rewrite -(size_eval_atomic_asize Hsub Hco) in H
  end.

Ltac to_size_eval_atomic H :=
  match type of H with
  | context f [asize ?a ?E] =>
    match goal with
    | Hsub : is_true (SSAVS.subset (vars_atomic a) (vars_env E)),
      Hco : SSAStore.conform ?s E |- _ =>
      rewrite -(size_eval_atomic_asize Hsub Hco) in H
    end
  end.

Ltac norm_tac :=
  rewrite_from_nat_simple;
  repeat
    match goal with
    | H : is_true (well_formed_instr _ _) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      move/andP: H => /= [H1 H2]
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      move/andP: H => [H1 H2]
    | H : is_true (are_defined _ _) |- _ =>
      move/defsubP: H => H
    | H : context f [QFBV.eval_exp (qfbv_atomic _) _] |- _ =>
      rewrite eval_exp_atomic in H
    | |- context f [QFBV.eval_exp (qfbv_atomic _) _] =>
      rewrite eval_exp_atomic
    | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
      Hco : SSAStore.conform ?s ?E |-
      context f [size (eval_atomic ?a ?s)] =>
      rewrite (size_eval_atomic_asize Hsub Hco)
    | Hco : SSAStore.conform ?s ?E,
      Htyp : is_true (atyp ?c ?E == Typ.Tbit),
      Hsub : is_true (SSAVS.subset (vars_atomic ?c) (vars_env ?E)) |- _ =>
      let b := fresh "b" in
      let Hb := fresh "Hb" in
      (move: (tbit_atomic_singleton Hco (eqP Htyp) Hsub) => [b Hb]);
      repeat match goal with
             | H : context f [eval_atomic c s] |- _ => rewrite Hb in H
             | |- context f [eval_atomic c s] => rewrite Hb
             end;
      move/eqP: Htyp=> Htyp
    end; intro_atomic_size.

Ltac solve_tac :=
  match goal with
  | |- SSAStore.Upd _ _ ?s ?s => apply: ssastore_reupd_imp; solve_tac
  | |- SSAStore.Upd2 _ _ _ _ ?s ?s => apply: ssastore_reupd2_imp; solve_tac
  | H : is_true (?l == ?r) |- ?r = ?l =>
    rewrite (eqP H); reflexivity
  end.

Lemma eval_bexp_instr_Imov E s :
  forall (t : SSAVarOrder.t) (a : atomic),
    well_formed_instr E (Imov t a) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Imov t a) E) ->
    QFBV.eval_bexp (bexp_instr E (Imov t a)) s -> eval_instr E (Imov t a) s s.
Proof. move=> /= *. apply: EImov. norm_tac. by solve_tac. Qed.

Lemma eval_bexp_instr_Ishl E s :
  forall (t : SSAVarOrder.t) (a : atomic) (n : nat),
    well_formed_instr E (Ishl t a n) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Ishl t a n) E) ->
    QFBV.eval_bexp (bexp_instr E (Ishl t a n)) s -> eval_instr E (Ishl t a n) s s.
Proof. move=> /= *. apply: EIshl. norm_tac. by solve_tac. Qed.

Lemma eval_bexp_instr_Icshl E s :
  forall (t t0 : SSAVarOrder.t) (a a0 : atomic) (n : nat),
    well_formed_instr E (Icshl t t0 a a0 n) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Icshl t t0 a a0 n) E) ->
    QFBV.eval_bexp (bexp_instr E (Icshl t t0 a a0 n)) s ->
    eval_instr E (Icshl t t0 a a0 n) s s.
Proof. move=> /= *. apply: EIcshl. norm_tac. by solve_tac. Qed.

Lemma eval_bexp_instr_Inondet E s :
  forall (t : SSAVarOrder.t) (t0 : Typ.typ),
    well_formed_instr E (Inondet t t0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Inondet t t0) E) ->
    QFBV.eval_bexp (bexp_instr E (Inondet t t0)) s -> eval_instr E (Inondet t t0) s s.
Proof.
  move=> /= v t Hwf Hco Hco' H. apply: (@EInondet _ _ _ _ _ (SSAStore.acc v s)).
  - move: (Hco' v) => HH. rewrite -HH.
    + rewrite (SSATE.vsize_add_eq (eqxx v)). reflexivity.
    + exact: SSATE.Lemmas.mem_add_eq.
  - exact: ssastore_reupd.
Qed.

Lemma eval_bexp_instr_Icmov E s :
  forall (t : SSAVarOrder.t) (a a0 a1 : atomic),
    well_formed_instr E (Icmov t a a0 a1) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Icmov t a a0 a1) E) ->
    QFBV.eval_bexp (bexp_instr E (Icmov t a a0 a1)) s ->
    eval_instr E (Icmov t a a0 a1) s s.
Proof.
  move=> /= v c a1 a2 Hwf Hco1 Hco2 Heq. norm_tac.
  case: b Hb Heq => /= Hb Heq.
  - apply: EIcmovT.
    + by rewrite Hb.
    + norm_tac. by solve_tac.
  - apply: EIcmovF.
    + by rewrite Hb.
    + norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Inop E s :
  well_formed_instr E Inop ->
  SSAStore.conform s E ->
  SSAStore.conform s (instr_succ_typenv Inop E) ->
  QFBV.eval_bexp (bexp_instr E Inop) s -> eval_instr E Inop s s.
Proof. move=> /= *. by apply: EInop. Qed.

Lemma eval_bexp_instr_Inot E s :
  forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a : atomic),
    well_formed_instr E (Inot t t0 a) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Inot t t0 a) E) ->
    QFBV.eval_bexp (bexp_instr E (Inot t t0 a)) s -> eval_instr E (Inot t t0 a) s s.
Proof. move=> /= *. apply: EInot. norm_tac. by solve_tac. Qed.

Lemma eval_bexp_instr_Iadd E s :
  forall (t : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Iadd t a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Iadd t a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Iadd t a a0)) s -> eval_instr E (Iadd t a a0) s s.
Proof. move=> /= *. apply: EIadd. norm_tac. by solve_tac. Qed.

Lemma eval_bexp_instr_Iadds E s :
  forall (t t0 : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Iadds t t0 a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Iadds t t0 a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Iadds t t0 a a0)) s ->
    eval_instr E (Iadds t t0 a a0) s s.
Proof.
  move=> /= c v a1 a2 Hwf Hco1 Hco2 Hev. apply: EIadds. norm_tac.
  have Hs: (size (eval_atomic a1 s) = size (eval_atomic a2 s))
             by rewrite Hsize Hsize0 (eqP H0).
  rewrite (addB_zext1_high1 Hs) in H1. of_asize.
  rewrite (addB_zext1_lown Hs) in H4. by solve_tac.
Qed.

Lemma eval_bexp_instr_Iadc E s :
  forall (t : SSAVarOrder.t) (a a0 a1 : atomic),
    well_formed_instr E (Iadc t a a0 a1) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Iadc t a a0 a1) E) ->
    QFBV.eval_bexp (bexp_instr E (Iadc t a a0 a1)) s ->
    eval_instr E (Iadc t a a0 a1) s s.
Proof.
  move=> /= v a1 a2 ac Hwf Hco1 Hco2 Hev. apply: EIadc. norm_tac.
  apply: ssastore_reupd_imp. rewrite (eqP Hev).
  have Hs: (size (eval_atomic a1 s) = size (eval_atomic a2 s)) by
      rewrite Hsize0 Hsize1 (eqP H1). of_asize.
  rewrite (adcB_zext1_lown b Hs). reflexivity.
Qed.

Lemma eval_bexp_instr_Iadcs E s :
  forall (t t0 : SSAVarOrder.t) (a a0 a1 : atomic),
    well_formed_instr E (Iadcs t t0 a a0 a1) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Iadcs t t0 a a0 a1) E) ->
    QFBV.eval_bexp (bexp_instr E (Iadcs t t0 a a0 a1)) s ->
    eval_instr E (Iadcs t t0 a a0 a1) s s.
Proof.
  move=> /= c v a1 a2 ac Hwf Hco1 Hco2 Hev. apply: EIadcs. norm_tac.
  have Hs: (size (eval_atomic a1 s) = size (eval_atomic a2 s))
    by rewrite Hsize0 Hsize1 (eqP H1). of_asize.
  rewrite (adcB_zext1_lown b Hs) in H6.
  rewrite (adcB_zext1_high1 b Hs) in H. by solve_tac.
Qed.

Lemma eval_bexp_instr_Isub E s :
  forall (t : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Isub t a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isub t a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Isub t a a0)) s -> eval_instr E (Isub t a a0) s s.
Proof.
  move=> /= v a1 a2 Hwf Hco1 Hco2 Hev. apply: EIsub. norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Isubc E s :
  forall (t t0 : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Isubc t t0 a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isubc t t0 a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Isubc t t0 a a0)) s ->
    eval_instr E (Isubc t t0 a a0) s s.
Proof.
  move=> /= c v a1 a2 Hwf Hco1 Hco2 Hev. apply: EIsubc. norm_tac.
  have Hs: (size (eval_atomic a1 s) = size (-# eval_atomic a2 s)%bits) by
      by rewrite size_negB Hsize Hsize0 (eqP H0). of_asize.
  rewrite (addB_zext1_high1 Hs) in H1. rewrite (addB_zext1_lown Hs) in H4.
    by solve_tac.
Qed.

Lemma eval_bexp_instr_Isubb E s :
  forall (t t0 : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Isubb t t0 a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isubb t t0 a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Isubb t t0 a a0)) s ->
    eval_instr E (Isubb t t0 a a0) s s.
Proof.
  move=> /= bw v a1 a2 Hwf Hco1 Hco2 Hev. apply: EIsubb. norm_tac.
  have Hs: (size (eval_atomic a1 s) = size (eval_atomic a2 s)%bits) by
      by rewrite Hsize Hsize0 (eqP H0). of_asize.
  rewrite (subB_zext1_lown Hs) in H4. rewrite (subB_zext1_high1 Hs) in H1.
    by solve_tac.
Qed.

Lemma eval_bexp_instr_Isbc E s :
  forall (t : SSAVarOrder.t) (a a0 a1 : atomic),
    well_formed_instr E (Isbc t a a0 a1) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isbc t a a0 a1) E) ->
    QFBV.eval_bexp (bexp_instr E (Isbc t a a0 a1)) s ->
    eval_instr E (Isbc t a a0 a1) s s.
Proof.
  move=> /= v a1 a2 ac Hwf Hco1 Hco2 Hev. apply: EIsbc. norm_tac.
  have Hs: size (eval_atomic a1 s) = size (~~# eval_atomic a2 s)%bits
    by rewrite size_invB Hsize0 Hsize1 (eqP H1). of_asize.
  rewrite (adcB_zext1_lown _ Hs) in Hev. by solve_tac.
Qed.

Lemma eval_bexp_instr_Isbcs E s :
  forall (t t0 : SSAVarOrder.t) (a a0 a1 : atomic),
    well_formed_instr E (Isbcs t t0 a a0 a1) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isbcs t t0 a a0 a1) E) ->
    QFBV.eval_bexp (bexp_instr E (Isbcs t t0 a a0 a1)) s ->
    eval_instr E (Isbcs t t0 a a0 a1) s s.
Proof.
  move=> /= c v a1 a2 ay Hwf Hco1 Hco2 Hev. apply: EIsbcs. norm_tac.
  have Hs: size (eval_atomic a1 s) = size (~~# eval_atomic a2 s)%bits
    by rewrite size_invB Hsize0 Hsize1 (eqP H1). of_asize.
  rewrite (adcB_zext1_high1 _ Hs) in H. rewrite (adcB_zext1_lown _ Hs) in H6.
    by solve_tac.
Qed.

Lemma eval_bexp_instr_Isbb E s :
  forall (t : SSAVarOrder.t) (a a0 a1 : atomic),
    well_formed_instr E (Isbb t a a0 a1) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isbb t a a0 a1) E) ->
    QFBV.eval_bexp (bexp_instr E (Isbb t a a0 a1)) s ->
    eval_instr E (Isbb t a a0 a1) s s.
Proof.
  move=> /= v a1 a2 ab Hwf Hco1 Hco2 Hev. apply: EIsbb. norm_tac.
  have Hs: size (eval_atomic a1 s) = size (eval_atomic a2 s)%bits
    by rewrite Hsize0 Hsize1 (eqP H1). of_asize.
  rewrite (sbbB_zext1_lown _ Hs) in Hev. by solve_tac.
Qed.

Lemma eval_bexp_instr_Isbbs E s :
  forall (t t0 : SSAVarOrder.t) (a a0 a1 : atomic),
    well_formed_instr E (Isbbs t t0 a a0 a1) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isbbs t t0 a a0 a1) E) ->
    QFBV.eval_bexp (bexp_instr E (Isbbs t t0 a a0 a1)) s ->
    eval_instr E (Isbbs t t0 a a0 a1) s s.
Proof.
  move=> /= b v a1 a2 ab Hwf Hco1 Hco2 Hev. apply: EIsbbs. norm_tac.
  have Hs: size (eval_atomic a1 s) = size (eval_atomic a2 s)%bits
    by rewrite Hsize0 Hsize1 (eqP H1). of_asize.
  rewrite (sbbB_zext1_lown _ Hs) in H6. rewrite (sbbB_zext1_high1 _ Hs) in H.
    by solve_tac.
Qed.

Lemma eval_bexp_instr_Imul E s :
  forall (t : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Imul t a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Imul t a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Imul t a a0)) s -> eval_instr E (Imul t a a0) s s.
Proof.
  move=> /= v a1 a2 Hwf Hco1 Hco2 Hev. apply: EImul. norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Imull E s :
  forall (t t0 : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Imull t t0 a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Imull t t0 a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Imull t t0 a a0)) s ->
    eval_instr E (Imull t t0 a a0) s s.
Proof.
  move=> /= vh vl a1 a2 Hwf Hco1 Hco2 Hev. apply: EImull. norm_tac.
  rewrite (eqP (mul_sext _ _)). to_asize. by solve_tac.
Qed.

Lemma eval_bexp_instr_Imulj E s :
  forall (t : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Imulj t a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Imulj t a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Imulj t a a0)) s -> eval_instr E (Imulj t a a0) s s.
Proof.
  move=> /= v a1 a2 Hwf Hco1 Hco2 Hev. apply: EImulj. norm_tac.
  rewrite (eqP (mul_sext _ _)). to_asize. by solve_tac.
Qed.

Lemma eval_bexp_instr_Isplit E s :
  forall (t t0 : SSAVarOrder.t) (a : atomic) (n : nat),
    well_formed_instr E (Isplit t t0 a n) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Isplit t t0 a n) E) ->
    QFBV.eval_bexp (bexp_instr E (Isplit t t0 a n)) s ->
    eval_instr E (Isplit t t0 a n) s s.
Proof.
  move=> /= vh vl a n Hwf Hco1 Hco2 Hev. dcase (atyp a E). case => wa Htyp.
  - have Hun: Typ.is_unsigned (atyp a E) by rewrite Htyp.
    rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
    apply: (EIsplitU Hun). norm_tac. by solve_tac.
  - have Hsn: Typ.is_signed (atyp a E) by rewrite Htyp.
    rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
    apply: (EIsplitS Hsn). norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Iand E s :
  forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a a0 : atomic),
    well_formed_instr E (Iand t t0 a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Iand t t0 a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Iand t t0 a a0)) s ->
    eval_instr E (Iand t t0 a a0) s s.
Proof.
  move=> /= v t a1 a2 Hwf Hco1 Hco2 Hev. apply: EIand. norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Ior E s :
  forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a a0 : atomic),
    well_formed_instr E (Ior t t0 a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Ior t t0 a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Ior t t0 a a0)) s ->
    eval_instr E (Ior t t0 a a0) s s.
Proof.
  move=> /= v t a1 a2 Hwf Hco1 Hco2 Hev. apply: EIor. norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Ixor E s :
  forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a a0 : atomic),
    well_formed_instr E (Ixor t t0 a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Ixor t t0 a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Ixor t t0 a a0)) s ->
    eval_instr E (Ixor t t0 a a0) s s.
Proof.
  move=> /= v t a1 a2 Hwf Hco1 Hco2 Hev. apply: EIxor. norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Icast E s :
  forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a : atomic),
    well_formed_instr E (Icast t t0 a) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Icast t t0 a) E) ->
    QFBV.eval_bexp (bexp_instr E (Icast t t0 a)) s ->
    eval_instr E (Icast t t0 a) s s.
Proof.
  move=> /= v t a Hwf Hco1 Hco2 Hev. apply: EIcast. norm_tac.
  rewrite /Typ.tcast /ucastB /scastB Hsize /=. move: Hev.
  case: (atyp a E) => wa /=.
  - case: (Typ.sizeof_typ t == wa) => /=.
    + norm_tac. by solve_tac.
    + case: (Typ.sizeof_typ t < wa) => /=; norm_tac; by solve_tac.
  - case: (Typ.sizeof_typ t == wa) => /=.
    + norm_tac. by solve_tac.
    + case: (Typ.sizeof_typ t < wa) => /=; norm_tac; by solve_tac.
Qed.

Lemma eval_bexp_instr_Ivpc E s :
  forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a : atomic),
    well_formed_instr E (Ivpc t t0 a) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Ivpc t t0 a) E) ->
    QFBV.eval_bexp (bexp_instr E (Ivpc t t0 a)) s ->
    eval_instr E (Ivpc t t0 a) s s.
Proof.
  move=> /= v t a Hwf Hco1 Hco2 Hev. apply: EIvpc.
  have Hwf': (well_formed_instr E (Icast v t a)) by exact: Hwf.
  move: (eval_bexp_instr_Icast Hwf' Hco1 Hco2 Hev). inversion_clear 1.
  assumption.
Qed.

Lemma eval_bexp_instr_Ijoin E s :
  forall (t : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Ijoin t a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Ijoin t a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Ijoin t a a0)) s ->
    eval_instr E (Ijoin t a a0) s s.
Proof.
  move=> /= v a1 a2 Hwf Hco1 Hco2 Hev. apply: EIjoin. norm_tac. by solve_tac.
Qed.

Lemma eval_bexp_instr_Iassume E s :
  forall b : bexp,
    well_formed_instr E (Iassume b) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Iassume b) E) ->
    QFBV.eval_bexp (bexp_instr E (rng_instr (Iassume b))) s ->
    eval_instr E (rng_instr (Iassume b)) s s.
Proof.
  move=> /= b Hwf Hco1 Hco2 Hev. case: b Hwf Hev => e r /= Hwf Hev.
  apply: EIassume. rewrite /eval_bexp /=. split; first by trivial.
  apply/eval_bexp_rbexp. assumption.
Qed.

Lemma eval_bexp_instr E i s :
  well_formed_instr E i ->
  SSAStore.conform s E -> SSAStore.conform s (instr_succ_typenv i E) ->
  QFBV.eval_bexp (bexp_instr E (rng_instr i)) s -> eval_instr E (rng_instr i) s s.
Proof.
  case: i.
  - exact: eval_bexp_instr_Imov.
  - exact: eval_bexp_instr_Ishl.
  - exact: eval_bexp_instr_Icshl.
  - exact: eval_bexp_instr_Inondet.
  - exact: eval_bexp_instr_Icmov.
  - exact: eval_bexp_instr_Inop.
  - exact: eval_bexp_instr_Inot.
  - exact: eval_bexp_instr_Iadd.
  - exact: eval_bexp_instr_Iadds.
  - exact: eval_bexp_instr_Iadc.
  - exact: eval_bexp_instr_Iadcs.
  - exact: eval_bexp_instr_Isub.
  - exact: eval_bexp_instr_Isubc.
  - exact: eval_bexp_instr_Isubb.
  - exact: eval_bexp_instr_Isbc.
  - exact: eval_bexp_instr_Isbcs.
  - exact: eval_bexp_instr_Isbb.
  - exact: eval_bexp_instr_Isbbs.
  - exact: eval_bexp_instr_Imul.
  - exact: eval_bexp_instr_Imull.
  - exact: eval_bexp_instr_Imulj.
  - exact: eval_bexp_instr_Isplit.
  - exact: eval_bexp_instr_Iand.
  - exact: eval_bexp_instr_Ior.
  - exact: eval_bexp_instr_Ixor.
  - exact: eval_bexp_instr_Icast.
  - exact: eval_bexp_instr_Ivpc.
  - exact: eval_bexp_instr_Ijoin.
  - exact: eval_bexp_instr_Iassume.
Qed.



(* Connect premises by conjunction. *)

Fixpoint eval_bexps_conj (es : seq QFBV.bexp) (s : SSAStore.t) : Prop :=
  match es with
  | [::] => True
  | hd::tl => QFBV.eval_bexp hd s /\ eval_bexps_conj tl s
  end.

Lemma eval_program_cons E hd tl s1 s3 :
  eval_program E (hd :: tl) s1 s3 ->
  exists s2, eval_instr E hd s1 s2 /\
             eval_program (instr_succ_typenv hd E) tl s2 s3.
Proof.
  move => Hev.
  inversion_clear Hev.
  exists t => //.
Qed.

Lemma bexp_program_eval E p s1 s2 :
  well_formed_ssa_program E p ->
  SSAStore.conform s1 E ->
  eval_program E p s1 s2 ->
  eval_bexps_conj (bexp_program E p) s2.
Proof.
  elim: p E s1 s2 => [| hd tl IH] E s1 s3 //=. move=> Hwfssa Hcon Hep.
  move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
  elim: (eval_program_cons Hep) => s2 [Hehd Hetl].
  move : (ssa_unchanged_program_cons1 Huc) => [Huchd Huctl]. split.
  - move: (well_formed_program_cons1 Hwf) => Hwfhd.
    move: (bexp_instr_eval Hwfhd Hcon Huchd Hehd).
    move: (ssa_unchanged_instr_succ_typenv_submap Huchd) => Hsubm.
    move/andP: Hwfhd=> [Hwd_hd Hwt_hd].
    move: (well_formed_ssa_vars_unchanged_hd Hwfssa) => Hun_hd.
    rewrite (bexp_instr_submap Hwd_hd Hsubm).
    exact: (eval_vars_unchanged_program_bexp_instr Hun_hd Hetl).
  - apply: (IH _ _ _ (well_formed_ssa_tl Hwfssa) _ Hetl).
    exact: (conform_eval_succ_typenv (well_formed_program_cons1 Hwf) Hcon Hehd).
Qed.

Definition valid_bexp_spec_conj (s : bexp_spec) : Prop :=
  forall st : SSAStore.t,
    QFBV.eval_bexp (bpre s) st ->
    eval_bexps_conj (bprog s) st ->
    QFBV.eval_bexp (bpost s) st.

Lemma bexp_spec_sound_conj (s : spec) :
  well_formed_ssa_spec s ->
  valid_bexp_spec_conj (bexp_of_rspec (sinputs s) (rspec_of_spec s)) ->
  valid_rspec (rspec_of_spec s).
Proof.
  destruct s as [te p g].
  rewrite /bexp_of_rspec /valid_bexp_spec_conj /=.
  move=> Hwfssa Hvalid s1 s2 /= Hcon Hf Hp.
  apply: eval_bexp_rbexp1.
  move: Hwfssa => /andP /= [/andP [Hwf Huc] Hssa].
  move : Hwf => /andP [/andP /= [Hwfb Hwfg] _].
  move : Hwfb => /= /andP [Hdef _].
  apply: Hvalid.
  - apply: eval_bexp_rbexp2.
    apply: (proj1 (ssa_unchanged_program_eval_rbexp _ Hp) Hf).
    rewrite ssa_vars_unchanged_rng_program.
    apply : (ssa_unchanged_program_subset Huc).
    move : (are_defined_subset (vars_rbexp_subset p) Hdef).
    by rewrite are_defined_subset_env.
  - apply : (bexp_program_eval _ Hcon Hp).
    rewrite /well_formed_ssa_program.
    apply /andP; split; first (apply /andP; split).
    + apply : (well_formed_rng_program Hwfg).
    + rewrite ssa_vars_unchanged_rng_program. exact: Huc.
    + apply : (ssa_single_assignment_rng_program Hssa).
Qed.

Lemma vars_exp_rexp e : QFBV.vars_exp (exp_rexp e) = vars_rexp e.
Proof.
  elim: e => //=.
  - move=> _ op e IH. case: op => /=; assumption.
  - move=> _ op e1 IH1 e2 IH2. case: op => /=; rewrite IH1 IH2; reflexivity.
Qed.

Lemma vars_bexp_rbexp e : QFBV.vars_bexp (bexp_rbexp e) = vars_rbexp e.
Proof.
  elim: e => //=.
  - move=> _ e1 e2. rewrite !vars_exp_rexp. reflexivity.
  - move=> _ op e1 e2. case: op => /=; rewrite !vars_exp_rexp; reflexivity.
  - move=> e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
  - move=> e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
Qed.

Ltac are_defined_dec :=
  match goal with
  | H : is_true (_ && _) |- _ => caseb H; intros; are_defined_dec
  | H : is_true (are_defined (SSAVS.singleton _) _) |- _ =>
    rewrite are_defined_singleton in H; are_defined_dec
  | H : is_true (are_defined (SSAVS.union _ _) _) |- _ =>
    let H1 := fresh in
    let H2 := fresh in
    rewrite are_defined_union in H; move/andP: H => [H1 H2]; are_defined_dec
  | |- is_true (are_defined (SSAVS.singleton _) _) =>
    rewrite are_defined_singleton; are_defined_dec
  | |- is_true (are_defined (SSAVS.union _ _) _) =>
    rewrite are_defined_union; apply/andP; split; are_defined_dec
  | |- context f [QFBV.vars_exp (qfbv_atomic _)] =>
    rewrite vars_qfbv_atomic; are_defined_dec
  | H : is_true (?x != ?y) |- is_true (is_defined ?y (SSATE.add ?x _ _)) =>
    rewrite eq_sym in H; rewrite (is_defined_add_neq _ _ H); are_defined_dec
  | |- context f [if ?b then _ else _] => case: b; simpl; are_defined_dec
  | |- is_true (is_defined ?v (SSATE.add ?v _ _)) =>
    exact: is_defined_add_eq
  | |- is_true (are_defined SSAVS.empty _) => exact: are_defined_empty
  | H : is_true (are_defined ?vs ?E) |-
    is_true (are_defined ?vs (SSATE.add _ _ ?E)) =>
    apply: are_defined_addr; assumption
  | H : is_true (are_defined ?vs ?E) |-
    is_true (are_defined ?vs (SSATE.add _ _ (SSATE.add _ _  ?E))) =>
    apply: are_defined_addr; apply: are_defined_addr; assumption
  | |- _ => idtac
  end.

Lemma bexp_instr_are_defined E i :
  well_defined_instr E i ->
  are_defined (QFBV.vars_bexp (bexp_instr E i)) (instr_succ_typenv i E).
Proof.
  case: i => //=; try (move=> *; are_defined_dec).
  match goal with
  | b : bexp, H : is_true (are_defined (vars_bexp ?b) _)
    |- context f [let (_, _) := ?b in _] =>
    case: b H => eb rb H
  end.
  rewrite vars_bexp_rbexp. move: (vars_rbexp_subset (eb, rb)) => /= Hsub.
  apply: (are_defined_subset Hsub). assumption.
Qed.


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
  valid_bexp_spec_imp (bexp_of_rspec (sinputs s) (rspec_of_spec s)) ->
  valid_rspec (rspec_of_spec s).
Proof.
  move=> Hw Hv.
  apply: (bexp_spec_sound_conj Hw).
  exact: valid_bexp_spec_imp_conj.
Qed.


(* Soundness of range check *)

Definition valid_bexp_spec := valid_bexp_spec_imp.

Theorem bexp_spec_sound (s : spec) :
  well_formed_ssa_spec s ->
  valid_bexp_spec (bexp_of_rspec (sinputs s) (rspec_of_spec s)) ->
  valid_rspec (rspec_of_spec s).
Proof.
  exact: bexp_spec_sound_imp.
Qed.


(* Define the safety condition in terms of a QFBV expression *)

Definition bexp_atomic_addB_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then
    qfbv_lneg (qfbv_uaddo (qfbv_atomic a1)
                          (qfbv_atomic a2))
  else
    qfbv_lneg (qfbv_saddo (qfbv_atomic a1)
                          (qfbv_atomic a2)).

Definition bexp_atomic_adcB_safe E a1 a2 ac : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
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
                     (qfbv_atomic ac))).

Definition bexp_atomic_subB_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then
    qfbv_lneg (qfbv_usubo (qfbv_atomic a1)
                          (qfbv_atomic a2))
  else
    qfbv_lneg (qfbv_ssubo (qfbv_atomic a1)
                          (qfbv_atomic a2)).

Definition bexp_atomic_sbbB_safe  E a1 a2 ab : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
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
                     (qfbv_atomic ab))).

Definition bexp_atomic_sbcB_safe  E a1 a2 ac : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
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
                               (qfbv_atomic ac)))).

Definition bexp_atomic_mulB_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then
    qfbv_lneg (qfbv_umulo (qfbv_atomic a1)
                          (qfbv_atomic a2))
  else
    qfbv_lneg (qfbv_smulo (qfbv_atomic a1)
                          (qfbv_atomic a2)).

Definition bexp_atomic_shl_safe E a n : QFBV.bexp :=
  let 'a_typ := atyp a E in
  if Typ.is_unsigned a_typ then
    qfbv_eq (qfbv_high n (qfbv_atomic a))
            (qfbv_zero n)
  else
    qfbv_disj (qfbv_eq (qfbv_high (n + 1) (qfbv_atomic a))
                       (qfbv_zero (n + 1)))
              (qfbv_eq (qfbv_high (n + 1) (qfbv_atomic a))
                       (qfbv_not (qfbv_zero (n + 1)))).

Definition bexp_atomic_cshl_safe E (a1 : atomic) a2 n  : QFBV.bexp :=
  let 'concatbv := qfbv_concat (qfbv_atomic a2) (qfbv_atomic a1) in
  if Typ.is_unsigned (atyp a1 E) then
    qfbv_eq (qfbv_high n concatbv) (qfbv_zero n)
  else
    qfbv_disj (qfbv_eq (qfbv_high (n + 1) concatbv)
                       (qfbv_zero (n + 1)))
              (qfbv_eq (qfbv_high (n + 1) concatbv)
                       (qfbv_not (qfbv_zero (n + 1)))).

Definition bexp_atomic_vpc_safe E t a : QFBV.bexp :=
  let 'a_typ := atyp a E in
  let 'a_size := Typ.sizeof_typ a_typ in
  let 't_size := Typ.sizeof_typ t in
  if Typ.is_unsigned a_typ then
    if Typ.is_unsigned t then
      if Typ.sizeof_typ a_typ <= Typ.sizeof_typ t then
        qfbv_true
      else
        qfbv_eq
          (qfbv_high (Typ.sizeof_typ a_typ - Typ.sizeof_typ t)
                     (qfbv_atomic a))
          (qfbv_zero (Typ.sizeof_typ a_typ - Typ.sizeof_typ t))
    else
      if Typ.sizeof_typ a_typ < Typ.sizeof_typ t then
        qfbv_true
      else
        qfbv_eq
          (qfbv_high (Typ.sizeof_typ a_typ - Typ.sizeof_typ t + 1)
                     (qfbv_atomic a))
          (qfbv_zero (Typ.sizeof_typ a_typ - Typ.sizeof_typ t + 1))
  else
    if Typ.is_unsigned t then
      if Typ.sizeof_typ a_typ - 1 <= Typ.sizeof_typ t then
        qfbv_eq
          (qfbv_high 1 (qfbv_atomic a))
          (qfbv_zero 1)
      else
        qfbv_eq
          (qfbv_high (Typ.sizeof_typ a_typ - Typ.sizeof_typ t)
                     (qfbv_atomic a))
          (qfbv_zero (Typ.sizeof_typ a_typ - Typ.sizeof_typ t))
    else
      if Typ.sizeof_typ a_typ <= Typ.sizeof_typ t then
        qfbv_true
      else
        qfbv_eq
          (qfbv_sext (Typ.sizeof_typ a_typ - Typ.sizeof_typ t)
                     (qfbv_low (Typ.sizeof_typ t) (qfbv_atomic a)))
          (qfbv_atomic a).

Definition bexp_instr_safe E (i : instr) : QFBV.bexp :=
  match i with
  | Iadd _ a1 a2 =>
    bexp_atomic_addB_safe E a1 a2
  | Iadc _ a1 a2 ac =>
    bexp_atomic_adcB_safe E a1 a2 ac
  | Isub _ a1 a2 =>
    bexp_atomic_subB_safe E a1 a2
  | Isbc _ a1 a2 ac =>
    bexp_atomic_sbcB_safe E a1 a2 ac
  | Isbb _ a1 a2 ab =>
    bexp_atomic_sbbB_safe E a1 a2 ab
  | Imul _ a1 a2 =>
    bexp_atomic_mulB_safe E a1 a2
  | Ishl v a n =>
    bexp_atomic_shl_safe E a n
  | Icshl h l a1 a2 n =>
    bexp_atomic_cshl_safe E a1 a2 n
  | Ivpc _ t a =>
    bexp_atomic_vpc_safe E t a
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
  end.

Lemma eval_bexp_atomic_addB_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_addB_safe E a1 a2) s <->
  addB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  case Ht : (Typ.is_unsigned (atyp a1 E));
    rewrite /bexp_atomic_addB_safe /addB_safe Ht /=.
  - rewrite /uaddB_safe /= !eval_exp_atomic //.
  - rewrite /saddB_safe /= !eval_exp_atomic //.
Qed.

Lemma eval_bexp_atomic_adcB_safe E a1 a2 ac s :
  QFBV.eval_bexp (bexp_atomic_adcB_safe E a1 a2 ac) s <->
  adcB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  case Ht : (Typ.is_unsigned (atyp a1 E));
    rewrite /bexp_atomic_adcB_safe /adcB_safe Ht /=.
  - rewrite /uadcB_safe /= !eval_exp_atomic //.
  - rewrite /sadcB_safe /= !eval_exp_atomic //.
Qed.

Lemma eval_bexp_atomic_subB_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_subB_safe E a1 a2) s <->
  subB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  case Ht : (Typ.is_unsigned (atyp a1 E));
    rewrite /bexp_atomic_subB_safe /subB_safe Ht /=.
  - rewrite /usubB_safe /= !eval_exp_atomic //.
  - rewrite /ssubB_safe /= !eval_exp_atomic //.
Qed.

Lemma eval_bexp_atomic_sbbB_safe E a1 a2 ac s :
  QFBV.eval_bexp (bexp_atomic_sbbB_safe E a1 a2 ac) s <->
  sbbB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  case Ht : (Typ.is_unsigned (atyp a1 E));
    rewrite /bexp_atomic_sbbB_safe /sbbB_safe Ht /=.
  - rewrite /usbbB_safe /= !eval_exp_atomic //.
  - rewrite /ssbbB_safe /= !eval_exp_atomic //.
Qed.

Lemma eval_bexp_atomic_sbcB_safe E a1 a2 ac s :
  QFBV.eval_bexp (bexp_atomic_sbcB_safe E a1 a2 ac) s <->
  sbcB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  case Ht : (Typ.is_unsigned (atyp a1 E));
    rewrite /bexp_atomic_sbcB_safe /sbcB_safe Ht /=.
  - rewrite /usbcB_safe /= !eval_exp_atomic //.
  - rewrite /ssbcB_safe /= !eval_exp_atomic //.
Qed.

Lemma eval_bexp_atomic_mulB_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_mulB_safe E a1 a2) s <->
  mulB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  case Ht : (Typ.is_unsigned (atyp a1 E));
    rewrite /bexp_atomic_mulB_safe /mulB_safe Ht /=.
  - rewrite /umulB_safe /= !eval_exp_atomic //.
  - rewrite /smulB_safe /= !eval_exp_atomic //.
Qed.

Lemma eval_bexp_atomic_shl_safe E a n s :
  QFBV.eval_bexp (bexp_atomic_shl_safe E a n) s <->
  shlBn_safe (atyp a E) (eval_atomic a s) n.
Proof.
  rewrite /bexp_atomic_shl_safe /shlBn_safe
          /ushlBn_safe /sshlBn_safe /=.
    case Ht : (Typ.is_unsigned (atyp a E)) => /=.
  - rewrite !eval_exp_atomic zeros_from_nat //.
  - rewrite !eval_exp_atomic zeros_from_nat
    -zeros_from_nat invB_zeros //.
Qed.

Lemma eval_bexp_atomic_cshl_safe E a1 a2 n s :
  QFBV.eval_bexp (bexp_atomic_cshl_safe E a1 a2 n) s <->
  cshlBn_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) n.
Proof.
  rewrite /bexp_atomic_cshl_safe /cshlBn_safe
          /ucshlBn_safe /scshlBn_safe
          /ushlBn_safe /sshlBn_safe /=.
  case : (Typ.is_unsigned (atyp a1 E)).
  - by rewrite /= -!zeros_from_nat !eval_exp_atomic.
  - by rewrite /= -!zeros_from_nat !eval_exp_atomic !invB_zeros.
Qed.

Lemma eval_bexp_atomic_vpc_safe E a t s :
  QFBV.eval_bexp (bexp_atomic_vpc_safe E t a) s <->
  vpc_safe t (atyp a E) (eval_atomic a s).
Proof.
  rewrite /bexp_atomic_vpc_safe /vpc_safe.
  case : (Typ.is_unsigned (atyp a E));
    case : (Typ.is_unsigned t).
  - case : (Typ.sizeof_typ (atyp a E) <= Typ.sizeof_typ t) => /=.
    + done.
    + rewrite -zeros_from_nat !eval_exp_atomic //.
  - case : (Typ.sizeof_typ (atyp a E) < Typ.sizeof_typ t) => /=.
    + done.
    + rewrite -zeros_from_nat !eval_exp_atomic //.
  - case : (Typ.sizeof_typ (atyp a E) - 1 <= Typ.sizeof_typ t) => /=.
    + rewrite !eval_exp_atomic //.
    + rewrite -zeros_from_nat !eval_exp_atomic //.
  - case : (Typ.sizeof_typ (atyp a E) <= Typ.sizeof_typ t) => /=.
    + done.
    + rewrite !eval_exp_atomic //.
Qed.

Lemma eval_bexp_instr_safe E i s :
  well_formed_instr E i ->
  (QFBV.eval_bexp (bexp_instr_safe E i) s <->
   ssa_instr_safe_at E i s).
Proof.
  move => /andP [Hdef _].
  move : Hdef; case i => /=; try done.
  - move => v a n _.
    apply eval_bexp_atomic_shl_safe.
  - move => h l a1 a2 n _.
    apply : eval_bexp_atomic_cshl_safe.
  - move => v a1 a2 _.
    apply : eval_bexp_atomic_addB_safe.
  - move => v a1 a2 ac _.
(* TODO: add safety for signed operations: adds, adcs, subc, subb, sbcs, and sbbs *)
(*
    apply : eval_bexp_atomic_adcB_safe.
  - move => v a1 a2 _.
    apply : eval_bexp_atomic_subB_safe.
  - move => v a1 a2 ac _.
    apply : eval_bexp_atomic_sbcB_safe.
  - move => v a1 a2 ac _.
    apply : eval_bexp_atomic_sbbB_safe.
  - move => v a1 a2 _.
    apply : eval_bexp_atomic_mulB_safe.
  - move => v t a _.
    apply : eval_bexp_atomic_vpc_safe.
*)
Admitted.

Lemma unchanged_instr_eval_instr E i a s1 s2 :
  ssa_vars_unchanged_instr (vars_atomic a) i ->
  eval_instr E i s1 s2 ->
  eval_atomic a s1 = eval_atomic a s2.
Proof.
  case a => //.
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
    apply : (acc_unchanged_instr Hun Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Ishl E t a n s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Ishl t a n)) (Ishl t a n) ->
  eval_instr E (Ishl t a n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Ishl t a n)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Ishl t a n)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_shl_safe.
  by case : (Typ.is_unsigned (atyp a E)) => /=;
       rewrite !eval_exp_atomic
               (ssa_unchanged_instr_eval_atomic Hun Hev).
Qed.


Lemma eval_bexp_instr_safe_succ_Icshl E t t0 a a0 n s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Icshl t t0 a a0 n))
                           (Icshl t t0 a a0 n) ->
  eval_instr E (Icshl t t0 a a0 n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Icshl t t0 a a0 n)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Icshl t t0 a a0 n)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_cshl_safe.
  by case : (Typ.is_unsigned (atyp a E)) => /=;
     rewrite !eval_exp_atomic;
     move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1];
     rewrite (ssa_unchanged_instr_eval_atomic Hun0 Hev)
             (ssa_unchanged_instr_eval_atomic Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Iadd E t a a0 s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Iadd t a a0)) (Iadd t a a0) ->
  eval_instr E (Iadd t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadd t a a0)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadd t a a0)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_addB_safe.
  rewrite !eval_bexp_if => /=.
  rewrite !eval_exp_atomic.
  move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1].
  by rewrite !(unchanged_instr_eval_instr Hun0 Hev)
             !(unchanged_instr_eval_instr Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Iadc E t a a0 a1 s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Iadc t a a0 a1))
                           (Iadc t a a0 a1) ->
  eval_instr E (Iadc t a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadc t a a0 a1)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadc t a a0 a1)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_adcB_safe !eval_bexp_if => /=.
  rewrite !eval_exp_atomic.
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun0 Hun].
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun1 Hunc].
  by rewrite !(unchanged_instr_eval_instr Hun0 Hev)
            !(unchanged_instr_eval_instr Hun1 Hev)
            !(unchanged_instr_eval_instr Hunc Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Isub E t a a0 s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Isub t a a0)) (Isub t a a0) ->
  eval_instr E (Isub t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isub t a a0)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isub t a a0)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_subB_safe !eval_bexp_if => /=.
  rewrite !eval_exp_atomic.
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun0 Hun1].
  by rewrite !(unchanged_instr_eval_instr Hun0 Hev)
             !(unchanged_instr_eval_instr Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Isbc E t a a0 a1 s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Isbc t a a0 a1))
                           (Isbc t a a0 a1) ->
  eval_instr E (Isbc t a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbc t a a0 a1)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbc t a a0 a1)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_sbcB_safe !eval_bexp_if => /=.
  rewrite !eval_exp_atomic.
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun0 Hun].
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun1 Hunc].
  by rewrite !(unchanged_instr_eval_instr Hun0 Hev)
             !(unchanged_instr_eval_instr Hun1 Hev)
             !(unchanged_instr_eval_instr Hunc Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Isbb E t a a0 a1 s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Isbb t a a0 a1))
                           (Isbb t a a0 a1) ->
  eval_instr E (Isbb t a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbb t a a0 a1)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbb t a a0 a1)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_sbbB_safe !eval_bexp_if => /=.
  rewrite !eval_exp_atomic.
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun0 Hun].
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun1 Hunc].
  by rewrite !(unchanged_instr_eval_instr Hun0 Hev)
             !(unchanged_instr_eval_instr Hun1 Hev)
             !(unchanged_instr_eval_instr Hunc Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Imul E t a a0 s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Imul t a a0)) (Imul t a a0) ->
  eval_instr E (Imul t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Imul t a a0)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Imul t a a0)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_mulB_safe !eval_bexp_if => /=.
  rewrite !eval_exp_atomic.
  move : (ssa_unchanged_instr_union1 Hun) =>
  {Hun} [Hun0 Hun1].
  by rewrite !(unchanged_instr_eval_instr Hun0 Hev)
             !(unchanged_instr_eval_instr Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succ_Ivpc E t t0 a s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr (Ivpc t t0 a)) (Ivpc t t0 a) ->
  eval_instr E (Ivpc t t0 a) s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Ivpc t t0 a)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Ivpc t t0 a)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_vpc_safe !eval_bexp_if => /=.
  rewrite !eval_exp_atomic.
  by rewrite !(unchanged_instr_eval_instr Hun Hev).
Qed.

Lemma eval_bexp_instr_safe_succ E i s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr i) i ->
  eval_instr E i s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s2.
Proof.
  case i; rewrite /bexp_instr_safe => //.
  - move => v a n; apply eval_bexp_instr_safe_succ_Ishl.
  - move => u v a0 a1 n; apply eval_bexp_instr_safe_succ_Icshl.
  - move => v a0 a1; apply eval_bexp_instr_safe_succ_Iadd.
  - move => v a0 a1 ac; apply eval_bexp_instr_safe_succ_Iadc.
  - move => v a0 a1; apply eval_bexp_instr_safe_succ_Isub.
  - move => v a0 a1 ac; apply eval_bexp_instr_safe_succ_Isbc.
  - move => v a0 a1 ac; apply eval_bexp_instr_safe_succ_Isbb.
  - move => v a0 a1; apply eval_bexp_instr_safe_succ_Imul.
  - move => v t a; apply eval_bexp_instr_safe_succ_Ivpc.
Qed.

Lemma eval_bexp_instr_safe_succs_Ishl E t a n p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Ishl t a n)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Ishl t a n)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Ishl t a n)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_shl_safe.
  by case : (Typ.is_unsigned (atyp a E)) => /=;
      rewrite !eval_exp_atomic
              (ssa_unchanged_program_eval_atomic Hun Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Icshl E t t0 a a0 n p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Icshl t t0 a a0 n)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Icshl t t0 a a0 n)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Icshl t t0 a a0 n)) s2.
Proof.
  move => Hun Hev /=.
  rewrite /bexp_atomic_cshl_safe.
  by case : (Typ.is_unsigned (atyp a E)) => /=;
       rewrite !eval_exp_atomic;
       move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1];
       rewrite (ssa_unchanged_program_eval_atomic Hun0 Hev)
               (ssa_unchanged_program_eval_atomic Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Iadd E t a a0 p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Iadd t a a0)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadd t a a0)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadd t a a0)) s2.
Proof.
  move => Hun Hev /=.
  rewrite !eval_bexp_if /= !eval_exp_atomic.
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1].
  by rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
             !(ssa_unchanged_program_eval_atomic Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Iadc E t a a0 a1 p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Iadc t a a0 a1)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadc t a a0 a1)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Iadc t a a0 a1)) s2.
Proof.
  move => Hun Hev /=.
  rewrite !eval_bexp_if /= !eval_exp_atomic.
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun].
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc].
  by rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
             !(ssa_unchanged_program_eval_atomic Hun1 Hev)
             !(ssa_unchanged_program_eval_atomic Hunc Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Isub E t a a0 p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Isub t a a0)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isub t a a0)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isub t a a0)) s2.
Proof.
  move => Hun Hev /=.
  rewrite !eval_bexp_if /= !eval_exp_atomic.
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1].
  by rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
             !(ssa_unchanged_program_eval_atomic Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Isbc E t a a0 a1 p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Isbc t a a0 a1)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbc t a a0 a1)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbc t a a0 a1)) s2.
Proof.
  move => Hun Hev /=.
  rewrite !eval_bexp_if /= !eval_exp_atomic.
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun].
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc].
  by rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
             !(ssa_unchanged_program_eval_atomic Hun1 Hev)
             !(ssa_unchanged_program_eval_atomic Hunc Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Isbb E t a a0 a1 p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Isbb t a a0 a1)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbb t a a0 a1)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Isbb t a a0 a1)) s2.
Proof.
  move => Hun Hev /=.
  rewrite !eval_bexp_if /= !eval_exp_atomic.
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun].
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc].
  by rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
             !(ssa_unchanged_program_eval_atomic Hun1 Hev)
             !(ssa_unchanged_program_eval_atomic Hunc Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Imul E t a a0 p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr (Imul t a a0)) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E (Imul t a a0)) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E (Imul t a a0)) s2.
Proof.
  move => Hun Hev /=.
  rewrite !eval_bexp_if /= !eval_exp_atomic.
  move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1].
  by rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
             !(ssa_unchanged_program_eval_atomic Hun1 Hev).
Qed.

Lemma eval_bexp_instr_safe_succs_Ivpc E t t0 a p s1 s2 :
 ssa_vars_unchanged_program (rvs_instr (Ivpc t t0 a)) p ->
 eval_program E p s1 s2 ->
 QFBV.eval_bexp (bexp_instr_safe E (Ivpc t t0 a)) s1 ->
 QFBV.eval_bexp (bexp_instr_safe E (Ivpc t t0 a)) s2.
Proof.
  move => Hun Hev /=.
  rewrite !eval_bexp_if /= !eval_exp_atomic.
  by rewrite (ssa_unchanged_program_eval_atomic Hun Hev).
Qed.

Lemma eval_bexp_instr_safe_succs E i p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr i) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s1 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s2.
Proof.
  case i; rewrite /bexp_instr_safe => //.
  - move => v a n; apply eval_bexp_instr_safe_succs_Ishl.
  - move => u v a0 a1 n; apply eval_bexp_instr_safe_succs_Icshl.
  - move => v a0 a1; apply eval_bexp_instr_safe_succs_Iadd.
  - move => v a0 a1 ac; apply eval_bexp_instr_safe_succs_Iadc.
  - move => v a0 a1; apply eval_bexp_instr_safe_succs_Isub.
  - move => v a0 a1 ac; apply eval_bexp_instr_safe_succs_Isbc.
  - move => v a0 a1 ac; apply eval_bexp_instr_safe_succs_Isbb.
  - move => v a0 a1; apply eval_bexp_instr_safe_succs_Imul.
  - move => v ty a; apply eval_bexp_instr_safe_succs_Ivpc.
Qed.

(*
Lemma eval_bexp_instr_safe_pred E i s1 s2 :
  ssa_vars_unchanged_instr (rvs_instr i) i ->
  eval_instr E i s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s2 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s1.
Proof.
  case i => //.
  - move => v a n Hun Hev.
    rewrite /= !eval_exp_atomic.
    rewrite (unchanged_instr_eval_instr Hun Hev) //.
  - move => u v a0 a1 n Hun Hev.
    rewrite /= !eval_exp_atomic.
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite (unchanged_instr_eval_instr Hun1 Hev) //.
  - move => v a0 a1 Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic. 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev) //.
  - move => v a0 a1 ac Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic. 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun].
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hunc].
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev)
            (unchanged_instr_eval_instr Hunc Hev) //.
  - move => v a0 a1 Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic. 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev) //.
  - move => v a0 a1 ac Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic. 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun].
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hunc].
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev)
            (unchanged_instr_eval_instr Hunc Hev) //.
  - move => v a0 a1 ac Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic. 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun].
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hunc].
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev)
            (unchanged_instr_eval_instr Hunc Hev) //.
  - move => v a0 a1 Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic. 
    move : (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite (unchanged_instr_eval_instr Hun0 Hev)
            (unchanged_instr_eval_instr Hun1 Hev) //.
  - move => v ty a Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    rewrite (unchanged_instr_eval_instr Hun Hev) //.
Qed.

Lemma eval_bexp_instr_safe_preds E i p s1 s2 :
  ssa_vars_unchanged_program (rvs_instr i) p ->
  eval_program E p s1 s2 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s2 ->
  QFBV.eval_bexp (bexp_instr_safe E i) s1.
Proof.
  case i; rewrite /bexp_instr_safe => //.
  - move => v a n Hun Hev.
    rewrite /= !eval_exp_atomic.
    rewrite (ssa_unchanged_program_eval_atomic Hun Hev) //.
  - move => u v a0 a1 n Hun Hev.
    rewrite /= !eval_exp_atomic.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite (ssa_unchanged_program_eval_atomic Hun1 Hev) //.
  - move => v a0 a1 Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) //.
  - move => v a0 a1 ac Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun].
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc].
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) //.
  - move => v a0 a1 Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) //.
  - move => v a0 a1 ac Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun].
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc].
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) //.
  - move => v a0 a1 ac Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun].
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hunc].
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev)
            !(ssa_unchanged_program_eval_atomic Hunc Hev) //.
  - move => v a0 a1 Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    move : (ssa_unchanged_program_union1 Hun) => {Hun} [Hun0 Hun1].
    rewrite !(ssa_unchanged_program_eval_atomic Hun0 Hev)
            !(ssa_unchanged_program_eval_atomic Hun1 Hev) //.
  - move => v ty a Hun Hev.
    rewrite !eval_bexp_if /= !eval_exp_atomic.
    rewrite (ssa_unchanged_program_eval_atomic Hun Hev) //.
Qed.
 *)
(*
Fixpoint bexp_program_qfbv E (p : program) : QFBV.bexp :=
  match p with
  | [::] => qfbv_true
  | hd::tl => qfbv_conj (bexp_instr E hd)
                        (bexp_program_qfbv (instr_succ_typenv hd E) tl)
  end.

Definition bexp_prefix_hd_safe E pre prefix hd : QFBV.bexp :=
  qfbv_disj (qfbv_lneg (qfbv_conj pre (bexp_program_qfbv E prefix)))
            (bexp_instr_safe (program_succ_typenv prefix E) hd).

Fixpoint bexp_program_safe_qfbv E pre prefix (p : program) : seq QFBV.bexp :=
  match p with
  | [::] => [::]
  | hd::tl => (bexp_prefix_hd_safe E pre prefix hd)
                ::(bexp_program_safe_qfbv (instr_succ_typenv hd E) pre (rcons prefix hd) tl)
  end.

Definition bexp_program_safe_at E (p : program) s : bool :=
  if (bexp_program E p) s then
    QFBV.eval_bexp (bexp_program_safe E p) s
  else
    true.
*)

Fixpoint bexp_program_safe_at E p : QFBV.bexp :=
  match p with
  | [::] => qfbv_true
  | hd::tl =>
    qfbv_conj (bexp_instr_safe E hd)
              (qfbv_disj
                 (qfbv_lneg (bexp_instr E (rng_instr hd)))
                 (bexp_program_safe_at (instr_succ_typenv hd E) tl))
  end.

(* Question: is (SSAStore.conform s E) too strong? *)
Lemma eval_bexp_program_safe1 E pre p :
  well_formed_rbexp E pre ->
  ssa_vars_unchanged_program (vars_rbexp pre) p ->
  well_formed_ssa_program E p ->
  (forall s, SSAStore.conform s E ->
             QFBV.eval_bexp (bexp_rbexp pre) s ->
             QFBV.eval_bexp (bexp_program_safe_at E p) s) ->
  (forall s, SSAStore.conform s E ->
             eval_rbexp pre s ->
             ssa_program_safe_at E p s).
Proof.
  move=> Hwf_pre Hun Hwf_p H s.
  have: (forall t : SSAStore.t,
            bvs_eqi E s t ->
            SSAStore.conform t E ->
            QFBV.eval_bexp (bexp_rbexp pre) t ->
            QFBV.eval_bexp (bexp_program_safe_at E p) t).
  { move=> t Heqi Hco Hpre. exact: (H _ Hco Hpre). }
  move: {H} Hwf_pre Hun Hwf_p s.

  elim: p E => [| i p IH] E /=.
  - move=> *. exact: ssa_program_safe_at_nil.
  - rewrite ssa_unchanged_program_cons /well_formed_ssa_program.
    rewrite well_formed_program_cons ssa_single_assignment_cons.
    rewrite ssa_unchanged_program_cons.
    move=> Hwf_pre /andP [Hun_prei Hun_prep]
            /andP [/andP [/andP
                           [Hwf_i Hwf_p] /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
    move=> s H Hco Hpre. apply: ssa_program_safe_at_cons.
    + move/eval_bexp_rbexp: Hpre => Hpre. apply/(eval_bexp_instr_safe _ Hwf_i).
      move: (H s (bvs_eqi_refl s) Hco Hpre) => /andP [H1 _]. exact: H1.
    + move=> t Hei. have Hssa_p: well_formed_ssa_program (instr_succ_typenv i E) p.
      { repeat (apply/andP; split); try assumption.
        apply: (ssa_unchanged_program_replace
                  (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
        rewrite ssa_unchanged_program_union. rewrite Hun_Ep /=. exact: Hun_ip. }

      move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsubm.
      rewrite -ssa_vars_unchanged_rng_instr in Hun_Ei.
      move: (bvs_eqi_eval_instr Hun_Ei Hei) => Hei_st.
      move: (well_formed_rbexp_submap Hsubm Hwf_pre) => Hwf_pre_succ.

      apply: (IH (instr_succ_typenv i E) Hwf_pre_succ Hun_prep Hssa_p).
      * move=> t' Heqi Hco' Hpre'.
        have Heqi': bvs_eqi E s t'.
        { move: (bvs_eqi_submap Hsubm Heqi) => Hei_st'.
          exact: (bvs_eqi_trans Hei_st Hei_st'). }
        move: (bvs_eqi_conform Heqi' Hco) => Hco'E.
        move: (H _ Heqi' Hco'E Hpre') => /andP [H1 H2].

        move: (bexp_instr_eval (well_formed_rng_instr Hwf_i) Hco Hun_Ei Hei).
        move/andP: Hwf_i => [Hwd_i Hwt_i].
        rewrite -rng_instr_succ_typenv in Heqi.
        rewrite (bvs_eqi_qfbv_eval_bexp
                 (bexp_instr_are_defined (well_defined_rng_instr Hwd_i)) Heqi).
        move=> Heb. rewrite Heb /= in H2. exact: H2.
      * rewrite -rng_instr_succ_typenv.
        exact: (conform_eval_succ_typenv (well_formed_rng_instr Hwf_i) Hco Hei).
      * rewrite -ssa_vars_unchanged_rng_instr in Hun_prei.
        apply/(ssa_unchanged_instr_eval_rbexp Hun_prei Hei). exact: Hpre.
Qed.

(* Evaluate safety conditions one by one.
   Typing environments are different for the safety conditions of
   different instructions. *)
Fixpoint bexp_program_safe_steps E p s : Prop :=
  SSAStore.conform s E ->
  match p with
  | [::] => True
  | hd::tl =>
    QFBV.eval_bexp (bexp_instr_safe E hd) s /\
    ((QFBV.eval_bexp (bexp_instr E (rng_instr hd)) s) ->
     (bexp_program_safe_steps (instr_succ_typenv hd E) tl s))
  end.

Lemma eval_bexp_program_safe_steps E pre p :
  well_formed_rbexp E pre ->
  ssa_vars_unchanged_program (vars_rbexp pre) p ->
  well_formed_ssa_program E p ->
  (forall s, QFBV.eval_bexp (bexp_rbexp pre) s ->
             bexp_program_safe_steps E p s) ->
  (forall s, SSAStore.conform s E ->
             eval_rbexp pre s ->
             ssa_program_safe_at E p s).
Proof.
  move=> Hwf_pre Hun Hwf_p H s.
  have: (forall t : SSAStore.t,
            bvs_eqi E s t ->
            QFBV.eval_bexp (bexp_rbexp pre) t ->
            bexp_program_safe_steps E p t).
  { move=> t Heqi Hpre. exact: (H _ Hpre). }
  move: {H} Hwf_pre Hun Hwf_p s.

  elim: p E => [| i p IH] E /=.
  - move=> *. exact: ssa_program_safe_at_nil.
  - rewrite ssa_unchanged_program_cons /well_formed_ssa_program.
    rewrite well_formed_program_cons ssa_single_assignment_cons.
    rewrite ssa_unchanged_program_cons.
    move=> Hwf_pre /andP [Hun_prei Hun_prep]
            /andP [/andP [/andP
                           [Hwf_i Hwf_p] /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
    move=> s H Hco Hpre. apply: ssa_program_safe_at_cons.
    + move/eval_bexp_rbexp: Hpre => Hpre. apply/(eval_bexp_instr_safe _ Hwf_i).
      move: (H s (bvs_eqi_refl s) Hpre Hco) => [H1 _]. exact: H1.
    + move=> t Hei. have Hssa_p: well_formed_ssa_program (instr_succ_typenv i E) p.
      { repeat (apply/andP; split); try assumption.
        apply: (ssa_unchanged_program_replace
                  (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
        rewrite ssa_unchanged_program_union. rewrite Hun_Ep /=. exact: Hun_ip. }

      move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsubm.
      rewrite -ssa_vars_unchanged_rng_instr in Hun_Ei.
      move: (bvs_eqi_eval_instr Hun_Ei Hei) => Hei_st.
      move: (well_formed_rbexp_submap Hsubm Hwf_pre) => Hwf_pre_succ.

      apply: (IH (instr_succ_typenv i E) Hwf_pre_succ Hun_prep Hssa_p).
      * move=> t' Heqi Hpre'.
        have Heqi': bvs_eqi E s t'.
        { move: (bvs_eqi_submap Hsubm Heqi) => Hei_st'.
          exact: (bvs_eqi_trans Hei_st Hei_st'). }
        move: (bvs_eqi_conform Heqi' Hco) => Hco'E.
        move: (H _ Heqi' Hpre' Hco'E) => [H1 H2].

        move: (bexp_instr_eval (well_formed_rng_instr Hwf_i) Hco Hun_Ei Hei).
        move/andP: Hwf_i => [Hwd_i Hwt_i].
        rewrite -rng_instr_succ_typenv in Heqi.
        rewrite (bvs_eqi_qfbv_eval_bexp
                   (bexp_instr_are_defined (well_defined_rng_instr Hwd_i)) Heqi).
        move=> Heb. rewrite Heb /= in H2. by apply: H2.
      * rewrite -rng_instr_succ_typenv.
        exact: (conform_eval_succ_typenv (well_formed_rng_instr Hwf_i) Hco Hei).
      * rewrite -ssa_vars_unchanged_rng_instr in Hun_prei.
        apply/(ssa_unchanged_instr_eval_rbexp Hun_prei Hei). exact: Hpre.
Qed.

(*
Lemma eval_bexp_program_safe2 E pre p :
  ssa_vars_unchanged_program (vars_rbexp pre) p ->
  well_formed_ssa_program E p ->
  (forall s, eval_rbexp pre s ->
             ssa_program_safe_at E p s) ->
  (forall s, QFBV.eval_bexp (bexp_rbexp pre) s ->
             QFBV.eval_bexp (bexp_program_safe_at E p) s).
Proof.
  elim : p E => /=.
  - done.
  - move => hd tl IH E Hun Hwf H s Hpre.
    move : (H s (eval_bexp_rbexp1 Hpre)) => Hhdtl.
    inversion_clear Hhdtl.
    apply /andP; split; [idtac | apply /andP; split].
    + apply eval_bexp_instr_safe.
      * move : Hwf; rewrite /well_formed_ssa_program
        => /andP [/andP [Hwf _] _].
        by move : (well_formed_program_cons1 Hwf).
      * done.
    + apply IH.
      * apply (ssa_unchanged_program_tl Hun).
      * apply : (well_formed_ssa_tl Hwf).
      * move => s' Hpre'.
        apply (H1 s').
        Check (H s'').
 *)


(* Soundness of safety check. *)

Definition ssa_spec_safe_qfbv sp : Prop :=
  forall s,
    SSAStore.conform s (sinputs sp) ->
    QFBV.eval_bexp (bexp_rbexp (rng_bexp (spre sp))) s ->
    QFBV.eval_bexp (bexp_program_safe_at (sinputs sp) (sprog sp)) s.

Lemma ssa_spec_safe_qfbv_sound sp :
  well_formed_ssa_spec sp -> ssa_spec_safe_qfbv sp -> ssa_spec_safe sp.
Proof.
  move=> Hwf. move: Hwf (well_formed_ssa_spec_program Hwf).
  case: sp => E f p g. rewrite /well_formed_ssa_spec /well_formed_spec
                               /ssa_spec_safe_qfbv /ssa_spec_safe /=.
  move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
          Hwf_ssa_p Hbv s Hco Hf.

  move: (well_formed_rng_bexp Hwf_f) => Hwf_f_rng.
  move: (Hwf_f_rng). move/andP=> [Hdef_f_rng Hwt_f_rng].
  move/defsubP: Hdef_f_rng => Hsub_f_rng.
  move: (ssa_unchanged_program_subset Hun_Ep Hsub_f_rng) => Hun_f_rng.

  apply: (eval_bexp_program_safe1 Hwf_f_rng Hun_f_rng Hwf_ssa_p _ Hco Hf).
  exact: Hbv.
Qed.


Definition ssa_spec_safe_qfbv_steps sp : Prop :=
  forall s, QFBV.eval_bexp (bexp_rbexp (rng_bexp (spre sp))) s ->
            bexp_program_safe_steps (sinputs sp) (sprog sp) s.

Lemma ssa_spec_safe_qfbv_steps_sound sp :
  well_formed_ssa_spec sp -> ssa_spec_safe_qfbv_steps sp -> ssa_spec_safe sp.
Proof.
  move=> Hwf. move: Hwf (well_formed_ssa_spec_program Hwf). case: sp => E f p g.
  rewrite /well_formed_ssa_spec /well_formed_spec /ssa_spec_safe_qfbv
          /ssa_spec_safe /ssa_spec_safe_qfbv_steps /=.
  move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
          Hwf_ssa_p /= Hbv s Hco Hf.

  move: (well_formed_rng_bexp Hwf_f) => Hwf_f_rng.
  move: (Hwf_f_rng). move/andP=> [Hdef_f_rng Hwt_f_rng].
  move/defsubP: Hdef_f_rng => Hsub_f_rng.
  move: (ssa_unchanged_program_subset Hun_Ep Hsub_f_rng) => Hun_f_rng.

  apply: (eval_bexp_program_safe_steps Hwf_f_rng Hun_f_rng Hwf_ssa_p _ Hco Hf).
  exact: Hbv.
Qed.

Lemma ssa_spec_safe_qfbv_steps_complete sp :
  well_formed_ssa_spec sp -> ssa_spec_safe sp -> ssa_spec_safe_qfbv_steps sp.
Proof.
  case: sp => E f p g.
  rewrite /well_formed_ssa_spec /well_formed_spec /ssa_spec_safe_qfbv
          /ssa_spec_safe /ssa_spec_safe_qfbv_steps /=.
  move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
          Hsafe s Hf.
  case: f Hwf_f Hsafe Hf => [ef rf] => /=.
  rewrite well_formed_bexp_split => /andP [/= Hwf_ef Hwf_rf] Hsafe Hf.
  clear ef Hwf_ef g Hwf_g. move: (Hsafe s) => {Hsafe} Hsafe.
  elim: p E rf Hwf_rf Hwf_p Hun_Ep Hssa s Hsafe Hf => [| i p IH] //=.
  move=> E f Hwf /andP [Hwf_i Hwf_p] Hun_Eip /andP [Hun_ip Hssa_p]
           s Hsafe Hf Hco.
  rewrite ssa_unchanged_program_cons in Hun_Eip.
  move/andP: Hun_Eip => [Hun_Ei Hun_Ep].
  move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsubm.
  move/eval_bexp_rbexp: Hf=> Hf. move: (Hsafe Hco Hf) => Hsafe_at.
  inversion_clear Hsafe_at. split.
  - apply/(eval_bexp_instr_safe s Hwf_i). assumption.
  - move=> His. apply: (IH (instr_succ_typenv i E) f
                           (well_formed_rbexp_submap Hsubm Hwf) Hwf_p
                           _ Hssa_p).
    + apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union Hun_Ep Hun_ip. exact: is_true_true.
    + move=> Hco_s Hf_s. apply: H0.
      exact: (eval_bexp_instr Hwf_i Hco Hco_s His).
    + apply/eval_bexp_rbexp. exact: Hf.
Qed.


Section SplitConditions.

  Import QFBV.

  (* Construct safety conditions with full prefix information. *)

  (*
   * E: the typing environment after pre_is and before p
   * pre_is: the prefix of instructions
   * pre_es: the QFBV expressions encoding the prefix of instructions
   * p: the remaining program to be converted
   *)
  Fixpoint bexp_program_safe_split_rec_full E pre_is (pre_es : seq QFBV.bexp) p :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (E, pre_is, pre_es, hd, tl, bexp_instr_safe E hd)
        ::(bexp_program_safe_split_rec_full
             (instr_succ_typenv hd E) (rcons pre_is hd)
             (rcons pre_es (bexp_instr E (rng_instr hd))) tl)
    end.

  Definition bexp_program_safe_split_full E p :=
    bexp_program_safe_split_rec_full E [::] [::] p.

  Lemma bexp_program_safe_split_rec_full_env E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_rec_full E pre_is pre_es p) ->
      forall Einit,
        E = program_succ_typenv pre_is Einit ->
        E' = program_succ_typenv pre_is' Einit.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. move=> _ Einit. by apply.
    - move=> Hin Einit H. apply: (IH _ _ _ _ _ _ _ _ _ Hin).
      rewrite program_succ_typenv_rcons. rewrite -H. reflexivity.
  Qed.

  Lemma bexp_program_safe_split_rec_full_is E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_rec_full E pre_is pre_es p) ->
      pre_is' ++ hd::tl = pre_is ++ p.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. reflexivity.
    - move=> Hin. rewrite -(cat_rcons i). apply: IH. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_rec_full_is_prefix E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_rec_full E pre_is pre_es p) ->
      exists suf, pre_is' = pre_is ++ suf.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. move=> _. exists [::]. rewrite cats0. reflexivity.
    - move=> Hin. move: (IH _ _ _ _ _ _ _ _ _ Hin) => [suf H]. exists (i::suf).
      rewrite -(cat_rcons). assumption.
  Qed.

  Lemma bexp_program_safe_split_rec_full_es E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_rec_full E pre_is pre_es p) ->
      forall Einit,
        E = program_succ_typenv pre_is Einit ->
        pre_es = bexp_program Einit (rng_program pre_is) ->
        pre_es' = bexp_program Einit (rng_program pre_is').
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. move=> _ Einit _. by apply.
    - move=> Hin Einit Hinit H. apply: (IH _ _ _ _ _ _ _ _ _ Hin).
      + rewrite program_succ_typenv_rcons. rewrite -Hinit. reflexivity.
      + rewrite rng_program_rcons. rewrite bexp_program_rcons.
        rewrite -H. rewrite rng_program_succ_typenv. rewrite -Hinit. reflexivity.
  Qed.

  Lemma bexp_program_safe_split_full_env E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      E' = program_succ_typenv pre_is' E.
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    apply: (bexp_program_safe_split_rec_full_env Hin). reflexivity.
  Qed.

  Lemma bexp_program_safe_split_full_is E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      pre_is' ++ (hd::tl) = p.
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_safe_split_rec_full_is Hin).
  Qed.

  Lemma bexp_program_safe_split_full_es E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      pre_es' = bexp_program E (rng_program pre_is').
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
      by apply: (bexp_program_safe_split_rec_full_es Hin).
  Qed.

  Lemma bexp_program_safe_split_rec_full_complete E pre_is pre_es p :
    forall pre_is' hd tl suf,
      pre_is' = pre_is ++ suf ->
      pre_is' ++ (hd :: tl) = pre_is ++ p ->
      exists E' pre_es' safe,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_safe_split_rec_full E pre_is pre_es p).
  Proof.
    elim: p E pre_is pre_es => [| i1 p IH] E pre_is pre_es /=.
    - move=> pre_is' hd tl suf Heq1 Heq2. rewrite Heq1 in Heq2.
      rewrite -catA in Heq2. move: (catsl_inj Heq2) => Heq3.
      have: size (suf ++ hd :: tl) = size ([::] : seq instr) by rewrite Heq3.
      rewrite seq.size_cat /=. rewrite -addn1. rewrite addnA.
      move/eqP. rewrite addn_eq0. move/andP=> [_ /eqP H]. discriminate.
    - move=> pre_is' hd tl suf Heq1 Heq2.
      move: (Heq2). rewrite {1}Heq1. rewrite -catA. move=> H.
      move: (catsl_inj H) => {H} Heq3. move: Heq1 Heq2 Heq3. case: suf => /=.
      + rewrite cats0. move=> ?; subst. move=> Heq1 [] => ? ?; subst.
        exists E. exists pre_es. exists (bexp_instr_safe E i1). left. reflexivity.
      + move=> suf_i suf_p Heq1 Heq2 Heq3. case: Heq3 => Heq Heq3.
        rewrite Heq in Heq1.
        rewrite -!cat_rcons in Heq1. rewrite -(cat_rcons i1) in Heq2.

        move: (IH (instr_succ_typenv i1 E) (rcons pre_is i1)
                  (rcons pre_es (bexp_instr E (rng_instr i1))) pre_is' hd tl suf_p
                  Heq1 Heq2). move=> [E' [pre_es' [safe' Hin]]].
        exists E'. exists pre_es'. exists safe'. right. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_full_complete E p :
    forall pre_is' hd tl,
      pre_is' ++ (hd :: tl) = p ->
      exists E' pre_es' safe,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_safe_split_full E p).
  Proof.
    move=> pre_is' hd tl Heq. apply: bexp_program_safe_split_rec_full_complete.
    - rewrite cat0s. reflexivity.
    - rewrite cat0s. assumption.
  Qed.

  Lemma bexp_program_safe_split_steps_full E f p :
    well_formed_ssa_program E p ->
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_safe_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe) s) ->
    (forall s, QFBV.eval_bexp f s ->
               bexp_program_safe_steps E p s).
  Proof.
    rewrite /bexp_program_safe_split_full. move=> Hwf He s.
    have: QFBV.eval_bexp (qfbv_conjs [::]) s by done.
    move: s He. move: [::]. move: [::].
    elim: p E f Hwf => [| i p IH] E f Hwf pre_es pre_is s //= He Hprefix Hf Hco. split.
    - move: (He E pre_is pre_es i p (bexp_instr_safe E i)
                (or_introl _ (Logic.eq_refl
                                (E, pre_is, pre_es, i, p, bexp_instr_safe E i)))
                s Hco).
      rewrite negb_and Hf Hprefix /=. by apply.
    - move=> His. move: (well_formed_ssa_tl Hwf) => Hwf_p.
      apply: (IH (instr_succ_typenv i E) f Hwf_p
                 (rcons pre_es (bexp_instr E (rng_instr i))) (rcons pre_is i)).
      + move=> E_t pre_is_t pre_es_t i_t p_t safe_t Hin_t t Hco_t.
        apply: (He E_t pre_is_t pre_es_t i_t p_t safe_t _ t Hco_t).
        right. assumption.
      + rewrite eval_qfbv_conjs_rcons. rewrite Hprefix His. exact: is_true_true.
      + exact: Hf.
  Qed.


  (* Construct safety conditions with less prefix information. *)

  Fixpoint bexp_program_safe_split_rec E (pre_es : seq QFBV.bexp) p :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (E, pre_es, bexp_instr_safe E hd)
        ::(bexp_program_safe_split_rec
             (instr_succ_typenv hd E) (rcons pre_es (bexp_instr E (rng_instr hd))) tl)
    end.

  Definition bexp_program_safe_split E p := bexp_program_safe_split_rec E [::] p.

  Lemma bexp_program_safe_split_rec_full_partial E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_rec_full E pre_is pre_es p) ->
      List.In (E', pre_es', safe) (bexp_program_safe_split_rec E pre_es p).
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ? ?; subst. left. reflexivity.
    - move=> Hin. right. exact: (IH _ _ _ _ _ _ _ _ _ Hin).
  Qed.

  Lemma bexp_program_safe_split_rec_partial_full Einit E pre_is pre_es p :
    forall E' pre_es' safe,
      List.In (E', pre_es', safe) (bexp_program_safe_split_rec E pre_es p) ->
      E = program_succ_typenv pre_is Einit ->
      pre_es = bexp_program Einit (rng_program pre_is) ->
    exists pre_is' hd tl,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_rec_full E pre_is pre_es p) /\
      (pre_is' ++ (hd :: tl) = pre_is ++ p) /\
      (pre_es' = bexp_program Einit (rng_program pre_is')).
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_es' safe. case.
    - case=> ? ? ?; subst. move=> _ Hes'. exists pre_is. exists i. exists p.
      repeat split.
      + left. reflexivity.
      + assumption.
    - move=> Hin HE Hes. move: (IH _ (rcons pre_is i) _ _ _ _ Hin).
      rewrite program_succ_typenv_rcons -HE.
      rewrite rng_program_rcons bexp_program_rcons -Hes.
      rewrite rng_program_succ_typenv -HE.
      move=> H. move: (H (Logic.eq_refl _) (Logic.eq_refl _)) => {H}.
      move=> [pre_is' [hd [tl [Hin' [His' Hes']]]]].
      exists pre_is'; exists hd; exists tl. repeat split.
      + right. assumption.
      + rewrite His'. rewrite cat_rcons. reflexivity.
      + assumption.
  Qed.

  Lemma bexp_program_safe_split_full_partial E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      List.In (E', pre_es', safe) (bexp_program_safe_split E p).
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    apply: bexp_program_safe_split_rec_full_partial. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_partial_full E p :
    forall E' pre_es' safe,
      List.In (E', pre_es', safe) (bexp_program_safe_split E p) ->
      exists pre_is' hd tl,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_safe_split_full E p) /\
        (pre_is' ++ (hd :: tl) = p) /\
        (pre_es' = bexp_program E (rng_program pre_is')).
  Proof.
    move=> E' pre_es' safe Hin.
    by apply: (bexp_program_safe_split_rec_partial_full Hin).
  Qed.

  Lemma bexp_program_safe_split_steps E f p :
    well_formed_ssa_program E p ->
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe) (bexp_program_safe_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe) s) ->
    (forall s, QFBV.eval_bexp f s ->
               bexp_program_safe_steps E p s).
  Proof.
    move=> Hwf He. apply: (bexp_program_safe_split_steps_full Hwf).
    move=> Ee pre_is pre_es hd tl safe Hin s Hco. apply: (He _ _ _ _ _ Hco).
    exact: (bexp_program_safe_split_full_partial Hin).
  Qed.

End SplitConditions.
