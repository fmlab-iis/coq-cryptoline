
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

Definition qfbv_const w n := QFBV.Econst (NBitsDef.from_nat w n).

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

Lemma size_exp_const E w n : QFBV.exp_size (qfbv_const w n) E = w.
Proof. rewrite /= size_from_nat. reflexivity. Qed.

Lemma to_nat_from_nat_very_small w n : n <= w -> to_nat (from_nat w n) = n.
Proof.
  move=> H. rewrite to_nat_from_nat. apply: div.modn_small.
  elim: w n H => [| w IH n H] //=. case: n H => [| n] H /=.
  - exact: Nats.expn2_gt0.
  - rewrite ltnS in H. move: (IH _ H) => {IH H} H.
    case: w H => [| w] H //=. rewrite -(addn1 n) expnS mul2n -addnn.
    apply: (Nats.ltn_addn H). exact: Nats.expn2_gt1.
Qed.

Lemma vars_exp_atomic a :
  QFBV.vars_exp (qfbv_atomic a) = vars_atomic a.
Proof. by case: a. Qed.

Lemma size_exp_atomic E a :
  are_defined (vars_atomic a) E -> size_matched_atomic a ->
  QFBV.exp_size (qfbv_atomic a) E = asize a E.
Proof.
  case: a => //=. move=> t bs _ Hs. rewrite (eqP Hs). reflexivity.
Qed.


(* Make conjunctions of QFBV expressions
   (right associativity, easy for induction) *)

Fixpoint qfbv_conjs es :=
  match es with
  | [::] => QFBV.Btrue
  | hd::tl => qfbv_conj hd (qfbv_conjs tl)
  end.

Lemma well_formed_bexp_qfbv_conjs_rcons E es e :
  QFBV.well_formed_bexp (qfbv_conjs (rcons es e)) E =
  QFBV.well_formed_bexp (qfbv_conjs es) E && QFBV.well_formed_bexp e E.
Proof.
  elim: es => [| hd tl IH] /=.
  - rewrite andbT. reflexivity.
  - rewrite -andbA. rewrite -IH. reflexivity.
Qed.

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

Lemma qfbv_conjs_inj es1 es2 :
  qfbv_conjs es1 = qfbv_conjs es2 -> es1 = es2.
Proof.
  elim: es1 es2 => [| e1 es1 IH] [| e2 es2] //=.
  case=> H1 H2. rewrite H1 (IH _ H2). reflexivity.
Qed.

(* Make conjunctions of QFBV expressions
   (left associativity, good for bit-blasting cache) *)

Fixpoint qfbv_conjs_rec pre_es es :=
  match es with
  | [::] => pre_es
  | hd::tl => qfbv_conjs_rec (qfbv_conj pre_es hd) tl
  end.

(* Add QFBV.Btrue at the beginning to make qfbv_conjs_la injective *)
Definition qfbv_conjs_la es :=
  match es with
  | [::] => QFBV.Btrue
  | e::es => qfbv_conjs_rec (qfbv_conj QFBV.Btrue e) es
  end.

Lemma qfbv_conjs_rec_singleton pre_es e :
  qfbv_conjs_rec pre_es [::e] = qfbv_conj pre_es e.
Proof. reflexivity. Qed.

Lemma qfbv_conjs_rec_cons pre_es e es :
  qfbv_conjs_rec pre_es (e::es) = qfbv_conjs_rec (qfbv_conj pre_es e) es.
Proof. reflexivity. Qed.

Lemma qfbv_conjs_rec_cat pre_es es1 es2 :
  qfbv_conjs_rec pre_es (es1 ++ es2) = qfbv_conjs_rec (qfbv_conjs_rec pre_es es1) es2.
Proof. elim: es1 pre_es es2 => [| e1 es1 IH] //=. Qed.

Lemma qfbv_conjs_rec_rcons pre_es es e :
  qfbv_conjs_rec pre_es (rcons es e) = qfbv_conj (qfbv_conjs_rec pre_es es) e.
Proof. by elim: es pre_es e => [| hd tl IH] //=. Qed.

Lemma qfbv_conjs_rec_conj e1 es1 e2 es2 :
  qfbv_conjs_rec (qfbv_conj QFBV.Btrue e1) es1 =
  qfbv_conjs_rec (qfbv_conj QFBV.Btrue e2) es2 ->
  e1 = e2 /\ es1 = es2.
Proof.
  move: es1 es2 e1 e2. apply: last_ind => //=.
  - case=> [| e3 es2] e1 e2 //=.
    + case. by move=> ->.
    + move=> H. apply: False_ind. move: H. move: {2}QFBV.Btrue.
      elim: es2 e1 e2 e3 => [| e es IH] e1 e2 e3 e4 //= H. apply: IH. exact: H.
  - move=> es1 le1 IH. case/lastP => //=.
    + move=> e1 e2 H. apply: False_ind. move: H. move: {1}QFBV.Btrue.
      clear IH. elim: es1 le1 e1 e2 => [| e es IH] e1 e2 e3 e4 //= H. apply: IH.
      exact: H.
    + move=> es2 le2 e1 e2 /= H. rewrite !qfbv_conjs_rec_rcons in H.
      case: H. move=> H1 ->. move: (IH _ _ _ H1). case=> -> ->. done.
Qed.

Lemma qfbv_conjs_la_inj es1 es2 :
  qfbv_conjs_la es1 = qfbv_conjs_la es2 -> es1 = es2.
Proof.
  rewrite /qfbv_conjs_la. case: es1 => [| e1 es1] //=.
  - case: es2 => [| e2 es2] //=. move: {2}QFBV.Btrue. move=> e1 H.
    apply: False_ind. elim: es2 e1 e2 H => [| e es IH] e1 e2 /= H.
    + discriminate.
    + apply: IH. exact: H.
  - case: es2 => [| e2 es2] //=.
    + move: {1}QFBV.Btrue. move=> e2 H. apply: False_ind.
      elim: es1 e1 e2 H => [| e es IH] e1 e2 /= H.
      * discriminate.
      * apply: IH. exact: H.
    + move=> H. move: (qfbv_conjs_rec_conj H) => [-> ->]. reflexivity.
Qed.

Lemma eval_qfbv_conjs_rec s pre_es es :
  QFBV.eval_bexp (qfbv_conjs_rec pre_es es) s =
  QFBV.eval_bexp pre_es s && QFBV.eval_bexp (qfbv_conjs_la es) s.
Proof.
  rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
  - rewrite andbT. reflexivity.
  - move: es pre_es e1. apply: last_ind => //=.
    move=> es le1 IH pre_es e1. rewrite !qfbv_conjs_rec_rcons /=.
    rewrite IH. rewrite !andbA. reflexivity.
Qed.

Lemma eval_qfbv_conjs_rec_ra s pre_es es :
  QFBV.eval_bexp (qfbv_conjs_rec pre_es es) s =
  QFBV.eval_bexp pre_es s && QFBV.eval_bexp (qfbv_conjs es) s.
Proof.
  elim: es pre_es => [| e1 es IH] pre_es //=.
  - rewrite andbT. reflexivity.
  - rewrite IH. rewrite /qfbv_conj /=. rewrite andbA. reflexivity.
Qed.

Lemma eval_qfbv_conjs_la_rcons es e s :
  QFBV.eval_bexp (qfbv_conjs_la (rcons es e)) s =
  QFBV.eval_bexp (qfbv_conjs_la es) s && QFBV.eval_bexp e s.
Proof.
  rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
  rewrite qfbv_conjs_rec_rcons /=. reflexivity.
Qed.

Lemma eval_qfbv_conjs_la_cat es1 es2 s :
  QFBV.eval_bexp (qfbv_conjs_la (es1 ++ es2)) s =
  QFBV.eval_bexp (qfbv_conjs_la es1) s && QFBV.eval_bexp (qfbv_conjs_la es2) s.
Proof.
  rewrite /qfbv_conjs_la. case: es1 => [| e1 es1] //=. case: es2 => [| e2 es2] //=.
  - rewrite cats0 andbT. reflexivity.
  - move: es2 e1 e2 es1. apply: last_ind => //=.
    + move=> e1 e2 es1. rewrite cats1. rewrite qfbv_conjs_rec_rcons /=.
      reflexivity.
    + move=> es2 le2 IH. move=> e1 e2 es1. rewrite qfbv_conjs_rec_rcons /=.
      rewrite -cat_rcons. rewrite -rcons_cat. rewrite qfbv_conjs_rec_rcons /=.
      rewrite cat_rcons. rewrite IH. rewrite !andbA. reflexivity.
Qed.

Lemma eval_qfbv_conjs_ra_la s es :
  QFBV.eval_bexp (qfbv_conjs es) s = QFBV.eval_bexp (qfbv_conjs_la es) s.
Proof.
  rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
  move: es e1. apply: last_ind => //=.
  - move=> e1. rewrite andbT. reflexivity.
  - move=> es le IH e1. rewrite qfbv_conjs_rec_rcons /=. rewrite -IH.
    rewrite eval_qfbv_conjs_rcons. rewrite andbA. reflexivity.
Qed.

Lemma well_formed_bexp_qfbv_conjs_rec_rcons E pre_es es e :
  QFBV.well_formed_bexp (qfbv_conjs_rec pre_es (rcons es e)) E =
  QFBV.well_formed_bexp (qfbv_conjs_rec pre_es es) E && QFBV.well_formed_bexp e E.
Proof.
  case: es => [| e1 es] //=. rewrite qfbv_conjs_rec_rcons /=. reflexivity.
Qed.

Lemma well_formed_bexp_qfbv_conjs_la_rcons E es e :
  QFBV.well_formed_bexp (qfbv_conjs_la (rcons es e)) E =
  QFBV.well_formed_bexp (qfbv_conjs_la es) E && QFBV.well_formed_bexp e E.
Proof.
  rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
  rewrite qfbv_conjs_rec_rcons /=. reflexivity.
Qed.

Lemma well_formed_bexp_ra_la E es :
  QFBV.well_formed_bexp (qfbv_conjs es) E = QFBV.well_formed_bexp (qfbv_conjs_la es) E.
Proof.
  rewrite /qfbv_conjs_la. case: es => [| e es] //=.
  move: es e. apply: last_ind => //=.
  - move=> e. rewrite andbT. reflexivity.
  - move=> es le IH e. rewrite well_formed_bexp_qfbv_conjs_rec_rcons.
    rewrite -IH. rewrite well_formed_bexp_qfbv_conjs_rcons. rewrite andbA.
    reflexivity.
Qed.


(* Some evaluation properties *)

Lemma eval_exp_var v s :
  QFBV.eval_exp (qfbv_var v) s = SSAStore.acc v s.
Proof.
  reflexivity.
Qed.

Lemma eval_exp_const s w n :
  QFBV.eval_exp (qfbv_const w n) s = from_nat w n.
Proof. reflexivity. Qed.

Lemma eval_exp_atomic a s :
  QFBV.eval_exp (qfbv_atomic a) s = eval_atomic a s.
Proof.
  case: a => /=; reflexivity.
Qed.

Lemma eval_exp_rexp (e : SSA.rexp) s:
  QFBV.eval_exp (exp_rexp e) s = eval_rexp e s.
  elim: e => w /=.
  - reflexivity.
  - reflexivity.
  - move=> op e IH. case: op => /=; rewrite IH; reflexivity.
  - move=> op e1 IH1 e2 IH2. case: op => /=; rewrite IH1 IH2; reflexivity.
  - move=> v IH n; rewrite IH. reflexivity.
  - move=> v IH n; rewrite IH. reflexivity.
Qed.

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
    let 'qec := qfbv_eq (qfbv_const 1 1) (qfbv_atomic c) in
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
    let 'qe2notext := qfbv_zext 1 (qfbv_not (qfbv_atomic a2)) in
    let 'qe1 := qfbv_zext a_size (qfbv_const 1 1) in
    let 'qerext := qfbv_add (qfbv_add qe1ext qe2notext) qe1 in
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
    let 'qe1ext :=
        if Typ.is_unsigned (atyp a1 E) then qfbv_zext a1_size (qfbv_atomic a1)
        else qfbv_sext a1_size (qfbv_atomic a1) in
    let 'qe2ext :=
        if Typ.is_unsigned (atyp a1 E) then qfbv_zext a1_size (qfbv_atomic a2)
        else qfbv_sext a1_size (qfbv_atomic a2) in
    let 'qerext := qfbv_mul qe1ext qe2ext in
    qfbv_conj (qfbv_eq (qfbv_var vh)
                       (qfbv_high a1_size qerext))
              (qfbv_eq (qfbv_var vl)
                       (qfbv_low a2_size qerext))
  (* Iumulj (v, a1, a2): v = the full multiplication of a1 * a2, which is equivalent
     to Iumull (vh, vl, a1, a2); Join (r, vh, vl) *)
  | SSA.Imulj v a1 a2 =>
    let 'a_size := asize a1 E  in
    let 'qe1ext :=
        if Typ.is_unsigned (atyp a1 E) then qfbv_zext a_size (qfbv_atomic a1)
        else qfbv_sext a_size (qfbv_atomic a1) in
    let 'qe2ext :=
        if Typ.is_unsigned (atyp a1 E) then qfbv_zext a_size (qfbv_atomic a2)
        else qfbv_sext a_size (qfbv_atomic a2) in
    let 'qerext := qfbv_mul qe1ext qe2ext in
    qfbv_eq (qfbv_var v) qerext
  (* Ishl (v, a, n): v = a * 2^n, overflow is forbidden *)
  (* need a better size for NBitsDef.from_nat *)
  | SSA.Ishl v a n =>
    let a_size := asize a E in
    let 'qea := qfbv_atomic a in
    let 'qen := qfbv_const a_size n in
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
    let 'qen := qfbv_const a_size n in
    let 'qeamn := qfbv_const a_size (a_size - n) in
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
    let 'qer := qfbv_shl (qfbv_concat qe1 qe2) (qfbv_const (a1_size + a2_size) n) in
    let 'qel := qfbv_low a2_size qer in
    let 'qeh := qfbv_high a1_size qer in
    qfbv_conj (qfbv_eq (qfbv_var vh) qeh)
              (qfbv_eq (qfbv_var vl) (qfbv_lshr qel (qfbv_const a2_size n)))
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
  mkQFBVSpec { binputs : SSATE.env;
               bpre : QFBV.bexp;
               bprog : seq QFBV.bexp;
               bpost : QFBV.bexp }.

Definition bexp_of_rspec E (s : rspec) : bexp_spec :=
  {| binputs := program_succ_typenv (rsprog s) E;
     bpre := bexp_rbexp (rspre s);
     bprog := bexp_program E (rsprog s);
     bpost := bexp_rbexp (rspost s) |}.


(* Properties of the conversion from programs to QFBV.bexp *)

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

Lemma size_exp_rexp E e :
  well_formed_rexp E e ->
  QFBV.exp_size (exp_rexp e) E = size_of_rexp e E.
Proof.
  elim: e => //=.
  - move=> n bs /andP /= [Hdef Hs]. apply/eqP. exact: Hs.
  - move=> w op e IH Hwf. move: (well_formed_rexp_unop Hwf) => {Hwf} [Hwfe Hse].
    move: (IH Hwfe) => {IH} IH. case: op => /=; rewrite IH; exact: Hse.
  - move=> w op e1 IH1 e2 IH2 Hwf.
    move: (well_formed_rexp_binop Hwf) => {Hwf} [Hwf1 [Hwf2 [Hs1 Hs2]]].
    move: (IH1 Hwf1) (IH2 Hwf2) => {IH1 IH2} IH1 IH2.
    case: op => /=; rewrite ?IH1 ?IH2 ?Hs1 ?Hs2 ?minnn ?maxnn; reflexivity.
  - move=> w e IH n Hwf. move: (well_formed_rexp_uext Hwf) => {Hwf} [Hwfe Hse].
    move: (IH Hwfe) => {IH} IH. rewrite IH Hse. reflexivity.
  - move=> w e IH n Hwf. move: (well_formed_rexp_sext Hwf) => {Hwf} [Hwfe Hse].
    move: (IH Hwfe) => {IH} IH. rewrite IH Hse. reflexivity.
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
    rewrite vars_exp_atomic; are_defined_dec
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

Ltac rewrite_eval_exp_atomic :=
  repeat rewrite -> eval_exp_atomic in *.

Lemma bexp_rng_instr E i : bexp_instr E (rng_instr i) = bexp_instr E i.
Proof.
  case: i => //=. move=> [e r] /=. reflexivity.
Qed.

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

Lemma bexp_instr_equal E1 E2 i :
  well_defined_instr E1 i -> SSATE.Equal E1 E2 ->
  bexp_instr E1 i = bexp_instr E2 i.
Proof.
  move=> Hwd Heq. exact: (bexp_instr_submap Hwd (TELemmas.Equal_submap Heq)).
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

Lemma bexp_rng_program E p :
  bexp_program E (rng_program p) = bexp_program E p.
Proof.
  elim: p E => [| i p IH] E //=. rewrite bexp_rng_instr.
  rewrite IH. rewrite rng_instr_succ_typenv. reflexivity.
Qed.

Lemma bexp_program_submap E1 E2 p :
  well_formed_program E1 p -> TELemmas.submap E1 E2 ->
  bexp_program E1 p = bexp_program E2 p.
Proof.
  elim: p E1 E2 => [| i p IH] E1 E2 //=. move/andP=> [Hwf_i Hwf_p] Hsub.
  move: (submap_instr_succ_typenv Hwf_i Hsub) => Hsub_succ.
  move/andP: Hwf_i => [Hwd_i Hwt_i]. rewrite (bexp_instr_submap Hwd_i Hsub).
  rewrite (IH _ _ Hwf_p Hsub_succ). reflexivity.
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
  - (* mull *)
    move : H1; case (Typ.is_unsigned (atyp a E)) => /=;
    move: (ssa_unchanged_program_add1 H) => {H} [H1 H2];
    move: (ssa_unchanged_program_add1 H2) => {H2} [H2 H3];
    move: (ssa_unchanged_program_union1 H3) => {H3} [H3 H4];
    rewrite -!(acc_unchanged_program H2 H0)
            -!(acc_unchanged_program H1 H0);
    rewrite_eval_exp_atomic;
    rewrite -!(ssa_unchanged_program_eval_atomic H4 H0)
            -!(ssa_unchanged_program_eval_atomic H3 H0);
    move => /andP [Hhi Hlo];
              apply /andP; split; done.
  - (* mulj *)
    move : H1; case (Typ.is_unsigned (atyp a E)) => /=;
    move: (ssa_unchanged_program_add1 H) => {H} [H1 H2];
    move: (ssa_unchanged_program_union1 H2) => {H2} [H2 H3];
    rewrite -!(acc_unchanged_program H1 H0);
    rewrite_eval_exp_atomic;
    rewrite -!(ssa_unchanged_program_eval_atomic H3 H0)
            -!(ssa_unchanged_program_eval_atomic H2 H0); done.
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

Ltac unfold_well_typed :=
  repeat
  match goal with
  | H : is_true (well_typed_instr _ _) |- _ =>
    rewrite /well_typed_instr in H
  | H : is_true (well_typed_atomic _ _) |- _ =>
    let H1 := fresh "Hwta" in
    let H2 := fresh "Hwta" in
    move/andP: H=> [H1 H2]
  | H : is_true (_ && _) |- _ =>
    let H1 := fresh "Hty" in
    let H2 := fresh "Hty" in
    move/andP: H => [H1 H2]
  end.

Ltac well_defined_to_vs_subset :=
  repeat
  match goal with
  | Hdef : is_true (well_defined_instr _ ?i) |- _ =>
    rewrite /well_defined_instr !are_defined_subset_env in Hdef
  | H : is_true (_ && _) |- _ =>
    let H1 := fresh "Hdef" in
    let H2 := fresh "Hdef" in
    move/andP: H => [H1 H2]
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

Ltac to_size_atyp a :=
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    Hsm : is_true (size_matched_atomic a)
    |- context f [size (eval_atomic a ?s)] =>
    rewrite (conform_size_eval_atomic Hsub Hco Hsm)
  end.

Ltac to_size_eval_atomic a :=
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    Hsm : is_true (size_matched_atomic a)
    |- context f [Typ.sizeof_typ (atyp ?a ?E)] =>
    rewrite -(conform_size_eval_atomic Hsub Hco Hsm)
  end.

Ltac intro_size a :=
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    Hsm : is_true (size_matched_atomic a)
    |- _ =>
    move: (conform_size_eval_atomic Hsub Hco Hsm)
  end.

Ltac intro_size1 a :=
  match goal with
  | H : is_true (atyp a ?E == Typ.Tbit) |- _ =>
    intro_size a; rewrite (eqP H) /=
  end.

Ltac intro_same_size a1 a2 :=
  match goal with
  | Hco : SSAStore.conform ?s ?E,
    Hsm1 : is_true (size_matched_atomic a1),
    Hsm2 : is_true (size_matched_atomic a2),
    Hsub1 : is_true (SSAVS.subset (vars_atomic a1) (vars_env ?E)),
    Hsub2 : is_true (SSAVS.subset (vars_atomic a2) (vars_env ?E)) |- _ =>
    match goal with
    | Heq : is_true (atyp a1 E == atyp a2 E) |- _ =>
      let H := fresh in
      (have: Typ.sizeof_typ (atyp a1 E) = Typ.sizeof_typ (atyp a2 E)
        by rewrite (eqP Heq));
      move=> H; move: (size_eval_atomic_same Hco Hsm1 Hsm2 Hsub1 Hsub2 H);
             clear H
    | Heq : Typ.sizeof_typ (atyp a1 ?E) = Typ.sizeof_typ (atyp a2 ?E) |- _ =>
      move: (size_eval_atomic_same Hco Hsm1 Hsm2 Hsub1 Hsub2 Heq)
    | Heq : is_true (Typ.sizeof_typ (atyp a1 ?E) == Typ.sizeof_typ (atyp a2 ?E))
      |- _ => move: (size_eval_atomic_same Hco Hsm1 Hsm2 Hsub1 Hsub2 Heq)
    | Heq : is_true (Typ.compatible (atyp a1 ?E) (atyp a2 ?E)) |- _ =>
      move: (size_eval_atomic_same Hco Hsm1 Hsm2 Hsub1 Hsub2 (eqP Heq))
    end
  end.

Lemma bexp_instr_eval_Imov E v a s1 s2 :
  well_formed_instr E (Imov v a) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Imov v a) ->
  eval_instr E (Imov v a) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Imov v a)) s2.
Proof.
  move => /andP [Hdef _] _ Hun Hinst /=.
  well_defined_to_vs_subset. eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst. by qfbv_store_acc.
Qed.

Lemma bexp_instr_eval_Ishl E t a n s1 s2 :
  well_formed_instr E (Ishl t a n) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ishl t a n) ->
  eval_instr E (Ishl t a n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ishl t a n)) s2.
Proof.
  move => /andP [Hdef Hwt] _ Hun Hinst /=.
  well_defined_to_vs_subset. unfold_well_typed.
  eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst. qfbv_store_acc.
  rewrite (to_nat_from_nat_very_small (ltnW Hty0)).
  exact: eqxx.
Qed.

Lemma lt_eq_addl p n m : p < n -> m = n -> p < m + n.
Proof.
  move=> H ->. rewrite -{1}(addn0 p). apply: (Nats.ltn_addn H).
  apply: (leq_ltn_trans _ H). done.
Qed.

Lemma bexp_instr_eval_Icshl E t t0 a a0 n s1 s2 :
  well_formed_instr E (Icshl t t0 a a0 n) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Icshl t t0 a a0 n) ->
  eval_instr E (Icshl t t0 a a0 n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Icshl t t0 a a0 n)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset. unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst. repeat qfbv_store_acc.
  rewrite (to_nat_from_nat_very_small Hty1).
  intro_same_size a a0. to_size_atyp a. to_size_atyp a0. move=> Hs.
  move: (leq0n (asize a E)) => Hs'.
  move: (leq_add Hs' Hty1) => Hadd. rewrite add0n in Hadd.
  rewrite (to_nat_from_nat_very_small Hadd).
  apply/andP; split; done.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  rewrite /joinlsb /=.
  intro_size1 a. move=> Hszc.
  inversion_clear Hinst; repeat qfbv_store_acc.
  + by rewrite (to_bool_bit_is_true Hszc H) //.
  + move : (not_to_bool_bit_is_false Hszc H). by move=> /eqP <- //.
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
  well_defined_to_vs_subset.
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
  well_defined_to_vs_subset.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_same_size a a0. move=> Hss.
  rewrite /asize. to_size_eval_atomic a.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_size1 a1. move=> Hsz1.
  intro_same_size a a0. move=> Hszeq.
  rewrite /asize. to_size_eval_atomic a.
  elim : (size1 Hsz1) => /eqP ->.
  - rewrite (adcB_zext1_lown false Hszeq). exact: eqxx.
  - rewrite (adcB_zext1_lown true Hszeq). exact: eqxx.
Qed.

Lemma bexp_instr_eval_Iadcs E t t0 a a0 a1 s1 s2 :
  well_formed_instr E (Iadcs t t0 a a0 a1) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iadcs t t0 a a0 a1) ->
  eval_instr E (Iadcs t t0 a a0 a1) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iadcs t t0 a a0 a1)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_same_size a a0. move=> Hsize.
  intro_size1 a1. move=> Hsz1.
  move: (size1 Hsz1). rewrite /asize. to_size_eval_atomic a.
  case=> /eqP ->;
          rewrite (adcB_zext1_high1 _ Hsize) eqxx andTb;
           rewrite (adcB_zext1_lown _ Hsize) eqxx; exact: is_true_true.
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
  well_defined_to_vs_subset.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_same_size a a0. move=> Hsize.
  have Hszneg: (size (eval_atomic a s1) = size (~~# eval_atomic a0 s1)%bits).
  { by rewrite size_invB -Hsize. }
  rewrite /asize. to_size_eval_atomic a.
  rewrite (adcB_zext1_high1 _ Hszneg) eqxx andTb.
  rewrite (adcB_zext1_lown _ Hszneg) eqxx. exact: is_true_true.
Qed.

Lemma bexp_instr_eval_Isubb E t t0 a a0 s1 s2 :
  well_formed_instr E (Isubb t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isubb t t0 a a0) ->
  eval_instr E (Isubb t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isubb t t0 a a0)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_same_size a a0. move=> Hsize.
  rewrite /asize. to_size_eval_atomic a.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_same_size a a0. move=> Hsize.
  intro_size1 a1. move=> Hsz1.
  have Hszinv: (size (eval_atomic a s1) = size (~~# eval_atomic a0 s1)%bits).
  { by rewrite size_invB -Hsize. }
  rewrite /asize. to_size_eval_atomic a.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_size1 a1. move=> Hsz1.
  intro_same_size a a0. move=> Hsize.
  have Hszinv : (size (eval_atomic a s1) = size (~~# eval_atomic a0 s1)%bits).
  { by rewrite size_invB -Hsize. }
  rewrite /asize. to_size_eval_atomic a.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_same_size a a0. move=> Hsize.
  intro_size1 a1. move=> Hsz1.
  rewrite /asize. to_size_eval_atomic a.
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
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  intro_same_size a a0. move=> Hsize.
  intro_size1 a1. move=> Hsz1.
  rewrite /asize. to_size_eval_atomic a.
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
  well_defined_to_vs_subset.
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
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  have Hinst' : eval_instr E (Imull t t0 a a0) s1 s2 by assumption.
  inversion_clear Hinst'; repeat qfbv_store_acc.
  - rewrite H /=. to_size_atyp a; to_size_atyp a0.
    apply/andP; split; by repeat eval_exp_exp_atomic_to_pred_state.
  - rewrite -Typ.not_signed_is_unsigned H /=.
    to_size_atyp a; to_size_atyp a0.
    apply/andP; split; by repeat eval_exp_exp_atomic_to_pred_state.
  (*
  rewrite (eqP (mul_sext (eval_atomic a s1) (eval_atomic a0 s1))).
  to_size_atyp a. to_size_atyp a0.
  apply/andP; split; done.
   *)
Qed.

Lemma bexp_instr_eval_Imulj E t a a0 s1 s2 :
  well_formed_instr E (Imulj t a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Imulj t a a0) ->
  eval_instr E (Imulj t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Imulj t a a0)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset.
  unfold_well_typed.
  repeat eval_exp_exp_atomic_to_pred_state.
  have Hinst' : eval_instr E (Imulj t a a0) s1 s2 by assumption.
  inversion_clear Hinst'; repeat qfbv_store_acc.
  - rewrite H /=. to_size_atyp a. by repeat eval_exp_exp_atomic_to_pred_state.
  - rewrite -Typ.not_signed_is_unsigned H /=.
    to_size_atyp a. by repeat eval_exp_exp_atomic_to_pred_state.
  (*
  rewrite (eqP (mul_sext (eval_atomic a s1) (eval_atomic a0 s1))).
  to_size_atyp a. exact: eqxx.
   *)
Qed.

Lemma bexp_instr_eval_Isplit E t t0 a n s1 s2 :
  well_formed_instr E (Isplit t t0 a n) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Isplit t t0 a n) ->
  eval_instr E (Isplit t t0 a n) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Isplit t t0 a n)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset. unfold_well_typed.
  rewrite eval_bexp_if /=. repeat eval_exp_exp_atomic_to_pred_state.
  rewrite (to_nat_from_nat_very_small (ltnW Hty1)).
  move: (leq_subr n (asize a E)) => Hs.
  rewrite (to_nat_from_nat_very_small Hs).
  inversion_clear Hinst; repeat qfbv_store_acc.
  - rewrite H. to_size_atyp a. apply/andP; split; done.
  - rewrite -Typ.not_signed_is_unsigned H /=.
    to_size_atyp a. apply/andP; split; done.
Qed.

Lemma bexp_instr_eval_Iand E t t0 a a0 s1 s2 :
  well_formed_instr E (Iand t t0 a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Iand t t0 a a0) ->
  eval_instr E (Iand t t0 a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Iand t t0 a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  well_defined_to_vs_subset.
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
  well_defined_to_vs_subset.
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
  well_defined_to_vs_subset.
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
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset. unfold_well_typed.
  rewrite !eval_exp_if /=.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  rewrite /Typ.tcast /ucastB /scastB /=.
  to_size_atyp a. by case (atyp a E).
Qed.

Lemma bexp_instr_eval_Ivpc E t t0 a s1 s2 :
  well_formed_instr E (Ivpc t t0 a) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ivpc t t0 a) ->
  eval_instr E (Ivpc t t0 a) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ivpc t t0 a)) s2.
Proof.
  move => /andP [Hdef Hty] Hcon Hun Hinst /=.
  well_defined_to_vs_subset. unfold_well_typed.
  rewrite !eval_exp_if /=.
  repeat eval_exp_exp_atomic_to_pred_state.
  inversion_clear Hinst; repeat qfbv_store_acc.
  rewrite /Typ.tcast /ucastB /scastB /=.
  to_size_atyp a. by case (atyp a E).
Qed.

Lemma bexp_instr_eval_Ijoin E t a a0 s1 s2 :
  well_formed_instr E (Ijoin t a a0) ->
  SSAStore.conform s1 E ->
  ssa_vars_unchanged_instr (vars_env E) (Ijoin t a a0) ->
  eval_instr E (Ijoin t a a0) s1 s2 ->
  QFBV.eval_bexp (bexp_instr E (Ijoin t a a0)) s2.
Proof.
  move => /andP [Hdef _] Hcon Hun Hinst /=.
  well_defined_to_vs_subset.
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
  well_defined_to_vs_subset.
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
    Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hsm : is_true (size_matched_atomic ?a) |- _ =>
    let Hsize := fresh "Hsize" in
    (move: (conform_size_eval_atomic Hsub Hco Hsm) => Hsize);
    move: Hsub; intro_atomic_size
  | |- _ => intros
  end.

Ltac to_asize :=
  repeat
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    Hsm : is_true (size_matched_atomic ?a) |-
    context f [size (eval_atomic ?a ?s)] =>
    rewrite (size_eval_atomic_asize Hsub Hco Hsm)
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    Hsm : is_true (size_matched_atomic ?a),
    H : context f [size (eval_atomic ?a ?s)] |- _ =>
    rewrite (size_eval_atomic_asize Hsub Hco Hsm) in H
  end.

Ltac of_asize :=
  repeat
  match goal with
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    Hsm : is_true (size_matched_atomic ?a) |-
    context f [asize ?a ?E] =>
    rewrite -(size_eval_atomic_asize Hsub Hco Hsm)
  | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
    Hco : SSAStore.conform ?s ?E,
    Hsm : is_true (size_matched_atomic ?a),
    H : context f [asize ?a ?E] |- _ =>
    rewrite -(size_eval_atomic_asize Hsub Hco Hsm) in H
  end.

Ltac norm_tac :=
  repeat
    match goal with
    | H : is_true (well_formed_instr _ _) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_typed_atomic _ _) |- _ =>
      let H1 := fresh "Hwta" in
      let H2 := fresh "Hwta" in
      move/andP: H=> [H1 H2]
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      move/andP: H => [H1 H2]
    | H : is_true (are_defined _ _) |- _ =>
      move/defsubP: H => H
    | Hs : is_true (?n < ?w),
      H : context f [to_nat (?w -bits of ?n)%bits] |- _ =>
      rewrite (to_nat_from_nat_very_small (ltnW Hs)) in H
    | Hs : is_true (?n <= ?w),
      H : context f [to_nat (?w -bits of ?n)%bits] |- _ =>
      rewrite (to_nat_from_nat_very_small Hs) in H
    | H : context f [QFBV.eval_exp (qfbv_atomic _) _] |- _ =>
      rewrite eval_exp_atomic in H
    | |- context f [QFBV.eval_exp (qfbv_atomic _) _] =>
      rewrite eval_exp_atomic
    | Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
      Hco : SSAStore.conform ?s ?E,
      Hsm : is_true (size_matched_atomic ?a) |-
      context f [size (eval_atomic ?a ?s)] =>
      rewrite (size_eval_atomic_asize Hsub Hco Hsm)
    | Hs : is_true (?n <= (asize ?a2 ?E)),
      Hc : is_true (Typ.compatible (atyp ?a1 ?E) (atyp ?a2 ?E)),
      H : context f [to_nat ((asize ?a1 ?E + asize ?a2 ?E) -bits of ?n)%bits] |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      intro_same_size a1 a2; to_size_atyp a1; to_size_atyp a2;
      (move=> H1); (move: (leq0n (asize a1 E)) => H2);
      (move: (leq_add H2 Hs) => {H2} H2); (rewrite add0n in H2);
      rewrite (to_nat_from_nat_very_small H2) in H
    | Hs : is_true (?n < (asize ?a ?E)),
      H : context f [to_nat ((asize ?a ?E) -bits of (asize ?a ?E - ?n))%bits] |- _ =>
      let H1 := fresh in
      (move: (leq_subr n (asize a E)) => H1);
      rewrite (to_nat_from_nat_very_small H1) in H
    | Hco : SSAStore.conform ?s ?E,
      Hsm : is_true (size_matched_atomic ?a),
      Htyp : is_true (atyp ?c ?E == Typ.Tbit),
      Hsub : is_true (SSAVS.subset (vars_atomic ?c) (vars_env ?E)) |- _ =>
      let b := fresh "b" in
      let Hb := fresh "Hb" in
      (move: (tbit_atomic_singleton Hco Hsm (eqP Htyp) Hsub) => [b Hb]);
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
  intro_same_size a1 a2 => Hs. of_asize.
  match goal with
  | H : context f [high 1 (zext 1 _ +# zext 1 _)%bits] |- _ =>
    rewrite (addB_zext1_high1 Hs) in H
  end.
  match goal with
  | H : context f [low (size ?bs1) (zext 1 ?bs1 +# zext 1 ?bs2)%bits] |- _ =>
    rewrite (addB_zext1_lown Hs) in H
  end.
    by solve_tac.
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
  intro_same_size a1 a2 => Hs. of_asize.
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
  intro_same_size a1 a2 => Hs. of_asize.
  match goal with
  | H : context f [low (size ?bs1)
                       (zext 1 ?bs1 +# zext 1 ?bs2 +# zext (size ?bs1) [:: ?b])%bits]
    |- _ => rewrite (adcB_zext1_lown b Hs) in H
  end.
  match goal with
  | H : context f [high 1
                        (zext 1 ?bs1 +# zext 1 ?bs2 +# zext (size ?bs1) [:: ?b])%bits]
    |- _ => rewrite (adcB_zext1_high1 b Hs) in H
  end.
    by solve_tac.
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
  have Hs: (size (eval_atomic a1 s) = size (~~# eval_atomic a2 s)%bits) by
      by rewrite size_invB Hsize Hsize0 (eqP H0). of_asize.
  rewrite (adcB_zext1_high1 _ Hs) in H1. rewrite (adcB_zext1_lown _ Hs) in H4.
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
  intro_same_size a1 a2 => Hs. of_asize.
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
    by rewrite size_invB Hsize Hsize0 (eqP H0). of_asize.
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
    by rewrite size_invB Hsize Hsize0 (eqP H0). of_asize.
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
  intro_same_size a1 a2 => Hs. of_asize.
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
  intro_same_size a1 a2 => Hs. of_asize.
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
  move=> /= vh vl a1 a2 Hwf Hco1 Hco2 Hev. dcase (atyp a1 E). case => wa1 Htyp.
  - have Hun: Typ.is_unsigned (atyp a1 E) by rewrite Htyp.
    rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
    apply: (EImullU Hun). norm_tac. by solve_tac.
  - have Hsn: Typ.is_signed (atyp a1 E) by rewrite Htyp.
    rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
    apply: (EImullS Hsn). norm_tac. by solve_tac.
  (*
  apply: EImull. norm_tac.
  rewrite (eqP (mul_sext _ _)). to_asize. by solve_tac.
   *)
Qed.

Lemma eval_bexp_instr_Imulj E s :
  forall (t : SSAVarOrder.t) (a a0 : atomic),
    well_formed_instr E (Imulj t a a0) ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv (Imulj t a a0) E) ->
    QFBV.eval_bexp (bexp_instr E (Imulj t a a0)) s ->
    eval_instr E (Imulj t a a0) s s.
Proof.
  move=> /= v a1 a2 Hwf Hco1 Hco2 Hev. dcase (atyp a1 E). case => wa1 Htyp.
  - have Hun: Typ.is_unsigned (atyp a1 E) by rewrite Htyp.
    rewrite Htyp /= in Hev.
    apply: (EImuljU Hun). norm_tac. by solve_tac.
  - have Hsn: Typ.is_signed (atyp a1 E) by rewrite Htyp.
    rewrite Htyp /= in Hev.
    apply: (EImuljS Hsn). norm_tac. by solve_tac.
  (*
  apply: EImulj. norm_tac.
  rewrite (eqP (mul_sext _ _)). to_asize. by solve_tac.
   *)
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
    exact: (conform_instr_succ_typenv (well_formed_program_cons1 Hwf) Hcon Hehd).
Qed.

Lemma bexp_program_eval_rng_program E p s :
  well_formed_ssa_program E p ->
  SSAStore.conform s (program_succ_typenv p E) ->
  eval_bexps_conj (bexp_program E (rng_program p)) s ->
  eval_program E (rng_program p) s s.
Proof.
  move/andP=> [/andP [Hwf Hun] Hssa] Hco Hev.
  move: (ssa_unchanged_program_succ_typenv_submap Hun Hssa) => Hsubm.
  elim: p E Hwf Hun Hssa Hco Hev Hsubm => /= [| i p IH] E Hwf Hun Hssa Hco Hev Hsubm.
  - exact: Enil.
  - move: Hev => [Hev_i Hev_p]. move/andP: Hwf => [Hwf_i Hwf_p].
    move: Hun. rewrite ssa_unchanged_program_cons. move/andP=> [Hun_i Hun_p].
    move/andP: Hssa => [Hssa_i Hssa_p].
    move: (conform_submap Hsubm Hco) => Hco_E.
    have Hun_p': ssa_vars_unchanged_program (vars_env (instr_succ_typenv i E)) p.
    { apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union. rewrite Hun_p Hssa_i.
      exact: is_true_true. }
    move: (ssa_unchanged_program_succ_typenv_submap Hun_p' Hssa_p) => Hsubm'.
    apply: (Econs (t:=s)).
    + apply: (eval_bexp_instr Hwf_i Hco_E _ Hev_i).
      exact: (conform_submap Hsubm' Hco).
    + rewrite rng_instr_succ_typenv. apply: (IH _ Hwf_p Hun_p' Hssa_p Hco _ Hsubm').
      rewrite -rng_instr_succ_typenv. exact: Hev_p.
Qed.

Definition valid_bexp_spec_conj (s : bexp_spec) : Prop :=
  forall st : SSAStore.t,
    SSAStore.conform st (binputs s) ->
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
  - exact: (conform_program_succ_typenv (well_formed_rng_program Hwfg) Hcon Hp).
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

Lemma bexp_spec_complete_conj (s : spec) :
  well_formed_ssa_spec s ->
  valid_rspec (rspec_of_spec s) ->
  valid_bexp_spec_conj (bexp_of_rspec (sinputs s) (rspec_of_spec s)).
Proof.
  case: s => E f p g. rewrite /well_formed_ssa_spec /valid_rspec /bexp_of_rspec /=.
  rewrite /well_formed_spec /valid_bexp_spec_conj /=.
  move/andP=> [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa_p].
  move=> Hvr s Hco /eval_bexp_rbexp Hf Heb. apply/eval_bexp_rbexp. apply: (Hvr s s).
  - apply: (conform_submap _ Hco). rewrite rng_program_succ_typenv.
    exact: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa_p).
  - exact: Hf.
  - rewrite rng_program_succ_typenv in Hco.
    apply: (bexp_program_eval_rng_program _ Hco Heb).
    rewrite /well_formed_ssa_program. rewrite Hwf_p Hun_Ep Hssa_p.
    exact: is_true_true.
Qed.


(* Connect premises by implication. *)

Fixpoint eval_bexps_imp (es : seq QFBV.bexp) (s : SSAStore.t) (p : Prop) : Prop :=
  match es with
  | [::] => p
  | hd::tl => QFBV.eval_bexp hd s -> eval_bexps_imp tl s p
  end.

Definition valid_bexp_spec_imp (s : bexp_spec) : Prop :=
  forall st : SSAStore.t,
    SSAStore.conform st (binputs s) ->
    QFBV.eval_bexp (bpre s) st ->
    eval_bexps_imp (bprog s) st (QFBV.eval_bexp (bpost s) st).

Lemma valid_bexp_spec_conj_imp (s : bexp_spec) :
  valid_bexp_spec_conj s -> valid_bexp_spec_imp s.
Proof.
  destruct s as [E f p g].
  move => Hc s /= Hco Hf.
  move: (Hc s Hco Hf) => /= {Hc Hf f} Hc.
  elim: p Hc => /=.
  - by apply.
  - move=> hd tl IH Hc Hhd.
    apply: IH => Htl.
    apply: Hc; split; assumption.
Qed.

Lemma valid_bexp_spec_imp_conj (s : bexp_spec) :
  valid_bexp_spec_imp s -> valid_bexp_spec_conj s.
Proof.
  destruct s as [E f p g].
  move => Hi s /= Hco Hf.
  move: (Hi s Hco Hf) => /= {Hi Hf f} Hi.
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

Lemma bexp_spec_complete_imp (s : spec) :
  well_formed_ssa_spec s ->
  valid_rspec (rspec_of_spec s) ->
  valid_bexp_spec_imp (bexp_of_rspec (sinputs s) (rspec_of_spec s)).
Proof.
  move=> Hwf Hvr. apply: valid_bexp_spec_conj_imp.
  exact: bexp_spec_complete_conj.
Qed.


(* Soundness and completeness of range check *)

Definition valid_bexp_spec := valid_bexp_spec_imp.

Theorem bexp_spec_sound (s : spec) :
  well_formed_ssa_spec s ->
  valid_bexp_spec (bexp_of_rspec (sinputs s) (rspec_of_spec s)) ->
  valid_rspec (rspec_of_spec s).
Proof.
  exact: bexp_spec_sound_imp.
Qed.

Theorem bexp_spec_complete (s : spec) :
  well_formed_ssa_spec s ->
  valid_rspec (rspec_of_spec s) ->
  valid_bexp_spec (bexp_of_rspec (sinputs s) (rspec_of_spec s)).
Proof.
  exact: bexp_spec_complete_imp.
Qed.


(* Construct a single QFBV expression for bit-blasting *)

Definition qfbv_bexp_spec (s : spec) : QFBV.bexp :=
  let bs := bexp_of_rspec (sinputs s) (rspec_of_spec s) in
  qfbv_imp (qfbv_conj (bpre bs) (qfbv_conjs (bprog bs)))
           (bpost bs).

Definition valid_qfbv_bexp_spec (s : spec) :=
  let fE := program_succ_typenv (sprog s) (sinputs s) in
  QFBV.valid fE (qfbv_bexp_spec s).

Lemma eval_bexps_conj_qfbv_conj es s :
  eval_bexps_conj es s <-> QFBV.eval_bexp (qfbv_conjs es) s.
Proof.
  elim: es => [| e es IH] //=. move: IH=> [IH1 IH2]. split.
  - move=> [H1 H2]. rewrite H1 (IH1 H2). exact: is_true_true.
  - move/andP=> [H1 H2]. rewrite H1. split; [exact: is_true_true | exact: (IH2 H2)].
Qed.

Lemma valid_qfbv_bexp_spec_conj s :
  valid_qfbv_bexp_spec s <-> valid_bexp_spec_conj (bexp_of_rspec (sinputs s) s).
Proof.
  case: s => E f p g. rewrite /valid_qfbv_bexp_spec /valid_bexp_spec_conj /=.
  split.
  - move=> H s Hco Hf Hp. rewrite rng_program_succ_typenv in Hco.
    move: (H s Hco) => /=. rewrite Hf.
    move/eval_bexps_conj_qfbv_conj: Hp => -> /=. by apply.
  - move=> H s Hco. rewrite -rng_program_succ_typenv in Hco.
    move: (H s Hco) => {H} /=.
    case Hf: (QFBV.eval_bexp (bexp_rbexp (rng_bexp f)) s) => //=.
    case Hp: (QFBV.eval_bexp (qfbv_conjs (bexp_program E (rng_program p))) s) => //=.
    move/eval_bexps_conj_qfbv_conj: Hp => Hp. by apply.
Qed.

Theorem qfbv_bexp_spec_sound s :
  well_formed_ssa_spec s ->
  valid_qfbv_bexp_spec s ->
  valid_rspec (rspec_of_spec s).
Proof.
  move=> Hwf Hv. apply: (bexp_spec_sound_conj Hwf).
  apply/valid_qfbv_bexp_spec_conj. assumption.
Qed.

Theorem qfbv_bexp_spec_complete s :
  well_formed_ssa_spec s ->
  valid_rspec (rspec_of_spec s) ->
  valid_qfbv_bexp_spec s.
Proof.
  move=> Hwf Hv. apply/valid_qfbv_bexp_spec_conj.
  apply: (bexp_spec_complete_conj Hwf). assumption.
Qed.


(* Well-formedness of the constructed QFBV expressions in range check *)

Ltac unfold_well_formed :=
  repeat
    match goal with
    | H : is_true (well_formed_eexp _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_formed_ebexp _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_formed_rexp _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_formed_rbexp _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_formed_bexp _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_formed_instr _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_formed_program _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_formed_ssa_program _ _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => /= [H1 H2]
    | H : is_true (well_typed_atomic _ _) |- _ =>
      let H1 := fresh "Hwta" in
      let H2 := fresh "Hwtqa" in
      move/andP: H => /= [H1 H2]
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh "Hwf" in
      let H2 := fresh "Hwf" in
      move/andP: H => [H1 H2]
    end.

Ltac split_disjoint :=
  match goal with
  | H : is_true (VSLemmas.disjoint _ (SSAVS.singleton _)) |- _ =>
    rewrite VSLemmas.disjoint_singleton in H
  | H : is_true (VSLemmas.disjoint _ (SSAVS.add _ _)) |- _ =>
    let H1 := fresh "Hdisj" in
    let H2 := fresh "Hdisj" in
    rewrite VSLemmas.disjoint_add in H; move/andP: H => [H1 H2]
  end.

Ltac ssa_vars_unchanged_instr_to_mem :=
  match goal with
  | H : is_true (ssa_vars_unchanged_instr ?vs ?i) |- _ =>
    let Hdisj := fresh "Hdisj" in
    (have: (ssa_vars_unchanged_instr vs i) by assumption);
    (rewrite ssa_unchanged_instr_disjoint_lvs => /= Hdisj);
    repeat split_disjoint
  end.

Ltac intro_subset_from_are_defined :=
  match goal with
  | H : is_true (are_defined _ _) |- _ =>
    let Hsub := fresh "Hsub" in
    move: (H) => /defsubP Hsub; move: H; intro_subset_from_are_defined
  | |- _ => intros
  end.

Section WellFormedRange.

  Lemma well_formed_qfbv_atomic E a :
    are_defined (vars_atomic a) E ->
    QFBV.well_formed_exp (qfbv_atomic a) E.
  Proof.
    case: a => //=. move=> v. rewrite are_defined_singleton.
    move/memdefP. by apply.
  Qed.

  Lemma well_formed_exp_rexp E e :
    well_formed_rexp E e -> QFBV.well_formed_exp (exp_rexp e) E.
  Proof.
    elim: e => //=.
    - move=> v Hwf. unfold_well_formed. rewrite are_defined_singleton in Hwf0.
      move/memdefP: Hwf0. by apply.
    - move=> w op e IH Hwf. move: (well_formed_rexp_unop Hwf) => {Hwf} [Hwf Hs].
      move: (IH Hwf) => {IH Hwf} Hwf. case: op => /=; assumption.
    - move=> w op e1 IH1 e2 IH2 Hwf.
      move: (well_formed_rexp_binop Hwf) => {Hwf} [Hwf1 [Hwf2 [Hs1 Hs2]]].
      move: (IH1 Hwf1) (IH2 Hwf2) => {IH1 IH2} Hqwf1 Hqwf2.
      case: op => /=; rewrite ?Hqwf1 ?Hqwf2 ?(size_exp_rexp Hwf1)
                      ?(size_exp_rexp Hwf2) ?Hs1 ?Hs2 eqxx; by trivial.
    - move=> w e IH n Hwf. move: (well_formed_rexp_uext Hwf) => {Hwf} [Hwf Hs].
      exact: (IH Hwf).
    - move=> w e IH n Hwf. move: (well_formed_rexp_sext Hwf) => {Hwf} [Hwf Hs].
      exact: (IH Hwf).
  Qed.

  Lemma well_formed_bexp_rbexp E e :
    well_formed_rbexp E e -> QFBV.well_formed_bexp (bexp_rbexp e) E.
  Proof.
    elim: e => //=.
    - move=> w e1 e2 Hwf. move: (well_formed_rbexp_eq Hwf) => [Hwf1 [Hwf2 [Hs1 Hs2]]].
      rewrite (well_formed_exp_rexp Hwf1) (well_formed_exp_rexp Hwf2).
      rewrite (size_exp_rexp Hwf1) Hs1 (size_exp_rexp Hwf2) Hs2.
      rewrite eqxx. exact: is_true_true.
    - move=> w op e1 e2 Hwf.
      move: (well_formed_rbexp_cmp Hwf) => {Hwf} [Hwf1 [Hwf2 [Hs1 Hs2]]].
      (case: op => /=);
        rewrite (well_formed_exp_rexp Hwf1) (well_formed_exp_rexp Hwf2)
                (size_exp_rexp Hwf1) Hs1 (size_exp_rexp Hwf2) Hs2 eqxx;
        exact: is_true_true.
    - move=> e1 IH1 e2 IH2 Hwf. move: (well_formed_rbexp_and Hwf) => [Hwf1 Hwf2].
      rewrite (IH1 Hwf1) (IH2 Hwf2). exact: is_true_true.
    - move=> e1 IH1 e2 IH2 Hwf. move: (well_formed_rbexp_or Hwf) => [Hwf1 Hwf2].
      rewrite (IH1 Hwf1) (IH2 Hwf2). exact: is_true_true.
  Qed.

  Ltac norm_tac ::=
    unfold_well_formed;
    ssa_vars_unchanged_instr_to_mem;
    intro_subset_from_are_defined;
    repeat
      match goal with
      | H : is_true (are_defined (vars_atomic ?a) ?E)
        |- context f [SSATE.add ?v ?t ?E] =>
        let H1 := fresh "Hdef" in
        (move: (are_defined_addr v t H) => H1);
        move: H
      end;
    intros;
    (* Generate all the inequalities that we may need *)
    match goal with
    | H : is_true (?x != ?y) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      move: (H); (move/idP/negP=> H1);
      move: (H); (rewrite (@eq_sym _ x y) => H2);
      move: (H2); (move/idP/negP=> H3)
    | |- _ => idtac
    end;
    repeat
      match goal with
      (* from simplify_types in SSA2ZSSA *)
      | H : context f [atyp ?a (SSATE.add ?v (atyp ?a ?E) ?E)] |- _ =>
        rewrite atyp_add_same in H
      | |- context f [atyp ?a (SSATE.add ?v (atyp ?a ?E) ?E)] =>
        rewrite atyp_add_same
      | H : context f [SSATE.vtyp ?v (SSATE.add ?v ?t ?E)] |- _ =>
        rewrite (SSATE.vtyp_add_eq (eqxx v)) in H
      | |- context f [SSATE.vtyp ?v (SSATE.add ?v ?t ?E)] =>
        rewrite (SSATE.vtyp_add_eq (eqxx v))
      | H : context f [SSATE.vtyp ?x (SSATE.add ?y _ _)],
        Hneq : is_true (?x != ?y) |- _ =>
        rewrite (SSATE.vtyp_add_neq Hneq) in H
      | Hneq : is_true (?x != ?y) |- context f [SSATE.vtyp ?x (SSATE.add ?y _ _)] =>
        rewrite (SSATE.vtyp_add_neq Hneq)
      | Hneq : is_true (?x != ?y),
        H : context f [SSATE.vtyp ?x (SSATE.add ?y _ _)] |- _ =>
        rewrite (SSATE.vtyp_add_neq Hneq) in H
      | Hmem : is_true (~~ SSAVS.mem ?v (vars_env ?E)),
        Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E))
        |- context f [atyp ?a (SSATE.add ?v ?t _)] =>
        rewrite (atyp_add_not_mem _ _ (SSAVS.Lemmas.not_mem_subset Hmem Hsub))
      | Hmem : is_true (~~ SSAVS.mem ?v (vars_env ?E)),
        Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
        H : context f [atyp ?a (SSATE.add ?v ?t _)] |- _ =>
        rewrite (atyp_add_not_mem _ _ (SSAVS.Lemmas.not_mem_subset Hmem Hsub)) in H
      (**)
      | |- context f [size (from_nat _ _)] => rewrite size_from_nat
      | |- context f [SSATE.mem ?v (SSATE.add ?v _ _)] =>
        rewrite (SSATE.Lemmas.mem_add_eq (eqxx v))
      | |- context f [SSATE.vsize ?v (SSATE.add ?v _ _)] =>
        rewrite (SSATE.vsize_add_eq (eqxx v))
      | H : is_true (are_defined (vars_atomic ?a) ?E)
        |- context f [QFBV.well_formed_exp (qfbv_atomic ?a) ?E] =>
        rewrite (well_formed_qfbv_atomic H)
      | Hdef : is_true (are_defined (vars_atomic ?a) ?E),
        Hsm : is_true (size_matched_atomic ?a)
        |- context f [QFBV.exp_size (qfbv_atomic ?a) ?E] =>
        rewrite (size_exp_atomic Hdef Hsm)
      | |- context f [asize ?a (SSATE.add _ (atyp ?a ?E) ?E)] =>
        rewrite asize_add_same
      | |- context f [asize _ _] => rewrite /asize
      | H : is_true (Typ.compatible ?t _)
        |- context f [Typ.sizeof_typ ?t] =>
        rewrite (eqP H)
      | H : ~ (is_true (?vl == ?vh))
        |- context f [SSATE.mem ?vl (SSATE.add ?vh _ _)] =>
        rewrite (SSATE.Lemmas.mem_add_neq H)
      | |- context f [SSATE.mem ?v (SSATE.add ?v _ _)] =>
        rewrite (SSATE.Lemmas.mem_add_eq (eqxx v))
      | H : is_true (?vl != ?vh)
        |- context f [SSATE.vsize ?vl (SSATE.add ?vh _ _)] =>
        rewrite (SSATE.vsize_add_neq H)
      | |- context f [SSATE.vsize ?v (SSATE.add ?v _ _)] =>
        rewrite (SSATE.vsize_add_eq (eqxx v))
      | H : is_true (atyp ?a ?E == Typ.Tbit)
        |- context f [1 == Typ.sizeof_typ (atyp ?a ?E)] =>
        rewrite (eqP H) /=
      | H : is_true (?x == _)
        |- context f [?x] =>
        rewrite (eqP H) /=
      | H : (?x == _) = true
        |- context f [?x] =>
        rewrite (eqP H) /=
      | Heq : is_true (?x == _),
        H : context f [?x] |- _ =>
        rewrite (eqP Heq) /= in H
      | Heq : (?x == _) = true,
        H : context f [?x] |- _ =>
        rewrite (eqP Heq) /= in H
      | |- context f [?n + 1 == 1 + ?n] =>
        rewrite (@addnC n 1) (@eqxx _ (1 + n))
      | |- context f [maxn ?n ?n] => rewrite maxnn
      | |- context f [minn ?n ?n] => rewrite minnn
      | |- context f [Typ.sizeof_typ (Typ.unsigned_typ _)] =>
        rewrite Typ.size_unsigned_typ
      | |- context f [Typ.sizeof_typ (Typ.double_typ _)] =>
        rewrite Typ.size_double_typ mul2n -addnn
      | |- context f [?n + (?m - ?n)] => rewrite subnKC
      | H : (?n < ?m) = false |- is_true (?m <= ?n) =>
        move/idP/negP: H; rewrite -leqNgt; by apply
      | |- context f [?x == ?x] => rewrite (eqxx x)
      | |- context f [if ?c then _ else _] =>
        let H := fresh in
        dcase c; case; simpl; intros
      end.

  Lemma well_formed_bexp_instr E i :
    ssa_vars_unchanged_instr (vars_env E) i ->
    well_formed_instr E i ->
    QFBV.well_formed_bexp (bexp_instr E i) (instr_succ_typenv i E).
  Proof.
    case: i => /=; try (move=> * ; norm_tac; exact: is_true_true).
    (* Iassume *)
    move=> [e r] Hun Hwf. apply: well_formed_bexp_rbexp.
    norm_tac. apply/andP; split.
    - rewrite are_defined_union in Hwf0. move/andP: Hwf0=> /= [H1 H2].
      exact: H2.
    - exact: (well_typed_rng_bexp Hwf1).
  Qed.

  Lemma well_formed_bexp_program E p :
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p ->
    well_formed_program E p ->
    QFBV.well_formed_bexp (qfbv_conjs (bexp_program E p)) (program_succ_typenv p E).
  Proof.
    elim: p E => [| i p IH] E //=.
    rewrite ssa_unchanged_program_cons => /andP [Hun_i Hun_p].
    move/andP=> [Hun_ip Hssa_p]. move/andP=> [Hwf_i Hwf_p].
    have Hun_iep: ssa_vars_unchanged_program (vars_env (instr_succ_typenv i E)) p.
    { apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
        by rewrite ssa_unchanged_program_union Hun_p Hun_ip. }
    move: (ssa_unchanged_program_succ_typenv_submap Hun_iep Hssa_p) => Hsubm.
    apply/andP; split.
    - apply: (QFBV.well_formed_bexp_submap Hsubm).
      exact: (well_formed_bexp_instr Hun_i Hwf_i).
    - exact: (IH _ Hun_iep Hssa_p Hwf_p).
  Qed.

  Theorem well_formed_qfbv_bexp_rspec s :
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    well_formed_ssa_spec s ->
    QFBV.well_formed_bexp (qfbv_bexp_spec s) fE.
  Proof.
    case s => E f p g /=. move=> Hwf.
    move/andP: Hwf => /= [/andP [Hwf Hun] Hssa].
    move/andP: Hwf => /= [/andP [Hwf_f Hwf_p] Hwf_g].
    move: (ssa_unchanged_program_succ_typenv_submap Hun Hssa) => Hsubm.
    apply/andP; split; first (apply/andP; split).
    - apply: well_formed_bexp_rbexp. move: (well_formed_rng_bexp Hwf_f) => H.
      exact: (well_formed_rbexp_submap Hsubm H).
    - rewrite -rng_program_succ_typenv. apply: well_formed_bexp_program.
      + rewrite ssa_vars_unchanged_rng_program. exact: Hun.
      + exact: (ssa_single_assignment_rng_program Hssa).
      + exact: (well_formed_rng_program Hwf_p).
    - apply: well_formed_bexp_rbexp. exact: (well_formed_rng_bexp Hwf_g).
  Qed.

End WellFormedRange.


(* Split range conditions and use qfbv_conjs_la *)

Section SplitRangeConditions.

  Import QFBV.

  Definition qfbv_bexp_spec_split_la (s : spec) : seq QFBV.bexp :=
    let bs := bexp_of_rspec (sinputs s) (rspec_of_spec s) in
    map (fun post => qfbv_imp (qfbv_conj (bpre bs) (qfbv_conjs_la (bprog bs))) post)
        (split_conj (bpost bs)).

  Definition valid_qfbv_bexp_spec_split_la (s : spec) :=
    let fE := program_succ_typenv (sprog s) (sinputs s) in
    valid_qfbv_bexps fE (qfbv_bexp_spec_split_la s).

  Lemma valid_qfbv_bexp_spec_ra_split_la s :
    valid_qfbv_bexp_spec s <-> valid_qfbv_bexp_spec_split_la s.
  Proof.
    rewrite /valid_qfbv_bexp_spec /valid_qfbv_bexp_spec_split_la.
    rewrite /qfbv_bexp_spec_split_la. case: s => [E f p g] /=. split=> H.
    - move=> s Hco e Hin. move: (H s Hco) => {H Hco}.
      move/mapP: Hin => [ee Hin] He. rewrite He => {e He} /=.
      case Hf: (eval_bexp (bexp_rbexp (rng_bexp f)) s) => //=.
      case Hp: (eval_bexp (qfbv_conjs (bexp_program E (rng_program p))) s) => //=.
      + rewrite -eval_qfbv_conjs_ra_la. rewrite Hp /=. move=> Hg.
        move/split_conj_eval: Hg. apply. assumption.
      + move=> _. apply/orP; left. apply/negP => Hp'. move/negP: Hp; apply.
        rewrite eval_qfbv_conjs_ra_la. assumption.
    - move=> s Hco. move: (H s Hco) => {H Hco} He /=.
      case Hf: (eval_bexp (bexp_rbexp (rng_bexp f)) s) => //=.
      case Hp: (eval_bexp (qfbv_conjs (bexp_program E (rng_program p))) s) => //=.
      apply/split_conj_eval. move=> e' Hin.
      move: (He ((fun post =>
                    qfbv_imp
                      (qfbv_conj
                         (bexp_rbexp (rng_bexp f))
                         (qfbv_conjs_la (bexp_program E (rng_program p)))) post)
                   e')) => /=. rewrite Hf.
      rewrite -eval_qfbv_conjs_ra_la Hp /=. apply. rewrite mem_map.
      + assumption.
      + move=> e1 e2. case. by apply.
  Qed.

  Lemma well_formed_qfbv_bexp_spec_ra_split_la E s :
    well_formed_bexp (qfbv_bexp_spec s) E =
    well_formed_bexps (qfbv_bexp_spec_split_la s) E.
  Proof.
    rewrite /qfbv_bexp_spec_split_la /qfbv_bexp_spec /=.
    move: (bexp_rbexp (rng_bexp (spre s))).
    move: (bexp_program (sinputs s) (rng_program (sprog s))).
    move: (bexp_rbexp (rng_bexp (spost s))). clear s.
    elim => //=.
    - move=> ps fs. rewrite !andbT. rewrite -well_formed_bexp_ra_la. reflexivity.
    - move=> ps fs. rewrite !andbT. rewrite -well_formed_bexp_ra_la. reflexivity.
    - move=> _ e1 e2 ps fs. rewrite andbT. rewrite -well_formed_bexp_ra_la.
      reflexivity.
    - move=> e IH ps fs. rewrite andbT. rewrite -well_formed_bexp_ra_la.
      reflexivity.
    - move=> e1 IH1 e2 IH2 ps fs. rewrite map_cat /=.
      rewrite well_formed_bexps_cat. rewrite -IH1 -IH2. rewrite !andbA.
      case: (well_formed_bexp fs E) => //=.
      case: (well_formed_bexp (qfbv_conjs ps) E) => //=.
      rewrite !andbT. reflexivity.
    - move=> e1 IH1 e2 IH2 ps fs. rewrite -well_formed_bexp_ra_la andbT.
      reflexivity.
  Qed.

End SplitRangeConditions.


(* Define the safety condition in terms of a QFBV expression *)

Definition bexp_atomic_uaddB_safe a1 a2 : QFBV.bexp :=
  qfbv_lneg (qfbv_uaddo (qfbv_atomic a1) (qfbv_atomic a2)).

Definition bexp_atomic_saddB_safe a1 a2 : QFBV.bexp :=
  qfbv_lneg (qfbv_saddo (qfbv_atomic a1) (qfbv_atomic a2)).

Definition bexp_atomic_addB_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then bexp_atomic_uaddB_safe a1 a2
  else bexp_atomic_saddB_safe a1 a2.

Definition bexp_atomic_adds_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then QFBV.Btrue
  else bexp_atomic_saddB_safe a1 a2.

Definition bexp_atomic_uadcB_safe a_size a1 a2 ac : QFBV.bexp :=
  qfbv_conj
    (qfbv_lneg
       (qfbv_uaddo (qfbv_atomic a1)
                   (qfbv_atomic a2)))
    (qfbv_lneg
       (qfbv_uaddo (qfbv_add (qfbv_atomic a1)
                             (qfbv_atomic a2))
                   (qfbv_zext (a_size - 1) (qfbv_atomic ac)))).

Definition bexp_atomic_sadcB_safe a_size a1 a2 ac : QFBV.bexp :=
  qfbv_conj
    (qfbv_lneg
       (qfbv_saddo (qfbv_atomic a1)
                   (qfbv_atomic a2)))
    (qfbv_lneg
       (qfbv_saddo (qfbv_add (qfbv_atomic a1)
                             (qfbv_atomic a2))
                   (qfbv_zext (a_size - 1) (qfbv_atomic ac)))).

Definition bexp_atomic_adcB_safe E a1 a2 ac : QFBV.bexp :=
  let a_typ := atyp a1 E in
  let a_size := asize a1 E in
  if Typ.is_unsigned a_typ then bexp_atomic_uadcB_safe a_size a1 a2 ac
  else bexp_atomic_sadcB_safe a_size a1 a2 ac.

Definition bexp_atomic_adcs_safe E a1 a2 ac : QFBV.bexp :=
  let a_typ := atyp a1 E in
  let a_size := asize a1 E in
  if Typ.is_unsigned a_typ then QFBV.Btrue
  else bexp_atomic_sadcB_safe a_size a1 a2 ac.

Definition bexp_atomic_usubB_safe a1 a2 : QFBV.bexp :=
  qfbv_lneg (qfbv_usubo (qfbv_atomic a1) (qfbv_atomic a2)).

Definition bexp_atomic_ssubB_safe a1 a2 : QFBV.bexp :=
  qfbv_lneg (qfbv_ssubo (qfbv_atomic a1) (qfbv_atomic a2)).

Definition bexp_atomic_subB_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then bexp_atomic_usubB_safe a1 a2
  else bexp_atomic_ssubB_safe a1 a2.

Definition bexp_atomic_subc_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then QFBV.Btrue
  else bexp_atomic_ssubB_safe a1 a2.

Definition bexp_atomic_subb_safe E a1 a2 : QFBV.bexp :=
  let 'a_typ := atyp a1 E in
  if Typ.is_unsigned a_typ then QFBV.Btrue
  else bexp_atomic_ssubB_safe a1 a2.

Definition bexp_atomic_usbbB_safe a_size a1 a2 ab : QFBV.bexp :=
  qfbv_conj
    (qfbv_lneg
       (qfbv_usubo (qfbv_atomic a1)
                   (qfbv_atomic a2)))
    (qfbv_lneg
       (qfbv_usubo (qfbv_sub (qfbv_atomic a1)
                             (qfbv_atomic a2))
                   (qfbv_zext (a_size - 1) (qfbv_atomic ab)))).

Definition bexp_atomic_ssbbB_safe a_size a1 a2 ab : QFBV.bexp :=
  qfbv_conj
    (qfbv_lneg
       (qfbv_ssubo (qfbv_atomic a1)
                   (qfbv_atomic a2)))
    (qfbv_lneg
       (qfbv_ssubo (qfbv_sub (qfbv_atomic a1)
                             (qfbv_atomic a2))
                   (qfbv_zext (a_size - 1) (qfbv_atomic ab)))).

Definition bexp_atomic_sbbB_safe E a1 a2 ab : QFBV.bexp :=
  let a_typ := atyp a1 E in
  let a_size := asize a1 E in
  if Typ.is_unsigned a_typ then bexp_atomic_usbbB_safe a_size a1 a2 ab
  else bexp_atomic_ssbbB_safe a_size a1 a2 ab.

Definition bexp_atomic_sbbs_safe E a1 a2 ab : QFBV.bexp :=
  let a_typ := atyp a1 E in
  let a_size := asize a1 E in
  if Typ.is_unsigned a_typ then QFBV.Btrue
  else bexp_atomic_ssbbB_safe a_size a1 a2 ab.

Definition bexp_atomic_usbcB_safe a_size a1 a2 ac : QFBV.bexp :=
  qfbv_conj
    (qfbv_lneg
       (qfbv_usubo (qfbv_atomic a1)
                   (qfbv_atomic a2)))
    (qfbv_lneg
       (qfbv_usubo (qfbv_sub (qfbv_atomic a1)
                             (qfbv_atomic a2))
                   (qfbv_zext (a_size - 1)
                              (qfbv_sub (qfbv_one 1) (qfbv_atomic ac))))).

Definition bexp_atomic_ssbcB_safe a_size a1 a2 ac : QFBV.bexp :=
  qfbv_conj
    (qfbv_lneg
       (qfbv_ssubo (qfbv_atomic a1)
                   (qfbv_atomic a2)))
    (qfbv_lneg
       (qfbv_ssubo (qfbv_sub (qfbv_atomic a1)
                             (qfbv_atomic a2))
                   (qfbv_zext (a_size - 1)
                              (qfbv_sub (qfbv_one 1) (qfbv_atomic ac))))).

Definition bexp_atomic_sbcB_safe E a1 a2 ac : QFBV.bexp :=
  let a_typ := atyp a1 E in
  let a_size := asize a1 E in
  if Typ.is_unsigned a_typ then bexp_atomic_usbcB_safe a_size a1 a2 ac
  else bexp_atomic_ssbcB_safe a_size a1 a2 ac.

Definition bexp_atomic_sbcs_safe E a1 a2 ac : QFBV.bexp :=
  let a_typ := atyp a1 E in
  let a_size := asize a1 E in
  if Typ.is_unsigned a_typ then QFBV.Btrue
  else bexp_atomic_ssbcB_safe a_size a1 a2 ac.

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
  let 'concatbv := qfbv_concat (qfbv_atomic a1) (qfbv_atomic a2) in
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
  | Iadds _ _ a1 a2 =>
    bexp_atomic_adds_safe E a1 a2
  | Iadc _ a1 a2 ac =>
    bexp_atomic_adcB_safe E a1 a2 ac
  | Iadcs _ _ a1 a2 ac =>
    bexp_atomic_adcs_safe E a1 a2 ac
  | Isub _ a1 a2 =>
    bexp_atomic_subB_safe E a1 a2
  | Isubc _ _ a1 a2 =>
    bexp_atomic_subc_safe E a1 a2
  | Isubb _ _ a1 a2 =>
    bexp_atomic_subb_safe E a1 a2
  | Isbc _ a1 a2 ac =>
    bexp_atomic_sbcB_safe E a1 a2 ac
  | Isbcs _ _ a1 a2 ac =>
    bexp_atomic_sbcs_safe E a1 a2 ac
  | Isbb _ a1 a2 ab =>
    bexp_atomic_sbbB_safe E a1 a2 ab
  | Isbbs _ _ a1 a2 ab =>
    bexp_atomic_sbbs_safe E a1 a2 ab
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
  - by rewrite /uaddB_safe /= !eval_exp_atomic.
  - by rewrite /saddB_safe /= !eval_exp_atomic.
Qed.

Lemma eval_bexp_atomic_adds_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_adds_safe E a1 a2) s <->
  adds_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  rewrite /bexp_atomic_adds_safe /adds_safe.
  case: (Typ.is_unsigned (atyp a1 E)) => //=.
  rewrite /saddB_safe !eval_exp_atomic. done.
Qed.

Lemma eval_bexp_atomic_adcB_safe E a1 a2 ac s :
  SSAStore.conform s E ->
  SSAVS.subset (vars_atomic a1) (vars_env E) ->
  size_matched_atomic a1 ->
  QFBV.eval_bexp (bexp_atomic_adcB_safe E a1 a2 ac) s <->
  adcB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  move=> Hco Hsub Hsm. rewrite /bexp_atomic_adcB_safe /adcB_safe /=.
  case: (Typ.is_unsigned (atyp a1 E)).
  - of_asize. by rewrite /uadcB_safe /= !eval_exp_atomic.
  - of_asize. by rewrite /sadcB_safe /= !eval_exp_atomic.
Qed.

Lemma eval_bexp_atomic_adcs_safe E a1 a2 ac s :
  SSAStore.conform s E ->
  SSAVS.subset (vars_atomic a1) (vars_env E) ->
  size_matched_atomic a1 ->
  QFBV.eval_bexp (bexp_atomic_adcs_safe E a1 a2 ac) s <->
  adcs_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  move=> Hco Hsub Hsm. rewrite /bexp_atomic_adcs_safe /adcs_safe.
  case: (Typ.is_unsigned (atyp a1 E)) => //=.
  rewrite /sadcB_safe !eval_exp_atomic. of_asize. done.
Qed.

Lemma eval_bexp_atomic_subB_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_subB_safe E a1 a2) s <->
  subB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  case Ht : (Typ.is_unsigned (atyp a1 E));
    rewrite /bexp_atomic_subB_safe /subB_safe Ht /=.
  - by rewrite /usubB_safe /= !eval_exp_atomic.
  - by rewrite /ssubB_safe /= !eval_exp_atomic.
Qed.

Lemma eval_bexp_atomic_subc_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_subc_safe E a1 a2) s <->
  subc_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  rewrite /bexp_atomic_subc_safe /subc_safe.
  case: (Typ.is_unsigned (atyp a1 E)) => //=.
  rewrite /ssubB_safe !eval_exp_atomic. done.
Qed.

Lemma eval_bexp_atomic_subb_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_subb_safe E a1 a2) s <->
  subb_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  rewrite /bexp_atomic_subb_safe /subb_safe.
  case: (Typ.is_unsigned (atyp a1 E)) => //=.
  rewrite /ssubB_safe !eval_exp_atomic. done.
Qed.

Lemma eval_bexp_atomic_sbbB_safe E a1 a2 ac s :
  SSAStore.conform s E ->
  SSAVS.subset (vars_atomic a1) (vars_env E) ->
  size_matched_atomic a1 ->
  QFBV.eval_bexp (bexp_atomic_sbbB_safe E a1 a2 ac) s <->
  sbbB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  move=> Hco Hsub Hsm. rewrite /bexp_atomic_sbbB_safe /sbbB_safe.
  case: (Typ.is_unsigned (atyp a1 E)).
  - rewrite /usbbB_safe /= !eval_exp_atomic. of_asize. done.
  - rewrite /ssbbB_safe /= !eval_exp_atomic. of_asize. done.
Qed.

Lemma eval_bexp_atomic_sbbs_safe E a1 a2 ac s :
  SSAStore.conform s E ->
  SSAVS.subset (vars_atomic a1) (vars_env E) ->
  size_matched_atomic a1 ->
  QFBV.eval_bexp (bexp_atomic_sbbs_safe E a1 a2 ac) s <->
  sbbs_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  move=> Hco Hsub Hsm. rewrite /bexp_atomic_sbbs_safe /sbbs_safe.
  case: (Typ.is_unsigned (atyp a1 E)) => //=.
  rewrite /ssbcB_safe !eval_exp_atomic. of_asize. done.
Qed.

Lemma eval_bexp_atomic_sbcB_safe E a1 a2 ac s :
  SSAStore.conform s E ->
  SSAVS.subset (vars_atomic a1) (vars_env E) ->
  size_matched_atomic a1 ->
  QFBV.eval_bexp (bexp_atomic_sbcB_safe E a1 a2 ac) s <->
  sbcB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  move=> Hco Hsub Hsm. rewrite /bexp_atomic_sbcB_safe /sbcB_safe.
  case: (Typ.is_unsigned (atyp a1 E)).
  - rewrite /usbcB_safe /= !eval_exp_atomic. of_asize. done.
  - rewrite /ssbcB_safe /= !eval_exp_atomic. of_asize. done.
Qed.

Lemma eval_bexp_atomic_sbcs_safe E a1 a2 ac s :
  SSAStore.conform s E ->
  SSAVS.subset (vars_atomic a1) (vars_env E) ->
  size_matched_atomic a1 ->
  QFBV.eval_bexp (bexp_atomic_sbcs_safe E a1 a2 ac) s <->
  sbcs_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s).
Proof.
  move=> Hco Hsub Hsm. rewrite /bexp_atomic_sbcs_safe /sbcs_safe.
  case: (Typ.is_unsigned (atyp a1 E)) => //=.
  rewrite /ssbcB_safe !eval_exp_atomic. of_asize. done.
Qed.

Lemma eval_bexp_atomic_mulB_safe E a1 a2 s :
  QFBV.eval_bexp (bexp_atomic_mulB_safe E a1 a2) s <->
  mulB_safe (atyp a1 E) (eval_atomic a1 s) (eval_atomic a2 s).
Proof.
  rewrite /bexp_atomic_mulB_safe /mulB_safe. case: (Typ.is_unsigned (atyp a1 E)).
  - by rewrite /umulB_safe /= !eval_exp_atomic.
  - by rewrite /smulB_safe /= !eval_exp_atomic.
Qed.

Lemma eval_bexp_atomic_shl_safe E a n s :
  QFBV.eval_bexp (bexp_atomic_shl_safe E a n) s <->
  shlBn_safe (atyp a E) (eval_atomic a s) n.
Proof.
  rewrite /bexp_atomic_shl_safe /shlBn_safe
          /ushlBn_safe /sshlBn_safe /=.
    case Ht : (Typ.is_unsigned (atyp a E)) => /=.
  - by rewrite !eval_exp_atomic zeros_from_nat.
  - by rewrite !eval_exp_atomic zeros_from_nat
       -zeros_from_nat invB_zeros.
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
  SSAStore.conform s E ->
  well_formed_instr E i ->
  (QFBV.eval_bexp (bexp_instr_safe E i) s <-> ssa_instr_safe_at E i s).
Proof.
  move=> Hco. case i => //=.
  - move => v a n Hwf. exact: eval_bexp_atomic_shl_safe.
  - move => h l a1 a2 n Hwf. exact: eval_bexp_atomic_cshl_safe.
  - move => v a1 a2 Hwf. exact: eval_bexp_atomic_addB_safe.
  - move => c v a1 a2 Hwf. exact: eval_bexp_atomic_adds_safe.
  - move=> v a1 a2 ac Hwf. unfold_well_formed.
    intro_subset_from_are_defined. exact: eval_bexp_atomic_adcB_safe.
  - move=> c v a1 a2 ac Hwf. unfold_well_formed.
    intro_subset_from_are_defined. exact: eval_bexp_atomic_adcs_safe.
  - move=> v a1 a2 Hwf. exact: eval_bexp_atomic_subB_safe.
  - move=> c v a1 a2 Hwf. exact: eval_bexp_atomic_subc_safe.
  - move=> c v a1 a2 Hwf. exact: eval_bexp_atomic_subb_safe.
  - move=> v a1 a2 ac Hwf. unfold_well_formed.
    intro_subset_from_are_defined. exact: eval_bexp_atomic_sbcB_safe.
  - move=> c v a1 a2 ac Hwf. unfold_well_formed.
    intro_subset_from_are_defined. exact: eval_bexp_atomic_sbcs_safe.
  - move=> v a1 a2 ab Hwf. unfold_well_formed.
    intro_subset_from_are_defined. exact: eval_bexp_atomic_sbbB_safe.
  - move=> b v a1 a2 ab Hwf. unfold_well_formed.
    intro_subset_from_are_defined. exact: eval_bexp_atomic_sbbs_safe.
  - move=> v a1 a2 Hwf. exact: eval_bexp_atomic_mulB_safe.
  - move=> v t a Hwf. exact: eval_bexp_atomic_vpc_safe.
Qed.

Lemma bexp_instr_safe_submap E1 E2 i :
  well_defined_instr E1 i -> TELemmas.submap E1 E2 ->
  bexp_instr_safe E1 i = bexp_instr_safe E2 i.
Proof.
  rewrite /bexp_instr_safe.
  rewrite /bexp_atomic_shl_safe /bexp_atomic_cshl_safe
          /bexp_atomic_addB_safe /bexp_atomic_adds_safe
          /bexp_atomic_adcB_safe/bexp_atomic_adcs_safe
          /bexp_atomic_subB_safe /bexp_atomic_subc_safe /bexp_atomic_subb_safe
          /bexp_atomic_sbcB_safe /bexp_atomic_sbcs_safe
          /bexp_atomic_sbbB_safe /bexp_atomic_sbbs_safe
          /bexp_atomic_mulB_safe /bexp_atomic_vpc_safe
          /bexp_atomic_uaddB_safe /bexp_atomic_saddB_safe
          /bexp_atomic_uadcB_safe /bexp_atomic_sadcB_safe
          /bexp_atomic_usubB_safe /bexp_atomic_ssubB_safe
          /bexp_atomic_usbcB_safe /bexp_atomic_sbcB_safe
          /bexp_atomic_ssbcB_safe
          /bexp_atomic_usbbB_safe /bexp_atomic_ssbbB_safe.
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


(* Well-formedness of bexp_instr_safe *)

Section WellFormedBexpInstrSafe.

  Ltac norm_tac :=
    unfold_well_formed;
    repeat
      match goal with
      | |- context f [if ?c then _ else _] =>
        dcase c; case => /=; intros
      | H : is_true (are_defined (vars_atomic ?a) ?E)
        |- context f [QFBV.well_formed_exp (qfbv_atomic ?a) ?E] =>
        rewrite (well_formed_qfbv_atomic H) /=
      | |- context f [size (_) -bits of (_)%bits] =>
        rewrite size_from_nat /=
      | |- context f [?n == ?n] => rewrite (eqxx n)
      | Hdef : is_true (are_defined (vars_atomic ?a) ?E),
        Hsm : is_true (size_matched_atomic ?a)
        |- context f [QFBV.exp_size (qfbv_atomic ?a) ?E] =>
        rewrite (size_exp_atomic Hdef Hsm) /=
      | |- context f [asize _ _] => rewrite /asize /=
      | H : is_true (Typ.compatible ?t1 ?t2)
        |- context f [Typ.sizeof_typ ?t1 == Typ.sizeof_typ ?t2] =>
        rewrite (eqP H) /=
      | H : is_true (?t1 == ?t2)
        |- context f [Typ.sizeof_typ ?t1 == Typ.sizeof_typ ?t2] =>
        rewrite (eqP H) /=
      | H : is_true (?t == Typ.Tbit)
        |- context f [Typ.sizeof_typ ?t] =>
        rewrite (eqP H) /=
      | |- context f [minn ?n ?n] => rewrite (minnn n)
      | |- context f [?n + (_ - ?n)] => rewrite subnKC
      | H : is_true (well_sized_atomic ?E ?a)
        |- is_true (0 < Typ.sizeof_typ (atyp ?a ?E)) =>
        exact: (well_sized_atomic_gt0 H)
      | H : (?n <= ?m) = false |- is_true (?m <= ?n) =>
        move/idP/negP: H; rewrite -ltnNge => H; exact: (ltnW H)
      end.

  Lemma bexp_instr_safe_well_formed E i :
    well_formed_instr E i ->
    QFBV.well_formed_bexp (bexp_instr_safe E i) E.
  Proof.
    case: i => //=.
    - move=> *. rewrite /bexp_atomic_shl_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_cshl_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_addB_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_adds_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_adcB_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_adcs_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_subB_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_subc_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_subb_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_sbcB_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_sbcs_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_sbbB_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_sbbs_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_mulB_safe /=. by norm_tac.
    - move=> *. rewrite /bexp_atomic_vpc_safe /=. by norm_tac.
  Qed.

End WellFormedBexpInstrSafe.


(* Program safety - fixed typing environment - initial typing environment *)

Section SafetyFixedInit.

  Fixpoint bexp_program_safe_fixed_init E p : QFBV.bexp :=
    match p with
    | [::] => qfbv_true
    | hd::tl =>
      qfbv_conj (bexp_instr_safe E hd)
                (qfbv_disj
                   (qfbv_lneg (bexp_instr E (rng_instr hd)))
                   (bexp_program_safe_fixed_init (instr_succ_typenv hd E) tl))
    end.

  Lemma eval_bexp_program_safe_fixed_init1 E pre p :
    well_formed_rbexp E pre ->
    ssa_vars_unchanged_program (vars_rbexp pre) p ->
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s E ->
               QFBV.eval_bexp (bexp_rbexp pre) s ->
               QFBV.eval_bexp (bexp_program_safe_fixed_init E p) s) ->
    (forall s, SSAStore.conform s E ->
               eval_rbexp pre s ->
               ssa_program_safe_at E p s).
  Proof.
    move=> Hwf_pre Hun Hwf_p H s.
    have: (forall t : SSAStore.t,
              bvs_eqi E s t ->
              SSAStore.conform t E ->
              QFBV.eval_bexp (bexp_rbexp pre) t ->
              QFBV.eval_bexp (bexp_program_safe_fixed_init E p) t).
    { move=> t Heqi Hco Hpre. exact: (H _ Hco Hpre). }
    move: {H} Hwf_pre Hun Hwf_p s.

    elim: p E => [| i p IH] E /=.
    - move=> *. exact: ssa_program_safe_at_nil.
    - rewrite ssa_unchanged_program_cons /well_formed_ssa_program.
      rewrite well_formed_program_cons ssa_single_assignment_cons.
      rewrite ssa_unchanged_program_cons.
      move=> Hwf_pre
               /andP [Hun_prei Hun_prep] /andP [
                 /andP [/andP [Hwf_i Hwf_p]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
      move=> s H Hco Hpre. apply: ssa_program_safe_at_cons.
      + move/eval_bexp_rbexp: Hpre => Hpre.
        apply/(eval_bexp_instr_safe Hco Hwf_i).
        move: (H s (bvs_eqi_refl s) Hco Hpre) => /andP [H1 _].
        exact: H1.
      + move=> t Hei.
        have Hssa_p: well_formed_ssa_program (instr_succ_typenv i E) p.
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
          exact: (conform_instr_succ_typenv (well_formed_rng_instr Hwf_i) Hco Hei).
        * rewrite -ssa_vars_unchanged_rng_instr in Hun_prei.
          apply/(ssa_unchanged_instr_eval_rbexp Hun_prei Hei). exact: Hpre.
  Qed.


  (* Soundness of bexp_program_safe_fixed. *)

  Definition ssa_spec_safe_qfbv_fixed_init sp : Prop :=
    forall s,
      SSAStore.conform s (sinputs sp) ->
      QFBV.eval_bexp (bexp_rbexp (rng_bexp (spre sp))) s ->
      QFBV.eval_bexp (bexp_program_safe_fixed_init (sinputs sp) (sprog sp)) s.

  Lemma ssa_spec_safe_qfbv_sound sp :
    well_formed_ssa_spec sp -> ssa_spec_safe_qfbv_fixed_init sp ->
    ssa_spec_safe sp.
  Proof.
    move=> Hwf. move: Hwf (well_formed_ssa_spec_program Hwf).
    case: sp => E f p g. rewrite /well_formed_ssa_spec /well_formed_spec
                                 /ssa_spec_safe_qfbv_fixed_init /ssa_spec_safe /=.
    move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
            Hwf_ssa_p Hbv s Hco Hf.

    move: (well_formed_rng_bexp Hwf_f) => Hwf_f_rng.
    move: (Hwf_f_rng). move/andP=> [Hdef_f_rng Hwt_f_rng].
    move/defsubP: Hdef_f_rng => Hsub_f_rng.
    move: (ssa_unchanged_program_subset Hun_Ep Hsub_f_rng) => Hun_f_rng.

    apply: (eval_bexp_program_safe_fixed_init1
              Hwf_f_rng Hun_f_rng Hwf_ssa_p _ Hco Hf).
    exact: Hbv.
  Qed.

End SafetyFixedInit.


(* Program safety - varying typing environment *)

Section SafetyVarying.

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
      move=> Hwf_pre /andP [Hun_prei Hun_prep] /andP [
                       /andP [/andP [Hwf_i Hwf_p] /andP
                               [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
      move=> s H Hco Hpre. apply: ssa_program_safe_at_cons.
      + move/eval_bexp_rbexp: Hpre => Hpre. apply/(eval_bexp_instr_safe Hco Hwf_i).
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
          exact: (conform_instr_succ_typenv (well_formed_rng_instr Hwf_i) Hco Hei).
        * rewrite -ssa_vars_unchanged_rng_instr in Hun_prei.
          apply/(ssa_unchanged_instr_eval_rbexp Hun_prei Hei). exact: Hpre.
  Qed.


  (* Soundness and completeness of bexp_program_safe_steps. *)

  Definition ssa_spec_safe_qfbv_steps sp : Prop :=
    forall s, QFBV.eval_bexp (bexp_rbexp (rng_bexp (spre sp))) s ->
              bexp_program_safe_steps (sinputs sp) (sprog sp) s.

  Lemma ssa_spec_safe_qfbv_steps_sound sp :
    well_formed_ssa_spec sp -> ssa_spec_safe_qfbv_steps sp -> ssa_spec_safe sp.
  Proof.
    move=> Hwf. move: Hwf (well_formed_ssa_spec_program Hwf).
    case: sp => E f p g. rewrite /well_formed_ssa_spec /well_formed_spec
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
    rewrite /well_formed_ssa_spec /well_formed_spec
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
    - apply/(eval_bexp_instr_safe Hco Hwf_i). assumption.
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

End SafetyVarying.


Section SplitConditionsVarying.

  Import QFBV.

  (* Construct safety conditions (full prefix information). *)

  (*
   * E: the typing environment after pre_is and before p
   * pre_is: the prefix of instructions
   * pre_es: the QFBV expressions encoding the prefix of instructions
   * p: the remaining program to be converted
   *)
  Fixpoint bexp_program_safe_split_full_rec E pre_is (pre_es : seq QFBV.bexp) p :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (E, pre_is, pre_es, hd, tl, bexp_instr_safe E hd)
        ::(bexp_program_safe_split_full_rec
             (instr_succ_typenv hd E) (rcons pre_is hd)
             (rcons pre_es (bexp_instr E (rng_instr hd))) tl)
    end.

  Definition bexp_program_safe_split_full E p :=
    bexp_program_safe_split_full_rec E [::] [::] p.

  Lemma bexp_program_safe_split_full_rec_env E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full_rec E pre_is pre_es p) ->
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

  Lemma bexp_program_safe_split_full_rec_submap E pre_is pre_es p :
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p ->
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full_rec E pre_is pre_es p) ->
      TELemmas.submap E E'.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    rewrite ssa_unchanged_program_cons.
    move=> /andP [Hun_i Hun_p] /andP [Hun_ip Hssa_p] E' pre_is' pre_es' hd tl safe.
    case.
    - case=> ? ? ? ? ?; subst. move=> _. exact: TELemmas.submap_refl.
    - move=> Hin. apply: (TELemmas.submap_trans
                            (ssa_unchanged_instr_succ_typenv_submap Hun_i)).
      apply: (IH _ _ _ _ Hssa_p _ _ _ _ _ _ Hin).
      apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union. rewrite Hun_p Hun_ip /=.
      exact: is_true_true.
  Qed.

  Lemma bexp_program_safe_split_full_rec_is E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full_rec E pre_is pre_es p) ->
      pre_is' ++ hd::tl = pre_is ++ p.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. reflexivity.
    - move=> Hin. rewrite -(cat_rcons i). apply: IH. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_full_rec_is_prefix E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full_rec E pre_is pre_es p) ->
      exists suf, pre_is' = pre_is ++ suf.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. move=> _. exists [::]. rewrite cats0. reflexivity.
    - move=> Hin. move: (IH _ _ _ _ _ _ _ _ _ Hin) => [suf H]. exists (i::suf).
      rewrite -(cat_rcons). assumption.
  Qed.

  Lemma bexp_program_safe_split_full_rec_es E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full_rec E pre_is pre_es p) ->
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

  Lemma bexp_program_safe_split_full_rec_cover E pre_is pre_es p :
    forall pre_is' hd tl suf,
      pre_is' = pre_is ++ suf ->
      pre_is' ++ (hd :: tl) = pre_is ++ p ->
      exists E' pre_es' safe,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_safe_split_full_rec E pre_is pre_es p).
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

  Lemma bexp_program_safe_split_full_env E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      E' = program_succ_typenv pre_is' E.
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    apply: (bexp_program_safe_split_full_rec_env Hin). reflexivity.
  Qed.

  Lemma bexp_program_safe_split_full_submap E p :
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p ->
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      TELemmas.submap E E'.
  Proof.
    move=> Hun Hssa E' pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_safe_split_full_rec_submap Hun Hssa Hin).
  Qed.

  Lemma bexp_program_safe_split_full_is E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      pre_is' ++ (hd::tl) = p.
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_safe_split_full_rec_is Hin).
  Qed.

  Lemma bexp_program_safe_split_full_es E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      pre_es' = bexp_program E (rng_program pre_is').
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
      by apply: (bexp_program_safe_split_full_rec_es Hin).
  Qed.

  Lemma bexp_program_safe_split_full_cover E p :
    forall pre_is' hd tl,
      pre_is' ++ (hd :: tl) = p ->
      exists E' pre_es' safe,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_safe_split_full E p).
  Proof.
    move=> pre_is' hd tl Heq. apply: bexp_program_safe_split_full_rec_cover.
    - rewrite cat0s. reflexivity.
    - rewrite cat0s. assumption.
  Qed.

  Lemma bexp_program_safe_split_full_steps E f p :
    well_formed_ssa_program E p ->
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_safe_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s).
  Proof.
    rewrite /bexp_program_safe_split_full. move=> Hwf He s.
    have: QFBV.eval_bexp (qfbv_conjs [::]) s by done.
    move: s He. move: [::]. move: [::].
    elim: p E f Hwf => [| i p IH] E f Hwf pre_es pre_is s //= He Hprefix Hf Hco.
    split.
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

  Lemma bexp_program_safe_steps_split_full E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s) ->
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_safe_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    rewrite /bexp_program_safe_split_full. move=> Hwf Hsteps.
    move=> Ee pre_is pre_es hd tl safe Hin s Hco /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hpre_es: (eval_bexp (qfbv_conjs pre_es) s) => //=.
    (* Make the precondition weaker. *)
    have: forall t : SSAStore.t,
        bvs_eqi E s t ->
        eval_bexp (qfbv_conjs (bexp_program E [::])) t ->
        eval_bexp (bexp_rbexp f) t -> bexp_program_safe_steps E p t
        by intros; apply: Hsteps.
    move: Ee pre_is pre_es hd tl safe Hin s Hco Hf Hpre_es.
    have: E = program_succ_typenv [::] E by done.
    have: [::] = bexp_program E (rng_program [::]) by done.
    have: (well_formed_ssa_program E ([::] ++ p)) by rewrite cat0s.
    move: {1 2 4}E => Einit. move: {Hsteps} Hwf.
    move: [::]. move: [::].
    elim: p E f => [| i p IH] E f pre_es pre_is //= Hwf Hwf_init Hpre HE.
    move=> E' pre_is' pre_es' hd tl safe Hin s Hco Hf Hpre_es' He.

    move/andP: (Hwf_init). rewrite well_formed_program_cat.
    rewrite ssa_unchanged_program_cat. rewrite ssa_single_assignment_cat.
    move=> [/andP [/andP [Hwf_Einit_pre_is' Hwf_Einit_ip]
                    /andP [Hun_Einit_pre_is' _]]
             /andP [/andP [Hssa_pre_is' _] _]].
    move: (ssa_unchanged_program_succ_typenv_submap
             Hun_Einit_pre_is' Hssa_pre_is') => Hsub_Einit.

    case: Hin.

    - case=> H1 H2 H3 H4 H5 H6. move: Hpre HE. subst => Hpre HE.
      apply: (proj1 (He s (bvs_eqi_refl s) _ Hf Hco)).
      rewrite Hpre in Hpre_es'. rewrite HE.
      rewrite -(bexp_program_submap Hwf_Einit_pre_is' Hsub_Einit).
      rewrite bexp_rng_program in Hpre_es'. exact: Hpre_es'.
    - move=> Hin. rewrite bexp_rng_instr in Hin.
      apply: (IH (instr_succ_typenv i E) f
                 (rcons pre_es (bexp_instr E i))
                 (rcons pre_is i) _ _ _ _ _ _ _ _ _ _ Hin _ Hco Hf Hpre_es').
      + exact: (well_formed_ssa_tl Hwf).
      + rewrite cat_rcons. exact: Hwf_init.
      + rewrite !bexp_rng_program in Hpre *. rewrite bexp_program_rcons.
        rewrite -Hpre -HE. reflexivity.
      + rewrite HE. rewrite program_succ_typenv_rcons. reflexivity.
      + move=> t Heqi Ht_pre_is_i Ht_f.
        move/andP: Hwf. rewrite well_formed_program_cons.
        rewrite ssa_unchanged_program_cons. rewrite ssa_single_assignment_cons.
        move=> [/andP [/andP [Hwf_i _] /andP [Hun_Ei Hun_Ep]]
                 /andP [Hun_ip Hssa_p]].
        move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsub_E.

        rewrite bexp_program_rcons in Ht_pre_is_i.
        rewrite eval_qfbv_conjs_rcons in Ht_pre_is_i.
        move/andP: Ht_pre_is_i => [Heval_pre_is_t Heval_i_t].

        rewrite -HE in Hwf_Einit_ip Hsub_Einit.
        move: (well_formed_program_submap
                 Hwf_Einit_pre_is' Hsub_Einit) => Hwf_E_pre_is.
        rewrite -(bexp_program_submap
                    Hwf_E_pre_is Hsub_E) in Heval_pre_is_t => {Hwf_E_pre_is}.

        have HiE: instr_succ_typenv i E = program_succ_typenv (rcons pre_is i) Einit.
        { rewrite HE. rewrite program_succ_typenv_rcons. reflexivity. }

        move: (bexp_program_safe_split_full_rec_env Hin HiE) => {HiE} HE'.
        move: (bvs_eqi_submap Hsub_E Heqi) => Heqi_Est.

        have Hsub_iEE': TELemmas.submap (instr_succ_typenv i E) E'.
        { apply: (bexp_program_safe_split_full_rec_submap _ Hssa_p Hin).
          apply: (ssa_unchanged_program_replace
                    (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          rewrite ssa_unchanged_program_union. by rewrite Hun_Ep Hun_ip. }

        have Hco_t: (SSAStore.conform t E).
        { move: (TELemmas.submap_trans Hsub_E Hsub_iEE') => Hsub_EE'.
          apply: (bvs_eqi_conform Heqi_Est).
          exact: (SSAStore.conform_submap Hsub_EE' Hco). }

        move: (He t Heqi_Est Heval_pre_is_t Ht_f Hco_t) => [H1 H2].
        apply: H2. rewrite bexp_rng_instr. rewrite HE.

        move: (TELemmas.submap_trans Hsub_Einit Hsub_E) => Hsub_Einit_iE.
        move: (submap_program_succ_typenv
                 Hwf_Einit_pre_is' Hsub_Einit_iE) => Hsub_succ.
        move/andP: Hwf_i => [Hwd_i Hwt_i]. rewrite HE in Hwd_i.
        rewrite (bexp_instr_submap Hwd_i Hsub_succ). exact: Heval_i_t.
  Qed.


  (* Well-formedness of bexp_program_safe_split_full *)

  Lemma bexp_program_safe_split_full_safe_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_is pre_es hd tl safe,
      List.In (Ee, pre_is, pre_es, hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      QFBV.well_formed_bexp safe Ee.
  Proof.
    rewrite /bexp_program_safe_split_full. move: [::]. move: [::].
    elim: p E => [| i p IH] E //= pre_es pre_is Hwf E' pre_is' pre_es' hd tl safe.
    case => Hin.
    - case: Hin=> ? ? ? ? ? ?; subst. apply: bexp_instr_safe_well_formed.
      exact: (well_formed_ssa_hd Hwf).
    - exact: (IH _ _ _ (well_formed_ssa_tl Hwf) _ _ _ _ _ _ Hin).
  Qed.

  Lemma bexp_program_safe_split_full_pre_es_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_is pre_es hd tl safe,
      List.In (Ee, pre_is, pre_es, hd, tl, safe)
              (bexp_program_safe_split_full E p) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) Ee.
  Proof.
    rewrite /bexp_program_safe_split_full.
    have: QFBV.well_formed_bexp (qfbv_conjs [::]) E by done.
    move: [::]. move: [::].
    elim: p E => [| i p IH] E //= pre_es pre_is Hwf_pre_es
                            Hwf E' pre_is' pre_es' hd tl safe.
    case=> Hin.
    - case: Hin => ? ? ? ? ? ?; subst. exact: Hwf_pre_es.
    - apply: (IH _ _ _ _ (well_formed_ssa_tl Hwf) _ _ _ _ _ _ Hin).
      rewrite bexp_rng_instr. rewrite well_formed_bexp_qfbv_conjs_rcons.
      move/andP: Hwf. rewrite well_formed_program_cons.
      rewrite ssa_unchanged_program_cons. rewrite ssa_single_assignment_cons.
      move=> [/andP [/andP [Hwf_i Hwf_iEp] /andP [Hun_Ei Hun_Ep]]
               /andP [Hun_ip Hssa_p]]. apply/andP; split.
      + apply: (well_formed_bexp_submap _ Hwf_pre_es).
        exact: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei).
      + exact: (well_formed_bexp_instr Hun_Ei).
  Qed.


  (* Verify safety conditions one by one (full prefix information). *)

  Fixpoint bexp_program_safe_split_full_checker_rec
           bexp_f
           (rs : seq (SSATE.env * seq SSA.instr * seq QFBV.bexp *
                      SSA.instr * SSA.program * QFBV.bexp)) :=
    match rs with
    | [::] => True
    | r::rs =>
      let '(Ee, pre_is, pre_es, hd, tl, safe) := r in
      (forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj bexp_f (qfbv_conjs pre_es))
                                   safe) s) /\
      bexp_program_safe_split_full_checker_rec bexp_f rs
    end.

  Definition bexp_program_safe_split_full_checker E f p :=
    bexp_program_safe_split_full_checker_rec (bexp_rbexp f)
                                             (bexp_program_safe_split_full E p).

  Lemma bexp_program_safe_split_full_checker_split_full E f p :
    bexp_program_safe_split_full_checker E f p ->
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_safe_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    rewrite /bexp_program_safe_split_full_checker.
    rewrite /bexp_program_safe_split_full.
    move: [::]. move: [::].
    elim: p f E => [| i p IH] //= f E pre_is pre_es [Hch1 Hch2]
                              E' pre_is' pre_es' hd tl safe Hin s Hco.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hpre_es': (eval_bexp (qfbv_conjs pre_es') s) => //=.
    case: Hin => Hin.
    - case: Hin=> ? ? ? ? ? ?; subst. move: (Hch1 s Hco).
      rewrite Hf Hpre_es' /=. by apply.
    - move: (IH f (instr_succ_typenv i E) _ _ Hch2 E' pre_is' pre_es' hd tl safe
                Hin s Hco) => /=. rewrite Hf Hpre_es' /=. by apply.
  Qed.

  Lemma bexp_program_safe_split_full_split_full_checker E f p :
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_safe_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    bexp_program_safe_split_full_checker E f p.
  Proof.
    rewrite /bexp_program_safe_split_full_checker.
    rewrite /bexp_program_safe_split_full.
    move: [::]. move: [::].
    elim: p f E => [| i p IH] //= f E pre_es pre_is H. split.
    - move=> s Hco. apply: (H _ _ _ _ _ _ _ s Hco). left. reflexivity.
    - apply: IH. move=> E' pre_is' pre_es' hd tl safe Hin s Hco.
      apply: (H _ _ _ _ _ _ _ s Hco). right. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_full_checker_steps E f p :
    well_formed_ssa_program E p ->
    bexp_program_safe_split_full_checker E f p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s).
  Proof.
    move=> Hwf Hch. apply: (bexp_program_safe_split_full_steps Hwf).
    exact: (bexp_program_safe_split_full_checker_split_full Hch).
  Qed.

  Lemma bexp_program_safe_steps_split_full_checker E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s) ->
    bexp_program_safe_split_full_checker E f p.
  Proof.
    move=> Hwf H. apply: bexp_program_safe_split_full_split_full_checker.
    exact: (bexp_program_safe_steps_split_full Hwf H).
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
              (bexp_program_safe_split_full_rec E pre_is pre_es p) ->
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
              (bexp_program_safe_split_full_rec E pre_is pre_es p) /\
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
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s).
  Proof.
    move=> Hwf He. apply: (bexp_program_safe_split_full_steps Hwf).
    move=> Ee pre_is pre_es hd tl safe Hin s Hco. apply: (He _ _ _ _ _ Hco).
    exact: (bexp_program_safe_split_full_partial Hin).
  Qed.

  Lemma bexp_program_safe_steps_split E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s) ->
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe) (bexp_program_safe_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    move=> Hwf H. move=> Ee pre_es safe Hin s Hco.
    move: (bexp_program_safe_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin_full [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_safe_steps_split_full Hwf H Hin_full Hco).
  Qed.


  (* Well-formedness of bexp_program_safe_split *)

  Lemma bexp_program_safe_split_safe_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_es safe,
      List.In (Ee, pre_es, safe) (bexp_program_safe_split E p) ->
      QFBV.well_formed_bexp safe Ee.
  Proof.
    move=> Hwf Ee pre_es safe Hin.
    move: (bexp_program_safe_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_safe_split_full_safe_well_formed Hwf Hin').
  Qed.

  Lemma bexp_program_safe_split_pre_es_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_es safe,
      List.In (Ee, pre_es, safe) (bexp_program_safe_split E p) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) Ee.
  Proof.
    move=> Hwf Ee pre_es safe Hin.
    move: (bexp_program_safe_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_safe_split_full_pre_es_well_formed Hwf Hin').
  Qed.

  Theorem bexp_program_safe_split_cond_well_formed E f p :
    well_formed_rbexp E f ->
    well_formed_ssa_program E p ->
    forall Ee pre_es safe,
      List.In (Ee, pre_es, safe) (bexp_program_safe_split E p) ->
      QFBV.well_formed_bexp
        (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es)) safe) Ee.
  Proof.
    move=> Hwf_f Hwf_p Ee pre_es safe Hin /=.
    move: (bexp_program_safe_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    move/andP: (Hwf_p) => [/andP [Hwf Hun] Hssa].
    move: (bexp_program_safe_split_full_submap Hun Hssa Hin') => Hsub.
    move: (well_formed_bexp_rbexp Hwf_f) => Hwf_Ee.
    rewrite (well_formed_bexp_submap Hsub Hwf_Ee) andTb.
    rewrite (bexp_program_safe_split_full_pre_es_well_formed Hwf_p Hin') andTb.
    exact: (bexp_program_safe_split_full_safe_well_formed Hwf_p Hin').
  Qed.


  (* Verify safety conditions one by one (less prefix information). *)

  Fixpoint bexp_program_safe_split_checker_rec
           bexp_f
           (rs : seq (SSATE.env * seq QFBV.bexp * QFBV.bexp)) :=
    match rs with
    | [::] => True
    | r::rs =>
      let '(Ee, pre_es, safe) := r in
      (forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj bexp_f (qfbv_conjs pre_es))
                                   safe) s) /\
      bexp_program_safe_split_checker_rec bexp_f rs
    end.

  Definition bexp_program_safe_split_checker E f p :=
    bexp_program_safe_split_checker_rec (bexp_rbexp f)
                                        (bexp_program_safe_split E p).

  Lemma bexp_program_safe_split_checker_split E f p :
    bexp_program_safe_split_checker E f p ->
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe)
                (bexp_program_safe_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    rewrite /bexp_program_safe_split_checker.
    rewrite /bexp_program_safe_split. move: [::].
    elim: p f E => [| i p IH] //= f E pre_es [Hch1 Hch2] E' pre_es' safe Hin s Hco.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hpre_es': (eval_bexp (qfbv_conjs pre_es') s) => //=.
    case: Hin => Hin.
    - case: Hin=> ? ? ?; subst. move: (Hch1 s Hco).
      rewrite Hf Hpre_es' /=. by apply.
    - move: (IH f (instr_succ_typenv i E) _ Hch2 E' pre_es' safe
                Hin s Hco) => /=. rewrite Hf Hpre_es' /=. by apply.
  Qed.

  Lemma bexp_program_safe_split_split_checker E f p :
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe)
                (bexp_program_safe_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    bexp_program_safe_split_checker E f p.
  Proof.
    rewrite /bexp_program_safe_split_checker.
    rewrite /bexp_program_safe_split. move: [::].
    elim: p f E => [| i p IH] //= f E pre_es H. split.
    - move=> s Hco. apply: (H _ _ _ _ s Hco). left. reflexivity.
    - apply: IH. move=> E' pre_es' safe Hin s Hco.
      apply: (H _ _ _ _ s Hco). right. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_checker_steps E f p :
    well_formed_ssa_program E p ->
    bexp_program_safe_split_checker E f p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s).
  Proof.
    move=> Hwf Hch. apply: (bexp_program_safe_split_steps Hwf).
    exact: (bexp_program_safe_split_checker_split Hch).
  Qed.

  Lemma bexp_program_safe_steps_split_checker E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_safe_steps E p s) ->
    bexp_program_safe_split_checker E f p.
  Proof.
    move=> Hwf H. apply: bexp_program_safe_split_split_checker.
    exact: (bexp_program_safe_steps_split Hwf H).
  Qed.


  (** Soundness and completeness *)

  Definition ssa_spec_safe_split (sp : spec) :=
    let E := sinputs sp in
    let f := bexp_rbexp (rng_bexp (spre sp)) in
    let p := sprog sp in
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe) (bexp_program_safe_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe) s).

  Theorem ssa_spec_safe_split_sound sp :
    well_formed_ssa_spec sp -> ssa_spec_safe_split sp -> ssa_spec_safe sp.
  Proof.
    move=> Hwf Hsp. apply: (ssa_spec_safe_qfbv_steps_sound Hwf).
    move: (well_formed_ssa_spec_program Hwf) => Hwfp.
    apply: (bexp_program_safe_split_steps Hwfp). exact: Hsp.
  Qed.

  Theorem ssa_spec_safe_split_complete sp :
    well_formed_ssa_spec sp -> ssa_spec_safe sp -> ssa_spec_safe_split sp.
  Proof.
    move=> Hwf Hsp. move: (well_formed_ssa_spec_program Hwf) => Hwfp.
    apply: (bexp_program_safe_steps_split Hwfp).
    exact: (ssa_spec_safe_qfbv_steps_complete Hwf Hsp).
  Qed.

  Definition ssa_spec_safe_split_checker (sp : spec) :=
    let E := sinputs sp in
    let f := bexp_rbexp (rng_bexp (spre sp)) in
    let p := sprog sp in
    bexp_program_safe_split_checker_rec f
                                        (bexp_program_safe_split E p).

  Theorem ssa_spec_safe_split_checker_sound sp :
    well_formed_ssa_spec sp ->
    ssa_spec_safe_split_checker sp -> ssa_spec_safe sp.
  Proof.
    move=> Hwf Hsp. apply: (ssa_spec_safe_split_sound Hwf).
    exact: (bexp_program_safe_split_checker_split Hsp).
  Qed.

  Theorem ssa_spec_safe_split_checker_complete sp :
    well_formed_ssa_spec sp ->
    ssa_spec_safe sp -> ssa_spec_safe_split_checker sp.
  Proof.
    move=> Hwf Hsp. apply: (bexp_program_safe_split_split_checker ).
    exact: (ssa_spec_safe_split_complete Hwf Hsp).
  Qed.

End SplitConditionsVarying.


(* Program safety - fixed typing environment - final typing environment *)

Section SafetyFixedFinal.

  Import QFBV.

  (* use the final typing environment *)
  Fixpoint bexp_program_safe_fixed_final E p : QFBV.bexp :=
    match p with
    | [::] => qfbv_true
    | hd::tl =>
      qfbv_conj (bexp_instr_safe E hd)
                (qfbv_imp
                   (bexp_instr E (rng_instr hd))
                   (bexp_program_safe_fixed_final E tl))
    end.

  Lemma eval_bexp_program_safe_fixed_final1 E pre p :
    let fE := (program_succ_typenv p E) in
    well_formed_rbexp E pre ->
    ssa_vars_unchanged_program (vars_rbexp pre) p ->
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp pre) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s) ->
    (forall s, SSAStore.conform s fE ->
               eval_rbexp pre s ->
               ssa_program_safe_at fE p s).
  Proof.
    move=> fE Hwf_pre Hun Hwf_p H s.
    have: (forall t : SSAStore.t,
              bvs_eqi E s t ->
              SSAStore.conform t fE ->
              eval_bexp (bexp_rbexp pre) t ->
              eval_bexp (bexp_program_safe_fixed_final fE p) t).
    { move=> t Heqi Hco Hpre. exact: (H _ Hco Hpre). }
    move: {H} Hwf_pre Hun Hwf_p s. rewrite /fE. clear fE.
    elim: p E => [| i p IH] E /=.
    - move=> *. exact: ssa_program_safe_at_nil.
    - rewrite ssa_unchanged_program_cons /well_formed_ssa_program.
      rewrite well_formed_program_cons ssa_single_assignment_cons.
      rewrite ssa_unchanged_program_cons.
      move=> Hwf_pre
               /andP [Hun_prei Hun_prep] /andP [
                 /andP [/andP [Hwf_i Hwf_p]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
      move: (well_formed_rng_instr Hwf_i) => Hwf_rng_Ei.
      move: (well_formed_instr_well_defined Hwf_i) => Hwd_Ei.
      move: (well_defined_rng_instr Hwd_Ei) => Hwd_rng_Ei.
      move=> s H Hco Hpre.
      move: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa) => Hsub_EpE.
      have Hun_iEp: ssa_vars_unchanged_program (vars_env (instr_succ_typenv i E)) p.
      { apply: (ssa_unchanged_program_replace
                  (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
        rewrite ssa_unchanged_program_union. rewrite Hun_Ep Hun_ip.
        exact: is_true_true. }
      move: (ssa_unchanged_program_succ_typenv_submap Hun_iEp Hssa) => Hsub_iEpiE.
      move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsub_EiE.
      move: (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE) => Hsub_EpiE.
      move: (conform_submap Hsub_iEpiE Hco) => Hco_iE.
      move: (conform_submap Hsub_EiE Hco_iE) => Hco_E.
      apply: ssa_program_safe_at_cons.
      + move/eval_bexp_rbexp: Hpre => Hpre.
        apply/(eval_bexp_instr_safe
                 Hco (well_formed_instr_submap Hwf_i Hsub_EpiE)).
        move: (H s (bvs_eqi_refl s) Hco Hpre) => /andP [H1 _].
        move/andP: Hwf_i => [Hwd_i Hwt_i]. exact: H1.
      + move=> t Hei.
        have Hssa_p: well_formed_ssa_program (instr_succ_typenv i E) p.
        { repeat (apply/andP; split); by assumption. }
        have Heq: SSATE.Equal
                    (program_succ_typenv p (instr_succ_typenv i E))
                    (instr_succ_typenv
                       i (program_succ_typenv p (instr_succ_typenv i E))).
        { symmetry. move: (are_defined_lvs_instr_succ_typenv E i) => Hdef.
          apply: env_unchanged_instr_succ_equal.
          - exact: (are_defined_submap Hsub_iEpiE Hdef).
          - apply: (env_unchanged_instr_submap Hsub_iEpiE Hdef).
            + apply: well_formed_instr_well_defined.
              exact: (well_formed_instr_submap Hwf_i Hsub_EiE).
            + exact: (env_unchanged_instr_succ Hwd_Ei Hun_Ei). }
        move: (TELemmas.Equal_submap Heq) => Hsub.
        apply/(ssa_program_safe_at_submap
                 _ Hsub (well_formed_program_submap Hwf_p Hsub_iEpiE)).
        rewrite -ssa_vars_unchanged_rng_instr in Hun_Ei.
          move/(submap_eval_instr _ _ Hsub_EpiE Hwd_rng_Ei): (Hei) => Hei_Est.
          move: (bvs_eqi_eval_instr Hun_Ei Hei_Est) => Heqi_Est.
        apply: (IH _ (well_formed_rbexp_submap Hsub_EiE Hwf_pre) Hun_prep Hssa_p).
        * move=> t' Heqi_tt' Hco_t' Hpre_t'.
          move: (bvs_eqi_submap Hsub_EiE Heqi_tt') => Heqi_Ett'.
          move: (H _ (bvs_eqi_trans Heqi_Est Heqi_Ett') Hco_t' Hpre_t').
          move/andP=> [_ Hevb].
          move: (bexp_instr_eval Hwf_rng_Ei Hco_E Hun_Ei Hei_Est) => Hevb_t.
          rewrite -rng_instr_succ_typenv in Heqi_tt'.
          rewrite (bvs_eqi_qfbv_eval_bexp
                     (bexp_instr_are_defined Hwd_rng_Ei) Heqi_tt') in Hevb_t.
          rewrite (bexp_instr_submap Hwd_rng_Ei Hsub_EpiE) in Hevb_t.
          rewrite Hevb_t /= in Hevb. exact: Hevb.
        * move: (well_formed_instr_submap Hwf_rng_Ei Hsub_EpiE) => Hwf_rng_piEi.
          move: (conform_instr_succ_typenv Hwf_rng_piEi Hco Hei).
          rewrite rng_instr_succ_typenv. apply: SSAStore.conform_submap.
          exact: (SSATE.Lemmas.Equal_submap Heq).
        * move: (bvs_eqi_sym Heqi_Est) => Heqi_Ets.
          move/andP: Hwf_pre => [Hwd_pre Hwt_pre].
          apply/(bvs_eqi_eval_rbexp Hwd_pre Heqi_Ets). exact: Hpre.
  Qed.

  Lemma eval_bexp_program_safe_fixed_final2 E pre p :
    let fE := (program_succ_typenv p E) in
    well_formed_rbexp E pre ->
    ssa_vars_unchanged_program (vars_rbexp pre) p ->
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_rbexp pre s ->
               ssa_program_safe_at fE p s) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp pre) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s).
  Proof.
    move=> fE. rewrite /fE. clear fE.
    move=> Hwf_Epre Hun_prep Hwf_ssa_Ep Hsafe s.
    have: (forall t,
              bvs_eqi (program_succ_typenv p E) s t ->
              SSAStore.conform t (program_succ_typenv p E) ->
              eval_rbexp pre t -> ssa_program_safe_at (program_succ_typenv p E) p t).
    { move=> t Heqi. by apply: Hsafe. }
    move: {Hsafe} Hwf_Epre Hun_prep Hwf_ssa_Ep s.
    elim: p E pre => [| i p IH] E pre //=.

    move=> Hwf_Epre.
    rewrite ssa_unchanged_program_cons. move/andP=> [Hnu_prei Hun_prep].
    move=> Hwf_ssa. move: (well_formed_ssa_tl Hwf_ssa) => Hwf_ssa_p. move: Hwf_ssa.
    rewrite /well_formed_ssa_program /=. rewrite ssa_unchanged_program_cons.
    move=> /andP [/andP [/andP [Hwf_Ei Hwf_iEp]
                          /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa_p]].
    move: (well_formed_instr_well_defined Hwf_Ei) => Hwd_Ei.
    move=> s Hsafe Hco Hpre_s.

    move: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa_p) => Hsub_EpE.
    have Hun_iEp: ssa_vars_unchanged_program (vars_env (instr_succ_typenv i E)) p.
    { apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union. rewrite Hun_Ep Hun_ip.
      exact: is_true_true. }
    move: (ssa_unchanged_program_succ_typenv_submap Hun_iEp Hssa_p) => Hsub_iEpiE.
    move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsub_EiE.
    move: (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE) => Hsub_EpiE.
    move: (conform_submap Hsub_iEpiE Hco) => Hco_iE.
    move: (conform_submap Hsub_EiE Hco_iE) => Hco_E.

    have Heq: SSATE.Equal
                (program_succ_typenv p (instr_succ_typenv i E))
                (instr_succ_typenv
                   i (program_succ_typenv p (instr_succ_typenv i E))).
    { symmetry. move: (are_defined_lvs_instr_succ_typenv E i) => Hdef.
      apply: env_unchanged_instr_succ_equal.
      - exact: (are_defined_submap Hsub_iEpiE Hdef).
      - apply: (env_unchanged_instr_submap Hsub_iEpiE Hdef).
        + apply: well_formed_instr_well_defined.
          exact: (well_formed_instr_submap Hwf_Ei Hsub_EiE).
        + exact: (env_unchanged_instr_succ Hwd_Ei Hun_Ei). }
    move: (TELemmas.Equal_submap Heq) => Hsub.

    move/eval_bexp_rbexp: Hpre_s => Hpre_s.
    move: (Hsafe s (bvs_eqi_refl s) Hco Hpre_s) => {Hsafe} Hsafe.
    inversion_clear Hsafe.
    apply/andP; split.
    - apply/(eval_bexp_instr_safe Hco (well_formed_instr_submap Hwf_Ei Hsub_EpiE)).
      assumption.
    - case Hsafe_i:
        (eval_bexp
           (bexp_instr
              (program_succ_typenv p (instr_succ_typenv i E)) (rng_instr i)) s) => //=.
      apply: (IH (instr_succ_typenv i E) pre).
      + exact: (well_formed_rbexp_submap Hsub_EiE Hwf_Epre).
      + exact: Hun_prep.
      + exact: Hwf_ssa_p.
      + move=> t Heqi_ts Hco_t Hpre_t.
        move: (well_formed_program_submap Hwf_iEp Hsub_iEpiE) => Hwf_piEp.
        apply: (bvs_eqi_ssa_program_safe_at Heqi_ts Hwf_piEp).
        apply/(ssa_program_safe_at_submap
                 _ Hsub (well_formed_program_submap Hwf_iEp Hsub_iEpiE)).
        apply: H0.
        apply: (eval_bexp_instr
                  (well_formed_instr_submap Hwf_Ei Hsub_EpiE) Hco _ Hsafe_i).
        apply: (SSAStore.conform_submap _ Hco).
        apply: TELemmas.Equal_submap. symmetry. exact: Heq.
      + exact: Hco.
      + apply/eval_bexp_rbexp. exact: Hpre_s.
  Qed.

  (* Soundness and completeness of bexp_program_safe_fixed_final. *)

  Definition ssa_spec_safe_qfbv_fixed_final sp : Prop :=
    let fE := program_succ_typenv (sprog sp) (sinputs sp) in
    forall s, SSAStore.conform s fE ->
              eval_bexp (bexp_rbexp (rng_bexp (spre sp))) s ->
              eval_bexp (bexp_program_safe_fixed_final fE (sprog sp)) s.

  Lemma ssa_spec_safe_qfbv_fixed_final_sound sp :
    well_formed_ssa_spec sp -> ssa_spec_safe_qfbv_fixed_final sp ->
    ssa_spec_safe_final sp.
  Proof.
    move=> Hwf. move: Hwf (well_formed_ssa_spec_program Hwf).
    case: sp => E f p g.
    rewrite /well_formed_ssa_spec /well_formed_spec
            /ssa_spec_safe_final /ssa_spec_safe_qfbv_fixed_final /=.
    move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
            Hwf_ssa_p /= Hbv s Hco Hf.

    move: (well_formed_rng_bexp Hwf_f) => Hwf_f_rng.
    move: (Hwf_f_rng). move/andP=> [Hdef_f_rng Hwt_f_rng].
    move/defsubP: Hdef_f_rng => Hsub_f_rng.
    move: (ssa_unchanged_program_subset Hun_Ep Hsub_f_rng) => Hun_f_rng.

    apply: (eval_bexp_program_safe_fixed_final1
              Hwf_f_rng Hun_f_rng Hwf_ssa_p _ Hco Hf).
    move=> t Hco_t Hf_t. move: (Hbv _ Hco_t Hf_t). by apply.
  Qed.

  Lemma ssa_spec_safe_qfbv_fixed_final_complete sp :
    well_formed_ssa_spec sp -> ssa_spec_safe_final sp ->
    ssa_spec_safe_qfbv_fixed_final sp.
  Proof.
    move=> Hwf. move: Hwf (well_formed_ssa_spec_program Hwf).
    case: sp => E f p g.
    rewrite /well_formed_ssa_spec /well_formed_spec
            /ssa_spec_safe_final /ssa_spec_safe_qfbv_fixed_final /=.
    move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
            Hwf_ssa_p /= Hsafe s Hco Hf.

    move: (well_formed_rng_bexp Hwf_f) => Hwf_f_rng.
    move: (Hwf_f_rng). move/andP=> [Hdef_f_rng Hwt_f_rng].
    move/defsubP: Hdef_f_rng => Hsub_f_rng.
    move: (ssa_unchanged_program_subset Hun_Ep Hsub_f_rng) => Hun_f_rng.
    apply: (eval_bexp_program_safe_fixed_final2
              Hwf_f_rng Hun_f_rng Hwf_ssa_p _ Hco Hf).
    exact: Hsafe.
  Qed.

End SafetyFixedFinal.


Section SplitConditionsFixedFinal.

  Import QFBV.

  (* Construct safety conditions. *)

  (*
   * E: the final typing environment
   * pre_is: the prefix of instructions
   * pre_es: the QFBV expressions encoding the prefix of instructions
   * p: the remaining program to be converted
   *)
  Fixpoint bexp_program_safe_split_fixed_final_full_rec
           E pre_is (pre_es : seq QFBV.bexp) (p : program) :
    seq (seq instr * seq QFBV.bexp * instr * seq instr * QFBV.bexp) :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (pre_is, pre_es, hd, tl, bexp_instr_safe E hd)
        ::(bexp_program_safe_split_fixed_final_full_rec
             E (rcons pre_is hd)
             (rcons pre_es (bexp_instr E (rng_instr hd))) tl)
    end.

  (*
   * E: the final typing environment
   * p: the remaining program to be converted
   *)
  Definition bexp_program_safe_split_fixed_final_full E p :=
    bexp_program_safe_split_fixed_final_full_rec E [::] [::] p.

  Lemma bexp_program_safe_split_fixed_final_full_rec_is E pre_is pre_es p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full_rec E pre_is pre_es p) ->
      pre_is' ++ hd::tl = pre_is ++ p.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. reflexivity.
    - move=> Hin. rewrite -(cat_rcons i). apply: IH. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_rec_is_prefix E pre_is pre_es p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full_rec E pre_is pre_es p) ->
      exists suf, pre_is' = pre_is ++ suf.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. exists [::]. rewrite cats0. reflexivity.
    - move=> Hin. move: (IH _ _ _ _ _ _ _ _ Hin) => [suf H]. exists (i::suf).
      rewrite -(cat_rcons). assumption.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_rec_es E pre_is pre_es p :
    well_formed_program E p ->
    are_defined (lvs_program p) E -> env_unchanged_program E p ->
    are_defined (lvs_program pre_is) E -> env_unchanged_program E pre_is ->
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full_rec E pre_is pre_es p) ->
      pre_es = bexp_program E (rng_program pre_is) ->
      pre_es' = bexp_program E (rng_program pre_is').
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move/andP=> [Hwf_Ei Hwf_iEp].
    rewrite are_defined_union. move/andP=> [Hdef_iE Hdef_pE].
    move/andP=> [Heun_Ei Heun_Ep].
    move=> Hdef_pre_is Heun_pre_is.
    move=> pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. by apply.
    - move=> Hin H.
      apply: (IH _ _ _ _ Hdef_pE Heun_Ep _ _ _ _ _ _ _ Hin).
      + apply: (well_formed_program_submap Hwf_iEp). apply: SSATE.Lemmas.Equal_submap.
        exact: (env_unchanged_instr_succ_equal Hdef_iE Heun_Ei).
      + apply/defsubP. rewrite lvs_program_rcons.
        apply: SSAVS.Lemmas.subset_union3.
        * apply/defsubP. exact: Hdef_pre_is.
        * apply/defsubP. exact: Hdef_iE.
      + rewrite env_unchanged_program_rcons. by rewrite Heun_pre_is Heun_Ei.
      + rewrite rng_program_rcons. rewrite bexp_program_rcons.
        rewrite -H. rewrite rng_program_succ_typenv.
        have ->:
             (bexp_instr E (rng_instr i)) =
             (bexp_instr (program_succ_typenv pre_is E) (rng_instr i)).
        { move: (well_formed_instr_well_defined Hwf_Ei) => Hwd_Ei.
          move: (well_defined_rng_instr Hwd_Ei) => Hwd_Ei_rng.
          apply: (bexp_instr_submap Hwd_Ei_rng).
          apply: SSATE.Lemmas.Equal_submap. symmetry.
          exact: (env_unchanged_program_succ_equal Hdef_pre_is Heun_pre_is). }
        reflexivity.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_is E p :
    let fE := program_succ_typenv p E in
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full fE p) ->
      pre_is' ++ (hd::tl) = p.
  Proof.
    move=> fE pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_safe_split_fixed_final_full_rec_is Hin).
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_es E p :
    well_formed_program E p ->
    are_defined (lvs_program p) E -> env_unchanged_program E p ->
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full E p) ->
      pre_es' = bexp_program E (rng_program pre_is').
  Proof.
    move=> Hwf_Ep Hdef_pE Heun_Ep pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_safe_split_fixed_final_full_rec_es
              Hwf_Ep Hdef_pE Heun_Ep _ _ Hin).
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_sound E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall pre_is pre_es hd tl safe,
        List.In (pre_is, pre_es, hd, tl, safe)
                (bexp_program_safe_split_fixed_final_full fE p) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s).
  Proof.
    rewrite /bexp_program_safe_split_fixed_final_full. move=> Hwf He s.
    have: eval_bexp (qfbv_conjs [::]) s by done.
    move: s He. move: [::]. move: [::].
    elim: p E f Hwf => [| i p IH] E f Hwf pre_es pre_is s //= He Hpre_es Hco Hf.
    apply/andP; split.
    - move: (He pre_is pre_es i p
                (bexp_instr_safe (program_succ_typenv p (instr_succ_typenv i E)) i)
                (or_introl
                   _
                   (Logic.eq_refl
                      (pre_is, pre_es, i, p,
                       bexp_instr_safe (program_succ_typenv
                                          p (instr_succ_typenv i E)) i)))
                s Hco) => /=.
      rewrite negb_and Hf Hpre_es /=. by apply.
    - case His:
        (eval_bexp
           (bexp_instr
              (program_succ_typenv p (instr_succ_typenv i E)) (rng_instr i)) s) => //=.
      move: (well_formed_ssa_tl Hwf) => Hwf_p.
      apply: (IH (instr_succ_typenv i E) f Hwf_p
                 (rcons pre_es
                        (bexp_instr
                           (program_succ_typenv p (instr_succ_typenv i E))
                           (rng_instr i))) (rcons pre_is i) _ _ _ Hco).
      + move=> pre_is_t pre_es_t i_t p_t safe_t Hin_t t Hco_t.
        apply: (He pre_is_t pre_es_t i_t p_t safe_t _ t Hco_t).
        right. assumption.
      + rewrite eval_qfbv_conjs_rcons. rewrite Hpre_es His. exact: is_true_true.
      + exact: Hf.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_complete E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s) ->
    (forall pre_is pre_es hd tl safe,
        List.In (pre_is, pre_es, hd, tl, safe)
                (bexp_program_safe_split_fixed_final_full fE p) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)).
  Proof.
    move=> fE.
    rewrite /bexp_program_safe_split_fixed_final_full. move=> Hwf Hsafe.
    move=> pre_is pre_es hd tl safe Hin s Hco /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hpre_es: (eval_bexp (qfbv_conjs pre_es) s) => //=.
    have: (forall s : SSAStore.t,
              SSAStore.conform s fE ->
              eval_bexp (qfbv_conjs (bexp_program fE [::])) s ->
              eval_bexp (bexp_rbexp f) s ->
              eval_bexp (bexp_program_safe_fixed_final fE p) s)
      by intros; apply: Hsafe.
    clear Hsafe.

    have: [::] = bexp_program fE (rng_program [::]) by done.
    have: are_defined (lvs_program [::]) fE by done.
    have: env_unchanged_program fE [::] by done.
    move: Hwf pre_is pre_es hd tl safe Hin s Hco Hf Hpre_es.
    rewrite /fE. clear fE. move: [::]. move: [::].
    elim: p E f => [| i p IH] E f pre_es pre_is //= Hwf_Eip.
    move=> pre_is' pre_es' hd tl safe Hin s Hco Hf Hpre_es'
                   Heun_pre_is Hdef_pre_is Hpre_es Hsafe.
    move: (env_unchanged_program_succ Hwf_Eip). move=> /= /andP [Heun_i Heun_p].
    move: (well_formed_ssa_tl Hwf_Eip) => Hwf_ssa_iEp.
    move: Hwf_Eip. rewrite /well_formed_ssa_program /=.
    rewrite ssa_unchanged_program_cons.
    move/andP=> [/andP [/andP [Hwf_Ei Hwf_iEp]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa_p]].
    move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsub_EiE.
    have Hsub_iEpiE: SSA.TELemmas.submap
                       (instr_succ_typenv i E)
                       (program_succ_typenv p (instr_succ_typenv i E)).
    { apply: (ssa_unchanged_program_succ_typenv_submap _ Hssa_p).
      apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union.
      rewrite Hun_Ep Hun_ip. exact: is_true_true. }
    move: (env_unchanged_program_succ_equal Hdef_pre_is Heun_pre_is) => Heq.
    move: (TELemmas.Equal_sym Heq) => {Heq} Heq.
    move: (well_formed_rng_instr
             (well_formed_instr_submap
                Hwf_Ei (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE))) => Hwf_piEi.
    case: Hin.

    - case=> ? ? ? ? ?; subst. rewrite bexp_rng_program in Hpre_es'.
      move: (Hsafe _ Hco Hpre_es' Hf). move/andP=> [H1 _]. exact: H1.
    - move=> Hin. apply: (IH _ _ _ _ Hwf_ssa_iEp
                             _ _ _ _ _ Hin _ Hco Hf Hpre_es').
      + rewrite env_unchanged_program_rcons. rewrite Heun_pre_is Heun_i /=.
        exact: is_true_true.
      + apply/defsubP. rewrite lvs_program_rcons.
        apply: VSLemmas.subset_union3.
        * apply/defsubP. exact: Hdef_pre_is.
        * apply/defsubP.
          apply: (are_defined_submap _ (are_defined_lvs_instr_succ_typenv E i)).
          exact: Hsub_iEpiE.
      + rewrite rng_program_rcons. rewrite bexp_program_rcons.
        rewrite -Hpre_es. rewrite rng_program_succ_typenv.
        rewrite -(bexp_instr_equal (well_formed_instr_well_defined Hwf_piEi) Heq).
        reflexivity.
      + move=> t Hco_t Hpre_is_t Hf_t. rewrite bexp_program_rcons in Hpre_is_t.
        rewrite eval_qfbv_conjs_rcons in Hpre_is_t.
        move/andP: Hpre_is_t => [Hpre_is_t Hei_t].
        move: (Hsafe t Hco_t Hpre_is_t Hf_t). rewrite -bexp_rng_instr in Hei_t.
        rewrite -(bexp_instr_equal (well_formed_instr_well_defined Hwf_piEi) Heq)
          in Hei_t. rewrite Hei_t /=. move/andP=> [_ H]. exact: H.
  Qed.


  (* Well-formedness of bexp_program_safe_split_fixed_final_full *)

  Lemma bexp_program_safe_split_fixed_final_full_safe_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_is pre_es hd tl safe,
      List.In (pre_is, pre_es, hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full fE p) ->
      QFBV.well_formed_bexp safe fE.
  Proof.
    rewrite /bexp_program_safe_split_fixed_final_full. move: [::]. move: [::].
    elim: p E => [| i p IH] E //= pre_es pre_is Hwf_Eip pre_is' pre_es' hd tl safe.

    move: (env_unchanged_program_succ Hwf_Eip). move=> /= /andP [Heun_i Heun_p].
    move: (well_formed_ssa_tl Hwf_Eip) => Hwf_ssa_iEp.
    move: Hwf_Eip. rewrite /well_formed_ssa_program /=.
    rewrite ssa_unchanged_program_cons.
    move/andP=> [/andP [/andP [Hwf_Ei Hwf_iEp]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa_p]].
    move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsub_EiE.
    have Hsub_iEpiE: SSA.TELemmas.submap
                       (instr_succ_typenv i E)
                       (program_succ_typenv p (instr_succ_typenv i E)).
    { apply: (ssa_unchanged_program_succ_typenv_submap _ Hssa_p).
      apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union.
      rewrite Hun_Ep Hun_ip. exact: is_true_true. }

    case => Hin.
    - case: Hin=> ? ? ? ? ?; subst. apply: bexp_instr_safe_well_formed.
      apply: (well_formed_instr_submap Hwf_Ei).
      exact: (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE).
    - exact: (IH _ _ _ Hwf_ssa_iEp _ _ _ _ _ Hin).
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_pre_es_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_is pre_es hd tl safe,
      List.In (pre_is, pre_es, hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full fE p) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) fE.
  Proof.
    rewrite /bexp_program_safe_split_fixed_final_full.
    have: QFBV.well_formed_bexp (qfbv_conjs [::]) (program_succ_typenv p E) by done.
    move: [::]. move: [::].
    elim: p E => [| i p IH] E //= pre_is pre_es Hwf_pre_es
                            Hwf_Eip pre_is' pre_es' hd tl safe.

    move: (env_unchanged_program_succ Hwf_Eip). move=> /= /andP [Heun_i Heun_p].
    move: (well_formed_ssa_tl Hwf_Eip) => Hwf_ssa_iEp.
    move: Hwf_Eip. rewrite /well_formed_ssa_program /=.
    rewrite ssa_unchanged_program_cons.
    move/andP=> [/andP [/andP [Hwf_Ei Hwf_iEp]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa_p]].
    move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsub_EiE.
    have Hsub_iEpiE: SSA.TELemmas.submap
                       (instr_succ_typenv i E)
                       (program_succ_typenv p (instr_succ_typenv i E)).
    { apply: (ssa_unchanged_program_succ_typenv_submap _ Hssa_p).
      apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union.
      rewrite Hun_Ep Hun_ip. exact: is_true_true. }

    case=> Hin.
    - case: Hin => ? ? ? ? ?; subst. exact: Hwf_pre_es.
    - apply: (IH _ _ _ _ Hwf_ssa_iEp _ _ _ _ _ Hin).
      rewrite bexp_rng_instr. rewrite well_formed_bexp_qfbv_conjs_rcons.
      apply/andP; split.
      + exact: (well_formed_bexp_submap _ Hwf_pre_es).
      + move: (well_formed_bexp_instr Hun_Ei Hwf_Ei) => Hwfb.
        rewrite -(bexp_instr_submap (well_formed_instr_well_defined Hwf_Ei)
                                    (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE)).
        exact: (well_formed_bexp_submap Hsub_iEpiE Hwfb).
  Qed.


  (* Construct safety conditions with less prefix information. *)

  (* pre_es: encoding of instructions in QFBV *)
  Fixpoint bexp_program_safe_split_fixed_final_rec E (pre_es : seq QFBV.bexp) p :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (pre_es, bexp_instr_safe E hd)
        ::(bexp_program_safe_split_fixed_final_rec
             E (rcons pre_es (bexp_instr E (rng_instr hd))) tl)
    end.

  Definition bexp_program_safe_split_fixed_final E p :=
    bexp_program_safe_split_fixed_final_rec E [::] p.

  Lemma bexp_program_safe_split_fixed_final_rec_full_partial E pre_is pre_es p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full_rec E pre_is pre_es p) ->
      (pre_es', safe) \in (bexp_program_safe_split_fixed_final_rec E pre_es p).
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. exact: mem_head.
    - move=> Hin. by rewrite in_cons (IH _ _ _ _ _ _ _ _ Hin) orbT.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_rec_partial_full E pre_is pre_es p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    pre_es = bexp_program fE (rng_program pre_is) ->
    are_defined (lvs_program pre_is) fE ->
    env_unchanged_program fE pre_is ->
    forall pre_es' safe,
      ((pre_es', safe) \in (bexp_program_safe_split_fixed_final_rec fE pre_es p)) ->
      pre_es = bexp_program fE (rng_program pre_is) ->
    exists pre_is' hd tl,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full_rec fE pre_is pre_es p) /\
      (pre_is' ++ (hd :: tl) = pre_is ++ p) /\
      (pre_es' = bexp_program fE (rng_program pre_is')).
  Proof.
    move=> fE. rewrite /fE. clear fE.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.

    move=> Hwf_Eip.
    move: (env_unchanged_program_succ Hwf_Eip). move=> /= /andP [Heun_i Heun_p].
    move: (well_formed_ssa_tl Hwf_Eip) => Hwf_ssa_iEp.
    move: Hwf_Eip. rewrite /well_formed_ssa_program /=.
    rewrite ssa_unchanged_program_cons.
    move/andP=> [/andP [/andP [Hwf_Ei Hwf_iEp]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa_p]].
    move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsub_EiE.
    have Hsub_iEpiE: SSA.TELemmas.submap
                       (instr_succ_typenv i E)
                       (program_succ_typenv p (instr_succ_typenv i E)).
    { apply: (ssa_unchanged_program_succ_typenv_submap _ Hssa_p).
      apply: (ssa_unchanged_program_replace
                (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
      rewrite ssa_unchanged_program_union.
      rewrite Hun_Ep Hun_ip. exact: is_true_true. }

    move=> Hpre_es Hdef_pre_is Heun_pre_is.
    move: (env_unchanged_program_succ_equal Hdef_pre_is Heun_pre_is) => Heq.
    move: (TELemmas.Equal_sym Heq) => {Heq} Heq.
    move: (well_formed_rng_instr
             (well_formed_instr_submap
                Hwf_Ei (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE))) => Hwf_piEi.

    move=> pre_es' safe. rewrite in_cons. case/orP.
    - case/eqP=> ? ? ?; subst. exists pre_is. exists i. exists p.
      repeat split. left. reflexivity.
    - move=> Hin Hes.

      have Hpre_es_i:
        rcons pre_es
              (bexp_instr
                 (program_succ_typenv p (instr_succ_typenv i E)) (rng_instr i)) =
        bexp_program (program_succ_typenv p (instr_succ_typenv i E))
                     (rng_program (rcons pre_is i)).
      { rewrite rng_program_rcons. rewrite bexp_program_rcons. rewrite -Hes.
        rewrite rng_program_succ_typenv.
        rewrite -(bexp_instr_equal (well_formed_instr_well_defined Hwf_piEi) Heq).
        reflexivity. }
      have Hdef_pre_is_i:
        are_defined (lvs_program (rcons pre_is i))
                    (program_succ_typenv p (instr_succ_typenv i E)).
      { apply/defsubP. rewrite lvs_program_rcons.
        move/defsubP: Hdef_pre_is => Hsub_pre_is.
        apply: VSLemmas.subset_union3.
        - exact: Hsub_pre_is.
        - rewrite vars_env_program_succ_typenv. apply: VSLemmas.subset_union1.
          rewrite vars_env_instr_succ_typenv.  apply: VSLemmas.subset_union2.
          exact: VSLemmas.subset_refl. }
      have Heun_pre_is_i:
        env_unchanged_program (program_succ_typenv p (instr_succ_typenv i E))
                              (rcons pre_is i).
      { rewrite env_unchanged_program_rcons. rewrite Heun_pre_is Heun_i /=.
        exact: is_true_true. }
      move: (IH (instr_succ_typenv i E) (rcons pre_is i)
                (rcons pre_es
                       (bexp_instr (program_succ_typenv p (instr_succ_typenv i E))
                   (rng_instr i)))
                Hwf_ssa_iEp Hpre_es_i Hdef_pre_is_i Heun_pre_is_i _ _ Hin Hpre_es_i).
      move=> [pre_is' [hd [tl [Hin' [Hpre_is' Hpre_es']]]]].
      exists pre_is'; exists hd; exists tl. repeat split.
      + right. assumption.
      + rewrite cat_rcons in Hpre_is'. exact: Hpre_is'.
      + exact: Hpre_es'.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_full_partial E p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_safe_split_fixed_final_full E p) ->
      (pre_es', safe) \in (bexp_program_safe_split_fixed_final E p).
  Proof.
    move=> pre_is' pre_es' hd tl safe Hin.
    apply: bexp_program_safe_split_fixed_final_rec_full_partial. exact: Hin.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_partial_full E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_es' safe,
      ((pre_es', safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
      exists pre_is' hd tl,
        List.In (pre_is', pre_es', hd, tl, safe)
                (bexp_program_safe_split_fixed_final_full fE p) /\
        (pre_is' ++ (hd :: tl) = p) /\
        (pre_es' = bexp_program fE (rng_program pre_is')).
  Proof.
    move=> fE Hwf_Ep pre_es' safe Hin.
      by apply:
           (bexp_program_safe_split_fixed_final_rec_partial_full Hwf_Ep _ _ _ Hin).
  Qed.

  Lemma bexp_program_safe_split_fixed_final_sound E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s).
  Proof.
    move=> fE Hwf_Ep He.
    apply: (bexp_program_safe_split_fixed_final_full_sound Hwf_Ep).
    move=> pre_is pre_es hd tl safe Hin s Hco. apply: (He _ _ _ _ Hco).
    exact: (bexp_program_safe_split_fixed_final_full_partial Hin).
  Qed.

  Lemma bexp_program_safe_split_fixed_final_complete E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s) ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)).
  Proof.
    move=> fE Hwf H pre_es safe Hin s Hco.
    move: (bexp_program_safe_split_fixed_final_partial_full Hwf Hin) =>
    [pre_is [hd [tl [Hin_full [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_safe_split_fixed_final_full_complete Hwf H Hin_full Hco).
  Qed.


  (* Well-formedness of bexp_program_safe_split *)

  Lemma bexp_program_safe_split_fixed_final_safe_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp safe fE.
  Proof.
    move=> fE Hwf pre_es safe Hin.
    move: (bexp_program_safe_split_fixed_final_partial_full Hwf Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_safe_split_fixed_final_full_safe_well_formed Hwf Hin').
  Qed.

  Lemma bexp_program_safe_split_fixed_final_pre_es_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) fE.
  Proof.
    move=> FE Hwf pre_es safe Hin.
    move: (bexp_program_safe_split_fixed_final_partial_full Hwf Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_safe_split_fixed_final_full_pre_es_well_formed Hwf Hin').
  Qed.

  Theorem bexp_program_safe_split_fixed_final_cond_well_formed E f p :
    let fE := program_succ_typenv p E in
    well_formed_rbexp E f ->
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp
        (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es)) safe) fE.
  Proof.
    move=> fE Hwf_Ef Hwf_ssa_Ep pre_es safe Hin /=.
    rewrite (bexp_program_safe_split_fixed_final_pre_es_well_formed Hwf_ssa_Ep Hin).
    rewrite (bexp_program_safe_split_fixed_final_safe_well_formed Hwf_ssa_Ep Hin).
    rewrite !andbT.
    move/andP: (Hwf_ssa_Ep) => [/andP [Hwf_Ep Hun_Ep] Hssa_p].
    move: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa_p) => Hsub_EpE.
    move: (well_formed_bexp_rbexp Hwf_Ef) => {Hwf_Ef} Hwf_Ef.
    rewrite (well_formed_bexp_submap Hsub_EpE Hwf_Ef).
    exact: is_true_true.
  Qed.

  (* Construct safety conditions with less prefix information and use qfbv_conjs_la. *)

  Lemma bexp_program_safe_split_fixed_final_sound_la E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es))
                                safe)) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s).
  Proof.
    move=> fE Hwf_Ep He.
    apply: (bexp_program_safe_split_fixed_final_sound Hwf_Ep).
    move=> pre_es safe Hin s Hco. move: (He pre_es safe Hin s Hco) => /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hsafe: (eval_bexp safe s) => /=.
    - rewrite !orbT. by apply.
    - rewrite !orbF. move/negP=> H. apply/negP=> H'. apply: H.
      rewrite -eval_qfbv_conjs_ra_la. assumption.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_complete_la E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_safe_fixed_final fE p) s) ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es))
                                safe)).
  Proof.
    move=> fE Hwf H pre_es safe Hin s Hco.
    move: (bexp_program_safe_split_fixed_final_complete Hwf H Hin Hco) => /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hsafe: (eval_bexp safe s) => /=.
    - rewrite !orbT. by apply.
    - rewrite !orbF. move/negP=> He. apply/negP=> He'. apply: He.
      rewrite eval_qfbv_conjs_ra_la. assumption.
  Qed.

  Lemma bexp_program_safe_split_fixed_final_cond_well_formed_la E f p :
    let fE := program_succ_typenv p E in
    well_formed_rbexp E f ->
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_safe_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp
        (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es)) safe) fE.
  Proof.
    move=> fE Hwf_Ef Hwf_Ep pre_es safe Hin.
    move: (bexp_program_safe_split_fixed_final_cond_well_formed Hwf_Ef Hwf_Ep Hin).
    simpl. move/andP=> [/andP [H1 H2] H3]. rewrite H1 H3 andbT /=.
    rewrite -well_formed_bexp_ra_la. assumption.
  Qed.

End SplitConditionsFixedFinal.
