
(** * Polynomial ring with integer coefficients *)

From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From Coq Require Import Ring_polynom ZArith.
From ssrlib Require Import Nats ZAriths Seqs.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** ** [PExpr Z] *)

(*
  R := Z
  rO := 0
  rI := 1
  radd := Z.add
  rmul := Z.mul
  rsub := Z.sub
  ropp := Z.opp
  C := Z
  cO := 0
  cI := 1
  cadd := Z.add
  cmul := Z.mul
  csub := Z.sub
  copp := Z.opp
  ceqb := Z.eqb
  phi := id
  req := Z.eq
  Cpow := Z
  Cp_phi := Z.of_N
  rpow := Z.pow
  cdiv := Z.quotrem
  RelationClasses.Equivalence req := RelationClasses.eq_equivalence
  ring_eq_ext := Zeqe.
  ring_theory := Zth
  almost_ring_theory := Zath
  power_theory := Zpower_theory
  ring_morph := Zrm
  div_theory := Zdt
  sign_theory := Zst
*)
Section ZPExpr.

  Local Open Scope Z_scope.

  (* Lemmas about the morphism from C to R *)
  Lemma Zrm_eqb_eq : forall x y : Z, Z.eqb x y -> Z.eq (id x) (id y).
  Proof. move=> x y /Z.eqb_eq. by apply. Qed.

  (* A ring_morph (identity function) from C to R *)
  Definition Zrm :=
    IDmorph 0 1 Z.add Z.mul Z.sub Z.opp RelationClasses.eq_equivalence
            Z.eqb Zrm_eqb_eq.

  (* almost_ring_theory *)
  Definition Zath := Rth_ARth RelationClasses.eq_equivalence Zeqe Zth.

  (* Lemma for sign_theory *)
  Lemma Zsign_spec : forall c c' : Z, get_signZ c = Some c' -> Z.eqb c (Z.opp c').
  Proof.
    move=> x y. rewrite /get_signZ. case: x => //=. move=> p [] <- /=.
    exact: Pos.eqb_refl.
  Qed.

  (* A sign_theory. The built-in sign_theory get_signZ_th relies on an old
     comparison function Zeq_bool. *)
  Definition Zst := @mksign_th Z Z.opp Z.eqb get_signZ Zsign_spec.

  (* div_theory *)
  Definition Zdt := Ztriv_div_th Zsth id.

  (* *)

  Definition Znorm_subst : PExpr Z -> Pol Z :=
    @norm_subst Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb Z.quotrem 0 [::].

  Definition ZPeq : Pol Z -> Pol Z -> bool := @Peq Z Z.eqb.

  Definition ZPEeval : seq Z -> PExpr Z -> Z :=
    @PEeval Z 0 1 Z.add Z.mul Z.sub Z.opp Z id Z Z.of_N Z.pow.

  Definition Zinterp_PElist :=
    @interp_PElist Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eq
                   Z id Z Z.of_N Z.pow.

  Definition Zmk_monpol_list :=
    @mk_monpol_list Z 0 1 Z.add Z.mul Z.sub Z.opp
                    Z.eqb Z.quotrem.

  Definition ZPeq_ok :=
    @Peq_ok Z 0 1 Z.add Z.mul Z.sub Z.opp
            Z.eq RelationClasses.eq_equivalence Zeqe
            Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb id
            Zrm.

  Definition ZPeq_spec :=
    @Peq_spec Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eq RelationClasses.eq_equivalence Zeqe
              Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb id Zrm.

  Definition Znorm_subst_spec :=
    @norm_subst_spec Z 0 1 Z.add Z.mul Z.sub Z.opp
                     Z.eq RelationClasses.eq_equivalence Zeqe Zath
                     Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb id Zrm
                     Z Z.of_N Z.pow Zpower_theory Z.quotrem Zdt.

  Definition Zring_rw_correct :=
    @ring_rw_correct Z 0 1 Z.add Z.mul Z.sub Z.opp
                     Z.eq RelationClasses.eq_equivalence Zeqe Zath
                     Z 0 1 Z.add Z.mul Z.sub
                     Z.opp Z.eqb id Zrm
                     Z Z.of_N Z.pow Zpower_theory
                     Z.quotrem Zdt get_signZ Zst.

  Definition ZPphi_dev_ok :=
    @Pphi_dev_ok Z 0 1 Z.add Z.mul Z.sub Z.opp
                 Z.eq RelationClasses.eq_equivalence Zeqe Zath
                 Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb id Zrm get_signZ Zst.

  Definition ZPExpr_eq := Field_theory.PExpr_eq Z.eqb.

  (* Two polynomials are syntactically equal after normalization *)
  Definition zpexpr_eqb (p1 p2 : PExpr Z) : bool :=
    ZPeq (Znorm_subst p1) (Znorm_subst p2).

  Lemma zpexpr_eq_zpeeval s e1 e2 :
    ZPExpr_eq e1 e2 -> ZPEeval s e1 = ZPEeval s e2.
  Proof.
    elim: e1 e2 => //=.
    - move=> c [] //=. move=> d Heq. apply/Z.eqb_eq. assumption.
    - move=> j [] //=. move=> k Heq. move/Pos.eqb_eq: Heq => ->. reflexivity.
    - move=> e1 IH1 e2 IH2 [] //=. move=> e3 e4. case Heq13: (ZPExpr_eq e1 e3) => //=.
      move=> Heq24. rewrite (IH1 _ Heq13) (IH2 _ Heq24). reflexivity.
    - move=> e1 IH1 e2 IH2 [] //=. move=> e3 e4. case Heq13: (ZPExpr_eq e1 e3) => //=.
      move=> Heq24. rewrite (IH1 _ Heq13) (IH2 _ Heq24). reflexivity.
    - move=> e1 IH1 e2 IH2 [] //=. move=> e3 e4. case Heq13: (ZPExpr_eq e1 e3) => //=.
      move=> Heq24. rewrite (IH1 _ Heq13) (IH2 _ Heq24). reflexivity.
    - move=> e1 IH1 [] //=. move=> e2 Heq. rewrite (IH1 _ Heq). reflexivity.
    - move=> e1 IH1 n [] //=. move=> e2 m. case Heq: (n =? m)%num => //=.
      move=> Heq12. rewrite (IH1 _ Heq12). move/N.eqb_eq: Heq => ->. reflexivity.
  Qed.

  Fixpoint zpexpr_all0 l (ps : seq (PExpr Z)) : Prop :=
    match ps with
    | [::] => True
    | hd::tl => ZPEeval l hd = 0 /\ zpexpr_all0 l tl
    end.

  Lemma zpexpr_all0_cons l e es :
    zpexpr_all0 l (e::es) <-> ZPEeval l e = 0 /\ zpexpr_all0 l es.
  Proof. done. Qed.

  Lemma zpexpr_all0_rcons l es e :
    zpexpr_all0 l (rcons es e) <-> zpexpr_all0 l es /\ ZPEeval l e = 0.
  Proof.
    elim: es e => [| hd tl IH] //=.
    - move=> e. tauto.
    - move=> e. move: (IH e) => [H1 H2]. tauto.
  Qed.

  Lemma zpexpr_all0_cat l es1 es2 :
    zpexpr_all0 l (es1 ++ es2) <-> zpexpr_all0 l es1 /\ zpexpr_all0 l es2.
  Proof.
    elim: es1 es2 => [| e1 es1 IH] //=.
    - tauto.
    - move=> es2. move: (IH es2) => [H1 H2]. tauto.
  Qed.

  Lemma zpexpr_all0_rev l es : zpexpr_all0 l (rev es) <-> zpexpr_all0 l es.
  Proof.
    elim: es => [| e es IH] //=. rewrite rev_cons. rewrite zpexpr_all0_rcons. tauto.
  Qed.

  Lemma zpexpr_all0_in l ps p :
    zpexpr_all0 l ps -> List.In p ps -> ZPEeval l p = 0%Z.
  Proof.
    elim: ps => [| e es IH] //=. move=> [H1 H2] [] H.
    - rewrite -H. assumption.
    - exact: (IH H2 H).
  Qed.

  (* (\forall p \in ps, p = 0) -> q1 = q2 *)
  Definition zpimply_eq ps q1 q2 :=
    forall l : list Z,
      zpexpr_all0 l ps -> ZPEeval l q1 = ZPEeval l q2.

  Lemma ZPEeval0 l : ZPEeval l PEO = 0.
  Proof. reflexivity. Qed.

  Lemma ZPEeval1 l : ZPEeval l PEI = 1.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_const l c : ZPEeval l (PEc c) = c.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_add l e1 e2 : ZPEeval l (PEadd e1 e2) = ZPEeval l e1 + ZPEeval l e2.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_sub l e1 e2 : ZPEeval l (PEsub e1 e2) = ZPEeval l e1 - ZPEeval l e2.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_mul l e1 e2 : ZPEeval l (PEmul e1 e2) = ZPEeval l e1 * ZPEeval l e2.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_opp l e : ZPEeval l (PEopp e) = - ZPEeval l e.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_pow l e n : ZPEeval l (PEpow e n) = Z.pow (ZPEeval l e) (Z.of_N n).
  Proof. reflexivity. Qed.

  Definition peadds {A : Type} es : PExpr A := foldl (@PEadd A) PEO es.

  Definition pemuls {A : Type} (es1 es2 : seq (PExpr A)) :=
    mapr (fun '(x, y) => PEmul x y) (zipr es1 es2).

  Lemma peadds_rcons {A : Type} ms (m : PExpr A) :
    peadds (rcons ms m) = PEadd (peadds ms) m.
  Proof. rewrite /peadds. rewrite foldl_rcons. reflexivity. Qed.

  Lemma pemulss0 {A : Type} (xs : seq (PExpr A)) : pemuls xs nil = nil.
  Proof. by case: xs. Qed.

  Lemma pemuls0s {A : Type} (ys : seq (PExpr A)) : pemuls nil ys = nil.
  Proof. by case: ys. Qed.

  Lemma pemuls_cons {A : Type} (x : PExpr A) xs y ys :
    pemuls (x::xs) (y::ys) = (PEmul x y)::(pemuls xs ys).
  Proof. rewrite /pemuls. rewrite zipr_cons mapr_rcons. reflexivity. Qed.

  Lemma pemuls_rcons {A : Type} (xs : seq (PExpr A)) x ys y :
    size xs = size ys ->
    pemuls (rcons xs x) (rcons ys y) = rcons (pemuls xs ys) (PEmul x y).
  Proof.
    move=> Hs. rewrite /pemuls (zipr_rcons _ _ Hs). rewrite mapr_cons. reflexivity.
  Qed.

  Lemma pemuls_cat {A : Type} (xs1 : seq (PExpr A)) xs2 ys1 ys2 :
    size xs1 = size ys1 ->
    pemuls (xs1 ++ xs2) (ys1 ++ ys2) = (pemuls xs1 ys1) ++ (pemuls xs2 ys2).
  Proof.
    move=> Hs. rewrite /pemuls. rewrite (zipr_cat _ _ Hs). rewrite mapr_cat. reflexivity.
  Qed.

  Definition ZPEevals l (es : seq (PExpr Z)) := map (ZPEeval l) es.

  Lemma ZPEevals_cons l e es : ZPEevals l (e::es) = (ZPEeval l e)::(ZPEevals l es).
  Proof. done. Qed.

  Lemma ZPEevals_rcons l es e : ZPEevals l (rcons es e) = rcons (ZPEevals l es) (ZPEeval l e).
  Proof.
    elim: es e => [| hd tl IH] e //=. rewrite IH. reflexivity.
  Qed.

  Lemma ZPEevals_cat l es1 es2 : ZPEevals l (es1 ++ es2) = (ZPEevals l es1) ++ (ZPEevals l es2).
  Proof.
    elim: es1 es2 => [| e1 es1 IH1] es2 //=. rewrite IH1. reflexivity.
  Qed.

  Lemma ZPEeval_peadds l es : ZPEeval l (peadds es) = zadds (ZPEevals l es).
  Proof.
    move: es. apply: last_ind => [| es e IH] //=. rewrite ZPEevals_rcons.
    rewrite peadds_rcons zadds_rcons /=. rewrite IH. reflexivity.
  Qed.

  Lemma ZPEevals_pemuls l es1 es2 :
    ZPEevals l (pemuls es1 es2) = zmuls2 (ZPEevals l es1) (ZPEevals l es2).
  Proof.
    elim: es1 es2 => [| e1 es1 IH] [| e2 es2] //=.
    rewrite pemuls_cons /=. rewrite IH zmuls2_cons. reflexivity.
  Qed.

  Lemma ZPEeval_peadds_cons l e es :
    ZPEeval l (peadds (e::es)) = ZPEeval l e + ZPEeval l (peadds es).
  Proof.
    move: es e; apply: last_ind => [| es e IH] hd //=.
    - rewrite Z.add_0_r. reflexivity.
    - rewrite -rcons_cons. rewrite !peadds_rcons /=. rewrite IH. ring.
  Qed.

  Lemma ZPEeval_peadds_rcons l es e :
    ZPEeval l (peadds (rcons es e)) = ZPEeval l (peadds es) + ZPEeval l e .
  Proof. rewrite peadds_rcons /=. rewrite Z.add_comm. reflexivity. Qed.


  (* zpexpr_bounded: variables in a PExpr Z are bounded by some positive *)

  Fixpoint zpexpr_bounded (pe : PExpr Z) (g : positive) : Prop :=
    match pe with
   | PEO => true
   | PEI => true
   | PEc c => true
   | PEX j => (j < g)%positive
   | PEadd pe1 pe2
   | PEsub pe1 pe2
   | PEmul pe1 pe2 => zpexpr_bounded pe1 g /\ zpexpr_bounded pe2 g
   | PEopp pe1 => zpexpr_bounded pe1 g
   | PEpow pe1 n => zpexpr_bounded pe1 g
    end.

  Fixpoint zpexprs_bounded (pes : seq (PExpr Z)) (g : positive) : Prop :=
    match pes with
    | [::] => True
    | hd::tl => zpexpr_bounded hd g /\ zpexprs_bounded tl g
    end.

  Lemma zpexpr_bounded_ge_bounded g g' pe :
    (g <= g')%positive -> zpexpr_bounded pe g -> zpexpr_bounded pe g'.
  Proof.
    elim: pe g g' => //=.
    - move=> p g g' Hle Hlt. exact: (Pos.lt_le_trans _ _ _ Hlt Hle).
    - move=> e1 IH1 e2 IH2 g g' Hle [H1g H2g].
      split; [exact: (IH1 _ _ Hle H1g) | exact: (IH2 _ _ Hle H2g)].
    - move=> e1 IH1 e2 IH2 g g' Hle [H1g H2g].
      split; [exact: (IH1 _ _ Hle H1g) | exact: (IH2 _ _ Hle H2g)].
    - move=> e1 IH1 e2 IH2 g g' Hle [H1g H2g].
      split; [exact: (IH1 _ _ Hle H1g) | exact: (IH2 _ _ Hle H2g)].
  Qed.

  Lemma zpexprs_bounded_ge_bounded g g' pes :
    (g <= g')%positive -> zpexprs_bounded pes g -> zpexprs_bounded pes g'.
  Proof.
    elim: pes => [| pe pes IH] //= Hg [He Hes]. split.
    - exact: (zpexpr_bounded_ge_bounded Hg He).
    - exact: (IH Hg Hes).
  Qed.

  Lemma zpexprs_bounded_cons z zs g :
    zpexprs_bounded (z::zs) g <-> zpexpr_bounded z g /\ zpexprs_bounded zs g.
  Proof. reflexivity. Qed.

  Lemma zpexprs_bounded_rcons zs z g :
    zpexprs_bounded (rcons zs z) g <-> zpexprs_bounded zs g /\ zpexpr_bounded z g.
  Proof. elim: zs => [| hd tl IH] => //=; tauto. Qed.

  Lemma zpexprs_bounded_cat zs1 zs2 g :
    zpexprs_bounded (zs1 ++ zs2) g <-> zpexprs_bounded zs1 g /\ zpexprs_bounded zs2 g.
  Proof. elim: zs1 => [| z1 zs1 IH] > //=; tauto. Qed.

  Lemma zpexpr_bounded_peadds zs g :
    zpexpr_bounded (peadds zs) g <-> zpexprs_bounded zs g.
  Proof.
    move: zs. apply: last_ind => [| zs z IH] //=.
    rewrite peadds_rcons /=. rewrite zpexprs_bounded_rcons. tauto.
  Qed.

  Lemma zpexprs_bounded_pemuls xs ys g :
    zpexprs_bounded xs g -> zpexprs_bounded ys g -> zpexprs_bounded (pemuls xs ys) g.
  Proof.
    elim: xs ys => [| x xs IHx] [| y ys] //=. move: (IHx ys).
    rewrite pemuls_cons zpexprs_bounded_cons /=. tauto.
  Qed.

  (* Utilities *)

  Definition zpexpr_is_zero (e : PExpr Z) : bool :=
    match e with
    | PEO => true
    | PEc n => n == 0
    | _ => false
    end.

End ZPExpr.


(** ** Some lemmas for BinList, which is used in the evaluation of [PExpr] *)

Section BinList.

  Variable A : Type.
  Variable default : A.

  Local Notation snth := (seq.nth default).
  Local Notation bnth := (BinList.nth default).
  Local Notation bjump := (@BinList.jump A).

  Lemma bjump_nil (p : positive) : bjump p [::] = [::].
  Proof.
    elim: p => //=.
    - move=> p IH. rewrite 2!IH. reflexivity.
    - move=> p IH. rewrite 2!IH. reflexivity.
  Qed.

  Lemma bnth_nil (p : positive) : bnth p [::] = default.
  Proof.
    elim: p => //=.
    - move=> p IH. rewrite bjump_nil. exact: IH.
    - move=> p IH. rewrite bjump_nil. exact: IH.
  Qed.

  Lemma snth_bjump (p : positive) (n : nat) (l : list A) :
    snth (bjump p l) n = snth l (n + Pos.to_nat p).
  Proof.
    elim: p n l => /=.
    - move=> p IH n l. rewrite 2!IH. rewrite nth_tl. rewrite Pos2Nat.inj_xI.
      rewrite -Nat.double_twice. rewrite -(addnA n) -(addnA n) addn1. reflexivity.
    - move=> p IH n j. rewrite 2!IH. rewrite Pos2Nat.inj_xO -Nat.double_twice.
      rewrite -addnA. reflexivity.
    - move=> n l. exact: nth_tl.
  Qed.

  Lemma bnth_snth (p : positive) (l : list A) : bnth p l = snth l (Pos.to_nat p - 1).
  Proof.
    elim: p l => /=.
    - move=> p IH l. case: l => [| hd tl] /=.
      + rewrite bjump_nil bnth_nil nth_nil. reflexivity.
      + rewrite IH. rewrite snth_bjump. rewrite Pos2Nat.inj_xI.
        rewrite -(addn1 (2 * Pos.to_nat p)). rewrite -subnBA; last by done.
        rewrite subnn subn0. rewrite nth_cons;
                               last by (rewrite muln_gt0 (pos_to_nat_is_pos p)).
        rewrite (addnBAC _ (pos_to_nat_is_pos p)).
        rewrite muln_mul -Nat.double_twice. reflexivity.
    - move=> p IH l. rewrite IH. rewrite snth_bjump. rewrite Pos2Nat.inj_xO.
      rewrite (addnBAC _ (pos_to_nat_is_pos p)). rewrite -Nat.double_twice.
      reflexivity.
    - by case.
  Qed.

  Lemma bnth_rcons (g : positive) (l : list A) (x : A) :
    Pos.to_nat g <= size l -> bnth g (rcons l x) = bnth g l.
  Proof.
    move=> Hs. rewrite 2!bnth_snth. rewrite nth_rcons.
    case H: (Pos.to_nat g - 1 < size l); first by reflexivity. move/idP/negP: H.
    rewrite subn1. rewrite (ltn_predK (pos_to_nat_is_pos g)) Hs. discriminate.
  Qed.

  Lemma bnth_cat (g : positive) (l1 l2 : list A) :
    Pos.to_nat g <= size l1 -> bnth g (l1 ++ l2) = bnth g l1.
  Proof.
    move: l2 l1 g. apply: last_ind => [| l2 x2 IH] l1 g //=.
    - rewrite cats0. reflexivity.
    - move=> Hg. rewrite -rcons_cat. rewrite bnth_rcons.
      + exact: (IH _ _ Hg).
      + rewrite size_cat. apply: (leq_trans Hg). exact: leq_addr.
  Qed.

  Lemma bnth_rcons_last (g : positive) (l : list A) (x : A) :
    Pos.to_nat g = size l + 1 -> bnth g (rcons l x) = x.
  Proof.
    move=> Hs. rewrite bnth_snth. rewrite Hs. rewrite addn1 subn1 succnK.
    rewrite nth_rcons. rewrite (ltnn (size l)) (eqxx (size l)). reflexivity.
  Qed.

End BinList.
