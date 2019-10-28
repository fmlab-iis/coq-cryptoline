
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder ZAriths Store Tactics.
From BitBlasting Require Import State.
From Cryptoline Require Import DSL SSA ZSSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Convert zspec to polynomial equations *)

Section PSpec.

  (* Singleton zbexp *)

  Inductive szbexp : Type :=
  | Seq : ZSSA.zexp -> ZSSA.zexp -> szbexp
  | Seqmod : ZSSA.zexp -> ZSSA.zexp -> ZSSA.zexp -> szbexp.

  Definition szbexp_eqn (e1 e2 : szbexp) : bool :=
    match e1, e2 with
    | Seq e1 e2, Seq e3 e4 => (Eeq e1 e2) == (Eeq e3 e4)
    | Seqmod e1 e2 p1, Seqmod e3 e4 p2 => (Eeqmod e1 e2 p1) == (Eeqmod e3 e4 p2)
    | _, _ => false
    end.

  Lemma szbexp_eqn_eq (e1 e2 : szbexp) : szbexp_eqn e1 e2 -> e1 = e2.
  Proof.
    elim: e1 e2 => [e1 e2 | e1 e2 p1] [] //=.
    - by move=> ? ? /eqP [] -> ->.
    - by move=> ? ? ? /eqP [] -> -> ->.
  Qed.

  Lemma szbexp_eqn_refl (e : szbexp) : szbexp_eqn e e.
  Proof. by elim: e => /=. Qed.

  Lemma szbexp_eqn_sym {e1 e2 : szbexp} : szbexp_eqn e1 e2 -> szbexp_eqn e2 e1.
  Proof. move=> H; rewrite (szbexp_eqn_eq H); exact: szbexp_eqn_refl. Qed.

  Lemma szbexp_eqn_trans {e1 e2 e3 : szbexp} :
    szbexp_eqn e1 e2 -> szbexp_eqn e2 e3 -> szbexp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (szbexp_eqn_eq H1) (szbexp_eqn_eq H2).
    exact: szbexp_eqn_refl.
  Qed.

  Lemma szbexp_eqP (e1 e2 : szbexp) : reflect (e1 = e2) (szbexp_eqn e1 e2).
  Proof.
    case H: (szbexp_eqn e1 e2).
    - apply: ReflectT. exact: (szbexp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: szbexp_eqn_refl.
  Qed.

  Definition szbexp_eqMixin := EqMixin szbexp_eqP.
  Canonical szbexp_eqType := Eval hnf in EqType szbexp szbexp_eqMixin.

  Definition eval_szbexp (e : szbexp) (s : ZSSAStore.t) : Prop :=
    match e with
    | Seq e1 e2 => ZSSA.eval_zbexp (Eeq e1 e2) s
    | Seqmod e1 e2 p => ZSSA.eval_zbexp (Eeqmod e1 e2 p) s
    end.

  (* Algebraic specification as polynomial equations *)

  Record pspec : Type := mkPolySpec { ppremises : seq szbexp;
                                      pconseq : szbexp }.

  Definition valid_pspec (s : pspec) : Prop :=
    forall st : ZSSAStore.t,
      (forall e : szbexp, e \in (ppremises s) -> eval_szbexp e st) ->
      eval_szbexp (pconseq s) st.

  (* Convert zspec to pspec *)

  Fixpoint split_zbexp (e : ZSSA.zbexp) : seq szbexp :=
    match e with
    | Etrue => [::]
    | Eeq e1 e2 => [::Seq e1 e2]
    | Eeqmod e1 e2 p => [::Seqmod e1 e2 p]
    | Eand e1 e2 => split_zbexp e1 ++ split_zbexp e2
    end.

  Definition szbexp_zinstr (i : ZSSA.zinstr) : szbexp :=
    match i with
    | ZSSA.Zassign v e => Seq (evar v) e
    | ZSSA.Zsplit vh vl e p => Seq (eadd (evar vl)
                                         (emul (evar vh)
                                               (SSA.eexpn2 (Z.of_nat p))))
                                   e
    end.

  Definition szbexp_zprogram (p : ZSSA.zprogram) : seq szbexp :=
    map szbexp_zinstr p.

  Definition pspecs_of_zspec (s : ZSSA.zspec) : seq pspec :=
    let premises := split_zbexp (ZSSA.zspre s) ++ szbexp_zprogram (ZSSA.zsprog s) in
    let conseqs := split_zbexp (ZSSA.zspost s) in
    map (fun conseq => {| ppremises := premises; pconseq := conseq |}) conseqs.

End PSpec.



From Coq Require Import Ring_polynom.

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
Section ZRing.

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

  Fixpoint zpexpr_all0 l (ps : seq (PExpr Z)) : Prop :=
    match ps with
    | [::] => True
    | hd::tl => ZPEeval l hd = 0 /\ zpexpr_all0 l tl
    end.

  (* (\forall p \in ps, p = 0) -> q1 = q2 *)
  Definition zpimply_eq ps q1 q2 :=
    forall l : list Z,
      zpexpr_all0 l ps -> ZPEeval l q1 = ZPEeval l q2.

End ZRing.



(* Convert polynomial equations to polynomials *)

Section PExpr.

  Definition init_pos : positive := 1.

  Definition init_vm := SSAVM.empty positive.

  Definition zpexpr_of_var (g : positive) (t : SSAVM.t positive)  (v : ssavar) :
    positive * SSAVM.t positive * PExpr Z :=
    match SSAVM.find v t with
    | None => ((g + 1)%positive, SSAVM.add v g t, PEX Z g)
    | Some r => (g, t, PEX Z r)
    end.

  Definition zpexpr_of_eunop (op : eunop) : PExpr Z -> PExpr Z :=
    match op with
    | Eneg => @PEopp Z
    end.

  Definition zpexpr_of_ebinop (op : ebinop) : PExpr Z -> PExpr Z -> PExpr Z :=
    match op with
    | Eadd => @PEadd Z
    | Esub => @PEsub Z
    | Emul => @PEmul Z
    end.

  Fixpoint zpexpr_of_zexp (g : positive) (t : SSAVM.t positive) (e : ZSSA.zexp) :
    positive * SSAVM.t positive * PExpr Z :=
    match e with
    | Evar v => zpexpr_of_var g t v
    | Econst n => (g, t, PEc n)
    | Eunop op e =>
      let '(g', t', e') := zpexpr_of_zexp g t e in
      (g', t', zpexpr_of_eunop op e')
    | Ebinop op e1 e2 =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      (g2, t2, zpexpr_of_ebinop op e1 e2)
    end.

  Definition zpexpr_of_premise (g : positive) (t : SSAVM.t positive) (e : szbexp) :
    positive * SSAVM.t positive * PExpr Z :=
    match e with
    | Seq e1 e2 =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      (g2, t2, PEsub e1 e2)
    | Seqmod e1 e2 p =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      let '(gp, tp, p) := zpexpr_of_zexp g2 t2 p in
      ((gp + 1)%positive, t, PEsub (PEsub e1 e2) (PEmul (PEc (Zpos gp)) p))
    end.

  Fixpoint zpexprs_of_premises (g : positive) (t : SSAVM.t positive) (es : seq szbexp) :
    positive * SSAVM.t positive * seq (PExpr Z) :=
    match es with
    | [::] => (g, t, [::])
    | e::es => let '(g_hd, t_hd, es_hd) := zpexpr_of_premise g t e in
               let '(g_tl, t_tl, es_tl) := zpexprs_of_premises g_hd t_hd es in
               (g_tl, t_tl, es_hd::es_tl)
    end.

  Definition zpexpr_of_conseq (g : positive) (t : SSAVM.t positive) (e : szbexp) :
    positive * SSAVM.t positive * PExpr Z * PExpr Z :=
    match e with
    | Seq e1 e2 =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      (g2, t2, PEsub e1 e2, PEc 0%Z)
    | Seqmod e1 e2 p =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      let '(gp, tp, p) := zpexpr_of_zexp g2 t2 p in
      (gp, t, PEsub e1 e2, p)
    end.

  (* ps: polynomials that equal 0
     m: modulus
     the goal is to prove that q = cs * ps + c * m for some coefficients cs and c *)
  Definition zpexprs_of_pspec (s : pspec) : seq (PExpr Z) * PExpr Z * PExpr Z :=
    let g := init_pos in
    let t := init_vm in
    let '(g_p, t_p, ps) := zpexprs_of_premises g t (ppremises s) in
    let '(g_q, t_q, q, m) := zpexpr_of_conseq g_p t_p (pconseq s) in
    (ps, m, q).

  (* find cs and c *)
  Variable find_coefficients : seq (PExpr Z) -> PExpr Z -> PExpr Z -> seq Z * Z.

  Definition combine_coefficients (cs : seq Z) (ps : seq (PExpr Z)) : seq (PExpr Z) :=
    map (fun '(c, p) => PEmul (PEc c) p) (zip cs ps).

  Fixpoint sum_polys (ps : seq (PExpr Z)) : PExpr Z :=
    match ps with
    | [::] => PEc 0%Z
    | hd::tl => PEadd hd (sum_polys tl)
    end.

  (* Two polynomials are semantically equal *)
  Definition zpexpr_eqb (p1 p2 : PExpr Z) : bool :=
    ZPeq (Znorm_subst p1) (Znorm_subst p2).

  (* Check if q = cs * ps + c * m *)
  Definition coefficients_checker ps m q cs c : bool :=
    (size ps == size cs) &&
    zpexpr_eqb q (PEadd (sum_polys (combine_coefficients cs ps)) (PEmul (PEc c) m)).

  (* If q = cs * ps + c * m and for each p \in ps, p = 0, then q = c * m *)
  Lemma checker_imply_eq ps m q cs c :
    coefficients_checker ps m q cs c ->
    zpimply_eq ps q (PEmul (PEc c) m).
  Proof.
    move/andP=> [Hs Heq] l Heq0. rewrite /ZPEeval.
    (* Convert the syntactical equality in the hypotheses to semantic equality *)
    rewrite /zpexpr_eqb /ZPeq in Heq. move: (ZPeq_ok Heq) => {Heq} Heq.
    move: (Heq l) => {Heq} Heq.
    (* Convert Pol evaluation to PExpr evaluation *)
    move: Heq. rewrite -Znorm_subst_spec; try done.
    rewrite -Znorm_subst_spec; try done.
    (* rewrite q = cs * ps + c * m *)
    move=> ->.
    (* Induction on ps *)
    rewrite /=. case: ps cs Hs Heq0 => [| hd tl] //=.
    - (* ps = [::] *) by case.
    - (* ps = hd::tl *) case=> //=. move=> cs_hd. (* cs = cs_hd::cs_tl *)
      elim: tl => [| tl_hd tl_tl IH] //=.
      + (* ps = [:: hd] *) case=> //=. (* cs = cs_hd *) rewrite /ZPEeval.
        move=> _ [-> _]. rewrite Z.mul_0_r !Z.add_0_l. reflexivity.
      + (* ps = hd::tl_hd::tl_tl *) case => //=. (* cs = cs_hd::cs_tl_hd::cs_tl_tl *)
        move=> cs_tl_hd cs_tl_tl. rewrite /ZPEeval=> Hsize [Hhd [Htl_hd Htl_tl]].
        rewrite Hhd in IH *. rewrite Htl_hd !Z.mul_0_r !Z.add_0_l.
        rewrite Z.mul_0_r in IH. rewrite -{2}(IH cs_tl_tl).
        * rewrite !Z.add_0_l. reflexivity.
        * rewrite -addn2 -(addn2 (size cs_tl_tl)) eqn_add2r in Hsize.
            by rewrite (eqP Hsize).
        * split; [exact: Hhd | exact: Htl_tl].
  Qed.

  Lemma zimply_eq_valid_pspec g t g' t' s ps q m c :
    zpexprs_of_premises init_pos init_vm (ppremises s) = (g, t, ps) ->
    zpexpr_of_conseq g t (pconseq s) = (g', t', q, m) ->
    zpimply_eq ps q (PEmul (PEc c) m) ->
    valid_pspec s.
  Proof.
  Admitted.

  (* If the coefficients are verified by the checker, the pspec is valid *)
  Theorem checker_valid_pspec s ps m q cs c :
    zpexprs_of_pspec s = (ps, m, q) ->
    coefficients_checker ps m q cs c ->
    valid_pspec s.
  Proof.
    rewrite /zpexprs_of_pspec.
    dcase (zpexprs_of_premises init_pos init_vm (ppremises s)).
    move=> [[g_p t_p] ps']. dcase (zpexpr_of_conseq g_p t_p (pconseq s)).
    move=> [[[g_q t_q] g'] m'] /=. move=> Hconseq Hpremises [] ? ? ?. subst.
    move=> Hch. move: (checker_imply_eq Hch) => Himply.
    exact: (zimply_eq_valid_pspec Hpremises Hconseq Himply).
  Qed.

End PExpr.
