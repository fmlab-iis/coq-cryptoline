
(** Range reduction.
    Convert a range specification in SSA and algebraic soundness conditions
    to SMT QF_BV queries. *)

From Coq Require Import Arith List OrderedType.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun prime.
From ssrlib Require Import Var Tactics Seqs.
From Cryptoline Require Import DSL SSA SSA2ZSSA.
From BitBlasting Require Import State QFBV TypEnv.
From nbits Require Import NBits.

Import QFBV SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section ForceConformDiff.

  Definition force_conform_diff (E : SSATE.env) (vs : SSAVS.t) (s : SSAStore.t) :=
    force_conform_vars E (SSAVS.elements (SSAVS.diff (vars_env E) vs)) s.

  Lemma force_conform_diff_notin E vs s v :
    SSATE.mem v E -> ~~ SSAVS.mem v vs ->
    SSAStore.acc v (force_conform_diff E vs s) = zeros (SSATE.vsize v E).
  Proof.
    move=> Hin Hnotin. rewrite /force_conform_diff.
    rewrite force_conform_vars_in; first reflexivity.
    apply: SSAVS.Lemmas.mem_in_elements. rewrite SSAVS.Lemmas.diff_b.
    by rewrite mem_vars_env Hin Hnotin.
  Qed.

  Lemma force_conform_diff_in E vs s v :
    SSAVS.mem v vs -> SSAStore.acc v (force_conform_diff E vs s) = SSAStore.acc v s.
  Proof.
    move=> Hmem. rewrite /force_conform_diff.
    rewrite force_conform_vars_notin; first reflexivity.
    apply/negP => Hin. move: (SSAVS.Lemmas.in_elements_mem Hin).
    rewrite SSAVS.Lemmas.diff_b. rewrite Hmem andbF. discriminate.
  Qed.

  Lemma agree_force_conform_notin_valid_bexp E1 E2 vs s :
    MA.agree vs E1 E2 -> SSAStore.conform s E1 ->
    SSAStore.conform (force_conform_diff E2 vs s) E2.
  Proof.
    move=> Hag Hco x Hmemx. case Hmemxvs: (SSAVS.mem x vs).
    - rewrite (force_conform_diff_in _ _ Hmemxvs). move: (Hag _ Hmemxvs) => Hfind.
      rewrite -(SSA.TELemmas.find_same_vsize Hfind). rewrite Hco; first reflexivity.
      rewrite SSATE.Lemmas.mem_find_b Hfind. by move: (SSATE.Lemmas.mem_find_some Hmemx) => [y ->].
    - move/idP/negP: Hmemxvs => Hmemxvs. rewrite (force_conform_diff_notin _ Hmemx Hmemxvs).
      rewrite size_zeros. reflexivity.
  Qed.

  Lemma force_conform_diff_eval_exp vs E e s :
    SSAVS.subset (QFBV.vars_exp e) vs ->
    QFBV.eval_exp e (force_conform_diff E vs s) = QFBV.eval_exp e s
  with force_conform_diff_eval_bexp vs E e s :
    SSAVS.subset (QFBV.vars_bexp e) vs ->
    QFBV.eval_bexp e (force_conform_diff E vs s) = QFBV.eval_bexp e s.
  Proof.
    (* force_conform_diff_eval_exp *)
    - case: e => //=.
      + move=> x Hsub. rewrite force_conform_diff_in; first reflexivity.
        exact: (SSAVS.Lemmas.subset_singleton1 Hsub).
      + move=> op e Hsub. rewrite (force_conform_diff_eval_exp _ _ _ _ Hsub). reflexivity.
      + move=> op e1 e2. rewrite SSAVS.Lemmas.subset_union6.
        move/andP=> [Hsub1 Hsub2]. rewrite (force_conform_diff_eval_exp _ _ _ _ Hsub1)
                                     (force_conform_diff_eval_exp _ _ _ _ Hsub2). reflexivity.
      + move=> b e1 e2. rewrite !SSAVS.Lemmas.subset_union6.
        move/andP=> [Hsubb /andP [Hsub1 Hsub2]].
        rewrite (force_conform_diff_eval_bexp _ _ _ _ Hsubb)
          (force_conform_diff_eval_exp _ _ _ _ Hsub1)
          (force_conform_diff_eval_exp _ _ _ _ Hsub2). reflexivity.
    (* force_conform_diff_eval_bexp *)
    - case: e => //=.
      + move=> op e1 e2. rewrite SSAVS.Lemmas.subset_union6. move/andP=> [Hsub1 Hsub2].
        rewrite (force_conform_diff_eval_exp _ _ _ _ Hsub1)
          (force_conform_diff_eval_exp _ _ _ _ Hsub2). reflexivity.
      + move=> e Hsub. rewrite (force_conform_diff_eval_bexp _ _ _ _ Hsub). reflexivity.
      + move=> e1 e2. rewrite SSAVS.Lemmas.subset_union6. move/andP=> [Hsub1 Hsub2].
        rewrite (force_conform_diff_eval_bexp _ _ _ _ Hsub1)
          (force_conform_diff_eval_bexp _ _ _ _ Hsub2). reflexivity.
      + move=> e1 e2. rewrite SSAVS.Lemmas.subset_union6. move/andP=> [Hsub1 Hsub2].
        rewrite (force_conform_diff_eval_bexp _ _ _ _ Hsub1)
          (force_conform_diff_eval_bexp _ _ _ _ Hsub2). reflexivity.
  Qed.

End ForceConformDiff.

Lemma agree_valid_bexp E1 E2 e :
  MA.agree (QFBV.vars_bexp e) E1 E2 ->
  valid_bexp E1 e <-> valid_bexp E2 e.
Proof.
  move=> Hag; split.
  - move=> Hv s Hco. move: (MA.agree_sym Hag) => {}Hag.
    move: (Hv (force_conform_diff E1 (QFBV.vars_bexp e) s)
             (agree_force_conform_notin_valid_bexp Hag Hco)).
    rewrite (force_conform_diff_eval_bexp _ _ (SSAVS.Lemmas.subset_refl _)). by apply.
  - move=> Hv s Hco. move: (Hv (force_conform_diff E2 (QFBV.vars_bexp e) s)
                              (agree_force_conform_notin_valid_bexp Hag Hco)).
    rewrite (force_conform_diff_eval_bexp _ _ (SSAVS.Lemmas.subset_refl _)). by apply.
Qed.

Lemma agree_valid_bexps E1 E2 es :
  MA.agree (QFBV.vars_bexps es) E1 E2 ->
  valid_bexps E1 es <-> valid_bexps E2 es.
Proof.
  elim: es => [| e es IH] //=. move/MA.agree_union_set => [Hag1 Hag2].
  rewrite !valid_bexps_cons. rewrite (agree_valid_bexp Hag1) (IH Hag2). tauto.
Qed.

Lemma agree_exp_size E1 E2 e :
  MA.agree (QFBV.vars_exp e) E1 E2 ->
  exp_size e E1 = exp_size e E2.
Proof.
  elim: e => //=.
  - move=> x H. apply: SSA.TELemmas.find_same_vsize. apply: (H x).
    apply: SSAVS.Lemmas.mem_singleton2. reflexivity.
  - move=> op e IH Hag. rewrite (IH Hag). reflexivity.
  - move=> op e1 IH1 e2 IH2 /MA.agree_union_set [Hag1 Hag2].
    rewrite (IH1 Hag1) (IH2 Hag2). reflexivity.
  - move=> b e1 IH1 e2 IH2 /MA.agree_union_set [Hagb /MA.agree_union_set [Hag1 Hag2]].
    rewrite (IH1 Hag1) (IH2 Hag2). reflexivity.
Qed.

Lemma agree_well_formed_eexp E1 E2 e :
  MA.agree (QFBV.vars_exp e) E1 E2 ->
  well_formed_exp e E1 = well_formed_exp e E2
with agree_well_formed_bexp E1 E2 e :
  MA.agree (QFBV.vars_bexp e) E1 E2 ->
  QFBV.well_formed_bexp e E1 = QFBV.well_formed_bexp e E2.
Proof.
  (* agree_well_formed_eexp *)
  - case: e => //=.
    + move=> x Hag. rewrite !SSATE.Lemmas.mem_find_b.
      rewrite (Hag x); first reflexivity. apply: SSAVS.Lemmas.mem_singleton2. reflexivity.
    + move=> _ e Hag. rewrite (agree_well_formed_eexp _ _ _ Hag). reflexivity.
    + move=> op e1 e2 /MA.agree_union_set [Hag1 Hag2].
      rewrite (agree_well_formed_eexp _ _ _ Hag1) (agree_well_formed_eexp _ _ _ Hag2).
      rewrite (agree_exp_size Hag1) (agree_exp_size Hag2). reflexivity.
    + move=> b e1 e2 /MA.agree_union_set [Hagb /MA.agree_union_set [Hag1 Hag2]].
      rewrite (agree_well_formed_bexp _ _ _ Hagb)
        (agree_well_formed_eexp _ _ _ Hag1) (agree_well_formed_eexp _ _ _ Hag2).
      rewrite (agree_exp_size Hag1) (agree_exp_size Hag2). reflexivity.
  (* agree_well_formed_bexp *)
  - case: e => //=.
    + move=> _ e1 e2 /MA.agree_union_set [Hag1 Hag2].
      rewrite (agree_well_formed_eexp _ _ _ Hag1) (agree_well_formed_eexp _ _ _ Hag2).
      rewrite (agree_exp_size Hag1) (agree_exp_size Hag2). reflexivity.
    + move=> e Hag. rewrite (agree_well_formed_bexp _ _ _ Hag). reflexivity.
    + move=> e1 e2 /MA.agree_union_set [Hag1 Hag2].
      rewrite (agree_well_formed_bexp _ _ _ Hag1) (agree_well_formed_bexp _ _ _ Hag2).
      reflexivity.
    + move=> e1 e2 /MA.agree_union_set [Hag1 Hag2].
      rewrite (agree_well_formed_bexp _ _ _ Hag1) (agree_well_formed_bexp _ _ _ Hag2).
      reflexivity.
Qed.

Lemma agree_well_formed_bexps E1 E2 es :
  MA.agree (QFBV.vars_bexps es) E1 E2 ->
  QFBV.well_formed_bexps es E1 = QFBV.well_formed_bexps es E2.
Proof.
  elim: es => [| e es IH] //=. move/MA.agree_union_set => [Hag1 Hag2].
  rewrite (agree_well_formed_bexp Hag1) (IH Hag2). reflexivity.
Qed.


(** Auxiliary lemmas *)

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
  by rewrite /addB to_nat_adcB' size_from_nat.
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

Lemma size_exp_const E w n : QFBV.exp_size (QFBV.Econst (NBitsDef.from_nat w n)) E = w.
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


(** Some tactics used across sections *)

Ltac to_asize :=
  repeat
    match goal with
    | Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
        Hco : SSAStore.conform ?s ?E,
          Hsm : is_true (size_matched_atom ?a) |-
        context f [size (eval_atom ?a ?s)] =>
        rewrite (size_eval_atom_asize Hsub Hco Hsm)
    | Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
        Hco : SSAStore.conform ?s ?E,
          Hsm : is_true (size_matched_atom ?a),
            H : context f [size (eval_atom ?a ?s)] |- _ =>
        rewrite (size_eval_atom_asize Hsub Hco Hsm) in H
    end.

Ltac of_asize :=
  repeat
    match goal with
    | Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
        Hco : SSAStore.conform ?s ?E,
          Hsm : is_true (size_matched_atom ?a) |-
        context f [asize ?a ?E] =>
        rewrite -(size_eval_atom_asize Hsub Hco Hsm)
    | Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
        Hco : SSAStore.conform ?s ?E,
          Hsm : is_true (size_matched_atom ?a),
            H : context f [asize ?a ?E] |- _ =>
        rewrite -(size_eval_atom_asize Hsub Hco Hsm) in H
    end.

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
    | H : is_true (well_typed_atom _ _) |- _ =>
        let H1 := fresh "Hwta" in
        let H2 := fresh "Hwtqa" in
        move/andP: H => /= [H1 H2]
    | H : is_true (_ && _) |- _ =>
        let H1 := fresh "Hwf" in
        let H2 := fresh "Hwf" in
        move/andP: H => [H1 H2]
    end.

Ltac intro_subset_from_are_defined :=
  match goal with
  | H : is_true (are_defined _ _) |- _ =>
      let Hsub := fresh "Hsub" in
      move: (H) => /defsubP Hsub; move: H; intro_subset_from_are_defined
  | |- _ => intros
  end.


Section Rspec2QFBV.

  (** A bexp_spec is a specification in terms of QF_BV predicates *)

  Record bexp_spec : Type :=
    { binputs : SSATE.env;
      bpre : QFBV.bexp;
      bprog : seq QFBV.bexp;
      bpost : QFBV.bexp }.

  Definition valid_bexp_spec (s : bexp_spec) : Prop :=
    forall st : SSAStore.t,
      SSAStore.conform st (binputs s) ->
      QFBV.eval_bexp (bpre s) st ->
      QFBV.eval_bexps (bprog s) st ->
      QFBV.eval_bexp (bpost s) st.

  Definition vars_bexp_spec s : SSAVS.t :=
    SSAVS.union
      (QFBV.vars_bexp (bpre s))
      (SSAVS.union
         (QFBV.vars_bexps (bprog s))
         (QFBV.vars_bexp (bpost s))).


  (** Relations between bvs_eqi and QFBV.eval_exp and between bvs_eqi and
    QFBV.eval_bexp *)

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


  (** Conversion from rbexp to QFBV.bexp *)

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
    | Rtrue => qfbv_true
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


  (** Properties about the conversion from rbexp to QFBV.bexp *)

  Lemma eval_exp_var v s :
    QFBV.eval_exp (qfbv_var v) s = SSAStore.acc v s.
  Proof.
    reflexivity.
  Qed.

  Lemma eval_exp_const s w n :
    QFBV.eval_exp (qfbv_const w n) s = from_nat w n.
  Proof. reflexivity. Qed.

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
    - move => e H. by iffb_tac.
    - move => e0 IH0 e1 IH1. by iffb_tac.
    - move => e0 IH0 e1 IH1. by iffb_tac.
  Qed.


  (** Conversion from programs to QFBV.bexp *)

  Definition qfbv_atom a :=
    match a with
    | SSA.Avar v => QFBV.Evar v
    | SSA.Aconst ty n => QFBV.Econst n
    end.

  Definition bexp_instr (E : SSATE.env) (i : SSA.instr) : QFBV.bexp :=
    match i with
    (* Inondet (v, t): v = a nondeterministic value of type t *)
    | SSA.Inondet _ _
    (* Inop: do nothing *)
    | SSA.Inop => QFBV.Btrue
    (* Imov (v, a): v = a *)
    | SSA.Imov v a =>
        qfbv_eq (qfbv_var v) (qfbv_atom a)
    (* Icmov (v, c, a1, a2): if c then v = a1 else v = a2 *)
    | SSA.Icmov v c a1 a2 =>
        let 'qec := qfbv_eq (qfbv_const 1 1) (qfbv_atom c) in
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
        qfbv_eq (qfbv_var v) (QFBV.Eite qec qe1 qe2)
    (* Iadd (v, a1, a2): v = a1 + a2, overflow is forbidden *)
    | SSA.Iadd v a1 a2 =>
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
        qfbv_eq (qfbv_var v) (qfbv_add qe1 qe2)
    (* Iadds (c, v, a1, a2): v = a1 + a2, c = carry flag *)
    | SSA.Iadds c v a1 a2 =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2ext := qfbv_zext 1 (qfbv_atom a2) in
        let 'qerext := qfbv_add qe1ext qe2ext in
        qfbv_conj
          (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
          (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
    (* Iadc (v, a1, a2, y): v = a1 + a2 + y, overflow is forbidden *)
    | SSA.Iadc v a1 a2 y =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2ext := qfbv_zext 1 (qfbv_atom a2) in
        let 'qeyext := qfbv_zext a_size (qfbv_atom y) in
        qfbv_eq (qfbv_var v)
          (qfbv_low a_size (qfbv_add (qfbv_add qe1ext qe2ext) qeyext))
    (* Iadcs (c, v, a1, a2, y): v = a1 + a2 + y, c = carry flag *)
    | SSA.Iadcs c v a1 a2 y =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2ext := qfbv_zext 1 (qfbv_atom a2) in
        let 'qeyext := qfbv_zext a_size (qfbv_atom y) in
        let 'qerext := qfbv_add (qfbv_add qe1ext qe2ext) qeyext in
        qfbv_conj (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
          (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
    (* Isub (v, a1, a2): v = a1 - a2, overflow is forbidden *)
    | SSA.Isub v a1 a2 =>
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
        qfbv_eq (qfbv_var v) (qfbv_sub qe1 qe2)
    (* Isubb (b, v, a1, a2): v = a1 - a2, b = borrow flag *)
    | SSA.Isubb b v a1 a2 =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2ext := qfbv_zext 1 (qfbv_atom a2) in
        let 'qerext := qfbv_sub qe1ext qe2ext in
        qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
          (qfbv_eq (qfbv_var v)
             (qfbv_low a_size qerext))
    (* Isubc (c, v, a1, a2): v = a1 + not(a2) + 1, c = carry flag *)
    | SSA.Isubc c v a1 a2 =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2notext := qfbv_zext 1 (qfbv_not (qfbv_atom a2)) in
        let 'qe1 := qfbv_zext a_size (qfbv_const 1 1) in
        let 'qerext := qfbv_add (qfbv_add qe1ext qe2notext) qe1 in
        qfbv_conj (qfbv_eq (qfbv_var c)
                     (qfbv_high 1 qerext))
          (qfbv_eq (qfbv_var v)
             (qfbv_low a_size qerext))
    (* Isbb (v, a1, a2, y): v = a1 - a2 - y *)
    | SSA.Isbb v a1 a2 y =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2ext := qfbv_zext 1 (qfbv_atom a2) in
        let 'qeyext := qfbv_zext a_size (qfbv_atom y) in
        qfbv_eq (qfbv_var v)
          (qfbv_low a_size (qfbv_sub (qfbv_sub qe1ext qe2ext) qeyext))
    (* Isbbs (b, v, a1, a2, y): v = a1 - a2 - y, b = borrow flag *)
    | SSA.Isbbs b v a1 a2 y =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2ext := qfbv_zext 1 (qfbv_atom a2) in
        let 'qeyext := qfbv_zext a_size (qfbv_atom y) in
        let 'qerext := qfbv_sub (qfbv_sub qe1ext qe2ext) qeyext in
        qfbv_conj (qfbv_eq (qfbv_var b) (qfbv_high 1 qerext))
          (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
    (* Isbc (v, a1, a2, y): v = a1 + not(a2) + y *)
    | SSA.Isbc v a1 a2 y =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2notext := qfbv_zext 1 (qfbv_not (qfbv_atom a2)) in
        let 'qeyext := qfbv_zext a_size (qfbv_atom y) in
        qfbv_eq (qfbv_var v)
          (qfbv_low a_size (qfbv_add (qfbv_add qe1ext qe2notext) qeyext))
    (* Isbcs (c, v, a1, a2, y): v = a1 + not(a2) + y, c = carry flag *)
    | SSA.Isbcs c v a1 a2 y =>
        let 'a_size := asize a1 E in
        let 'qe1ext := qfbv_zext 1 (qfbv_atom a1) in
        let 'qe2notext := qfbv_zext 1 (qfbv_not (qfbv_atom a2)) in
        let 'qeyext := qfbv_zext a_size (qfbv_atom y) in
        let 'qerext := qfbv_add (qfbv_add qe1ext qe2notext) qeyext in
        qfbv_conj (qfbv_eq (qfbv_var c) (qfbv_high 1 qerext))
          (qfbv_eq (qfbv_var v) (qfbv_low a_size qerext))
    (* Imul (v, a1, a2): v = a1 * a2, overflow is forbidden *)
    | SSA.Imul v a1 a2 =>
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
        qfbv_eq (qfbv_var v) (qfbv_mul qe1 qe2)
    (* Imull (vh, vl, a1, a2): vh and vl are respectively the high part and
     the low part of the full multiplication a1 * a2 *)
    | SSA.Imull vh vl a1 a2 =>
        let 'a1_size := asize a1 E in
        let 'a2_size := asize a2 E in
        let 'qe1ext :=
          if Typ.is_unsigned (atyp a1 E) then qfbv_zext a1_size (qfbv_atom a1)
          else qfbv_sext a1_size (qfbv_atom a1) in
        let 'qe2ext :=
          if Typ.is_unsigned (atyp a1 E) then qfbv_zext a1_size (qfbv_atom a2)
          else qfbv_sext a1_size (qfbv_atom a2) in
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
          if Typ.is_unsigned (atyp a1 E) then qfbv_zext a_size (qfbv_atom a1)
          else qfbv_sext a_size (qfbv_atom a1) in
        let 'qe2ext :=
          if Typ.is_unsigned (atyp a1 E) then qfbv_zext a_size (qfbv_atom a2)
          else qfbv_sext a_size (qfbv_atom a2) in
        let 'qerext := qfbv_mul qe1ext qe2ext in
        qfbv_eq (qfbv_var v) qerext
    (* Ishl (v, a, n): v = a * 2^n, overflow is forbidden *)
    (* need a better size for NBitsDef.from_nat *)
    | SSA.Ishl v a n =>
        let a_size := asize a E in
        let 'qea := qfbv_atom a in
        let 'qen := qfbv_const a_size n in
        qfbv_eq (qfbv_var v) (qfbv_shl qea qen)
    (* Ijoin (v, ah, al): v = ah * 2^w + al where w is the bit-width of al *)
    | SSA.Ijoin v ah al =>
        let 'qeh := qfbv_atom ah in
        let 'qel := qfbv_atom al in
        qfbv_eq (qfbv_var v) (qfbv_concat qeh qel)
    (* Isplit (vh, vl, a, n): vh is the high (w - n) bits (signed extended to w bits)
     of a and vl is the low n bits (zero extended to w bits) of a where w is the
     bit-width of a *)
    | SSA.Isplit vh vl a n =>
        let 'a_size := asize a E in
        let 'qen := qfbv_const a_size n in
        let 'qeamn := qfbv_const a_size (a_size - n) in
        let 'qea := qfbv_atom a in
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
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
        let 'qer := qfbv_shl (qfbv_concat qe1 qe2) (qfbv_const (a1_size + a2_size) n) in
        let 'qel := qfbv_low a2_size qer in
        let 'qeh := qfbv_high a1_size qer in
        qfbv_conj (qfbv_eq (qfbv_var vh) qeh)
          (qfbv_eq (qfbv_var vl) (qfbv_lshr qel (qfbv_const a2_size n)))
    (* Inot (v, t, a): v = not(a), the one's complement of a, v is of type t *)
    | SSA.Inot v t a =>
        let 'qea := qfbv_atom a in
        qfbv_eq (qfbv_var v) (qfbv_not qea)
    (* Iand (v, t, a1, a2): v = the bitwise AND of a1 and a2, v is of type t *)
    | SSA.Iand v t a1 a2 =>
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
        let 'qer := qfbv_and qe1 qe2 in
        qfbv_eq (qfbv_var v) qer
    (* Ior (v, t, a1, a2): v = the bitwise OR of a1 and a2, v is of type t *)
    | SSA.Ior v t a1 a2 =>
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
        let 'qer := qfbv_or qe1 qe2 in
        qfbv_eq (qfbv_var v) qer
    (* Ixor (v, t, a1, a2): v = the bitwise XOR of a1 and a2, v is of type t *)
    | SSA.Ixor v t a1 a2 =>
        let 'qe1 := qfbv_atom a1 in
        let 'qe2 := qfbv_atom a2 in
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
        let 'qea := qfbv_atom a in
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


  Global Instance add_proper_bexp_instr : Proper (SSATE.Equal ==> eq ==> eq) bexp_instr.
  Proof.
    move=> E1 E2 Heq i1 i2 ?; subst.
    (case: i2 => //=); intros; case_if; subst; simpl;
    repeat match goal with
      | Heq : SSATE.Equal ?E1 ?E2 |- context c [asize _ ?E1] => rewrite Heq
      | Heq : SSATE.Equal ?E1 ?E2 |- context c [atyp _ ?E1] => rewrite Heq
      | Heq : SSATE.Equal ?E1 ?E2, H : context c [asize _ ?E1] |- _ => rewrite Heq in H
      | Heq : SSATE.Equal ?E1 ?E2, H : context c [atyp _ ?E1] |- _ => rewrite Heq in H
      | H1 : ?e = true, H2 : ?e = false |- _ => rewrite H1 in H2; discriminate
      end;
    by reflexivity.
  Qed.

  Global Instance add_proper_bexp_program : Proper (SSATE.Equal ==> eq ==> eq) bexp_program.
  Proof.
    move=> E1 E2 Heq p1 p2 ?; subst. elim: p2 E1 E2 Heq => [| i p IH] E1 E2 Heq //=.
    apply/eqP. rewrite eqseq_cons. apply/andP; split.
    - rewrite Heq. exact: eqxx.
    - apply/eqP. apply: IH. rewrite Heq. reflexivity.
  Qed.


  (** Properties of the conversion from programs to QFBV.bexp *)

  Lemma size_exp_atom E a :
    are_defined (vars_atom a) E -> size_matched_atom a ->
    QFBV.exp_size (qfbv_atom a) E = asize a E.
  Proof.
    case: a => //=. move=> t bs _ Hs. rewrite (eqP Hs). reflexivity.
  Qed.

  Lemma size_exp_rexp E e :
    well_formed_rexp E e ->
    QFBV.exp_size (exp_rexp e) E = size_of_rexp e E.
  Proof.
    elim: e => //=.
    - move=> n bs /andP /= [Hdef [/andP [Hw Hs]]]. apply/eqP. exact: Hs.
    - move=> w op e IH Hwf. move: (well_formed_rexp_unop Hwf) => {Hwf} [Hwfe [Hw Hse]].
      move: (IH Hwfe) => {IH} IH. case: op => /=; rewrite IH; exact: Hse.
    - move=> w op e1 IH1 e2 IH2 Hwf.
      move: (well_formed_rexp_binop Hwf) => {Hwf} [Hwf1 [Hwf2 [Hw [Hs1 Hs2]]]].
      move: (IH1 Hwf1) (IH2 Hwf2) => {IH1 IH2} IH1 IH2.
      case: op => /=; rewrite ?IH1 ?IH2 ?Hs1 ?Hs2 ?minnn ?maxnn; reflexivity.
    - move=> w e IH n Hwf. move: (well_formed_rexp_uext Hwf) => {Hwf} [Hwfe [Hw Hse]].
      move: (IH Hwfe) => {IH} IH. rewrite IH Hse. reflexivity.
    - move=> w e IH n Hwf. move: (well_formed_rexp_sext Hwf) => {Hwf} [Hwfe [Hw Hse]].
      move: (IH Hwfe) => {IH} IH. rewrite IH Hse. reflexivity.
  Qed.

  Lemma eval_exp_atom a s :
    QFBV.eval_exp (qfbv_atom a) s = eval_atom a s.
  Proof.
    case: a => /=; reflexivity.
  Qed.

  Lemma vars_exp_atom a :
    QFBV.vars_exp (qfbv_atom a) = vars_atom a.
  Proof. by case: a. Qed.

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

  Lemma vars_bexp_instr E i : SSAVS.subset (QFBV.vars_bexp (bexp_instr E i)) (vars_instr i).
  Proof.
    (case: i => //=); intros; case_if; case_option; subst; simpl;
    repeat match goal with
      | |- context c [QFBV.vars_exp (qfbv_atom _)] => rewrite vars_exp_atom
      end; try SSAVS.Lemmas.dp_subset.
    case: b => [e r] /=. rewrite /vars_bexp vars_bexp_rbexp /=.
    by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma vars_bexp_program E p : SSAVS.subset (QFBV.vars_bexps (bexp_program E p)) (vars_program p).
  Proof.
    elim: p E => [| i p IH] E //=. move: (vars_bexp_instr E i) => Hsubi.
    move: (IH (instr_succ_typenv i E)) => Hsubp. by SSAVS.Lemmas.dp_subset.
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
    | |- context f [QFBV.vars_exp (qfbv_atom _)] =>
        rewrite vars_exp_atom; are_defined_dec
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
    | b : SSA.bexp, H : is_true (are_defined (SSA.vars_bexp ?b) _)
      |- context f [let (_, _) := ?b in _] =>
        case: b H => eb rb H
    end.
    rewrite vars_bexp_rbexp. move: (vars_rbexp_subset (eb, rb)) => /= Hsub.
    apply: (are_defined_subset Hsub). assumption.
  Qed.

  Ltac rewrite_eval_exp_atom :=
    repeat rewrite -> eval_exp_atom in *.

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
                H2 : is_true (are_defined (vars_atom ?a) ?E1) |-
                context f [asize ?a ?E2] =>
                rewrite -(asize_submap H1 H2)
            | H1 : TELemmas.submap ?E1 ?E2,
                H2 : is_true (are_defined (vars_atom ?a) ?E1) |-
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
    case : i => /=; intros; rewrite_eval_exp_atom;
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
                       H2 : is_true (ssa_vars_unchanged_program (vars_atom ?a) ?p) |-
                       context f [eval_atom ?a ?s2] =>
                       (* convert (eval_atom a s2) to (eval_atom a s1) *)
                       rewrite -(ssa_unchanged_program_eval_atom H2 H1); tac
                   | _ => by assumption
                   end in tac || idtac).
    - (* mull *)
      move : H1; (case (Typ.is_unsigned (atyp a E)) => /=);
        (move: (ssa_unchanged_program_add1 H) => {H} [H1 H2]);
        (move: (ssa_unchanged_program_add1 H2) => {H2} [H2 H3]);
        (move: (ssa_unchanged_program_union1 H3) => {H3} [H3 H4]);
        rewrite -!(acc_unchanged_program H2 H0)
          -!(acc_unchanged_program H1 H0);
        rewrite_eval_exp_atom;
        rewrite -!(ssa_unchanged_program_eval_atom H4 H0)
          -!(ssa_unchanged_program_eval_atom H3 H0);
        (move => /andP [Hhi Hlo]);
        apply /andP; split; done.
    - (* mulj *)
      move : H1; (case (Typ.is_unsigned (atyp a E)) => /=);
        (move: (ssa_unchanged_program_add1 H) => {H} [H1 H2]);
        (move: (ssa_unchanged_program_union1 H2) => {H2} [H2 H3]);
        rewrite -!(acc_unchanged_program H1 H0);
        rewrite_eval_exp_atom;
        rewrite -!(ssa_unchanged_program_eval_atom H3 H0)
          -!(ssa_unchanged_program_eval_atom H2 H0); done.
    - (* split *)
      move : H1; (case (Typ.is_unsigned (atyp a E)) => /=);
        (move: (ssa_unchanged_program_add1 H) => {H} [H1 H2]);
        (move: (ssa_unchanged_program_add1 H2) => {H2} [H2 H3]);
        rewrite -!(acc_unchanged_program H2 H0)
          -!(acc_unchanged_program H1 H0);
        rewrite_eval_exp_atom;
        rewrite -(ssa_unchanged_program_eval_atom H3 H0);
        (move => /andP [Hhi Hlo]);
        apply /andP; split; done.
    - (* cast *)
      move : H1; (case (Typ.is_unsigned (atyp a E)) => /=);
        (case (Typ.sizeof_typ t0 == Typ.sizeof_typ (atyp a E)) => /=);
        [ idtac
        | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /=
        | idtac
        | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /= ];
        (move: (ssa_unchanged_program_add1 H) => {H} [H H1]);
        rewrite -!(acc_unchanged_program H H0);
        rewrite_eval_exp_atom;
        by rewrite -(ssa_unchanged_program_eval_atom H1 H0) //.
    - (* vpc *)
      move : H1; (case (Typ.is_unsigned (atyp a E)) => /=);
        (case (Typ.sizeof_typ t0 == Typ.sizeof_typ (atyp a E)) => /=);
        [ idtac
        | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /=
        | idtac
        | case (Typ.sizeof_typ t0 < Typ.sizeof_typ (atyp a E)) => /= ];
        (move: (ssa_unchanged_program_add1 H) => {H} [H H1]);
        rewrite -!(acc_unchanged_program H H0);
        rewrite_eval_exp_atom;
        by rewrite -(ssa_unchanged_program_eval_atom H1 H0) //.
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
        (move : (SSAVS.Lemmas.subset_singleton1 Hsub) => {Hsub});
        rewrite VSLemmas.OP.P.Dec.F.union_b;
        (case /orP => Hsub);
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
        (move : (ssa_unchanged_instr_singleton1 Hun) => {Hun});
        rewrite /ssa_var_unchanged_instr /lvs_instr => H0
    end.

  Ltac not_mem_rewrite_vtyp :=
    match goal with
    | Hnmem : is_true (~~ SSAVS.mem ?v (SSAVS.singleton ?u))
      |- _ =>
        (move : (SSAVS.Lemmas.not_mem_singleton1 Hnmem) => {Hnmem} /negP Hnmem);
        rewrite !SSATE.vtyp_add_neq //
    | Hnmem : is_true (~~ SSAVS.mem ?v (SSAVS.add ?u (SSAVS.singleton ?w)))
      |- _ =>
        let Hneq := fresh in
        let H := fresh in
        (move : (not_mem_add Hnmem) => {Hnmem} [Hneq H]);
        (move : (SSAVS.Lemmas.not_mem_singleton1 H) => {H} /negP H);
        rewrite !SSATE.vtyp_add_neq //
    | _ => idtac
    end.

  Lemma atyp_well_defined_unchanged E i a :
    well_defined_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    SSAVS.subset (vars_atom a) (rvs_instr i) ->
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
    SSAVS.subset (vars_atom a) (rvs_instr i) ->
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
        (move : (ssa_unchanged_instr_union1 Hun) => {Hun} [H0 H1]);
        try decompose_ssa_vars_unchanged_instr
    end.

  Ltac unfold_well_typed :=
    repeat
      match goal with
      | H : is_true (well_typed_instr _ _) |- _ =>
          rewrite /well_typed_instr in H
      | H : is_true (well_typed_atom _ _) |- _ =>
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

  Ltac eval_exp_exp_atom_to_pred_state :=
    match goal with
    | Hsub : is_true (SSAVS.subset (vars_atom ?a) _),
        Hun : is_true (ssa_vars_unchanged_instr _ ?i),
          Hinst : eval_instr _ ?i _ ?s2
      |-
        context f [QFBV.eval_exp (qfbv_atom ?a) ?s2]   =>
        rewrite eval_exp_atom
        -(ssa_unchanged_instr_eval_atom
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
    | Hsub : is_true (SSAVS.subset (vars_atom a) (vars_env ?E)),
        Hco : SSAStore.conform ?s ?E,
          Hsm : is_true (size_matched_atom a)
      |- context f [size (eval_atom a ?s)] =>
        rewrite (conform_size_eval_atom Hsub Hco Hsm)
    end.

  Ltac to_size_eval_atom a :=
    match goal with
    | Hsub : is_true (SSAVS.subset (vars_atom a) (vars_env ?E)),
        Hco : SSAStore.conform ?s ?E,
          Hsm : is_true (size_matched_atom a)
      |- context f [Typ.sizeof_typ (atyp ?a ?E)] =>
        rewrite -(conform_size_eval_atom Hsub Hco Hsm)
    end.

  Ltac intro_size a :=
    match goal with
    | Hsub : is_true (SSAVS.subset (vars_atom a) (vars_env ?E)),
        Hco : SSAStore.conform ?s ?E,
          Hsm : is_true (size_matched_atom a)
      |- _ =>
        move: (conform_size_eval_atom Hsub Hco Hsm)
    end.

  Ltac intro_size1 a :=
    match goal with
    | H : is_true (atyp a ?E == Typ.Tbit) |- _ =>
        intro_size a; rewrite (eqP H) /=
    end.

  Ltac intro_same_size a1 a2 :=
    match goal with
    | Hco : SSAStore.conform ?s ?E,
        Hsm1 : is_true (size_matched_atom a1),
          Hsm2 : is_true (size_matched_atom a2),
            Hsub1 : is_true (SSAVS.subset (vars_atom a1) (vars_env ?E)),
              Hsub2 : is_true (SSAVS.subset (vars_atom a2) (vars_env ?E)) |- _ =>
        match goal with
        | Heq : is_true (atyp a1 E == atyp a2 E) |- _ =>
            let H := fresh in
            (have: Typ.sizeof_typ (atyp a1 E) = Typ.sizeof_typ (atyp a2 E)
              by rewrite (eqP Heq));
            move=> H; move: (size_eval_atom_same Hco Hsm1 Hsm2 Hsub1 Hsub2 H);
                   clear H
        | Heq : Typ.sizeof_typ (atyp a1 ?E) = Typ.sizeof_typ (atyp a2 ?E) |- _ =>
            move: (size_eval_atom_same Hco Hsm1 Hsm2 Hsub1 Hsub2 Heq)
        | Heq : is_true (Typ.sizeof_typ (atyp a1 ?E) == Typ.sizeof_typ (atyp a2 ?E))
          |- _ => move: (size_eval_atom_same Hco Hsm1 Hsm2 Hsub1 Hsub2 Heq)
        | Heq : is_true (Typ.compatible (atyp a1 ?E) (atyp a2 ?E)) |- _ =>
            move: (size_eval_atom_same Hco Hsm1 Hsm2 Hsub1 Hsub2 (eqP Heq))
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
    well_defined_to_vs_subset. eval_exp_exp_atom_to_pred_state.
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
    eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst. qfbv_store_acc.
    rewrite shlBB_shlB. rewrite (to_nat_from_nat_very_small (ltnW Hty0)).
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst. repeat qfbv_store_acc.
    rewrite shlBB_shlB shrBB_shrB. rewrite (to_nat_from_nat_very_small Hty1).
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_same_size a a0. move=> Hss.
    rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_size1 a1. move=> Hsz1.
    intro_same_size a a0. move=> Hszeq.
    rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_same_size a a0. move=> Hsize.
    intro_size1 a1. move=> Hsz1.
    move: (size1 Hsz1). rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_same_size a a0. move=> Hsize.
    have Hszneg: (size (eval_atom a s1) = size (~~# eval_atom a0 s1)%bits).
    { by rewrite size_invB -Hsize. }
    rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_same_size a a0. move=> Hsize.
    rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_same_size a a0. move=> Hsize.
    intro_size1 a1. move=> Hsz1.
    have Hszinv: (size (eval_atom a s1) = size (~~# eval_atom a0 s1)%bits).
    { by rewrite size_invB -Hsize. }
    rewrite /asize. to_size_eval_atom a.
    (case (size1 Hsz1) => /eqP ->);
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_size1 a1. move=> Hsz1.
    intro_same_size a a0. move=> Hsize.
    have Hszinv : (size (eval_atom a s1) = size (~~# eval_atom a0 s1)%bits).
    { by rewrite size_invB -Hsize. }
    rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_same_size a a0. move=> Hsize.
    intro_size1 a1. move=> Hsz1.
    rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
    inversion_clear Hinst; repeat qfbv_store_acc.
    intro_same_size a a0. move=> Hsize.
    intro_size1 a1. move=> Hsz1.
    rewrite /asize. to_size_eval_atom a.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
    have Hinst' : eval_instr E (Imull t t0 a a0) s1 s2 by assumption.
    inversion_clear Hinst'; repeat qfbv_store_acc.
    - rewrite H /=. to_size_atyp a; to_size_atyp a0.
      apply/andP; split; by repeat eval_exp_exp_atom_to_pred_state.
    - rewrite -Typ.not_signed_is_unsigned H /=.
      to_size_atyp a; to_size_atyp a0.
      apply/andP; split; by repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
    have Hinst' : eval_instr E (Imulj t a a0) s1 s2 by assumption.
    inversion_clear Hinst'; repeat qfbv_store_acc.
    - rewrite H /=. to_size_atyp a. by repeat eval_exp_exp_atom_to_pred_state.
    - rewrite -Typ.not_signed_is_unsigned H /=.
      to_size_atyp a. by repeat eval_exp_exp_atom_to_pred_state.
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
    rewrite eval_bexp_if /=. repeat eval_exp_exp_atom_to_pred_state.
    rewrite shlBB_shlB !shrBB_shrB sarBB_sarB.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
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
    repeat eval_exp_exp_atom_to_pred_state.
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


  (** From QFBV to instruction evaluation *)

  Lemma ssastore_reupd v s : SSAStore.Upd v (SSAStore.acc v s) s s.
  Proof.
    move=> x. case Hxv: (x == v).
    - rewrite (SSAStore.acc_upd_eq Hxv). rewrite (eqP Hxv). reflexivity.
    - move/idP/negP: Hxv => Hxv. rewrite (SSAStore.acc_upd_neq Hxv). reflexivity.
  Qed.

  Lemma ssastore_reupd_imp v bs s : bs = SSAStore.acc v s -> SSAStore.Upd v bs s s.
  Proof. move=> ->. exact: ssastore_reupd. Qed.

  Lemma ssastore_reupd2 vl vh s :
    SSAStore.Upd2 vl (SSAStore.acc vl s) vh (SSAStore.acc vh s) s s.
  Proof.
    move=> x. case Hxh: (x == vh).
    - rewrite (SSAStore.acc_upd_eq Hxh). rewrite (eqP Hxh). reflexivity.
    - move/idP/negP: Hxh => Hxh. rewrite (SSAStore.acc_upd_neq Hxh).
      case Hxl: (x == vl).
      + rewrite (SSAStore.acc_upd_eq Hxl). rewrite (eqP Hxl). reflexivity.
      + move/idP/negP: Hxl => Hxl. rewrite (SSAStore.acc_upd_neq Hxl).
        reflexivity.
  Qed.

  Lemma ssastore_reupd2_imp vl vh bsl bsh s :
    bsl = SSAStore.acc vl s ->
    bsh = SSAStore.acc vh s ->
    SSAStore.Upd2 vl bsl vh bsh s s.
  Proof. move=> -> ->.  exact: ssastore_reupd2. Qed.

  Ltac intro_atom_size :=
    match goal with
    | Hco : SSAStore.conform ?bs ?E,
        Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
          Hsm : is_true (size_matched_atom ?a) |- _ =>
        let Hsize := fresh "Hsize" in
        (move: (conform_size_eval_atom Hsub Hco Hsm) => Hsize);
        move: Hsub; intro_atom_size
    | |- _ => intros
    end.

  Ltac norm_tac :=
    repeat
      match goal with
      | H : is_true (well_formed_instr _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/andP: H => /= [H1 H2]
      | H : is_true (well_typed_atom _ _) |- _ =>
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
      | H : context f [QFBV.eval_exp (qfbv_atom _) _] |- _ =>
          rewrite eval_exp_atom in H
      | |- context f [QFBV.eval_exp (qfbv_atom _) _] =>
          rewrite eval_exp_atom
      | Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
          Hco : SSAStore.conform ?s ?E,
            Hsm : is_true (size_matched_atom ?a) |-
          context f [size (eval_atom ?a ?s)] =>
          rewrite (size_eval_atom_asize Hsub Hco Hsm)
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
          Hsm : is_true (size_matched_atom ?a),
            Htyp : is_true (atyp ?c ?E == Typ.Tbit),
              Hsub : is_true (SSAVS.subset (vars_atom ?c) (vars_env ?E)) |- _ =>
          let b := fresh "b" in
          let Hb := fresh "Hb" in
          (move: (tbit_atom_singleton Hco Hsm (eqP Htyp) Hsub) => [b Hb]);
          repeat match goal with
            | H : context f [eval_atom c s] |- _ => rewrite Hb in H
            | |- context f [eval_atom c s] => rewrite Hb
            end;
          move/eqP: Htyp=> Htyp
      | H : context [shlBB _ _] |- _ => rewrite shlBB_shlB in H
      | H : context [shrBB _ _] |- _ => rewrite shrBB_shrB in H
      | H : context [sarBB _ _] |- _ => rewrite sarBB_sarB in H
      end; intro_atom_size.

  Ltac solve_tac :=
    match goal with
    | |- SSAStore.Upd _ _ ?s ?s => apply: ssastore_reupd_imp; solve_tac
    | |- SSAStore.Upd2 _ _ _ _ ?s ?s => apply: ssastore_reupd2_imp; solve_tac
    | H : is_true (?l == ?r) |- ?r = ?l =>
        rewrite (eqP H); reflexivity
    end.

  Lemma eval_bexp_instr_Imov E s :
    forall (t : SSAVarOrder.t) (a : atom),
      is_rng_instr (Imov t a) ->
      well_formed_instr E (Imov t a) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Imov t a) E) ->
      QFBV.eval_bexp (bexp_instr E (Imov t a)) s -> eval_instr E (Imov t a) s s.
  Proof. move=> /= *. apply: EImov. norm_tac. by solve_tac. Qed.

  Lemma eval_bexp_instr_Ishl E s :
    forall (t : SSAVarOrder.t) (a : atom) (n : nat),
      is_rng_instr (Ishl t a n) ->
      well_formed_instr E (Ishl t a n) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Ishl t a n) E) ->
      QFBV.eval_bexp (bexp_instr E (Ishl t a n)) s -> eval_instr E (Ishl t a n) s s.
  Proof. move=> /= *. apply: EIshl. norm_tac. by solve_tac. Qed.

  Lemma eval_bexp_instr_Icshl E s :
    forall (t t0 : SSAVarOrder.t) (a a0 : atom) (n : nat),
      is_rng_instr (Icshl t t0 a a0 n) ->
      well_formed_instr E (Icshl t t0 a a0 n) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Icshl t t0 a a0 n) E) ->
      QFBV.eval_bexp (bexp_instr E (Icshl t t0 a a0 n)) s ->
      eval_instr E (Icshl t t0 a a0 n) s s.
  Proof. move=> /= *. apply: EIcshl. norm_tac. by solve_tac. Qed.

  Lemma eval_bexp_instr_Inondet E s :
    forall (t : SSAVarOrder.t) (t0 : Typ.typ),
      is_rng_instr (Inondet t t0) ->
      well_formed_instr E (Inondet t t0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Inondet t t0) E) ->
      QFBV.eval_bexp (bexp_instr E (Inondet t t0)) s -> eval_instr E (Inondet t t0) s s.
  Proof.
    move=> /= v t _ Hwf Hco Hco' H. apply: (@EInondet _ _ _ _ _ (SSAStore.acc v s)).
    - move: (Hco' v) => HH. rewrite -HH.
      + rewrite (SSATE.vsize_add_eq (eqxx v)). reflexivity.
      + apply: SSATE.Lemmas.mem_add_eq. reflexivity.
    - exact: ssastore_reupd.
  Qed.

  Lemma eval_bexp_instr_Icmov E s :
    forall (t : SSAVarOrder.t) (a a0 a1 : atom),
      is_rng_instr (Icmov t a a0 a1) ->
      well_formed_instr E (Icmov t a a0 a1) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Icmov t a a0 a1) E) ->
      QFBV.eval_bexp (bexp_instr E (Icmov t a a0 a1)) s ->
      eval_instr E (Icmov t a a0 a1) s s.
  Proof.
    move=> /= v c a1 a2 _ Hwf Hco1 Hco2 Heq. norm_tac.
    case: b Hb Heq => /= Hb Heq.
    - apply: EIcmovT.
      + by rewrite Hb.
      + norm_tac. by solve_tac.
    - apply: EIcmovF.
      + by rewrite Hb.
      + norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Inop E s :
    is_rng_instr Inop ->
    well_formed_instr E Inop ->
    SSAStore.conform s E ->
    SSAStore.conform s (instr_succ_typenv Inop E) ->
    QFBV.eval_bexp (bexp_instr E Inop) s -> eval_instr E Inop s s.
  Proof. move=> /= *. by apply: EInop. Qed.

  Lemma eval_bexp_instr_Inot E s :
    forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a : atom),
      is_rng_instr (Inot t t0 a) ->
      well_formed_instr E (Inot t t0 a) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Inot t t0 a) E) ->
      QFBV.eval_bexp (bexp_instr E (Inot t t0 a)) s -> eval_instr E (Inot t t0 a) s s.
  Proof. move=> /= *. apply: EInot. norm_tac. by solve_tac. Qed.

  Lemma eval_bexp_instr_Iadd E s :
    forall (t : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Iadd t a a0) ->
      well_formed_instr E (Iadd t a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Iadd t a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Iadd t a a0)) s -> eval_instr E (Iadd t a a0) s s.
  Proof. move=> /= *. apply: EIadd. norm_tac. by solve_tac. Qed.

  Lemma eval_bexp_instr_Iadds E s :
    forall (t t0 : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Iadds t t0 a a0) ->
      well_formed_instr E (Iadds t t0 a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Iadds t t0 a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Iadds t t0 a a0)) s ->
      eval_instr E (Iadds t t0 a a0) s s.
  Proof.
    move=> /= c v a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIadds. norm_tac.
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
    forall (t : SSAVarOrder.t) (a a0 a1 : atom),
      is_rng_instr (Iadc t a a0 a1) ->
      well_formed_instr E (Iadc t a a0 a1) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Iadc t a a0 a1) E) ->
      QFBV.eval_bexp (bexp_instr E (Iadc t a a0 a1)) s ->
      eval_instr E (Iadc t a a0 a1) s s.
  Proof.
    move=> /= v a1 a2 ac _ Hwf Hco1 Hco2 Hev. apply: EIadc. norm_tac.
    apply: ssastore_reupd_imp. rewrite (eqP Hev).
    intro_same_size a1 a2 => Hs. of_asize.
    rewrite (adcB_zext1_lown b Hs). reflexivity.
  Qed.

  Lemma eval_bexp_instr_Iadcs E s :
    forall (t t0 : SSAVarOrder.t) (a a0 a1 : atom),
      is_rng_instr (Iadcs t t0 a a0 a1) ->
      well_formed_instr E (Iadcs t t0 a a0 a1) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Iadcs t t0 a a0 a1) E) ->
      QFBV.eval_bexp (bexp_instr E (Iadcs t t0 a a0 a1)) s ->
      eval_instr E (Iadcs t t0 a a0 a1) s s.
  Proof.
    move=> /= c v a1 a2 ac _ Hwf Hco1 Hco2 Hev. apply: EIadcs. norm_tac.
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
    forall (t : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Isub t a a0) ->
      well_formed_instr E (Isub t a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isub t a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Isub t a a0)) s -> eval_instr E (Isub t a a0) s s.
  Proof.
    move=> /= v a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIsub. norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Isubc E s :
    forall (t t0 : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Isubc t t0 a a0) ->
      well_formed_instr E (Isubc t t0 a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isubc t t0 a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Isubc t t0 a a0)) s ->
      eval_instr E (Isubc t t0 a a0) s s.
  Proof.
    move=> /= c v a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIsubc. norm_tac.
    have Hs: (size (eval_atom a1 s) = size (~~# eval_atom a2 s)%bits) by
        by rewrite size_invB Hsize Hsize0 (eqP H0). of_asize.
    rewrite (adcB_zext1_high1 _ Hs) in H1. rewrite (adcB_zext1_lown _ Hs) in H4.
    by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Isubb E s :
    forall (t t0 : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Isubb t t0 a a0) ->
      well_formed_instr E (Isubb t t0 a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isubb t t0 a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Isubb t t0 a a0)) s ->
      eval_instr E (Isubb t t0 a a0) s s.
  Proof.
    move=> /= bw v a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIsubb. norm_tac.
    intro_same_size a1 a2 => Hs. of_asize.
    rewrite (subB_zext1_lown Hs) in H4. rewrite (subB_zext1_high1 Hs) in H1.
    by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Isbc E s :
    forall (t : SSAVarOrder.t) (a a0 a1 : atom),
      is_rng_instr (Isbc t a a0 a1) ->
      well_formed_instr E (Isbc t a a0 a1) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isbc t a a0 a1) E) ->
      QFBV.eval_bexp (bexp_instr E (Isbc t a a0 a1)) s ->
      eval_instr E (Isbc t a a0 a1) s s.
  Proof.
    move=> /= v a1 a2 ac _ Hwf Hco1 Hco2 Hev. apply: EIsbc. norm_tac.
    have Hs: size (eval_atom a1 s) = size (~~# eval_atom a2 s)%bits
      by rewrite size_invB Hsize Hsize0 (eqP H0). of_asize.
    rewrite (adcB_zext1_lown _ Hs) in Hev. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Isbcs E s :
    forall (t t0 : SSAVarOrder.t) (a a0 a1 : atom),
      is_rng_instr (Isbcs t t0 a a0 a1) ->
      well_formed_instr E (Isbcs t t0 a a0 a1) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isbcs t t0 a a0 a1) E) ->
      QFBV.eval_bexp (bexp_instr E (Isbcs t t0 a a0 a1)) s ->
      eval_instr E (Isbcs t t0 a a0 a1) s s.
  Proof.
    move=> /= c v a1 a2 ay _ Hwf Hco1 Hco2 Hev. apply: EIsbcs. norm_tac.
    have Hs: size (eval_atom a1 s) = size (~~# eval_atom a2 s)%bits
      by rewrite size_invB Hsize Hsize0 (eqP H0). of_asize.
    rewrite (adcB_zext1_high1 _ Hs) in H. rewrite (adcB_zext1_lown _ Hs) in H6.
    by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Isbb E s :
    forall (t : SSAVarOrder.t) (a a0 a1 : atom),
      is_rng_instr (Isbb t a a0 a1) ->
      well_formed_instr E (Isbb t a a0 a1) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isbb t a a0 a1) E) ->
      QFBV.eval_bexp (bexp_instr E (Isbb t a a0 a1)) s ->
      eval_instr E (Isbb t a a0 a1) s s.
  Proof.
    move=> /= v a1 a2 ab _ Hwf Hco1 Hco2 Hev. apply: EIsbb. norm_tac.
    intro_same_size a1 a2 => Hs. of_asize.
    rewrite (sbbB_zext1_lown _ Hs) in Hev. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Isbbs E s :
    forall (t t0 : SSAVarOrder.t) (a a0 a1 : atom),
      is_rng_instr (Isbbs t t0 a a0 a1) ->
      well_formed_instr E (Isbbs t t0 a a0 a1) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isbbs t t0 a a0 a1) E) ->
      QFBV.eval_bexp (bexp_instr E (Isbbs t t0 a a0 a1)) s ->
      eval_instr E (Isbbs t t0 a a0 a1) s s.
  Proof.
    move=> /= b v a1 a2 ab _ Hwf Hco1 Hco2 Hev. apply: EIsbbs. norm_tac.
    intro_same_size a1 a2 => Hs. of_asize.
    rewrite (sbbB_zext1_lown _ Hs) in H6. rewrite (sbbB_zext1_high1 _ Hs) in H.
    by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Imul E s :
    forall (t : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Imul t a a0) ->
      well_formed_instr E (Imul t a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Imul t a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Imul t a a0)) s -> eval_instr E (Imul t a a0) s s.
  Proof.
    move=> /= v a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EImul. norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Imull E s :
    forall (t t0 : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Imull t t0 a a0) ->
      well_formed_instr E (Imull t t0 a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Imull t t0 a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Imull t t0 a a0)) s ->
      eval_instr E (Imull t t0 a a0) s s.
  Proof.
    move=> /= vh vl a1 a2 _ Hwf Hco1 Hco2 Hev. dcase (atyp a1 E). case => wa1 Htyp.
    - have Hun: Typ.is_unsigned (atyp a1 E) by rewrite Htyp.
      rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
      apply: (EImullU Hun). norm_tac. by solve_tac.
    - have Hsn: Typ.is_signed (atyp a1 E) by rewrite Htyp.
      rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
      apply: (EImullS Hsn). norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Imulj E s :
    forall (t : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Imulj t a a0) ->
      well_formed_instr E (Imulj t a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Imulj t a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Imulj t a a0)) s ->
      eval_instr E (Imulj t a a0) s s.
  Proof.
    move=> /= v a1 a2 _ Hwf Hco1 Hco2 Hev. dcase (atyp a1 E). case => wa1 Htyp.
    - have Hun: Typ.is_unsigned (atyp a1 E) by rewrite Htyp.
      rewrite Htyp /= in Hev.
      apply: (EImuljU Hun). norm_tac. by solve_tac.
    - have Hsn: Typ.is_signed (atyp a1 E) by rewrite Htyp.
      rewrite Htyp /= in Hev.
      apply: (EImuljS Hsn). norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Isplit E s :
    forall (t t0 : SSAVarOrder.t) (a : atom) (n : nat),
      is_rng_instr (Isplit t t0 a n) ->
      well_formed_instr E (Isplit t t0 a n) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Isplit t t0 a n) E) ->
      QFBV.eval_bexp (bexp_instr E (Isplit t t0 a n)) s ->
      eval_instr E (Isplit t t0 a n) s s.
  Proof.
    move=> /= vh vl a n _ Hwf Hco1 Hco2 Hev. dcase (atyp a E). case => wa Htyp.
    - have Hun: Typ.is_unsigned (atyp a E) by rewrite Htyp.
      rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
      apply: (EIsplitU Hun). norm_tac. by solve_tac.
    - have Hsn: Typ.is_signed (atyp a E) by rewrite Htyp.
      rewrite Htyp /= in Hev. move/andP: Hev => [Hev1 Hev2].
      apply: (EIsplitS Hsn). norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Iand E s :
    forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a a0 : atom),
      is_rng_instr (Iand t t0 a a0) ->
      well_formed_instr E (Iand t t0 a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Iand t t0 a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Iand t t0 a a0)) s ->
      eval_instr E (Iand t t0 a a0) s s.
  Proof.
    move=> /= v t a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIand. norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Ior E s :
    forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a a0 : atom),
      is_rng_instr (Ior t t0 a a0) ->
      well_formed_instr E (Ior t t0 a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Ior t t0 a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Ior t t0 a a0)) s ->
      eval_instr E (Ior t t0 a a0) s s.
  Proof.
    move=> /= v t a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIor. norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Ixor E s :
    forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a a0 : atom),
      is_rng_instr (Ixor t t0 a a0) ->
      well_formed_instr E (Ixor t t0 a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Ixor t t0 a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Ixor t t0 a a0)) s ->
      eval_instr E (Ixor t t0 a a0) s s.
  Proof.
    move=> /= v t a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIxor. norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Icast E s :
    forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a : atom),
      is_rng_instr (Icast t t0 a) ->
      well_formed_instr E (Icast t t0 a) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Icast t t0 a) E) ->
      QFBV.eval_bexp (bexp_instr E (Icast t t0 a)) s ->
      eval_instr E (Icast t t0 a) s s.
  Proof.
    move=> /= v t a _ Hwf Hco1 Hco2 Hev. apply: EIcast. norm_tac.
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
    forall (t : SSAVarOrder.t) (t0 : Typ.typ) (a : atom),
      is_rng_instr (Ivpc t t0 a) ->
      well_formed_instr E (Ivpc t t0 a) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Ivpc t t0 a) E) ->
      QFBV.eval_bexp (bexp_instr E (Ivpc t t0 a)) s ->
      eval_instr E (Ivpc t t0 a) s s.
  Proof.
    move=> /= v t a Hrng Hwf Hco1 Hco2 Hev. apply: EIvpc.
    have Hwf': (well_formed_instr E (Icast v t a)) by exact: Hwf.
    move: (eval_bexp_instr_Icast Hrng Hwf' Hco1 Hco2 Hev). inversion_clear 1.
    assumption.
  Qed.

  Lemma eval_bexp_instr_Ijoin E s :
    forall (t : SSAVarOrder.t) (a a0 : atom),
      is_rng_instr (Ijoin t a a0) ->
      well_formed_instr E (Ijoin t a a0) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Ijoin t a a0) E) ->
      QFBV.eval_bexp (bexp_instr E (Ijoin t a a0)) s ->
      eval_instr E (Ijoin t a a0) s s.
  Proof.
    move=> /= v a1 a2 _ Hwf Hco1 Hco2 Hev. apply: EIjoin. norm_tac. by solve_tac.
  Qed.

  Lemma eval_bexp_instr_Iassume E s :
    forall b : SSA.bexp,
      is_rng_instr (Iassume b) ->
      well_formed_instr E (Iassume b) ->
      SSAStore.conform s E ->
      SSAStore.conform s (instr_succ_typenv (Iassume b) E) ->
      QFBV.eval_bexp (bexp_instr E (Iassume b)) s ->
      eval_instr E (Iassume b) s s.
  Proof.
    move=> /= b Hrng Hwf Hco1 Hco2 Hev. case: b Hrng Hwf Hev => e r /= Hrng Hwf Hev.
    apply: EIassume. rewrite /eval_bexp /=. split; first by rewrite (eqP Hrng).
    apply/eval_bexp_rbexp. assumption.
  Qed.

  Lemma eval_bexp_instr E i s :
    is_rng_instr i ->
    well_formed_instr E i ->
    SSAStore.conform s E -> SSAStore.conform s (instr_succ_typenv i E) ->
    QFBV.eval_bexp (bexp_instr E i) s -> eval_instr E i s s.
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

  Lemma bexp_program_eval E p s1 s2 :
    well_formed_ssa_program E p ->
    SSAStore.conform s1 E ->
    eval_program E p s1 s2 ->
    QFBV.eval_bexps (bexp_program E p) s2.
  Proof.
    elim: p E s1 s2 => [| hd tl IH] E s1 s3 //=. move=> Hwfssa Hcon Hep.
    move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
    elim: (eval_program_cons Hep) => s2 [Hehd Hetl].
    move: (ssa_unchanged_program_cons1 Huc) => [Huchd Huctl].
    rewrite (IH _ _ _
               (well_formed_ssa_tl Hwfssa)
               (conform_instr_succ_typenv (well_formed_program_cons1 Hwf) Hcon Hehd) Hetl) andbT.
    move: (well_formed_program_cons1 Hwf) => Hwfhd.
    move: (bexp_instr_eval Hwfhd Hcon Huchd Hehd).
    move: (ssa_unchanged_instr_succ_typenv_submap Huchd) => Hsubm.
    move/andP: Hwfhd=> [Hwd_hd Hwt_hd].
    move: (well_formed_ssa_vars_unchanged_hd Hwfssa) => Hun_hd.
    rewrite (bexp_instr_submap Hwd_hd Hsubm).
    exact: (eval_vars_unchanged_program_bexp_instr Hun_hd Hetl).
  Qed.

  Lemma bexp_program_eval_rng_program E p s :
    is_rng_program p ->
    well_formed_ssa_program E p ->
    SSAStore.conform s (program_succ_typenv p E) ->
    QFBV.eval_bexps (bexp_program E p) s ->
    eval_program E p s s.
  Proof.
    move=> Hrng /andP [/andP [Hwf Hun] Hssa] Hco Hev.
    move: (ssa_unchanged_program_succ_typenv_submap Hun Hssa) => Hsubm.
    elim: p E Hrng Hwf Hun Hssa Hco Hev Hsubm => /= [| i p IH] E Hrng Hwf Hun Hssa Hco Hev Hsubm.
    - exact: Enil.
    - move/andP: Hrng => [Hrng_i Hrng_p]. move/andP: Hev => [Hev_i Hev_p].
      move/andP: Hwf => [Hwf_i Hwf_p].
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
      + apply: (eval_bexp_instr Hrng_i Hwf_i Hco_E _ Hev_i).
        exact: (conform_submap Hsubm' Hco).
      + apply: (IH _ Hrng_p Hwf_p Hun_p' Hssa_p Hco _ Hsubm'). exact: Hev_p.
  Qed.

  (** Conversion from a rspec to bexp_spec *)

  Definition bexp_of_rspec E (s : rspec) : bexp_spec :=
    {| binputs := program_succ_typenv (rsprog s) E;
      bpre := bexp_rbexp (rspre s);
      bprog := bexp_program E (rsprog s);
      bpost := bexp_rbexp (rspost s) |}.

  Lemma vars_bexp_of_rspec E s :
    SSAVS.subset (vars_bexp_spec (bexp_of_rspec E s)) (vars_rspec s).
  Proof.
    case: s => [Es f p g] //=. rewrite /bexp_of_rspec /vars_bexp_spec /vars_rspec /=.
    rewrite !vars_bexp_rbexp. move: (vars_bexp_program E p) => Hp.
    by SSAVS.Lemmas.dp_subset.
  Qed.


  (** Soundness and completeness of bexp_of_rspec *)

  Theorem bexp_of_rspec_sound (s : rspec) :
    well_formed_ssa_rspec s ->
    valid_bexp_spec (bexp_of_rspec (rsinputs s) s) ->
    valid_rspec s.
  Proof.
    destruct s as [te f p g]. rewrite /bexp_of_rspec /valid_bexp_spec /=.
    move=> Hwfssa Hvalid s1 s2 /= Hcon Hf Hp. apply/eval_bexp_rbexp.
    move: Hwfssa => /andP /= [/andP [Hwf Huc] Hssa].
    move : Hwf => /andP [/andP /= [Hwf_f Hwf_p] _].
    move : Hwf_f => /= /andP [Hdef_f _]. apply: Hvalid.
    - exact: (conform_program_succ_typenv Hwf_p Hcon Hp).
    - apply/eval_bexp_rbexp.
      apply: (proj1 (ssa_unchanged_program_eval_rbexp _ Hp) Hf).
      apply : (ssa_unchanged_program_subset Huc).
      rewrite -are_defined_subset_env. exact: Hdef_f.
    - apply : (bexp_program_eval _ Hcon Hp).
      rewrite /well_formed_ssa_program. by rewrite Hwf_p Huc Hssa.
  Qed.

  Theorem bexp_of_rspec_complete (s : rspec) :
    is_rng_rspec s ->
    well_formed_ssa_rspec s ->
    valid_rspec s ->
    valid_bexp_spec (bexp_of_rspec (rsinputs s) s).
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /valid_rspec /bexp_of_rspec /=.
    rewrite /valid_bexp_spec /is_rng_rspec /=.
    move=> Hrng_p /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa_p].
    move=> Hvr s Hco /eval_bexp_rbexp Hf Heb. apply/eval_bexp_rbexp. apply: (Hvr s s _ Hf).
    - apply: (conform_submap _ Hco).
      exact: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa_p).
    - apply: (bexp_program_eval_rng_program Hrng_p _ Hco Heb).
      rewrite /well_formed_ssa_program. by rewrite Hwf_p Hun_Ep Hssa_p.
  Qed.

End Rspec2QFBV.


(** Range reduction version 1:
    a simple conversion from a range specification to a QF_BV query *)

Section Rngred.

  Definition rngred_rspec (s : rspec) : QFBV.bexp :=
    let bs := bexp_of_rspec (rsinputs s) s in
    qfbv_imp (qfbv_conj (bpre bs) (qfbv_conjs (bprog bs)))
      (bpost bs).

  Definition valid_rngred_rspec (s : rspec) :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    QFBV.valid fE (rngred_rspec s).

  Lemma valid_rngred_rspec_valid_bexp_spec s :
    valid_rngred_rspec s <-> valid_bexp_spec (bexp_of_rspec (rsinputs s) s).
  Proof.
    case: s => E f p g. rewrite /valid_rngred_rspec /valid_bexp_spec /=.
    split.
    - move=> H s Hco Hf Hp. move: (H s Hco) => /=. rewrite Hf /=.
      rewrite qfbv_conjs_eval Hp /=. by apply.
    - move=> H s Hco. move: (H s Hco) => {H} /=.
      case Hf: (QFBV.eval_bexp (bexp_rbexp f) s) => //=.
      case Hp: (QFBV.eval_bexp (qfbv_conjs (bexp_program E p)) s) => //=.
      rewrite qfbv_conjs_eval in Hp. rewrite Hp. by apply.
  Qed.

  Theorem rngred_rspec_sound s :
    well_formed_ssa_rspec s -> valid_rngred_rspec s -> valid_rspec s.
  Proof.
    move=> Hwf Hv. apply: (bexp_of_rspec_sound Hwf).
    apply/valid_rngred_rspec_valid_bexp_spec. assumption.
  Qed.

  Theorem rngred_rspec_complete s :
    is_rng_rspec s -> well_formed_ssa_rspec s -> valid_rspec s ->
    valid_rngred_rspec s.
  Proof.
    move=> Hrng Hwf Hv. apply/valid_rngred_rspec_valid_bexp_spec.
    exact: (bexp_of_rspec_complete Hrng Hwf Hv).
  Qed.


  (** Well-formedness of the QF_BV query constructed by rngred_rspec *)

  Section WellFormedRange.

    Lemma well_formed_qfbv_atom E a :
      are_defined (vars_atom a) E -> QFBV.well_formed_exp (qfbv_atom a) E.
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
      - move=> w op e IH Hwf. move: (well_formed_rexp_unop Hwf) => {Hwf} [Hwf [Hw Hs]].
        move: (IH Hwf) => {IH Hwf} Hwf. case: op => /=; assumption.
      - move=> w op e1 IH1 e2 IH2 Hwf.
        move: (well_formed_rexp_binop Hwf) => {Hwf} [Hwf1 [Hwf2 [Hw [Hs1 Hs2]]]].
        move: (IH1 Hwf1) (IH2 Hwf2) => {IH1 IH2} Hqwf1 Hqwf2.
        case: op => /=; rewrite ?Hqwf1 ?Hqwf2 ?(size_exp_rexp Hwf1)
                      ?(size_exp_rexp Hwf2) ?Hs1 ?Hs2 eqxx !andbT !andTb;
                      by trivial.
      - move=> w e IH n Hwf. move: (well_formed_rexp_uext Hwf) => {Hwf} [Hwf [Hw Hs]].
        exact: (IH Hwf).
      - move=> w e IH n Hwf. move: (well_formed_rexp_sext Hwf) => {Hwf} [Hwf [Hw Hs]].
        exact: (IH Hwf).
    Qed.

    Lemma well_formed_bexp_rbexp E e :
      well_formed_rbexp E e -> QFBV.well_formed_bexp (bexp_rbexp e) E.
    Proof.
      elim: e => //=.
      - move=> w e1 e2 Hwf. move: (well_formed_rbexp_eq Hwf) =>
                                  [Hwf1 [Hwf2 [Hw [Hs1 Hs2]]]].
        rewrite (well_formed_exp_rexp Hwf1) (well_formed_exp_rexp Hwf2).
        rewrite (size_exp_rexp Hwf1) Hs1 (size_exp_rexp Hwf2) Hs2.
        rewrite eqxx. exact: is_true_true.
      - move=> w op e1 e2 Hwf.
        move: (well_formed_rbexp_cmp Hwf) => {Hwf} [Hwf1 [Hwf2 [Hw [Hs1 Hs2]]]].
        (case: op => /=);
        rewrite (well_formed_exp_rexp Hwf1) (well_formed_exp_rexp Hwf2)
          (size_exp_rexp Hwf1) Hs1 (size_exp_rexp Hwf2) Hs2 eqxx;
        exact: is_true_true.
      - move=> e1 IH1 e2 IH2 Hwf. move: (well_formed_rbexp_and Hwf) => [Hwf1 Hwf2].
        rewrite (IH1 Hwf1) (IH2 Hwf2). exact: is_true_true.
      - move=> e1 IH1 e2 IH2 Hwf. move: (well_formed_rbexp_or Hwf) => [Hwf1 Hwf2].
        rewrite (IH1 Hwf1) (IH2 Hwf2). exact: is_true_true.
    Qed.

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

    Ltac norm_tac :=
      unfold_well_formed;
      ssa_vars_unchanged_instr_to_mem;
      intro_subset_from_are_defined;
      repeat
        match goal with
        | H : is_true (are_defined (vars_atom ?a) ?E)
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
            Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E))
          |- context f [atyp ?a (SSATE.add ?v ?t _)] =>
            rewrite (atyp_add_not_mem _ _ (SSAVS.Lemmas.not_mem_subset Hmem Hsub))
        | Hmem : is_true (~~ SSAVS.mem ?v (vars_env ?E)),
            Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
              H : context f [atyp ?a (SSATE.add ?v ?t _)] |- _ =>
            rewrite (atyp_add_not_mem _ _ (SSAVS.Lemmas.not_mem_subset Hmem Hsub)) in H
        | Hwsa : is_true (well_sized_atom ?E ?a) |-
            context f [0 < Typ.sizeof_typ (atyp ?a ?E)] =>
            rewrite (well_sized_atom_gt0 Hwsa) /=
        | |- context f [0 < _ + _] =>
            rewrite addn_gt0
        (**)
        | |- context f [size (from_nat _ _)] => rewrite size_from_nat
        | |- context f [SSATE.mem ?v (SSATE.add ?v _ _)] =>
            rewrite (SSATE.Lemmas.mem_add_eq (eqxx v))
        | |- context f [SSATE.vsize ?v (SSATE.add ?v _ _)] =>
            rewrite (SSATE.vsize_add_eq (eqxx v))
        | H : is_true (are_defined (vars_atom ?a) ?E)
          |- context f [QFBV.well_formed_exp (qfbv_atom ?a) ?E] =>
            rewrite (well_formed_qfbv_atom H)
        | Hdef : is_true (are_defined (vars_atom ?a) ?E),
            Hsm : is_true (size_matched_atom ?a)
          |- context f [QFBV.exp_size (qfbv_atom ?a) ?E] =>
            rewrite (size_exp_atom Hdef Hsm)
        | |- context f [asize ?a (SSATE.add _ (atyp ?a ?E) ?E)] =>
            rewrite asize_add_same
        | |- context f [asize _ _] => rewrite /asize
        | H : is_true (Typ.compatible _ ?t)
          |- context f [Typ.sizeof_typ ?t] =>
            rewrite -(eqP H)
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

    Theorem well_formed_qfbv_rngred_rspec s :
      let fE := program_succ_typenv (rsprog s) (rsinputs s) in
      well_formed_ssa_rspec s ->
      QFBV.well_formed_bexp (rngred_rspec s) fE.
    Proof.
      case s => E f p g /=. move=> Hwf.
      move/andP: Hwf => /= [/andP [Hwf Hun] Hssa].
      move/andP: Hwf => /= [/andP [Hwf_f Hwf_p] Hwf_g].
      move: (ssa_unchanged_program_succ_typenv_submap Hun Hssa) => Hsubm.
      apply/andP; split; first (apply/andP; split).
      - exact: (well_formed_bexp_rbexp (well_formed_rbexp_submap Hsubm Hwf_f)).
      - exact: (well_formed_bexp_program Hun Hssa Hwf_p).
      - exact: (well_formed_bexp_rbexp Hwf_g).
    Qed.

  End WellFormedRange.

End Rngred.


(** Range reduction version 2:
    split range conditions and apply qfbv_conjs_la *)

Section RngredSplitLeftAssoc.

  Definition rngred_rspec_split_la (s : rspec) : seq QFBV.bexp :=
    let bs := bexp_of_rspec (rsinputs s) s in
    map (fun post => qfbv_imp (qfbv_conj (bpre bs) (qfbv_conjs_la (bprog bs))) post)
      (split_conj (bpost bs)).

  Ltac mytac :=
    (repeat match goal with
       | |- context c [QFBV.vars_exp (exp_rexp _)] => rewrite vars_exp_rexp
       | |- context c [QFBV.vars_bexp (bexp_rbexp _)] => rewrite vars_bexp_rbexp
       | |- context c [QFBV.vars_bexp (qfbv_conjs_la _)] => rewrite vars_qfbv_conjs_la
       end);
    try SSAVS.Lemmas.dp_subset.

  Lemma vars_rngred_rspec_split_la s :
    SSAVS.subset (vars_bexps (rngred_rspec_split_la s)) (SSA.vars_rspec s).
  Proof.
    case: s => [E f p g]. rewrite /rngred_rspec_split_la /vars_rspec /=.
    move: (vars_bexp_program E p) => ?. elim: g => //=.
    - by mytac.
    - move=> _ e1 e2. by mytac.
    - move=> _ [] e1 e2.
      + rewrite /qfbv_ult /=; by mytac.
      + rewrite /qfbv_ule /=; by mytac.
      + rewrite /qfbv_ugt /=; by mytac.
      + rewrite /qfbv_uge /=; by mytac.
      + rewrite /qfbv_slt /=; by mytac.
      + rewrite /qfbv_sle /=; by mytac.
      + rewrite /qfbv_sgt /=; by mytac.
      + rewrite /qfbv_sge /=; by mytac.
    - move=> e IH. by mytac.
    - move=> e1 IH1 e2 IH2. rewrite map_cat vars_bexps_cat. apply: SSAVS.Lemmas.subset_union3.
      + apply: (SSAVS.Lemmas.subset_trans IH1). by SSAVS.Lemmas.dp_subset.
      + apply: (SSAVS.Lemmas.subset_trans IH2). by SSAVS.Lemmas.dp_subset.
    - move=> e1 IH1 e2 IH2. by mytac.
  Qed.

  Definition valid_rngred_rspec_split_la (s : rspec) :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    valid_bexps fE (rngred_rspec_split_la s).

  Lemma imp_split_conj_eval e f s :
    QFBV.eval_bexps (map (fun f => qfbv_imp e f) (split_conj f)) s =
      QFBV.eval_bexp (qfbv_imp e f) s.
  Proof.
    elim: f => //=.
    - rewrite orbF andbT. reflexivity.
    - rewrite orbT andbT. reflexivity.
    - move=> op f1 f2. rewrite andbT. reflexivity.
    - move=> f IH. rewrite andbT. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite map_cat.
      rewrite eval_bexps_cat. rewrite IH1 IH2. by case: (QFBV.eval_bexp e s) => //=.
    - move=> e1 IH1 e2 IH2. rewrite andbT. reflexivity.
  Qed.

  Lemma imp_split_conj_valid E e f :
    QFBV.valid_bexps E (map (fun f => qfbv_imp e f) (split_conj f)) <->
      QFBV.valid_bexp E (qfbv_imp e f).
  Proof.
    split.
    - move=> H s Hco. rewrite -imp_split_conj_eval. move: (H _ Hco) => {}H. assumption.
    - move=> H s Hco. move: (H s Hco). rewrite -imp_split_conj_eval. by apply.
  Qed.

  Lemma rngred_rspec_split_la_eval fE s :
    QFBV.valid_bexps fE (rngred_rspec_split_la s) <-> QFBV.valid_bexp fE (rngred_rspec s).
  Proof.
    rewrite /rngred_rspec_split_la. case: s => [E f p g] /=. split=> H.
    - move/imp_split_conj_valid: H. rewrite /rngred_rspec /=.
      move=> H s Hco /=. rewrite eval_qfbv_conjs_ra_la. exact: (H _ Hco).
    - apply/imp_split_conj_valid. move=> s Hco /=. rewrite -eval_qfbv_conjs_ra_la.
      exact: (H _ Hco).
  Qed.

  Lemma rngred_rspec_split_la_valid s :
    valid_rngred_rspec s <-> valid_rngred_rspec_split_la s.
  Proof.
    split => H.
    - move=> fE Hco. rewrite /rngred_rspec_split_la imp_split_conj_eval /=.
      rewrite -eval_qfbv_conjs_ra_la. exact: (H _ Hco).
    - move=> fE Hco. move: (H _ Hco).
      rewrite /rngred_rspec_split_la imp_split_conj_eval /=.
      rewrite -eval_qfbv_conjs_ra_la. by apply.
  Qed.

  Theorem rngred_rspec_split_la_sound s :
    well_formed_ssa_rspec s -> valid_rngred_rspec_split_la s ->
    valid_rspec s.
  Proof.
    move=> Hwf Hv. apply: (rngred_rspec_sound Hwf).
    apply/rngred_rspec_split_la_valid. assumption.
  Qed.

  Theorem rngred_rspec_split_la_complete s :
    is_rng_rspec s -> well_formed_ssa_rspec s -> valid_rspec s ->
    valid_rngred_rspec_split_la s.
  Proof.
    move=> Hrng Hwf Hv. apply/rngred_rspec_split_la_valid.
    exact: (rngred_rspec_complete Hrng Hwf Hv).
  Qed.

  Lemma well_formed_rngred_rspec_split_la_ra E s :
    QFBV.well_formed_bexps (rngred_rspec_split_la s) E =
      QFBV.well_formed_bexp (rngred_rspec s) E.
  Proof.
    rewrite /rngred_rspec_split_la /rngred_rspec /=.
    move: (bexp_rbexp (rspre s)). move: (bexp_program (rsinputs s) (rsprog s)).
    move: (bexp_rbexp (rspost s)). clear s. elim => //=.
    - move=> ps fs. rewrite !andbT. rewrite -well_formed_bexp_ra_la. reflexivity.
    - move=> ps fs. rewrite !andbT. rewrite -well_formed_bexp_ra_la. reflexivity.
    - move=> _ e1 e2 ps fs. rewrite andbT. rewrite -well_formed_bexp_ra_la. reflexivity.
    - move=> e IH ps fs. rewrite andbT. rewrite -well_formed_bexp_ra_la. reflexivity.
    - move=> e1 IH1 e2 IH2 ps fs. rewrite map_cat /=.
      rewrite well_formed_bexps_cat. rewrite IH1 IH2. rewrite !andbA.
      case: (QFBV.well_formed_bexp fs E) => //=.
      case: (QFBV.well_formed_bexp (qfbv_conjs ps) E) => //=.
      rewrite !andbT. reflexivity.
    - move=> e1 IH1 e2 IH2 ps fs. rewrite -well_formed_bexp_ra_la andbT.
      reflexivity.
  Qed.

  Theorem well_formed_qfbv_rngred_rspec_split_la s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    QFBV.well_formed_bexps (rngred_rspec_split_la s) fE.
  Proof.
    move=> fE Hwf. rewrite well_formed_rngred_rspec_split_la_ra.
    exact: well_formed_qfbv_rngred_rspec.
  Qed.


  (* Apply to a sequence of rspec *)

  Definition rngred_rspec_split_las (rs : seq rspec) : seq QFBV.bexp :=
    tflatten (tmap rngred_rspec_split_la rs).

  Lemma rngred_rspec_split_las_cons r rs :
    rngred_rspec_split_las (r::rs) = rngred_rspec_split_las rs ++ rev (rngred_rspec_split_la r).
  Proof.
    rewrite /rngred_rspec_split_las. rewrite !tmap_map /=. rewrite tflatten_cons.
    reflexivity.
  Qed.

  Lemma rngred_rspec_split_las_eval rs s :
    eval_bexps (rngred_rspec_split_las rs) s <->
      (forall r, In r rs -> eval_bexps (rngred_rspec_split_la r) s).
  Proof.
    elim: rs => [| r rs [IH1 IH2]] //=. rewrite rngred_rspec_split_las_cons.
    rewrite eval_bexps_cat eval_bexps_rev. split.
    - move/andP => [H1 H2] t [] Hin.
      + subst. assumption.
      + exact: (IH1 H1 _ Hin).
    - move=> H. apply/andP; split.
      + apply: IH2. move=> t Hin. apply: H. by right.
      + apply: H. by left.
  Qed.

  Lemma rngred_rspec_split_las_valid fE rs :
    valid_bexps fE (rngred_rspec_split_las rs) <->
      (forall r, In r rs -> valid_bexps fE (rngred_rspec_split_la r)).
  Proof.
    elim: rs => [| r rs [IH1 IH2]] //=. rewrite rngred_rspec_split_las_cons.
    rewrite valid_bexps_cat. rewrite valid_bexps_rev. split.
    - move=> [Hrs Hr] t [] Hin.
      + subst. assumption.
      + exact: (IH1 Hrs _ Hin).
    - move=> H. split.
      + apply: IH2. move=> t Hin. apply: H. by right.
      + apply: H. by left.
  Qed.

  Lemma rngred_rspec_split_las_well_formed fE rs :
    (forall r, In r rs -> MA.agree (vars_bexps (rngred_rspec_split_la r))
                            fE (program_succ_typenv (rsprog r) (rsinputs r))) ->
    (forall r, In r rs -> well_formed_ssa_rspec r) ->
    well_formed_bexps (rngred_rspec_split_las rs) fE.
  Proof.
    elim: rs => [| r rs IH] //=. move=> Hag Hwf.
    rewrite rngred_rspec_split_las_cons well_formed_bexps_cat well_formed_bexps_rev.
    apply/andP; split.
    - apply: IH.
      + move=> t Hin. apply: Hag. by right.
      + move=> t Hin. apply: Hwf. by right.
    - rewrite (@agree_well_formed_bexps fE (program_succ_typenv (rsprog r) (rsinputs r))).
      + apply: well_formed_qfbv_rngred_rspec_split_la. apply: Hwf. by left.
      + apply: Hag. by left.
  Qed.

End RngredSplitLeftAssoc.

(* Some properties about [tmap slice_rspec (split_rspec s)] *)

  Lemma slice_rspec_split_rspec_valid s :
    valid_rspecs (tmap slice_rspec (split_rspec s)) -> valid_rspec s.
  Proof.
    rewrite tmap_map. move=> H. apply/split_rspec_correct. case: s H => [E f p g].
    elim: g => //=.
    - rewrite /valid_rspecs /=. move=> H s [] //=. move=> ?; subst.
      apply: slice_rspec_sound. apply: H. left. reflexivity.
    - move=> n e1 e2. rewrite /valid_rspecs /=. move=> H s [] //=. move=> ?; subst.
      apply: slice_rspec_sound. apply: H. left. reflexivity.
    - move=> n op e1 e2. rewrite /valid_rspecs /=. move=> H s [] //=. move=> ?; subst.
      apply: slice_rspec_sound. apply: H. left. reflexivity.
    - move=> e IH. rewrite /valid_rspecs /=. move=> H s [] //=. move=> ?; subst.
      apply: slice_rspec_sound. apply: H. left. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite /valid_rspecs /=. rewrite !split_rspec_rand.
      move=> H s Hin. rewrite map_cat in H. case: (in_cat Hin) => {}Hin.
      + apply: slice_rspec_sound. apply: H. apply: in_cat_l. apply: in_map. exact: Hin.
      + apply: slice_rspec_sound. apply: H. apply: in_cat_r. apply: in_map. exact: Hin.
    - move=> e1 IH1 e2 IH2. rewrite /valid_rspecs /=. move=> H s [] //=. move=> ?; subst.
      apply: slice_rspec_sound. apply: H. left. reflexivity.
  Qed.

  Lemma slice_rspec_split_rspec_well_formed s :
    well_formed_rspec s ->
    (forall t, In t (tmap slice_rspec (split_rspec s)) -> well_formed_rspec t).
  Proof.
    move=> Hwf t Hint. move/split_rspec_well_formed_rspec : Hwf => Hwf.
    rewrite tmap_map in Hint. move: (in_map_exists Hint) => [y [Hiny ->]].
    exact: (well_formed_rspec_slice_rspec (Hwf _ Hiny)).
  Qed.

  Lemma slice_rspec_split_rspec_well_formed_ssa s :
    well_formed_ssa_rspec s ->
    (forall t, In t (tmap slice_rspec (split_rspec s)) -> well_formed_ssa_rspec t).
  Proof.
    move=> Hwf t Hint. move/split_rspec_well_formed_ssa: Hwf => Hwf.
    rewrite tmap_map in Hint. move: (in_map_exists Hint) => [y [Hiny ->]].
    apply: well_formed_ssa_rspec_slice_rspec. exact: (Hwf y Hiny).
  Qed.

  Lemma slice_rspec_split_rspec_agree s r :
    In r (tmap slice_rspec (split_rspec s)) ->
    MA.agree (vars_bexps (rngred_rspec_split_la r)) (program_succ_typenv (rsprog s) (rsinputs s))
      (program_succ_typenv (rsprog r) (rsinputs r)).
  Proof.
    rewrite tmap_map => Hin. move: (in_map_exists Hin) => [y [Hiny ->]].
    rewrite -(split_rspec_rsprog Hiny) -(split_rspec_rsinputs Hiny). clear Hin Hiny r s.
    case: y => [E f p g] /=.
    apply: (@MA.subset_set_agree _ _ (depvars_rpre_rprogram_sat f p (vars_rbexp g))).
    - apply: (SSAVS.Lemmas.subset_trans
                (vars_rngred_rspec_split_la
                   (slice_rspec {| rsinputs := E; rspre := f; rsprog := p; rspost := g |}))).
      exact: (slice_rspec_subset {| rsinputs := E; rspre := f; rsprog := p; rspost := g |}).
    - apply: slice_rprogram_succ_typenv.
      exact: depvars_rpre_rprogram_sat_partition2.
  Qed.


(** Range reduction version 3:
    slice range specification, split range conditions, and apply qfbv_conjs_la *)

Section RngredSlicing.

  Import QFBV.

  Definition rngred_rspec_slice_split_la (s : rspec) : seq QFBV.bexp :=
    rngred_rspec_split_las (tmap slice_rspec (SSA.split_rspec s)).

  Definition valid_rngred_rspec_slice_split_la (s : rspec) :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    valid_bexps fE (rngred_rspec_slice_split_la s).

  Lemma rngred_rspec_split_la_valid_rspecs fE rs :
    (forall r, In r rs -> MA.agree
                            (vars_bexps (rngred_rspec_split_la r))
                            fE (program_succ_typenv (rsprog r) (rsinputs r))) ->
    (forall r, In r rs -> well_formed_ssa_rspec r) ->
    (forall r, In r rs -> valid_bexps fE (rngred_rspec_split_la r)) ->
    valid_rspecs rs.
  Proof.
    move=> Hag Hwf Hva. move=> s Hin. apply: rngred_rspec_split_la_sound.
    - exact: (Hwf _ Hin).
    - rewrite /valid_rngred_rspec_split_la. move: (Hva _ Hin).
      rewrite (agree_valid_bexps (Hag _ Hin)). by apply.
  Qed.

  Lemma valid_rngred_rspec_slice_split_la_split_la s :
    is_rng_rspec s -> well_formed_ssa_rspec s ->
    valid_rngred_rspec_slice_split_la s ->
    valid_rngred_rspec_split_la s.
  Proof.
    move=> Hrng Hwf /rngred_rspec_split_las_valid Hv.
    apply: (rngred_rspec_split_la_complete Hrng Hwf).
    apply: slice_rspec_split_rspec_valid.
    apply: (rngred_rspec_split_la_valid_rspecs _ _ Hv).
    - move=> r Hinr. exact: (slice_rspec_split_rspec_agree Hinr).
    - exact: (slice_rspec_split_rspec_well_formed_ssa Hwf).
  Qed.

  Theorem rngred_rspec_slice_split_la_sound s :
    is_rng_rspec s -> well_formed_ssa_rspec s ->
    valid_rngred_rspec_slice_split_la s ->
    valid_rspec s.
  Proof.
    move=> Hrng Hwf Hv. apply: (rngred_rspec_sound Hwf).
    apply/rngred_rspec_split_la_valid.
    exact: (valid_rngred_rspec_slice_split_la_split_la Hrng Hwf Hv).
  Qed.

  Lemma rngred_rspec_slice_split_la_well_formed s :
    well_formed_ssa_rspec s ->
    QFBV.well_formed_bexps (rngred_rspec_slice_split_la s)
      (program_succ_typenv (rsprog s) (rsinputs s)).
  Proof.
    move=> Hwf. rewrite /rngred_rspec_slice_split_la.
    apply: rngred_rspec_split_las_well_formed.
    - exact: slice_rspec_split_rspec_agree.
    - exact: (slice_rspec_split_rspec_well_formed_ssa Hwf).
  Qed.

End RngredSlicing.


(* Define the safety condition in terms of a QFBV expression *)

Section AlgsndInstr.

  Definition bexp_atom_uaddB_algsnd a1 a2 : QFBV.bexp :=
    qfbv_lneg (qfbv_uaddo (qfbv_atom a1) (qfbv_atom a2)).

  Definition bexp_atom_saddB_algsnd a1 a2 : QFBV.bexp :=
    qfbv_lneg (qfbv_saddo (qfbv_atom a1) (qfbv_atom a2)).

  Definition bexp_atom_addB_algsnd E a1 a2 : QFBV.bexp :=
    let 'a_typ := atyp a1 E in
    if Typ.is_unsigned a_typ then bexp_atom_uaddB_algsnd a1 a2
    else bexp_atom_saddB_algsnd a1 a2.

  Definition bexp_atom_adds_algsnd E a1 a2 : QFBV.bexp :=
    let 'a_typ := atyp a1 E in
    if Typ.is_unsigned a_typ then QFBV.Btrue
    else bexp_atom_saddB_algsnd a1 a2.

  Definition bexp_atom_uadcB_algsnd a_size a1 a2 ac : QFBV.bexp :=
    qfbv_conj
      (qfbv_lneg
         (qfbv_uaddo (qfbv_atom a1)
            (qfbv_atom a2)))
      (qfbv_lneg
         (qfbv_uaddo (qfbv_add (qfbv_atom a1)
                        (qfbv_atom a2))
            (qfbv_zext (a_size - 1) (qfbv_atom ac)))).

  Definition bexp_atom_sadcB_algsnd a_size a1 a2 ac : QFBV.bexp :=
    qfbv_conj
      (qfbv_lneg
         (qfbv_saddo (qfbv_atom a1)
            (qfbv_atom a2)))
      (qfbv_lneg
         (qfbv_saddo (qfbv_add (qfbv_atom a1)
                        (qfbv_atom a2))
            (qfbv_zext (a_size - 1) (qfbv_atom ac)))).

  Definition bexp_atom_adcB_algsnd E a1 a2 ac : QFBV.bexp :=
    let a_typ := atyp a1 E in
    let a_size := asize a1 E in
    if Typ.is_unsigned a_typ then bexp_atom_uadcB_algsnd a_size a1 a2 ac
    else bexp_atom_sadcB_algsnd a_size a1 a2 ac.

  Definition bexp_atom_adcs_algsnd E a1 a2 ac : QFBV.bexp :=
    let a_typ := atyp a1 E in
    let a_size := asize a1 E in
    if Typ.is_unsigned a_typ then QFBV.Btrue
    else bexp_atom_sadcB_algsnd a_size a1 a2 ac.

  Definition bexp_atom_usubB_algsnd a1 a2 : QFBV.bexp :=
    qfbv_lneg (qfbv_usubo (qfbv_atom a1) (qfbv_atom a2)).

  Definition bexp_atom_ssubB_algsnd a1 a2 : QFBV.bexp :=
    qfbv_lneg (qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2)).

  Definition bexp_atom_subB_algsnd E a1 a2 : QFBV.bexp :=
    let 'a_typ := atyp a1 E in
    if Typ.is_unsigned a_typ then bexp_atom_usubB_algsnd a1 a2
    else bexp_atom_ssubB_algsnd a1 a2.

  Definition bexp_atom_subc_algsnd E a1 a2 : QFBV.bexp :=
    let 'a_typ := atyp a1 E in
    if Typ.is_unsigned a_typ then QFBV.Btrue
    else bexp_atom_ssubB_algsnd a1 a2.

  Definition bexp_atom_subb_algsnd E a1 a2 : QFBV.bexp :=
    let 'a_typ := atyp a1 E in
    if Typ.is_unsigned a_typ then QFBV.Btrue
    else bexp_atom_ssubB_algsnd a1 a2.

  Definition bexp_atom_usbbB_algsnd a_size a1 a2 ab : QFBV.bexp :=
    qfbv_conj
      (qfbv_lneg
         (qfbv_usubo (qfbv_atom a1)
            (qfbv_atom a2)))
      (qfbv_lneg
         (qfbv_usubo (qfbv_sub (qfbv_atom a1)
                        (qfbv_atom a2))
            (qfbv_zext (a_size - 1) (qfbv_atom ab)))).

  Definition bexp_atom_ssbbB_algsnd a_size a1 a2 ab : QFBV.bexp :=
    qfbv_conj
      (qfbv_lneg
         (qfbv_ssubo (qfbv_atom a1)
            (qfbv_atom a2)))
      (qfbv_lneg
         (qfbv_ssubo (qfbv_sub (qfbv_atom a1)
                        (qfbv_atom a2))
            (qfbv_zext (a_size - 1) (qfbv_atom ab)))).

  Definition bexp_atom_sbbB_algsnd E a1 a2 ab : QFBV.bexp :=
    let a_typ := atyp a1 E in
    let a_size := asize a1 E in
    if Typ.is_unsigned a_typ then bexp_atom_usbbB_algsnd a_size a1 a2 ab
    else bexp_atom_ssbbB_algsnd a_size a1 a2 ab.

  Definition bexp_atom_sbbs_algsnd E a1 a2 ab : QFBV.bexp :=
    let a_typ := atyp a1 E in
    let a_size := asize a1 E in
    if Typ.is_unsigned a_typ then QFBV.Btrue
    else bexp_atom_ssbbB_algsnd a_size a1 a2 ab.

  Definition bexp_atom_usbcB_algsnd a_size a1 a2 ac : QFBV.bexp :=
    qfbv_conj
      (qfbv_lneg
         (qfbv_usubo (qfbv_atom a1)
            (qfbv_atom a2)))
      (qfbv_lneg
         (qfbv_usubo (qfbv_sub (qfbv_atom a1)
                        (qfbv_atom a2))
            (qfbv_zext (a_size - 1)
               (qfbv_sub (qfbv_one 1) (qfbv_atom ac))))).

  Definition bexp_atom_ssbcB_algsnd a_size a1 a2 ac : QFBV.bexp :=
    qfbv_conj
      (qfbv_lneg
         (qfbv_ssubo (qfbv_atom a1)
            (qfbv_atom a2)))
      (qfbv_lneg
         (qfbv_ssubo (qfbv_sub (qfbv_atom a1)
                        (qfbv_atom a2))
            (qfbv_zext (a_size - 1)
               (qfbv_sub (qfbv_one 1) (qfbv_atom ac))))).

  Definition bexp_atom_sbcB_algsnd E a1 a2 ac : QFBV.bexp :=
    let a_typ := atyp a1 E in
    let a_size := asize a1 E in
    if Typ.is_unsigned a_typ then bexp_atom_usbcB_algsnd a_size a1 a2 ac
    else bexp_atom_ssbcB_algsnd a_size a1 a2 ac.

  Definition bexp_atom_sbcs_algsnd E a1 a2 ac : QFBV.bexp :=
    let a_typ := atyp a1 E in
    let a_size := asize a1 E in
    if Typ.is_unsigned a_typ then QFBV.Btrue
    else bexp_atom_ssbcB_algsnd a_size a1 a2 ac.

  Definition bexp_atom_mulB_algsnd E a1 a2 : QFBV.bexp :=
    let 'a_typ := atyp a1 E in
    if Typ.is_unsigned a_typ then
      qfbv_lneg (qfbv_umulo (qfbv_atom a1)
                   (qfbv_atom a2))
    else
      qfbv_lneg (qfbv_smulo (qfbv_atom a1)
                   (qfbv_atom a2)).

  Definition bexp_atom_shl_algsnd E a n : QFBV.bexp :=
    let 'a_typ := atyp a E in
    if Typ.is_unsigned a_typ then
      qfbv_eq (qfbv_high n (qfbv_atom a))
        (qfbv_zero n)
    else
      qfbv_disj (qfbv_eq (qfbv_high (n + 1) (qfbv_atom a))
                   (qfbv_zero (n + 1)))
        (qfbv_eq (qfbv_high (n + 1) (qfbv_atom a))
           (qfbv_not (qfbv_zero (n + 1)))).

  Definition bexp_atom_cshl_algsnd E (a1 : atom) a2 n  : QFBV.bexp :=
    let 'concatbv := qfbv_concat (qfbv_atom a1) (qfbv_atom a2) in
    if Typ.is_unsigned (atyp a1 E) then
      qfbv_eq (qfbv_high n concatbv) (qfbv_zero n)
    else
      qfbv_disj (qfbv_eq (qfbv_high (n + 1) concatbv)
                   (qfbv_zero (n + 1)))
        (qfbv_eq (qfbv_high (n + 1) concatbv)
           (qfbv_not (qfbv_zero (n + 1)))).

  Definition bexp_atom_vpc_algsnd E t a : QFBV.bexp :=
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
               (qfbv_atom a))
            (qfbv_zero (Typ.sizeof_typ a_typ - Typ.sizeof_typ t))
      else
        if Typ.sizeof_typ a_typ < Typ.sizeof_typ t then
          qfbv_true
        else
          qfbv_eq
            (qfbv_high (Typ.sizeof_typ a_typ - Typ.sizeof_typ t + 1)
               (qfbv_atom a))
            (qfbv_zero (Typ.sizeof_typ a_typ - Typ.sizeof_typ t + 1))
    else
      if Typ.is_unsigned t then
        if Typ.sizeof_typ a_typ - 1 <= Typ.sizeof_typ t then
          qfbv_eq
            (qfbv_high 1 (qfbv_atom a))
            (qfbv_zero 1)
        else
          qfbv_eq
            (qfbv_high (Typ.sizeof_typ a_typ - Typ.sizeof_typ t)
               (qfbv_atom a))
            (qfbv_zero (Typ.sizeof_typ a_typ - Typ.sizeof_typ t))
      else
        if Typ.sizeof_typ a_typ <= Typ.sizeof_typ t then
          qfbv_true
        else
          qfbv_eq
            (qfbv_sext (Typ.sizeof_typ a_typ - Typ.sizeof_typ t)
               (qfbv_low (Typ.sizeof_typ t) (qfbv_atom a)))
            (qfbv_atom a).

  Definition bexp_instr_algsnd E (i : instr) : QFBV.bexp :=
    match i with
    | Iadd _ a1 a2 =>
        bexp_atom_addB_algsnd E a1 a2
    | Iadds _ _ a1 a2 =>
        bexp_atom_adds_algsnd E a1 a2
    | Iadc _ a1 a2 ac =>
        bexp_atom_adcB_algsnd E a1 a2 ac
    | Iadcs _ _ a1 a2 ac =>
        bexp_atom_adcs_algsnd E a1 a2 ac
    | Isub _ a1 a2 =>
        bexp_atom_subB_algsnd E a1 a2
    | Isubc _ _ a1 a2 =>
        bexp_atom_subc_algsnd E a1 a2
    | Isubb _ _ a1 a2 =>
        bexp_atom_subb_algsnd E a1 a2
    | Isbc _ a1 a2 ac =>
        bexp_atom_sbcB_algsnd E a1 a2 ac
    | Isbcs _ _ a1 a2 ac =>
        bexp_atom_sbcs_algsnd E a1 a2 ac
    | Isbb _ a1 a2 ab =>
        bexp_atom_sbbB_algsnd E a1 a2 ab
    | Isbbs _ _ a1 a2 ab =>
        bexp_atom_sbbs_algsnd E a1 a2 ab
    | Imul _ a1 a2 =>
        bexp_atom_mulB_algsnd E a1 a2
    | Ishl v a n =>
        bexp_atom_shl_algsnd E a n
    | Icshl h l a1 a2 n =>
        bexp_atom_cshl_algsnd E a1 a2 n
    | Ivpc _ t a =>
        bexp_atom_vpc_algsnd E t a
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

  Lemma eval_bexp_atom_addB_algsnd E a1 a2 s :
    QFBV.eval_bexp (bexp_atom_addB_algsnd E a1 a2) s <->
      addB_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s).
  Proof.
    case Ht : (Typ.is_unsigned (atyp a1 E));
      rewrite /bexp_atom_addB_algsnd /addB_algsnd Ht /=.
    - by rewrite /uaddB_algsnd /= !eval_exp_atom.
    - by rewrite /saddB_algsnd /= !eval_exp_atom.
  Qed.

  Lemma eval_bexp_atom_adds_algsnd E a1 a2 s :
    QFBV.eval_bexp (bexp_atom_adds_algsnd E a1 a2) s <->
      adds_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s).
  Proof.
    rewrite /bexp_atom_adds_algsnd /adds_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)) => //=.
    rewrite /saddB_algsnd !eval_exp_atom. done.
  Qed.

  Lemma eval_bexp_atom_adcB_algsnd E a1 a2 ac s :
    SSAStore.conform s E ->
    SSAVS.subset (vars_atom a1) (vars_env E) ->
    size_matched_atom a1 ->
    QFBV.eval_bexp (bexp_atom_adcB_algsnd E a1 a2 ac) s <->
      adcB_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s).
  Proof.
    move=> Hco Hsub Hsm. rewrite /bexp_atom_adcB_algsnd /adcB_algsnd /=.
    case: (Typ.is_unsigned (atyp a1 E)).
    - of_asize. by rewrite /uadcB_algsnd /= !eval_exp_atom.
    - of_asize. by rewrite /sadcB_algsnd /= !eval_exp_atom.
  Qed.

  Lemma eval_bexp_atom_adcs_algsnd E a1 a2 ac s :
    SSAStore.conform s E ->
    SSAVS.subset (vars_atom a1) (vars_env E) ->
    size_matched_atom a1 ->
    QFBV.eval_bexp (bexp_atom_adcs_algsnd E a1 a2 ac) s <->
      adcs_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s).
  Proof.
    move=> Hco Hsub Hsm. rewrite /bexp_atom_adcs_algsnd /adcs_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)) => //=.
    rewrite /sadcB_algsnd !eval_exp_atom. of_asize. done.
  Qed.

  Lemma eval_bexp_atom_subB_algsnd E a1 a2 s :
    QFBV.eval_bexp (bexp_atom_subB_algsnd E a1 a2) s <->
      subB_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s).
  Proof.
    case Ht : (Typ.is_unsigned (atyp a1 E));
      rewrite /bexp_atom_subB_algsnd /subB_algsnd Ht /=.
    - by rewrite /usubB_algsnd /= !eval_exp_atom.
    - by rewrite /ssubB_algsnd /= !eval_exp_atom.
  Qed.

  Lemma eval_bexp_atom_subc_algsnd E a1 a2 s :
    QFBV.eval_bexp (bexp_atom_subc_algsnd E a1 a2) s <->
      subc_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s).
  Proof.
    rewrite /bexp_atom_subc_algsnd /subc_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)) => //=.
    rewrite /ssubB_algsnd !eval_exp_atom. done.
  Qed.

  Lemma eval_bexp_atom_subb_algsnd E a1 a2 s :
    QFBV.eval_bexp (bexp_atom_subb_algsnd E a1 a2) s <->
      subb_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s).
  Proof.
    rewrite /bexp_atom_subb_algsnd /subb_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)) => //=.
    rewrite /ssubB_algsnd !eval_exp_atom. done.
  Qed.

  Lemma eval_bexp_atom_sbbB_algsnd E a1 a2 ac s :
    SSAStore.conform s E ->
    SSAVS.subset (vars_atom a1) (vars_env E) ->
    size_matched_atom a1 ->
    QFBV.eval_bexp (bexp_atom_sbbB_algsnd E a1 a2 ac) s <->
      sbbB_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s).
  Proof.
    move=> Hco Hsub Hsm. rewrite /bexp_atom_sbbB_algsnd /sbbB_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)).
    - rewrite /usbbB_algsnd /= !eval_exp_atom. of_asize. done.
    - rewrite /ssbbB_algsnd /= !eval_exp_atom. of_asize. done.
  Qed.

  Lemma eval_bexp_atom_sbbs_algsnd E a1 a2 ac s :
    SSAStore.conform s E ->
    SSAVS.subset (vars_atom a1) (vars_env E) ->
    size_matched_atom a1 ->
    QFBV.eval_bexp (bexp_atom_sbbs_algsnd E a1 a2 ac) s <->
      sbbs_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s).
  Proof.
    move=> Hco Hsub Hsm. rewrite /bexp_atom_sbbs_algsnd /sbbs_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)) => //=.
    rewrite /ssbcB_algsnd !eval_exp_atom. of_asize. done.
  Qed.

  Lemma eval_bexp_atom_sbcB_algsnd E a1 a2 ac s :
    SSAStore.conform s E ->
    SSAVS.subset (vars_atom a1) (vars_env E) ->
    size_matched_atom a1 ->
    QFBV.eval_bexp (bexp_atom_sbcB_algsnd E a1 a2 ac) s <->
      sbcB_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s).
  Proof.
    move=> Hco Hsub Hsm. rewrite /bexp_atom_sbcB_algsnd /sbcB_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)).
    - rewrite /usbcB_algsnd /= !eval_exp_atom. of_asize. done.
    - rewrite /ssbcB_algsnd /= !eval_exp_atom. of_asize. done.
  Qed.

  Lemma eval_bexp_atom_sbcs_algsnd E a1 a2 ac s :
    SSAStore.conform s E ->
    SSAVS.subset (vars_atom a1) (vars_env E) ->
    size_matched_atom a1 ->
    QFBV.eval_bexp (bexp_atom_sbcs_algsnd E a1 a2 ac) s <->
      sbcs_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s).
  Proof.
    move=> Hco Hsub Hsm. rewrite /bexp_atom_sbcs_algsnd /sbcs_algsnd.
    case: (Typ.is_unsigned (atyp a1 E)) => //=.
    rewrite /ssbcB_algsnd !eval_exp_atom. of_asize. done.
  Qed.

  Lemma eval_bexp_atom_mulB_algsnd E a1 a2 s :
    QFBV.eval_bexp (bexp_atom_mulB_algsnd E a1 a2) s <->
      mulB_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s).
  Proof.
    rewrite /bexp_atom_mulB_algsnd /mulB_algsnd. case: (Typ.is_unsigned (atyp a1 E)).
    - by rewrite /umulB_algsnd /= !eval_exp_atom.
    - by rewrite /smulB_algsnd /= !eval_exp_atom.
  Qed.

  Lemma eval_bexp_atom_shl_algsnd E a n s :
    QFBV.eval_bexp (bexp_atom_shl_algsnd E a n) s <->
      shlBn_algsnd (atyp a E) (eval_atom a s) n.
  Proof.
    rewrite /bexp_atom_shl_algsnd /shlBn_algsnd
      /ushlBn_algsnd /sshlBn_algsnd /=.
    case Ht : (Typ.is_unsigned (atyp a E)) => /=.
    - by rewrite !eval_exp_atom zeros_from_nat.
    - by rewrite !eval_exp_atom zeros_from_nat
         -zeros_from_nat invB_zeros.
  Qed.

  Lemma eval_bexp_atom_cshl_algsnd E a1 a2 n s :
    QFBV.eval_bexp (bexp_atom_cshl_algsnd E a1 a2 n) s <->
      cshlBn_algsnd (atyp a1 E) (eval_atom a1 s) (eval_atom a2 s) n.
  Proof.
    rewrite /bexp_atom_cshl_algsnd /cshlBn_algsnd
      /ucshlBn_algsnd /scshlBn_algsnd
      /ushlBn_algsnd /sshlBn_algsnd /=.
    case : (Typ.is_unsigned (atyp a1 E)).
    - by rewrite /= -!zeros_from_nat !eval_exp_atom.
    - by rewrite /= -!zeros_from_nat !eval_exp_atom !invB_zeros.
  Qed.

  Lemma eval_bexp_atom_vpc_algsnd E a t s :
    QFBV.eval_bexp (bexp_atom_vpc_algsnd E t a) s <->
      vpc_algsnd t (atyp a E) (eval_atom a s).
  Proof.
    rewrite /bexp_atom_vpc_algsnd /vpc_algsnd.
    case : (Typ.is_unsigned (atyp a E));
      case : (Typ.is_unsigned t).
    - case : (Typ.sizeof_typ (atyp a E) <= Typ.sizeof_typ t) => /=.
      + done.
      + rewrite -zeros_from_nat !eval_exp_atom //.
    - case : (Typ.sizeof_typ (atyp a E) < Typ.sizeof_typ t) => /=.
      + done.
      + rewrite -zeros_from_nat !eval_exp_atom //.
    - case : (Typ.sizeof_typ (atyp a E) - 1 <= Typ.sizeof_typ t) => /=.
      + rewrite !eval_exp_atom //.
      + rewrite -zeros_from_nat !eval_exp_atom //.
    - case : (Typ.sizeof_typ (atyp a E) <= Typ.sizeof_typ t) => /=.
      + done.
      + rewrite !eval_exp_atom //.
  Qed.

  Lemma eval_bexp_instr_algsnd E i s :
    SSAStore.conform s E ->
    well_formed_instr E i ->
    (QFBV.eval_bexp (bexp_instr_algsnd E i) s <-> ssa_instr_algsnd_at E i s).
  Proof.
    move=> Hco. case i => //=.
    - move => v a n Hwf. exact: eval_bexp_atom_shl_algsnd.
    - move => h l a1 a2 n Hwf. exact: eval_bexp_atom_cshl_algsnd.
    - move => v a1 a2 Hwf. exact: eval_bexp_atom_addB_algsnd.
    - move => c v a1 a2 Hwf. exact: eval_bexp_atom_adds_algsnd.
    - move=> v a1 a2 ac Hwf. unfold_well_formed.
      intro_subset_from_are_defined. exact: eval_bexp_atom_adcB_algsnd.
    - move=> c v a1 a2 ac Hwf. unfold_well_formed.
      intro_subset_from_are_defined. exact: eval_bexp_atom_adcs_algsnd.
    - move=> v a1 a2 Hwf. exact: eval_bexp_atom_subB_algsnd.
    - move=> c v a1 a2 Hwf. exact: eval_bexp_atom_subc_algsnd.
    - move=> c v a1 a2 Hwf. exact: eval_bexp_atom_subb_algsnd.
    - move=> v a1 a2 ac Hwf. unfold_well_formed.
      intro_subset_from_are_defined. exact: eval_bexp_atom_sbcB_algsnd.
    - move=> c v a1 a2 ac Hwf. unfold_well_formed.
      intro_subset_from_are_defined. exact: eval_bexp_atom_sbcs_algsnd.
    - move=> v a1 a2 ab Hwf. unfold_well_formed.
      intro_subset_from_are_defined. exact: eval_bexp_atom_sbbB_algsnd.
    - move=> b v a1 a2 ab Hwf. unfold_well_formed.
      intro_subset_from_are_defined. exact: eval_bexp_atom_sbbs_algsnd.
    - move=> v a1 a2 Hwf. exact: eval_bexp_atom_mulB_algsnd.
    - move=> v t a Hwf. exact: eval_bexp_atom_vpc_algsnd.
  Qed.

  Lemma bexp_instr_algsnd_submap E1 E2 i :
    well_defined_instr E1 i -> TELemmas.submap E1 E2 ->
    bexp_instr_algsnd E1 i = bexp_instr_algsnd E2 i.
  Proof.
    rewrite /bexp_instr_algsnd.
    rewrite /bexp_atom_shl_algsnd /bexp_atom_cshl_algsnd
      /bexp_atom_addB_algsnd /bexp_atom_adds_algsnd
      /bexp_atom_adcB_algsnd/bexp_atom_adcs_algsnd
      /bexp_atom_subB_algsnd /bexp_atom_subc_algsnd /bexp_atom_subb_algsnd
      /bexp_atom_sbcB_algsnd /bexp_atom_sbcs_algsnd
      /bexp_atom_sbbB_algsnd /bexp_atom_sbbs_algsnd
      /bexp_atom_mulB_algsnd /bexp_atom_vpc_algsnd
      /bexp_atom_uaddB_algsnd /bexp_atom_saddB_algsnd
      /bexp_atom_uadcB_algsnd /bexp_atom_sadcB_algsnd
      /bexp_atom_usubB_algsnd /bexp_atom_ssubB_algsnd
      /bexp_atom_usbcB_algsnd /bexp_atom_sbcB_algsnd
      /bexp_atom_ssbcB_algsnd
      /bexp_atom_usbbB_algsnd /bexp_atom_ssbbB_algsnd.
    by (case: i => //=); (move=> * );
    repeat (match goal with
            | H : is_true (_ && _) |- _ =>
                let H1 := fresh in
                let H2 := fresh in
                move/andP: H => [H1 H2]
            | H1 : TELemmas.submap ?E1 ?E2,
                H2 : is_true (are_defined (vars_atom ?a) ?E1) |-
                context f [asize ?a ?E2] =>
                rewrite -(asize_submap H1 H2)
            | H1 : TELemmas.submap ?E1 ?E2,
                H2 : is_true (are_defined (vars_atom ?a) ?E1) |-
                context f [atyp ?a ?E2] =>
                rewrite -(atyp_submap H1 H2)
            | |- ?e = ?e => reflexivity
            end).
  Qed.


  (* Well-formedness of bexp_instr_algsnd *)

  Section WellFormedBexpInstrSafe.

    Ltac norm_tac :=
      unfold_well_formed;
      repeat
        match goal with
        | |- context f [if ?c then _ else _] =>
            dcase c; case => /=; intros
        | H : is_true (are_defined (vars_atom ?a) ?E)
          |- context f [QFBV.well_formed_exp (qfbv_atom ?a) ?E] =>
            rewrite (well_formed_qfbv_atom H) /=
        | |- context f [size (_) -bits of (_)%bits] =>
            rewrite size_from_nat /=
        | |- context f [?n == ?n] => rewrite (eqxx n)
        | Hdef : is_true (are_defined (vars_atom ?a) ?E),
            Hsm : is_true (size_matched_atom ?a)
          |- context f [QFBV.exp_size (qfbv_atom ?a) ?E] =>
            rewrite (size_exp_atom Hdef Hsm) /=
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
        | H : is_true (well_sized_atom ?E ?a) |-
            context f [0 < Typ.sizeof_typ (atyp ?a ?E)] =>
            rewrite (well_sized_atom_gt0 H) /=
        | |- context f [0 < _ + _] =>
            rewrite addn_gt0
        | H : is_true (well_sized_atom ?E ?a)
          |- is_true (0 < Typ.sizeof_typ (atyp ?a ?E)) =>
            exact: (well_sized_atom_gt0 H)
        | H : (?n <= ?m) = false |- is_true (?m <= ?n) =>
            move/idP/negP: H; rewrite -ltnNge => H; exact: (ltnW H)
        end.

    Lemma bexp_instr_algsnd_well_formed E i :
      well_formed_instr E i ->
      QFBV.well_formed_bexp (bexp_instr_algsnd E i) E.
    Proof.
      case: i => //=.
      - move=> *. rewrite /bexp_atom_shl_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_cshl_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_addB_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_adds_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_adcB_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_adcs_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_subB_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_subc_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_subb_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_sbcB_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_sbcs_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_sbbB_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_sbbs_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_mulB_algsnd /=. by norm_tac.
      - move=> *. rewrite /bexp_atom_vpc_algsnd /=. by norm_tac.
    Qed.

  End WellFormedBexpInstrSafe.

End AlgsndInstr.


(* Program safety - fixed typing environment - initial typing environment *)

Section SafetyFixedInit.

  Fixpoint bexp_program_algsnd_fixed_init E p : QFBV.bexp :=
    match p with
    | [::] => qfbv_true
    | hd::tl =>
      qfbv_conj (bexp_instr_algsnd E hd)
                (qfbv_disj
                   (qfbv_lneg (bexp_instr E hd))
                   (bexp_program_algsnd_fixed_init (instr_succ_typenv hd E) tl))
    end.

  Lemma eval_bexp_program_algsnd_fixed_init1 E pre p :
    well_formed_rbexp E pre ->
    ssa_vars_unchanged_program (vars_rbexp pre) p ->
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s E ->
               QFBV.eval_bexp (bexp_rbexp pre) s ->
               QFBV.eval_bexp (bexp_program_algsnd_fixed_init E p) s) ->
    (forall s, SSAStore.conform s E ->
               eval_rbexp pre s ->
               ssa_program_algsnd_at E p s).
  Proof.
    move=> Hwf_pre Hun Hwf_p H s.
    have: (forall t : SSAStore.t,
              bvs_eqi E s t ->
              SSAStore.conform t E ->
              QFBV.eval_bexp (bexp_rbexp pre) t ->
              QFBV.eval_bexp (bexp_program_algsnd_fixed_init E p) t).
    { move=> t Heqi Hco Hpre. exact: (H _ Hco Hpre). }
    move: {H} Hwf_pre Hun Hwf_p s.

    elim: p E => [| i p IH] E /=.
    - move=> *. exact: ssa_program_algsnd_at_nil.
    - rewrite ssa_unchanged_program_cons /well_formed_ssa_program.
      rewrite well_formed_program_cons ssa_single_assignment_cons.
      rewrite ssa_unchanged_program_cons.
      move=> Hwf_pre
               /andP [Hun_prei Hun_prep] /andP [
                 /andP [/andP [Hwf_i Hwf_p]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
      move=> s H Hco Hpre. apply: ssa_program_algsnd_at_cons.
      + move/eval_bexp_rbexp: Hpre => Hpre.
        apply/(eval_bexp_instr_algsnd Hco Hwf_i).
        move: (H s (bvs_eqi_refl s) Hco Hpre) => /andP [H1 _].
        exact: H1.
      + move=> t Hei.
        have Hssa_p: well_formed_ssa_program (instr_succ_typenv i E) p.
        { repeat (apply/andP; split); try assumption.
          apply: (ssa_unchanged_program_replace
                    (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          rewrite ssa_unchanged_program_union. rewrite Hun_Ep /=. exact: Hun_ip. }

        move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsubm.
        move: (bvs_eqi_eval_instr Hun_Ei Hei) => Hei_st.
        move: (well_formed_rbexp_submap Hsubm Hwf_pre) => Hwf_pre_succ.

        apply: (IH (instr_succ_typenv i E) Hwf_pre_succ Hun_prep Hssa_p).
        * move=> t' Heqi Hco' Hpre'.
          have Heqi': bvs_eqi E s t'.
          { move: (bvs_eqi_submap Hsubm Heqi) => Hei_st'.
            exact: (bvs_eqi_trans Hei_st Hei_st'). }
          move: (bvs_eqi_conform Heqi' Hco) => Hco'E.
          move: (H _ Heqi' Hco'E Hpre') => /andP [H1 H2].

          move: (bexp_instr_eval Hwf_i Hco Hun_Ei Hei).
          move/andP: Hwf_i => [Hwd_i Hwt_i].
          rewrite (bvs_eqi_qfbv_eval_bexp (bexp_instr_are_defined Hwd_i) Heqi).
          move=> Heb. rewrite Heb /= in H2. exact: H2.
        * exact: (conform_instr_succ_typenv Hwf_i Hco Hei).
        * apply/(ssa_unchanged_instr_eval_rbexp Hun_prei Hei). exact: Hpre.
  Qed.


  (* Soundness of bexp_program_algsnd_fixed. *)

  Definition ssa_spec_algsnd_qfbv_fixed_init sp : Prop :=
    forall s,
      SSAStore.conform s (rsinputs sp) ->
      QFBV.eval_bexp (bexp_rbexp (rspre sp)) s ->
      QFBV.eval_bexp (bexp_program_algsnd_fixed_init (rsinputs sp) (rsprog sp)) s.

  Lemma ssa_spec_algsnd_qfbv_sound sp :
    well_formed_ssa_rspec sp -> ssa_spec_algsnd_qfbv_fixed_init sp ->
    ssa_spec_algsnd sp.
  Proof.
    case: sp => E f p g. rewrite /well_formed_ssa_rspec /well_formed_rspec
                                 /ssa_spec_algsnd_qfbv_fixed_init /ssa_spec_algsnd /=.
    move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
            Hbv s Hco Hf.

    move/andP: (Hwf_f) => [Hdef_f _]. move/defsubP: Hdef_f => Hsub_f.
    move: (ssa_unchanged_program_subset Hun_Ep Hsub_f) => Hun_f.
    apply: (eval_bexp_program_algsnd_fixed_init1 Hwf_f Hun_f _ Hbv Hco Hf).
    rewrite /well_formed_ssa_program.
    by rewrite Hwf_p Hun_Ep Hssa.
  Qed.

End SafetyFixedInit.


(* Program safety - varying typing environment *)

Section SafetyVarying.

  (* Evaluate safety conditions one by one.
   Typing environments are different for the safety conditions of
   different instructions. *)
  Fixpoint bexp_program_algsnd_steps E p s : Prop :=
    SSAStore.conform s E ->
    match p with
    | [::] => True
    | hd::tl =>
      QFBV.eval_bexp (bexp_instr_algsnd E hd) s /\
      ((QFBV.eval_bexp (bexp_instr E hd) s) ->
       (bexp_program_algsnd_steps (instr_succ_typenv hd E) tl s))
    end.

  Lemma eval_bexp_program_algsnd_steps E pre p :
    well_formed_rbexp E pre ->
    ssa_vars_unchanged_program (vars_rbexp pre) p ->
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp pre) s ->
               bexp_program_algsnd_steps E p s) ->
    (forall s, SSAStore.conform s E ->
               eval_rbexp pre s ->
               ssa_program_algsnd_at E p s).
  Proof.
    move=> Hwf_pre Hun Hwf_p H s.
    have: (forall t : SSAStore.t,
              bvs_eqi E s t ->
              QFBV.eval_bexp (bexp_rbexp pre) t ->
              bexp_program_algsnd_steps E p t).
    { move=> t Heqi Hpre. exact: (H _ Hpre). }
    move: {H} Hwf_pre Hun Hwf_p s.

    elim: p E => [| i p IH] E /=.
    - move=> *. exact: ssa_program_algsnd_at_nil.
    - rewrite ssa_unchanged_program_cons /well_formed_ssa_program.
      rewrite well_formed_program_cons ssa_single_assignment_cons.
      rewrite ssa_unchanged_program_cons.
      move=> Hwf_pre /andP [Hun_prei Hun_prep] /andP [
                       /andP [/andP [Hwf_i Hwf_p] /andP
                               [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
      move=> s H Hco Hpre. apply: ssa_program_algsnd_at_cons.
      + move/eval_bexp_rbexp: Hpre => Hpre. apply/(eval_bexp_instr_algsnd Hco Hwf_i).
        move: (H s (bvs_eqi_refl s) Hpre Hco) => [H1 _]. exact: H1.
      + move=> t Hei. have Hssa_p: well_formed_ssa_program (instr_succ_typenv i E) p.
        { repeat (apply/andP; split); try assumption.
          apply: (ssa_unchanged_program_replace
                    (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          rewrite ssa_unchanged_program_union. rewrite Hun_Ep /=. exact: Hun_ip. }

        move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsubm.
        move: (bvs_eqi_eval_instr Hun_Ei Hei) => Hei_st.
        move: (well_formed_rbexp_submap Hsubm Hwf_pre) => Hwf_pre_succ.

        apply: (IH (instr_succ_typenv i E) Hwf_pre_succ Hun_prep Hssa_p).
        * move=> t' Heqi Hpre'.
          have Heqi': bvs_eqi E s t'.
          { move: (bvs_eqi_submap Hsubm Heqi) => Hei_st'.
            exact: (bvs_eqi_trans Hei_st Hei_st'). }
          move: (bvs_eqi_conform Heqi' Hco) => Hco'E.
          move: (H _ Heqi' Hpre' Hco'E) => [H1 H2].

          move: (bexp_instr_eval Hwf_i Hco Hun_Ei Hei).
          move/andP: Hwf_i => [Hwd_i Hwt_i].
          rewrite (bvs_eqi_qfbv_eval_bexp (bexp_instr_are_defined Hwd_i) Heqi).
          move=> Heb. rewrite Heb /= in H2. by apply: H2.
        * exact: (conform_instr_succ_typenv Hwf_i Hco Hei).
        * apply/(ssa_unchanged_instr_eval_rbexp Hun_prei Hei). exact: Hpre.
  Qed.


  (* Soundness and completeness of bexp_program_algsnd_steps. *)

  Definition ssa_spec_algsnd_qfbv_steps (sp : rspec) : Prop :=
    forall s, QFBV.eval_bexp (bexp_rbexp (rspre sp)) s ->
              bexp_program_algsnd_steps (rsinputs sp) (rsprog sp) s.

  Lemma ssa_spec_algsnd_qfbv_steps_sound sp :
    well_formed_ssa_rspec sp -> ssa_spec_algsnd_qfbv_steps sp -> ssa_spec_algsnd sp.
  Proof.
    case: sp => E f p g. rewrite /well_formed_ssa_rspec /well_formed_rspec
                                 /ssa_spec_algsnd /ssa_spec_algsnd_qfbv_steps /=.
    move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
            /= Hbv s Hco Hf.

    move: (Hwf_f). move/andP=> [Hdef_f _]. move/defsubP: Hdef_f => Hsub_f.
    move: (ssa_unchanged_program_subset Hun_Ep Hsub_f) => Hun_f.

    apply: (eval_bexp_program_algsnd_steps Hwf_f Hun_f _ Hbv Hco Hf).
    rewrite /well_formed_ssa_program. by rewrite Hwf_p Hun_Ep Hssa.
  Qed.

  Lemma ssa_spec_algsnd_qfbv_steps_complete sp :
    is_rng_rspec sp ->
    well_formed_ssa_rspec sp -> ssa_spec_algsnd sp -> ssa_spec_algsnd_qfbv_steps sp.
  Proof.
    case: sp => E f p g.
    rewrite /is_rng_rspec /well_formed_ssa_rspec /well_formed_rspec
            /ssa_spec_algsnd /ssa_spec_algsnd_qfbv_steps /=.
    move=> Hrng /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
                Hsafe s Hf.
    clear g Hwf_g. move: (Hsafe s) => {Hsafe} Hsafe.
    elim: p E f Hrng Hwf_f Hwf_p Hun_Ep Hssa s Hsafe Hf => [| i p IH] //=.
    move=> E f /andP [Hrng_i Hrng_p] Hwf /andP [Hwf_i Hwf_p] Hun_Eip /andP [Hun_ip Hssa_p]
             s Hsafe Hf Hco.
    rewrite ssa_unchanged_program_cons in Hun_Eip.
    move/andP: Hun_Eip => [Hun_Ei Hun_Ep].
    move: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei) => Hsubm.
    move/eval_bexp_rbexp: Hf=> Hf. move: (Hsafe Hco Hf) => Hsafe_at.
    inversion_clear Hsafe_at. split.
    - apply/(eval_bexp_instr_algsnd Hco Hwf_i). assumption.
    - move=> His. apply: (IH (instr_succ_typenv i E) f Hrng_p
                             (well_formed_rbexp_submap Hsubm Hwf) Hwf_p
                             _ Hssa_p).
      + apply: (ssa_unchanged_program_replace
                  (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
        rewrite ssa_unchanged_program_union Hun_Ep Hun_ip. exact: is_true_true.
      + move=> Hco_s Hf_s. apply: H0.
        exact: (eval_bexp_instr Hrng_i Hwf_i Hco Hco_s His).
      + apply/eval_bexp_rbexp. exact: Hf.
  Qed.

End SafetyVarying.


Section SafetySplitConditionsVarying.

  Import QFBV.

  (* Construct safety conditions (full prefix information). *)

  (*
   * E: the typing environment after pre_is and before p
   * pre_is: the prefix of instructions
   * pre_es: the QFBV expressions encoding the prefix of instructions
   * p: the remaining program to be converted
   *)
  Fixpoint bexp_program_algsnd_split_full_rec E pre_is (pre_es : seq QFBV.bexp) p :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (E, pre_is, pre_es, hd, tl, bexp_instr_algsnd E hd)
        ::(bexp_program_algsnd_split_full_rec
             (instr_succ_typenv hd E) (rcons pre_is hd)
             (rcons pre_es (bexp_instr E hd)) tl)
    end.

  Definition bexp_program_algsnd_split_full E p :=
    bexp_program_algsnd_split_full_rec E [::] [::] p.

  Lemma bexp_program_algsnd_split_full_rec_env E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full_rec E pre_is pre_es p) ->
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

  Lemma bexp_program_algsnd_split_full_rec_submap E pre_is pre_es p :
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p ->
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full_rec E pre_is pre_es p) ->
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

  Lemma bexp_program_algsnd_split_full_rec_is E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full_rec E pre_is pre_es p) ->
      pre_is' ++ hd::tl = pre_is ++ p.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. reflexivity.
    - move=> Hin. rewrite -(cat_rcons i). apply: IH. exact: Hin.
  Qed.

  Lemma bexp_program_algsnd_split_full_rec_is_prefix E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full_rec E pre_is pre_es p) ->
      exists suf, pre_is' = pre_is ++ suf.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. move=> _. exists [::]. rewrite cats0. reflexivity.
    - move=> Hin. move: (IH _ _ _ _ _ _ _ _ _ Hin) => [suf H]. exists (i::suf).
      rewrite -(cat_rcons). assumption.
  Qed.

  Lemma bexp_program_algsnd_split_full_rec_es E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full_rec E pre_is pre_es p) ->
      forall Einit,
        E = program_succ_typenv pre_is Einit ->
        pre_es = bexp_program Einit pre_is ->
        pre_es' = bexp_program Einit pre_is'.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. move=> _ Einit _. by apply.
    - move=> Hin Einit Hinit H. apply: (IH _ _ _ _ _ _ _ _ _ Hin).
      + rewrite program_succ_typenv_rcons. rewrite -Hinit. reflexivity.
      + rewrite bexp_program_rcons. rewrite -H. rewrite -Hinit. reflexivity.
  Qed.

  Lemma bexp_program_algsnd_split_full_rec_cover E pre_is pre_es p :
    forall pre_is' hd tl suf,
      pre_is' = pre_is ++ suf ->
      pre_is' ++ (hd :: tl) = pre_is ++ p ->
      exists E' pre_es' safe,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_algsnd_split_full_rec E pre_is pre_es p).
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
        exists E. exists pre_es. exists (bexp_instr_algsnd E i1). left. reflexivity.
      + move=> suf_i suf_p Heq1 Heq2 Heq3. case: Heq3 => Heq Heq3.
        rewrite Heq in Heq1.
        rewrite -!cat_rcons in Heq1. rewrite -(cat_rcons i1) in Heq2.

        move: (IH (instr_succ_typenv i1 E) (rcons pre_is i1)
                  (rcons pre_es (bexp_instr E i1)) pre_is' hd tl suf_p
                  Heq1 Heq2). move=> [E' [pre_es' [safe' Hin]]].
        exists E'. exists pre_es'. exists safe'. right. exact: Hin.
  Qed.

  Lemma bexp_program_algsnd_split_full_env E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full E p) ->
      E' = program_succ_typenv pre_is' E.
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    apply: (bexp_program_algsnd_split_full_rec_env Hin). reflexivity.
  Qed.

  Lemma bexp_program_algsnd_split_full_submap E p :
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p ->
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full E p) ->
      TELemmas.submap E E'.
  Proof.
    move=> Hun Hssa E' pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_algsnd_split_full_rec_submap Hun Hssa Hin).
  Qed.

  Lemma bexp_program_algsnd_split_full_is E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full E p) ->
      pre_is' ++ (hd::tl) = p.
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_algsnd_split_full_rec_is Hin).
  Qed.

  Lemma bexp_program_algsnd_split_full_es E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full E p) ->
      pre_es' = bexp_program E pre_is'.
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
      by apply: (bexp_program_algsnd_split_full_rec_es Hin).
  Qed.

  Lemma bexp_program_algsnd_split_full_cover E p :
    forall pre_is' hd tl,
      pre_is' ++ (hd :: tl) = p ->
      exists E' pre_es' safe,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_algsnd_split_full E p).
  Proof.
    move=> pre_is' hd tl Heq. apply: bexp_program_algsnd_split_full_rec_cover.
    - rewrite cat0s. reflexivity.
    - rewrite cat0s. assumption.
  Qed.

  Lemma bexp_program_algsnd_split_full_steps E f p :
    well_formed_ssa_program E p ->
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_algsnd_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s).
  Proof.
    rewrite /bexp_program_algsnd_split_full. move=> Hwf He s.
    have: QFBV.eval_bexp (qfbv_conjs [::]) s by done.
    move: s He. move: [::]. move: [::].
    elim: p E f Hwf => [| i p IH] E f Hwf pre_es pre_is s //= He Hprefix Hf Hco.
    split.
    - move: (He E pre_is pre_es i p (bexp_instr_algsnd E i)
                (or_introl _ (Logic.eq_refl
                                (E, pre_is, pre_es, i, p, bexp_instr_algsnd E i)))
                s Hco).
      rewrite negb_and Hf Hprefix /=. by apply.
    - move=> His. move: (well_formed_ssa_tl Hwf) => Hwf_p.
      apply: (IH (instr_succ_typenv i E) f Hwf_p
                 (rcons pre_es (bexp_instr E i)) (rcons pre_is i)).
      + move=> E_t pre_is_t pre_es_t i_t p_t safe_t Hin_t t Hco_t.
        apply: (He E_t pre_is_t pre_es_t i_t p_t safe_t _ t Hco_t).
        right. assumption.
      + rewrite eval_qfbv_conjs_rcons. rewrite Hprefix His. exact: is_true_true.
      + exact: Hf.
  Qed.

  Lemma bexp_program_algsnd_steps_split_full E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s) ->
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_algsnd_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    rewrite /bexp_program_algsnd_split_full. move=> Hwf Hsteps.
    move=> Ee pre_is pre_es hd tl safe Hin s Hco /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hpre_es: (eval_bexp (qfbv_conjs pre_es) s) => //=.
    (* Make the precondition weaker. *)
    have: forall t : SSAStore.t,
        bvs_eqi E s t ->
        eval_bexp (qfbv_conjs (bexp_program E [::])) t ->
        eval_bexp (bexp_rbexp f) t -> bexp_program_algsnd_steps E p t
        by intros; apply: Hsteps.
    move: Ee pre_is pre_es hd tl safe Hin s Hco Hf Hpre_es.
    have: E = program_succ_typenv [::] E by done.
    have: [::] = bexp_program E [::] by done.
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
      rewrite -(bexp_program_submap Hwf_Einit_pre_is' Hsub_Einit). exact: Hpre_es'.
    - move=> Hin.
      apply: (IH (instr_succ_typenv i E) f
                 (rcons pre_es (bexp_instr E i))
                 (rcons pre_is i) _ _ _ _ _ _ _ _ _ _ Hin _ Hco Hf Hpre_es').
      + exact: (well_formed_ssa_tl Hwf).
      + rewrite cat_rcons. exact: Hwf_init.
      + rewrite bexp_program_rcons. rewrite -Hpre -HE. reflexivity.
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

        move: (bexp_program_algsnd_split_full_rec_env Hin HiE) => {HiE} HE'.
        move: (bvs_eqi_submap Hsub_E Heqi) => Heqi_Est.

        have Hsub_iEE': TELemmas.submap (instr_succ_typenv i E) E'.
        { apply: (bexp_program_algsnd_split_full_rec_submap _ Hssa_p Hin).
          apply: (ssa_unchanged_program_replace
                    (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          rewrite ssa_unchanged_program_union. by rewrite Hun_Ep Hun_ip. }

        have Hco_t: (SSAStore.conform t E).
        { move: (TELemmas.submap_trans Hsub_E Hsub_iEE') => Hsub_EE'.
          apply: (bvs_eqi_conform Heqi_Est).
          exact: (SSAStore.conform_submap Hsub_EE' Hco). }

        move: (He t Heqi_Est Heval_pre_is_t Ht_f Hco_t) => [H1 H2].
        apply: H2. rewrite HE.

        move: (TELemmas.submap_trans Hsub_Einit Hsub_E) => Hsub_Einit_iE.
        move: (submap_program_succ_typenv
                 Hwf_Einit_pre_is' Hsub_Einit_iE) => Hsub_succ.
        move/andP: Hwf_i => [Hwd_i Hwt_i]. rewrite HE in Hwd_i.
        rewrite (bexp_instr_submap Hwd_i Hsub_succ). exact: Heval_i_t.
  Qed.


  (* Well-formedness of bexp_program_algsnd_split_full *)

  Lemma bexp_program_algsnd_split_full_algsnd_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_is pre_es hd tl safe,
      List.In (Ee, pre_is, pre_es, hd, tl, safe)
              (bexp_program_algsnd_split_full E p) ->
      QFBV.well_formed_bexp safe Ee.
  Proof.
    rewrite /bexp_program_algsnd_split_full. move: [::]. move: [::].
    elim: p E => [| i p IH] E //= pre_es pre_is Hwf E' pre_is' pre_es' hd tl safe.
    case => Hin.
    - case: Hin=> ? ? ? ? ? ?; subst. apply: bexp_instr_algsnd_well_formed.
      exact: (well_formed_ssa_hd Hwf).
    - exact: (IH _ _ _ (well_formed_ssa_tl Hwf) _ _ _ _ _ _ Hin).
  Qed.

  Lemma bexp_program_algsnd_split_full_pre_es_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_is pre_es hd tl safe,
      List.In (Ee, pre_is, pre_es, hd, tl, safe)
              (bexp_program_algsnd_split_full E p) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) Ee.
  Proof.
    rewrite /bexp_program_algsnd_split_full.
    have: QFBV.well_formed_bexp (qfbv_conjs [::]) E by done.
    move: [::]. move: [::].
    elim: p E => [| i p IH] E //= pre_es pre_is Hwf_pre_es
                            Hwf E' pre_is' pre_es' hd tl safe.
    case=> Hin.
    - case: Hin => ? ? ? ? ? ?; subst. exact: Hwf_pre_es.
    - apply: (IH _ _ _ _ (well_formed_ssa_tl Hwf) _ _ _ _ _ _ Hin).
      rewrite well_formed_bexp_qfbv_conjs_rcons.
      move/andP: Hwf. rewrite well_formed_program_cons.
      rewrite ssa_unchanged_program_cons. rewrite ssa_single_assignment_cons.
      move=> [/andP [/andP [Hwf_i Hwf_iEp] /andP [Hun_Ei Hun_Ep]]
               /andP [Hun_ip Hssa_p]]. apply/andP; split.
      + apply: (well_formed_bexp_submap _ Hwf_pre_es).
        exact: (ssa_unchanged_instr_succ_typenv_submap Hun_Ei).
      + exact: (well_formed_bexp_instr Hun_Ei).
  Qed.


  (* Verify safety conditions one by one (full prefix information). *)

  Fixpoint bexp_program_algsnd_split_full_checker_rec
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
      bexp_program_algsnd_split_full_checker_rec bexp_f rs
    end.

  Definition bexp_program_algsnd_split_full_checker E f p :=
    bexp_program_algsnd_split_full_checker_rec (bexp_rbexp f)
                                             (bexp_program_algsnd_split_full E p).

  Lemma bexp_program_algsnd_split_full_checker_split_full E f p :
    bexp_program_algsnd_split_full_checker E f p ->
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_algsnd_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    rewrite /bexp_program_algsnd_split_full_checker.
    rewrite /bexp_program_algsnd_split_full.
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

  Lemma bexp_program_algsnd_split_full_split_full_checker E f p :
    (forall Ee pre_is pre_es hd tl safe,
        List.In (Ee, pre_is, pre_es, hd, tl, safe)
                (bexp_program_algsnd_split_full E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    bexp_program_algsnd_split_full_checker E f p.
  Proof.
    rewrite /bexp_program_algsnd_split_full_checker.
    rewrite /bexp_program_algsnd_split_full.
    move: [::]. move: [::].
    elim: p f E => [| i p IH] //= f E pre_es pre_is H. split.
    - move=> s Hco. apply: (H _ _ _ _ _ _ _ s Hco). left. reflexivity.
    - apply: IH. move=> E' pre_is' pre_es' hd tl safe Hin s Hco.
      apply: (H _ _ _ _ _ _ _ s Hco). right. exact: Hin.
  Qed.

  Lemma bexp_program_algsnd_split_full_checker_steps E f p :
    well_formed_ssa_program E p ->
    bexp_program_algsnd_split_full_checker E f p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s).
  Proof.
    move=> Hwf Hch. apply: (bexp_program_algsnd_split_full_steps Hwf).
    exact: (bexp_program_algsnd_split_full_checker_split_full Hch).
  Qed.

  Lemma bexp_program_algsnd_steps_split_full_checker E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s) ->
    bexp_program_algsnd_split_full_checker E f p.
  Proof.
    move=> Hwf H. apply: bexp_program_algsnd_split_full_split_full_checker.
    exact: (bexp_program_algsnd_steps_split_full Hwf H).
  Qed.


  (* Construct safety conditions with less prefix information. *)

  Fixpoint bexp_program_algsnd_split_rec E (pre_es : seq QFBV.bexp) p :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (E, pre_es, bexp_instr_algsnd E hd)
        ::(bexp_program_algsnd_split_rec
             (instr_succ_typenv hd E) (rcons pre_es (bexp_instr E hd)) tl)
    end.

  Definition bexp_program_algsnd_split E p := bexp_program_algsnd_split_rec E [::] p.

  Lemma bexp_program_algsnd_split_rec_full_partial E pre_is pre_es p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full_rec E pre_is pre_es p) ->
      List.In (E', pre_es', safe) (bexp_program_algsnd_split_rec E pre_es p).
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ? ?; subst. left. reflexivity.
    - move=> Hin. right. exact: (IH _ _ _ _ _ _ _ _ _ Hin).
  Qed.

  Lemma bexp_program_algsnd_split_rec_partial_full Einit E pre_is pre_es p :
    forall E' pre_es' safe,
      List.In (E', pre_es', safe) (bexp_program_algsnd_split_rec E pre_es p) ->
      E = program_succ_typenv pre_is Einit ->
      pre_es = bexp_program Einit pre_is ->
    exists pre_is' hd tl,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full_rec E pre_is pre_es p) /\
      (pre_is' ++ (hd :: tl) = pre_is ++ p) /\
      (pre_es' = bexp_program Einit pre_is').
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> E' pre_es' safe. case.
    - case=> ? ? ?; subst. move=> _ Hes'. exists pre_is. exists i. exists p.
      repeat split.
      + left. reflexivity.
      + assumption.
    - move=> Hin HE Hes. move: (IH _ (rcons pre_is i) _ _ _ _ Hin).
      rewrite program_succ_typenv_rcons -HE.
      rewrite bexp_program_rcons -Hes. rewrite -HE.
      move=> H. move: (H (Logic.eq_refl _) (Logic.eq_refl _)) => {H}.
      move=> [pre_is' [hd [tl [Hin' [His' Hes']]]]].
      exists pre_is'; exists hd; exists tl. repeat split.
      + right. assumption.
      + rewrite His'. rewrite cat_rcons. reflexivity.
      + assumption.
  Qed.

  Lemma bexp_program_algsnd_split_full_partial E p :
    forall E' pre_is' pre_es' hd tl safe,
      List.In (E', pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_full E p) ->
      List.In (E', pre_es', safe) (bexp_program_algsnd_split E p).
  Proof.
    move=> E' pre_is' pre_es' hd tl safe Hin.
    apply: bexp_program_algsnd_split_rec_full_partial. exact: Hin.
  Qed.

  Lemma bexp_program_algsnd_split_partial_full E p :
    forall E' pre_es' safe,
      List.In (E', pre_es', safe) (bexp_program_algsnd_split E p) ->
      exists pre_is' hd tl,
        List.In (E', pre_is', pre_es', hd, tl, safe)
                (bexp_program_algsnd_split_full E p) /\
        (pre_is' ++ (hd :: tl) = p) /\
        (pre_es' = bexp_program E pre_is').
  Proof.
    move=> E' pre_es' safe Hin.
    by apply: (bexp_program_algsnd_split_rec_partial_full Hin).
  Qed.

  Lemma bexp_program_algsnd_split_steps E f p :
    well_formed_ssa_program E p ->
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe) (bexp_program_algsnd_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s).
  Proof.
    move=> Hwf He. apply: (bexp_program_algsnd_split_full_steps Hwf).
    move=> Ee pre_is pre_es hd tl safe Hin s Hco. apply: (He _ _ _ _ _ Hco).
    exact: (bexp_program_algsnd_split_full_partial Hin).
  Qed.

  Lemma bexp_program_algsnd_steps_split E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s) ->
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe) (bexp_program_algsnd_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    move=> Hwf H. move=> Ee pre_es safe Hin s Hco.
    move: (bexp_program_algsnd_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin_full [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_algsnd_steps_split_full Hwf H Hin_full Hco).
  Qed.


  (* Well-formedness of bexp_program_algsnd_split *)

  Lemma bexp_program_algsnd_split_algsnd_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_es safe,
      List.In (Ee, pre_es, safe) (bexp_program_algsnd_split E p) ->
      QFBV.well_formed_bexp safe Ee.
  Proof.
    move=> Hwf Ee pre_es safe Hin.
    move: (bexp_program_algsnd_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_algsnd_split_full_algsnd_well_formed Hwf Hin').
  Qed.

  Lemma bexp_program_algsnd_split_pre_es_well_formed E p :
    well_formed_ssa_program E p ->
    forall Ee pre_es safe,
      List.In (Ee, pre_es, safe) (bexp_program_algsnd_split E p) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) Ee.
  Proof.
    move=> Hwf Ee pre_es safe Hin.
    move: (bexp_program_algsnd_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_algsnd_split_full_pre_es_well_formed Hwf Hin').
  Qed.

  Theorem bexp_program_algsnd_split_cond_well_formed E f p :
    well_formed_rbexp E f ->
    well_formed_ssa_program E p ->
    forall Ee pre_es safe,
      List.In (Ee, pre_es, safe) (bexp_program_algsnd_split E p) ->
      QFBV.well_formed_bexp
        (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es)) safe) Ee.
  Proof.
    move=> Hwf_f Hwf_p Ee pre_es safe Hin /=.
    move: (bexp_program_algsnd_split_partial_full Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    move/andP: (Hwf_p) => [/andP [Hwf Hun] Hssa].
    move: (bexp_program_algsnd_split_full_submap Hun Hssa Hin') => Hsub.
    move: (well_formed_bexp_rbexp Hwf_f) => Hwf_Ee.
    rewrite (well_formed_bexp_submap Hsub Hwf_Ee) andTb.
    rewrite (bexp_program_algsnd_split_full_pre_es_well_formed Hwf_p Hin') andTb.
    exact: (bexp_program_algsnd_split_full_algsnd_well_formed Hwf_p Hin').
  Qed.


  (* Verify safety conditions one by one (less prefix information). *)

  Fixpoint bexp_program_algsnd_split_checker_rec
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
      bexp_program_algsnd_split_checker_rec bexp_f rs
    end.

  Definition bexp_program_algsnd_split_checker E f p :=
    bexp_program_algsnd_split_checker_rec (bexp_rbexp f)
                                        (bexp_program_algsnd_split E p).

  Lemma bexp_program_algsnd_split_checker_split E f p :
    bexp_program_algsnd_split_checker E f p ->
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe)
                (bexp_program_algsnd_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s).
  Proof.
    rewrite /bexp_program_algsnd_split_checker.
    rewrite /bexp_program_algsnd_split. move: [::].
    elim: p f E => [| i p IH] //= f E pre_es [Hch1 Hch2] E' pre_es' safe Hin s Hco.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hpre_es': (eval_bexp (qfbv_conjs pre_es') s) => //=.
    case: Hin => Hin.
    - case: Hin=> ? ? ?; subst. move: (Hch1 s Hco).
      rewrite Hf Hpre_es' /=. by apply.
    - move: (IH f (instr_succ_typenv i E) _ Hch2 E' pre_es' safe
                Hin s Hco) => /=. rewrite Hf Hpre_es' /=. by apply.
  Qed.

  Lemma bexp_program_algsnd_split_split_checker E f p :
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe)
                (bexp_program_algsnd_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                   safe) s) ->
    bexp_program_algsnd_split_checker E f p.
  Proof.
    rewrite /bexp_program_algsnd_split_checker.
    rewrite /bexp_program_algsnd_split. move: [::].
    elim: p f E => [| i p IH] //= f E pre_es H. split.
    - move=> s Hco. apply: (H _ _ _ _ s Hco). left. reflexivity.
    - apply: IH. move=> E' pre_es' safe Hin s Hco.
      apply: (H _ _ _ _ s Hco). right. exact: Hin.
  Qed.

  Lemma bexp_program_algsnd_split_checker_steps E f p :
    well_formed_ssa_program E p ->
    bexp_program_algsnd_split_checker E f p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s).
  Proof.
    move=> Hwf Hch. apply: (bexp_program_algsnd_split_steps Hwf).
    exact: (bexp_program_algsnd_split_checker_split Hch).
  Qed.

  Lemma bexp_program_algsnd_steps_split_checker E f p :
    well_formed_ssa_program E p ->
    (forall s, QFBV.eval_bexp (bexp_rbexp f) s ->
               bexp_program_algsnd_steps E p s) ->
    bexp_program_algsnd_split_checker E f p.
  Proof.
    move=> Hwf H. apply: bexp_program_algsnd_split_split_checker.
    exact: (bexp_program_algsnd_steps_split Hwf H).
  Qed.


  (** Soundness and completeness *)

  Definition ssa_spec_algsnd_split (sp : rspec) :=
    let E := rsinputs sp in
    let f := bexp_rbexp (rspre sp) in
    let p := rsprog sp in
    (forall Ee pre_es safe,
        List.In (Ee, pre_es, safe) (bexp_program_algsnd_split E p) ->
        forall s,
          SSAStore.conform s Ee ->
          QFBV.eval_bexp (qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe) s).

  Theorem ssa_spec_algsnd_split_sound sp :
    well_formed_ssa_rspec sp -> ssa_spec_algsnd_split sp -> ssa_spec_algsnd sp.
  Proof.
    move=> Hwf Hsp. apply: (ssa_spec_algsnd_qfbv_steps_sound Hwf).
    move: (well_formed_ssa_rspec_program Hwf) => Hwfp.
    apply: (bexp_program_algsnd_split_steps Hwfp). exact: Hsp.
  Qed.

  Theorem ssa_spec_algsnd_split_complete sp :
    is_rng_rspec sp -> well_formed_ssa_rspec sp -> ssa_spec_algsnd sp ->
    ssa_spec_algsnd_split sp.
  Proof.
    move=> Hrng Hwf Hsp. move: (well_formed_ssa_rspec_program Hwf) => Hwfp.
    apply: (bexp_program_algsnd_steps_split Hwfp).
    exact: (ssa_spec_algsnd_qfbv_steps_complete Hrng Hwf Hsp).
  Qed.

  Definition ssa_spec_algsnd_split_checker (sp : rspec) :=
    let E := rsinputs sp in
    let f := bexp_rbexp (rspre sp) in
    let p := rsprog sp in
    bexp_program_algsnd_split_checker_rec f
                                          (bexp_program_algsnd_split E p).

  Theorem ssa_spec_algsnd_split_checker_sound sp :
    well_formed_ssa_rspec sp ->
    ssa_spec_algsnd_split_checker sp -> ssa_spec_algsnd sp.
  Proof.
    move=> Hwf Hsp. apply: (ssa_spec_algsnd_split_sound Hwf).
    exact: (bexp_program_algsnd_split_checker_split Hsp).
  Qed.

  Theorem ssa_spec_algsnd_split_checker_complete sp :
    is_rng_rspec sp -> well_formed_ssa_rspec sp ->
    ssa_spec_algsnd sp -> ssa_spec_algsnd_split_checker sp.
  Proof.
    move=> Hrng Hwf Hsp. apply: (bexp_program_algsnd_split_split_checker ).
    exact: (ssa_spec_algsnd_split_complete Hrng Hwf Hsp).
  Qed.

End SafetySplitConditionsVarying.


(** Program safety - fixed typing environment - final typing environment *)

Section SafetyFixedFinal.

  Import QFBV.

  (* use the final typing environment *)
  Fixpoint bexp_program_algsnd_fixed_final E p : QFBV.bexp :=
    match p with
    | [::] => qfbv_true
    | hd::tl =>
      qfbv_conj (bexp_instr_algsnd E hd)
                (qfbv_imp
                   (bexp_instr E hd)
                   (bexp_program_algsnd_fixed_final E tl))
    end.

  Lemma eval_bexp_program_algsnd_fixed_final1 E pre p :
    let fE := (program_succ_typenv p E) in
    well_formed_rbexp E pre ->
    ssa_vars_unchanged_program (vars_rbexp pre) p ->
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp pre) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s) ->
    (forall s, SSAStore.conform s fE ->
               eval_rbexp pre s ->
               ssa_program_algsnd_at fE p s).
  Proof.
    move=> fE Hwf_pre Hun Hwf_p H s.
    have: (forall t : SSAStore.t,
              bvs_eqi E s t ->
              SSAStore.conform t fE ->
              eval_bexp (bexp_rbexp pre) t ->
              eval_bexp (bexp_program_algsnd_fixed_final fE p) t).
    { move=> t Heqi Hco Hpre. exact: (H _ Hco Hpre). }
    move: {H} Hwf_pre Hun Hwf_p s. rewrite /fE. clear fE.
    elim: p E => [| i p IH] E /=.
    - move=> *. exact: ssa_program_algsnd_at_nil.
    - rewrite ssa_unchanged_program_cons /well_formed_ssa_program.
      rewrite well_formed_program_cons ssa_single_assignment_cons.
      rewrite ssa_unchanged_program_cons.
      move=> Hwf_pre
               /andP [Hun_prei Hun_prep] /andP [
                 /andP [/andP [Hwf_i Hwf_p]
                         /andP [Hun_Ei Hun_Ep]] /andP [Hun_ip Hssa]].
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
      apply: ssa_program_algsnd_at_cons.
      + move/eval_bexp_rbexp: Hpre => Hpre.
        apply/(eval_bexp_instr_algsnd
                 Hco (well_formed_instr_submap Hwf_i Hsub_EpiE)).
        move: (H s (bvs_eqi_refl s) Hco Hpre) => /andP [H1 _].
        move/andP: Hwf_i => [Hwd_i Hwt_i]. exact: H1.
      + move=> t Hei. move/andP: (Hwf_i) => [Hwd_Ei Hwt_Ei].
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
        apply/(ssa_program_algsnd_at_submap
                 _ Hsub (well_formed_program_submap Hwf_p Hsub_iEpiE)).
        move/(submap_eval_instr _ _ Hsub_EpiE Hwd_Ei): (Hei) => Hei_Est.
        move: (bvs_eqi_eval_instr Hun_Ei Hei_Est) => Heqi_Est.
        apply: (IH _ (well_formed_rbexp_submap Hsub_EiE Hwf_pre) Hun_prep Hssa_p).
        * move=> t' Heqi_tt' Hco_t' Hpre_t'.
          move: (bvs_eqi_submap Hsub_EiE Heqi_tt') => Heqi_Ett'.
          move: (H _ (bvs_eqi_trans Heqi_Est Heqi_Ett') Hco_t' Hpre_t').
          move/andP=> [_ Hevb].
          move: (bexp_instr_eval Hwf_i Hco_E Hun_Ei Hei_Est) => Hevb_t.
          rewrite (bvs_eqi_qfbv_eval_bexp
                     (bexp_instr_are_defined Hwd_Ei) Heqi_tt') in Hevb_t.
          rewrite (bexp_instr_submap Hwd_Ei Hsub_EpiE) in Hevb_t.
          rewrite Hevb_t /= in Hevb. exact: Hevb.
        * move: (well_formed_instr_submap Hwf_i Hsub_EpiE) => Hwf_piEi.
          move: (conform_instr_succ_typenv Hwf_piEi Hco Hei).
          apply: SSAStore.conform_submap. exact: (SSATE.Lemmas.Equal_submap Heq).
        * move: (bvs_eqi_sym Heqi_Est) => Heqi_Ets.
          move/andP: Hwf_pre => [Hwd_pre Hwt_pre].
          apply/(bvs_eqi_eval_rbexp Hwd_pre Heqi_Ets). exact: Hpre.
  Qed.

  Lemma eval_bexp_program_algsnd_fixed_final2 E pre p :
    let fE := (program_succ_typenv p E) in
    is_rng_program p ->
    well_formed_rbexp E pre ->
    ssa_vars_unchanged_program (vars_rbexp pre) p ->
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_rbexp pre s ->
               ssa_program_algsnd_at fE p s) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp pre) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s).
  Proof.
    move=> fE. rewrite /fE. clear fE.
    move=> Hrng Hwf_Epre Hun_prep Hwf_ssa_Ep Hsafe s.
    have: (forall t,
              bvs_eqi (program_succ_typenv p E) s t ->
              SSAStore.conform t (program_succ_typenv p E) ->
              eval_rbexp pre t -> ssa_program_algsnd_at (program_succ_typenv p E) p t).
    { move=> t Heqi. by apply: Hsafe. }
    move: {Hsafe} Hrng Hwf_Epre Hun_prep Hwf_ssa_Ep s.
    elim: p E pre => [| i p IH] E pre //=.

    move=> /andP [Hrng_i Hrng_p] Hwf_Epre.
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
    inversion_clear Hsafe. apply/andP; split.
    - apply/(eval_bexp_instr_algsnd Hco (well_formed_instr_submap Hwf_Ei Hsub_EpiE)).
      assumption.
    - case Hsafe_i:
        (eval_bexp
           (bexp_instr
              (program_succ_typenv p (instr_succ_typenv i E)) i) s) => //=.
      apply: (IH
                (instr_succ_typenv i E) pre Hrng_p (well_formed_rbexp_submap Hsub_EiE Hwf_Epre)
                Hun_prep Hwf_ssa_p _ _ Hco).
      + move=> t Heqi_ts Hco_t Hpre_t.
        move: (well_formed_program_submap Hwf_iEp Hsub_iEpiE) => Hwf_piEp.
        apply: (bvs_eqi_ssa_program_algsnd_at Heqi_ts Hwf_piEp).
        apply/(ssa_program_algsnd_at_submap
                 _ Hsub (well_formed_program_submap Hwf_iEp Hsub_iEpiE)).
        apply: H0.
        apply: (eval_bexp_instr Hrng_i
                  (well_formed_instr_submap Hwf_Ei Hsub_EpiE) Hco _ Hsafe_i).
        apply: (SSAStore.conform_submap _ Hco).
        apply: TELemmas.Equal_submap. symmetry. exact: Heq.
      + apply/eval_bexp_rbexp. exact: Hpre_s.
  Qed.

  (* Soundness and completeness of bexp_program_algsnd_fixed_final. *)

  Definition ssa_spec_algsnd_qfbv_fixed_final sp : Prop :=
    let fE := program_succ_typenv (rsprog sp) (rsinputs sp) in
    forall s, SSAStore.conform s fE ->
              eval_bexp (bexp_rbexp (rspre sp)) s ->
              eval_bexp (bexp_program_algsnd_fixed_final fE (rsprog sp)) s.

  Lemma ssa_spec_algsnd_qfbv_fixed_final_sound sp :
    well_formed_ssa_rspec sp -> ssa_spec_algsnd_qfbv_fixed_final sp ->
    ssa_spec_algsnd_final sp.
  Proof.
    move=> Hwf. move: Hwf (well_formed_ssa_rspec_program Hwf).
    case: sp => E f p g.
    rewrite /well_formed_ssa_rspec /well_formed_rspec
            /ssa_spec_algsnd_final /ssa_spec_algsnd_qfbv_fixed_final /=.
    move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
            Hwf_ssa_p /= Hbv s Hco Hf.

    move/andP: (Hwf_f)=> [Hdef_f Hwt_f]. move/defsubP: Hdef_f => Hsub_f.
    move: (ssa_unchanged_program_subset Hun_Ep Hsub_f) => Hun_f.

    apply: (eval_bexp_program_algsnd_fixed_final1 Hwf_f Hun_f Hwf_ssa_p _ Hco Hf).
    move=> t Hco_t Hf_t. move: (Hbv _ Hco_t Hf_t). by apply.
  Qed.

  Lemma ssa_spec_algsnd_qfbv_fixed_final_complete sp :
    is_rng_rspec sp ->
    well_formed_ssa_rspec sp -> ssa_spec_algsnd_final sp ->
    ssa_spec_algsnd_qfbv_fixed_final sp.
  Proof.
    move=> Hrng Hwf. move: Hwf (well_formed_ssa_rspec_program Hwf).
    case: sp Hrng => E f p g Hrng.
    rewrite /well_formed_ssa_rspec /well_formed_rspec
            /ssa_spec_algsnd_final /ssa_spec_algsnd_qfbv_fixed_final /=.
    move=> /andP [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hun_Ep] Hssa]
            Hwf_ssa_p /= Hsafe s Hco Hf.

    move/andP: (Hwf_f)=> [Hdef_f Hwt_f]. move/defsubP: Hdef_f => Hsub_f.
    move: (ssa_unchanged_program_subset Hun_Ep Hsub_f) => Hun_f.
    apply: (eval_bexp_program_algsnd_fixed_final2 Hrng Hwf_f Hun_f Hwf_ssa_p _ Hco Hf).
    exact: Hsafe.
  Qed.

End SafetyFixedFinal.


Section SafetySplitConditionsFixedFinal.

  Import QFBV.

  (* Construct safety conditions. *)

  (*
   * E: the final typing environment
   * pre_is: the prefix of instructions
   * pre_es: the QFBV expressions encoding the prefix of instructions
   * p: the remaining program to be converted
   *)
  Fixpoint bexp_program_algsnd_split_fixed_final_full_rec
           E pre_is (pre_es : seq QFBV.bexp) (p : program) :
    seq (seq instr * seq QFBV.bexp * instr * seq instr * QFBV.bexp) :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (pre_is, pre_es, hd, tl, bexp_instr_algsnd E hd)
        ::(bexp_program_algsnd_split_fixed_final_full_rec
             E (rcons pre_is hd)
             (rcons pre_es (bexp_instr E hd)) tl)
    end.

  (*
   * E: the final typing environment
   * p: the remaining program to be converted
   *)
  Definition bexp_program_algsnd_split_fixed_final_full E p :=
    bexp_program_algsnd_split_fixed_final_full_rec E [::] [::] p.

  Lemma bexp_program_algsnd_split_fixed_final_full_rec_is E pre_is pre_es p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full_rec E pre_is pre_es p) ->
      pre_is' ++ hd::tl = pre_is ++ p.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. reflexivity.
    - move=> Hin. rewrite -(cat_rcons i). apply: IH. exact: Hin.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_rec_is_prefix E pre_is pre_es p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full_rec E pre_is pre_es p) ->
      exists suf, pre_is' = pre_is ++ suf.
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. exists [::]. rewrite cats0. reflexivity.
    - move=> Hin. move: (IH _ _ _ _ _ _ _ _ Hin) => [suf H]. exists (i::suf).
      rewrite -(cat_rcons). assumption.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_rec_es E pre_is pre_es p :
    well_formed_program E p ->
    are_defined (lvs_program p) E -> env_unchanged_program E p ->
    are_defined (lvs_program pre_is) E -> env_unchanged_program E pre_is ->
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full_rec E pre_is pre_es p) ->
      pre_es = bexp_program E pre_is ->
      pre_es' = bexp_program E pre_is'.
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
      + rewrite bexp_program_rcons. rewrite -H.
        have ->:
             (bexp_instr E i) = (bexp_instr (program_succ_typenv pre_is E) i).
        { move: (well_formed_instr_well_defined Hwf_Ei) => Hwd_Ei.
          apply: (bexp_instr_submap Hwd_Ei). apply: SSATE.Lemmas.Equal_submap. symmetry.
          exact: (env_unchanged_program_succ_equal Hdef_pre_is Heun_pre_is). }
        reflexivity.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_is E p :
    let fE := program_succ_typenv p E in
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full fE p) ->
      pre_is' ++ (hd::tl) = p.
  Proof.
    move=> fE pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_algsnd_split_fixed_final_full_rec_is Hin).
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_es E p :
    well_formed_program E p ->
    are_defined (lvs_program p) E -> env_unchanged_program E p ->
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full E p) ->
      pre_es' = bexp_program E pre_is'.
  Proof.
    move=> Hwf_Ep Hdef_pE Heun_Ep pre_is' pre_es' hd tl safe Hin.
    exact: (bexp_program_algsnd_split_fixed_final_full_rec_es
              Hwf_Ep Hdef_pE Heun_Ep _ _ Hin).
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_sound E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall pre_is pre_es hd tl safe,
        List.In (pre_is, pre_es, hd, tl, safe)
                (bexp_program_algsnd_split_fixed_final_full fE p) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s).
  Proof.
    rewrite /bexp_program_algsnd_split_fixed_final_full. move=> Hwf He s.
    have: eval_bexp (qfbv_conjs [::]) s by done.
    move: s He. move: [::]. move: [::].
    elim: p E f Hwf => [| i p IH] E f Hwf pre_es pre_is s //= He Hpre_es Hco Hf.
    apply/andP; split.
    - move: (He pre_is pre_es i p
                (bexp_instr_algsnd (program_succ_typenv p (instr_succ_typenv i E)) i)
                (or_introl
                   _
                   (Logic.eq_refl
                      (pre_is, pre_es, i, p,
                       bexp_instr_algsnd (program_succ_typenv
                                          p (instr_succ_typenv i E)) i)))
                s Hco) => /=.
      rewrite negb_and Hf Hpre_es /=. by apply.
    - case His:
        (eval_bexp
           (bexp_instr
              (program_succ_typenv p (instr_succ_typenv i E)) i) s) => //=.
      move: (well_formed_ssa_tl Hwf) => Hwf_p.
      apply: (IH (instr_succ_typenv i E) f Hwf_p
                 (rcons pre_es
                        (bexp_instr
                           (program_succ_typenv p (instr_succ_typenv i E))
                           i)) (rcons pre_is i) _ _ _ Hco).
      + move=> pre_is_t pre_es_t i_t p_t safe_t Hin_t t Hco_t.
        apply: (He pre_is_t pre_es_t i_t p_t safe_t _ t Hco_t).
        right. assumption.
      + rewrite eval_qfbv_conjs_rcons. rewrite Hpre_es His. exact: is_true_true.
      + exact: Hf.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_complete E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s) ->
    (forall pre_is pre_es hd tl safe,
        List.In (pre_is, pre_es, hd, tl, safe)
                (bexp_program_algsnd_split_fixed_final_full fE p) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)).
  Proof.
    move=> fE.
    rewrite /bexp_program_algsnd_split_fixed_final_full. move=> Hwf Hsafe.
    move=> pre_is pre_es hd tl safe Hin s Hco /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hpre_es: (eval_bexp (qfbv_conjs pre_es) s) => //=.
    have: (forall s : SSAStore.t,
              SSAStore.conform s fE ->
              eval_bexp (qfbv_conjs (bexp_program fE [::])) s ->
              eval_bexp (bexp_rbexp f) s ->
              eval_bexp (bexp_program_algsnd_fixed_final fE p) s)
      by intros; apply: Hsafe.
    clear Hsafe.

    have: [::] = bexp_program fE [::] by done.
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
    move: (well_formed_instr_submap
             Hwf_Ei (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE)) => Hwf_piEi.
    case: Hin.

    - case=> ? ? ? ? ?; subst. move: (Hsafe _ Hco Hpre_es' Hf).
      move/andP=> [H1 _]. exact: H1.
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
      + rewrite bexp_program_rcons. rewrite -Hpre_es.
        rewrite -(bexp_instr_equal (well_formed_instr_well_defined Hwf_piEi) Heq).
        reflexivity.
      + move=> t Hco_t Hpre_is_t Hf_t. rewrite bexp_program_rcons in Hpre_is_t.
        rewrite eval_qfbv_conjs_rcons in Hpre_is_t.
        move/andP: Hpre_is_t => [Hpre_is_t Hei_t]. move: (Hsafe t Hco_t Hpre_is_t Hf_t).
        rewrite -(bexp_instr_equal (well_formed_instr_well_defined Hwf_piEi) Heq)
          in Hei_t. rewrite Hei_t /=. move/andP=> [_ H]. exact: H.
  Qed.


  (* Well-formedness of bexp_program_algsnd_split_fixed_final_full *)

  Lemma bexp_program_algsnd_split_fixed_final_full_algsnd_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_is pre_es hd tl safe,
      List.In (pre_is, pre_es, hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full fE p) ->
      QFBV.well_formed_bexp safe fE.
  Proof.
    rewrite /bexp_program_algsnd_split_fixed_final_full. move: [::]. move: [::].
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
    - case: Hin=> ? ? ? ? ?; subst. apply: bexp_instr_algsnd_well_formed.
      apply: (well_formed_instr_submap Hwf_Ei).
      exact: (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE).
    - exact: (IH _ _ _ Hwf_ssa_iEp _ _ _ _ _ Hin).
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_pre_es_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_is pre_es hd tl safe,
      List.In (pre_is, pre_es, hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full fE p) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) fE.
  Proof.
    rewrite /bexp_program_algsnd_split_fixed_final_full.
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
      rewrite well_formed_bexp_qfbv_conjs_rcons. apply/andP; split.
      + exact: (well_formed_bexp_submap _ Hwf_pre_es).
      + move: (well_formed_bexp_instr Hun_Ei Hwf_Ei) => Hwfb.
        rewrite -(bexp_instr_submap (well_formed_instr_well_defined Hwf_Ei)
                                    (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE)).
        exact: (well_formed_bexp_submap Hsub_iEpiE Hwfb).
  Qed.


  (* Construct safety conditions with less prefix information. *)

  (* pre_es: encoding of instructions in QFBV *)
  Fixpoint bexp_program_algsnd_split_fixed_final_rec E (pre_es : seq QFBV.bexp) p :=
    match p with
    | [::] => [::]
    | hd::tl =>
      (pre_es, bexp_instr_algsnd E hd)
        ::(bexp_program_algsnd_split_fixed_final_rec
             E (rcons pre_es (bexp_instr E hd)) tl)
    end.

  Definition bexp_program_algsnd_split_fixed_final E p :=
    bexp_program_algsnd_split_fixed_final_rec E [::] p.

  Lemma bexp_program_algsnd_split_fixed_final_rec_full_partial E pre_is pre_es p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full_rec E pre_is pre_es p) ->
      (pre_es', safe) \in (bexp_program_algsnd_split_fixed_final_rec E pre_es p).
  Proof.
    elim: p E pre_is pre_es => [| i p IH] E pre_is pre_es //=.
    move=> pre_is' pre_es' hd tl safe. case.
    - case=> ? ? ? ? ?; subst. exact: mem_head.
    - move=> Hin. by rewrite in_cons (IH _ _ _ _ _ _ _ _ Hin) orbT.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_rec_partial_full E pre_is pre_es p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    pre_es = bexp_program fE pre_is ->
    are_defined (lvs_program pre_is) fE ->
    env_unchanged_program fE pre_is ->
    forall pre_es' safe,
      ((pre_es', safe) \in (bexp_program_algsnd_split_fixed_final_rec fE pre_es p)) ->
      pre_es = bexp_program fE pre_is ->
    exists pre_is' hd tl,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full_rec fE pre_is pre_es p) /\
      (pre_is' ++ (hd :: tl) = pre_is ++ p) /\
      (pre_es' = bexp_program fE pre_is').
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
    move: (well_formed_instr_submap
             Hwf_Ei (TELemmas.submap_trans Hsub_EiE Hsub_iEpiE)) => Hwf_piEi.

    move=> pre_es' safe. rewrite in_cons. case/orP.
    - case/eqP=> ? ? ?; subst. exists pre_is. exists i. exists p.
      repeat split. left. reflexivity.
    - move=> Hin Hes.

      have Hpre_es_i:
        rcons pre_es
              (bexp_instr
                 (program_succ_typenv p (instr_succ_typenv i E)) i) =
        bexp_program (program_succ_typenv p (instr_succ_typenv i E))
                     (rcons pre_is i).
      { rewrite bexp_program_rcons. rewrite -Hes.
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
                   i))
                Hwf_ssa_iEp Hpre_es_i Hdef_pre_is_i Heun_pre_is_i _ _ Hin Hpre_es_i).
      move=> [pre_is' [hd [tl [Hin' [Hpre_is' Hpre_es']]]]].
      exists pre_is'; exists hd; exists tl. repeat split.
      + right. assumption.
      + rewrite cat_rcons in Hpre_is'. exact: Hpre_is'.
      + exact: Hpre_es'.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_full_partial E p :
    forall pre_is' pre_es' hd tl safe,
      List.In (pre_is', pre_es', hd, tl, safe)
              (bexp_program_algsnd_split_fixed_final_full E p) ->
      (pre_es', safe) \in (bexp_program_algsnd_split_fixed_final E p).
  Proof.
    move=> pre_is' pre_es' hd tl safe Hin.
    apply: bexp_program_algsnd_split_fixed_final_rec_full_partial. exact: Hin.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_partial_full E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_es' safe,
      ((pre_es', safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
      exists pre_is' hd tl,
        List.In (pre_is', pre_es', hd, tl, safe)
                (bexp_program_algsnd_split_fixed_final_full fE p) /\
        (pre_is' ++ (hd :: tl) = p) /\
        (pre_es' = bexp_program fE pre_is').
  Proof.
    move=> fE Hwf_Ep pre_es' safe Hin.
      by apply:
           (bexp_program_algsnd_split_fixed_final_rec_partial_full Hwf_Ep _ _ _ Hin).
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_sound E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s).
  Proof.
    move=> fE Hwf_Ep He.
    apply: (bexp_program_algsnd_split_fixed_final_full_sound Hwf_Ep).
    move=> pre_is pre_es hd tl safe Hin s Hco. apply: (He _ _ _ _ Hco).
    exact: (bexp_program_algsnd_split_fixed_final_full_partial Hin).
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_complete E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s) ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es))
                                safe)).
  Proof.
    move=> fE Hwf H pre_es safe Hin s Hco.
    move: (bexp_program_algsnd_split_fixed_final_partial_full Hwf Hin) =>
    [pre_is [hd [tl [Hin_full [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_algsnd_split_fixed_final_full_complete Hwf H Hin_full Hco).
  Qed.


  (* Well-formedness of bexp_program_algsnd_split *)

  Lemma bexp_program_algsnd_split_fixed_final_algsnd_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp safe fE.
  Proof.
    move=> fE Hwf pre_es safe Hin.
    move: (bexp_program_algsnd_split_fixed_final_partial_full Hwf Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_algsnd_split_fixed_final_full_algsnd_well_formed Hwf Hin').
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_pre_es_well_formed E p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp (qfbv_conjs pre_es) fE.
  Proof.
    move=> FE Hwf pre_es safe Hin.
    move: (bexp_program_algsnd_split_fixed_final_partial_full Hwf Hin) =>
    [pre_is [hd [tl [Hin' [Hpre_is Hpre_es]]]]].
    exact: (bexp_program_algsnd_split_fixed_final_full_pre_es_well_formed Hwf Hin').
  Qed.

  Theorem bexp_program_algsnd_split_fixed_final_cond_well_formed E f p :
    let fE := program_succ_typenv p E in
    well_formed_rbexp E f ->
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp
        (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es)) safe) fE.
  Proof.
    move=> fE Hwf_Ef Hwf_ssa_Ep pre_es safe Hin /=.
    rewrite (bexp_program_algsnd_split_fixed_final_pre_es_well_formed Hwf_ssa_Ep Hin).
    rewrite (bexp_program_algsnd_split_fixed_final_algsnd_well_formed Hwf_ssa_Ep Hin).
    rewrite !andbT.
    move/andP: (Hwf_ssa_Ep) => [/andP [Hwf_Ep Hun_Ep] Hssa_p].
    move: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa_p) => Hsub_EpE.
    move: (well_formed_bexp_rbexp Hwf_Ef) => {Hwf_Ef} Hwf_Ef.
    rewrite (well_formed_bexp_submap Hsub_EpE Hwf_Ef).
    exact: is_true_true.
  Qed.

  (* Construct safety conditions with less prefix information and use qfbv_conjs_la. *)

  Lemma bexp_program_algsnd_split_fixed_final_sound_la E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es))
                                safe)) ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s).
  Proof.
    move=> fE Hwf_Ep He.
    apply: (bexp_program_algsnd_split_fixed_final_sound Hwf_Ep).
    move=> pre_es safe Hin s Hco. move: (He pre_es safe Hin s Hco) => /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hsafe: (eval_bexp safe s) => /=.
    - rewrite !orbT. by apply.
    - rewrite !orbF. move/negP=> H. apply/negP=> H'. apply: H.
      rewrite -eval_qfbv_conjs_ra_la. assumption.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_complete_la E f p :
    let fE := program_succ_typenv p E in
    well_formed_ssa_program E p ->
    (forall s, SSAStore.conform s fE ->
               eval_bexp (bexp_rbexp f) s ->
               eval_bexp (bexp_program_algsnd_fixed_final fE p) s) ->
    (forall pre_es safe,
        ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
        QFBV.valid fE (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es))
                                safe)).
  Proof.
    move=> fE Hwf H pre_es safe Hin s Hco.
    move: (bexp_program_algsnd_split_fixed_final_complete Hwf H Hin Hco) => /=.
    case Hf: (eval_bexp (bexp_rbexp f) s) => //=.
    case Hsafe: (eval_bexp safe s) => /=.
    - rewrite !orbT. by apply.
    - rewrite !orbF. move/negP=> He. apply/negP=> He'. apply: He.
      rewrite eval_qfbv_conjs_ra_la. assumption.
  Qed.

  Lemma bexp_program_algsnd_split_fixed_final_cond_well_formed_la E f p :
    let fE := program_succ_typenv p E in
    well_formed_rbexp E f ->
    well_formed_ssa_program E p ->
    forall pre_es safe,
      ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final fE p)) ->
      QFBV.well_formed_bexp
        (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es)) safe) fE.
  Proof.
    move=> fE Hwf_Ef Hwf_Ep pre_es safe Hin.
    move: (bexp_program_algsnd_split_fixed_final_cond_well_formed Hwf_Ef Hwf_Ep Hin).
    simpl. move/andP=> [/andP [H1 H2] H3]. rewrite H1 H3 andbT /=.
    rewrite -well_formed_bexp_ra_la. assumption.
  Qed.

End SafetySplitConditionsFixedFinal.


Import QFBV.


(** Construct QF_BV expressions by qfbv_conjs for safety conditions *)

Section Algsnd.

  Fixpoint qfbv_spec_algsnd_rec f es :=
    match es with
    | [::] => [::]
    | (pre_es, safe)::tl =>
      (qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe)::(qfbv_spec_algsnd_rec f tl)
    end.

  Definition qfbv_spec_algsnd (s : rspec) : seq QFBV.bexp :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    qfbv_spec_algsnd_rec (bexp_rbexp (rspre s))
                         (bexp_program_algsnd_split_fixed_final fE (rsprog s)).

  Definition valid_qfbv_spec_algsnd (s : rspec) : Prop :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    valid_bexps fE (qfbv_spec_algsnd s).
  Lemma qfbv_spec_algsnd_rec_format E f p e :
    (e \in (qfbv_spec_algsnd_rec
              f
              (bexp_program_algsnd_split_fixed_final E p))) ->
    exists pre_es, exists safe,
        e = qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe.
  Proof.
    rewrite /bexp_program_algsnd_split_fixed_final. move: [::].
    elim: p e => [| i p IH] e //=. move=> pre_es'. rewrite in_cons. case/orP=> Hin.
    - exists pre_es'; exists (bexp_instr_algsnd E i). exact: (eqP Hin).
    - apply: IH. exact: Hin.
  Qed.

  Lemma qfbv_spec_algsnd_rec_in E f p pre_es safe:
    ((qfbv_imp (qfbv_conj f (qfbv_conjs pre_es)) safe) \in
        (qfbv_spec_algsnd_rec
           f
           (bexp_program_algsnd_split_fixed_final E p)))
    <->
    ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final E p)).
  Proof.
    rewrite /bexp_program_algsnd_split_fixed_final. move: [::].
    elim: p pre_es safe => [| i p IH] pre_es safe pre_es' //=. split.
    - rewrite in_cons. case/orP=> Hin.
      + rewrite in_cons. case: (eqP Hin). move=> H ->.
        rewrite (qfbv_conjs_inj H). rewrite eqxx /=. reflexivity.
      + apply/orP; right. apply/IH. assumption.
    - rewrite in_cons. case/orP=> Hin.
      + case: (eqP Hin)=> -> ->. exact: mem_head.
      + apply/orP; right. apply/IH. assumption.
  Qed.

  Lemma qfbv_spec_algsnd_rec_well_formed E f es :
    well_formed_bexp f E ->
    (forall pres safe, (pres, safe) \in es -> well_formed_bexps pres E /\ well_formed_bexp safe E) ->
    well_formed_bexps (qfbv_spec_algsnd_rec f es) E.
  Proof.
    move=> Hf. elim: es => [| e es IH] //=. case: e => [pres safe] => /=.
    move=> H. rewrite Hf /=. move: (H pres safe (mem_head _ _)) => [H1 H2].
    rewrite qfbv_conjs_well_formed. rewrite H1 H2 /=. apply: IH.
    move=> pres0 safe0 Hin. apply: H. rewrite in_cons Hin orbT. reflexivity.
  Qed.

  Lemma qfbv_spec_algsnd_well_formed s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    well_formed_bexps (qfbv_spec_algsnd s) fE.
  Proof.
    move => fE Hwf. apply: qfbv_spec_algsnd_rec_well_formed.
    - apply: well_formed_bexp_rbexp. exact: (SSA.well_formed_ssa_rspec_final_pre Hwf).
    - move: (well_formed_ssa_rspec_program Hwf) => Hssa. move=> pres safe Hin. split.
      + move: (bexp_program_algsnd_split_fixed_final_pre_es_well_formed Hssa Hin).
        rewrite qfbv_conjs_well_formed. by apply.
      + exact: (bexp_program_algsnd_split_fixed_final_algsnd_well_formed Hssa Hin).
  Qed.

  Lemma qfbv_spec_algsnd_sound s :
    well_formed_ssa_rspec s -> valid_qfbv_spec_algsnd s -> ssa_spec_algsnd s.
  Proof.
    move=> Hwf Hq. apply: (ssa_spec_algsnd_final_init Hwf).
    apply: (ssa_spec_algsnd_qfbv_fixed_final_sound Hwf).
    move: Hwf Hq. rewrite /valid_qfbv_spec_algsnd /ssa_spec_algsnd_qfbv_fixed_final.
    rewrite /qfbv_spec_algsnd. case: s => [E f p g] /=.
    move=> Hwf Hq. move: (well_formed_ssa_rspec_program Hwf) => /= Hwf_ssa_Ep.
    apply: (bexp_program_algsnd_split_fixed_final_sound Hwf_ssa_Ep).
    move=> pre_es safe Hin s Hco. move: (Hq _ Hco). move/allP; apply.
    apply/qfbv_spec_algsnd_rec_in. assumption.
  Qed.

  Lemma qfbv_spec_algsnd_complete s :
    is_rng_rspec s -> well_formed_ssa_rspec s -> ssa_spec_algsnd s ->
    valid_qfbv_spec_algsnd s.
  Proof.
    move=> Hrng Hwf Hq. move: (ssa_spec_algsnd_init_final Hwf Hq) => {} Hq.
    move: (ssa_spec_algsnd_qfbv_fixed_final_complete Hrng Hwf Hq) => {} Hq.
    move: Hrng Hwf Hq. rewrite /valid_qfbv_spec_algsnd /ssa_spec_algsnd_qfbv_fixed_final.
    rewrite /qfbv_spec_algsnd. case: s => [E f p g] /=.
    move=> Hrng Hwf Hq. move: (well_formed_ssa_rspec_program Hwf) => /= Hwf_ssa_Ep.
    move: (bexp_program_algsnd_split_fixed_final_complete Hwf_ssa_Ep Hq) => {Hq} Hq.
    move=> s Hco. apply/allP => e Hin. move: (qfbv_spec_algsnd_rec_format Hin) => [pre_es [safe He]].
    rewrite He in Hin *. apply: (Hq _ _ _ _ Hco).
    apply/qfbv_spec_algsnd_rec_in. exact: Hin.
  Qed.

End Algsnd.


(* Use qfbv_conjs_la to combine QFBV formulas *)

Section AlgsndLeftAssoc.

  Fixpoint qfbv_spec_algsnd_la_rec f es :=
    match es with
    | [::] => [::]
    | (pre_es, safe)::tl =>
      (qfbv_imp (qfbv_conj f (qfbv_conjs_la pre_es))
                safe)::(qfbv_spec_algsnd_la_rec f tl)
    end.

  Definition qfbv_spec_algsnd_la (s : rspec) : seq QFBV.bexp :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    qfbv_spec_algsnd_la_rec (bexp_rbexp (rspre s))
                            (bexp_program_algsnd_split_fixed_final fE (rsprog s)).

  Definition valid_qfbv_spec_algsnd_la (s : rspec) : Prop :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    valid_bexps fE (qfbv_spec_algsnd_la s).

  Lemma qfbv_spec_algsnd_la_eval s t :
    eval_bexps (qfbv_spec_algsnd_la s) t = eval_bexps (qfbv_spec_algsnd s) t.
  Proof.
    rewrite /qfbv_spec_algsnd_la /qfbv_spec_algsnd.
    move: (bexp_program_algsnd_split_fixed_final
             (program_succ_typenv (rsprog s) (rsinputs s)) (rsprog s))
            (bexp_rbexp (rspre s)). clear s.
    elim => [| e es IH] f //=. case: e => [pres safe] /=.
    rewrite eval_qfbv_conjs_ra_la IH. reflexivity.
  Qed.

  Lemma qfbv_spec_algsnd_la_valid E s :
    valid_bexps E (qfbv_spec_algsnd_la s) <-> valid_bexps E (qfbv_spec_algsnd s).
  Proof.
    split.
    - move=> H t Hco. rewrite -qfbv_spec_algsnd_la_eval. exact: H.
    - move=> H t Hco. rewrite qfbv_spec_algsnd_la_eval. exact: H.
  Qed.

  Lemma valid_qfbv_spec_algsnd_la_ra s :
    valid_qfbv_spec_algsnd_la s <-> valid_qfbv_spec_algsnd s.
  Proof.
    split.
    - move=> H fE. rewrite -qfbv_spec_algsnd_la_valid. assumption.
    - move=> H fE. rewrite qfbv_spec_algsnd_la_valid. assumption.
  Qed.

  Lemma qfbv_spec_algsnd_la_rec_format E f p e :
    (e \in (qfbv_spec_algsnd_la_rec
              f
              (bexp_program_algsnd_split_fixed_final E p))) ->
    exists pre_es, exists safe,
        e = qfbv_imp (qfbv_conj f (qfbv_conjs_la pre_es)) safe.
  Proof.
    rewrite /bexp_program_algsnd_split_fixed_final. move: [::].
    elim: p e => [| i p IH] e //=. move=> pre_es'. rewrite in_cons. case/orP=> Hin.
    - exists pre_es'; exists (bexp_instr_algsnd E i). exact: (eqP Hin).
    - apply: IH. exact: Hin.
  Qed.

  Lemma qfbv_spec_algsnd_la_rec_in E f p pre_es safe:
    ((qfbv_imp (qfbv_conj f (qfbv_conjs_la pre_es)) safe) \in
        (qfbv_spec_algsnd_la_rec
           f
           (bexp_program_algsnd_split_fixed_final E p)))
    <->
    ((pre_es, safe) \in (bexp_program_algsnd_split_fixed_final E p)).
  Proof.
    rewrite /bexp_program_algsnd_split_fixed_final. move: [::].
    elim: p pre_es safe => [| i p IH] pre_es safe pre_es' //=. split.
    - rewrite in_cons. case/orP=> Hin.
      + rewrite in_cons. case: (eqP Hin). move=> H ->.
        rewrite (qfbv_conjs_la_inj H). rewrite eqxx /=. reflexivity.
      + apply/orP; right. apply/IH. assumption.
    - rewrite in_cons. case/orP=> Hin.
      + case: (eqP Hin)=> -> ->. exact: mem_head.
      + apply/orP; right. apply/IH. assumption.
  Qed.

  Lemma qfbv_spec_algsnd_la_rec_well_formed E f es :
    well_formed_bexp f E ->
    (forall pres safe, (pres, safe) \in es -> well_formed_bexps pres E /\ well_formed_bexp safe E) ->
    well_formed_bexps (qfbv_spec_algsnd_la_rec f es) E.
  Proof.
    move=> Hf. elim: es => [| e es IH] //=. case: e => [pres safe] => /=.
    move=> H. rewrite Hf /=. move: (H pres safe (mem_head _ _)) => [H1 H2].
    rewrite qfbv_conjs_la_well_formed. rewrite H1 H2 /=. apply: IH.
    move=> pres0 safe0 Hin. apply: H. rewrite in_cons Hin orbT. reflexivity.
  Qed.

  Lemma qfbv_spec_algsnd_la_well_formed s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    well_formed_bexps (qfbv_spec_algsnd_la s) fE.
  Proof.
    move => fE Hwf. apply: qfbv_spec_algsnd_la_rec_well_formed.
    - apply: well_formed_bexp_rbexp. exact: (SSA.well_formed_ssa_rspec_final_pre Hwf).
    - move: (well_formed_ssa_rspec_program Hwf) => Hssa. move=> pres safe Hin. split.
      + move: (bexp_program_algsnd_split_fixed_final_pre_es_well_formed Hssa Hin).
        rewrite qfbv_conjs_well_formed. by apply.
      + exact: (bexp_program_algsnd_split_fixed_final_algsnd_well_formed Hssa Hin).
  Qed.

  Lemma qfbv_spec_algsnd_la_sound s :
    well_formed_ssa_rspec s -> valid_qfbv_spec_algsnd_la s -> ssa_spec_algsnd s.
  Proof.
    move=> Hwf Hq. apply: (ssa_spec_algsnd_final_init Hwf).
    apply: (ssa_spec_algsnd_qfbv_fixed_final_sound Hwf).
    move: Hwf Hq. rewrite /valid_qfbv_spec_algsnd_la /ssa_spec_algsnd_qfbv_fixed_final.
    rewrite /qfbv_spec_algsnd_la. case: s => [E f p g] /=.
    move=> Hwf Hq. move: (well_formed_ssa_rspec_program Hwf) => /= Hwf_ssa_Ep.
    apply: (bexp_program_algsnd_split_fixed_final_sound Hwf_ssa_Ep).
    move=> pre_es safe Hin s Hco.
    replace (eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es)) safe) s) with
      (eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es)) safe) s).
    - move: (Hq _ Hco). move/allP; apply. apply/qfbv_spec_algsnd_la_rec_in. assumption.
    - by simpl; rewrite -eval_qfbv_conjs_ra_la.
  Qed.

  Lemma qfbv_spec_algsnd_la_complete s :
    is_rng_rspec s -> well_formed_ssa_rspec s -> ssa_spec_algsnd s ->
    valid_qfbv_spec_algsnd_la s.
  Proof.
    move=> Hrng Hwf Hq. move: (ssa_spec_algsnd_init_final Hwf Hq) => {} Hq.
    move: (ssa_spec_algsnd_qfbv_fixed_final_complete Hrng Hwf Hq) => {} Hq.
    move: Hrng Hwf Hq. rewrite /valid_qfbv_spec_algsnd_la /ssa_spec_algsnd_qfbv_fixed_final.
    rewrite /qfbv_spec_algsnd_la. case: s => [E f p g] /=.
    move=> Hrng Hwf Hq. move: (well_formed_ssa_rspec_program Hwf) => /= Hwf_ssa_Ep.
    move: (bexp_program_algsnd_split_fixed_final_complete Hwf_ssa_Ep Hq) => {} Hq.
    move=> s Hco. apply/allP => e Hin. move: (qfbv_spec_algsnd_la_rec_format Hin) => [pre_es [safe He]].
    rewrite He in Hin *.
    replace (eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs_la pre_es)) safe) s) with
      (eval_bexp (qfbv_imp (qfbv_conj (bexp_rbexp f) (qfbv_conjs pre_es)) safe) s).
    - apply: (Hq _ _ _ _ Hco). apply/qfbv_spec_algsnd_la_rec_in. exact: Hin.
    - by simpl; rewrite -eval_qfbv_conjs_ra_la.
  Qed.

End AlgsndLeftAssoc.


(* Algebraic soundness version 3 (with slicing) *)

Section AlgsndSliceLeftAssoc.

  (* algsnd_after *)

  Definition algsnd_after (E : SSATE.env) (f : rbexp) (p : program) (i : instr) : Prop :=
    forall s1 s2, SSAStore.conform s1 E ->
                  eval_rbexp f s1 ->
                  eval_program E p s1 s2 ->
                  ssa_instr_algsnd_at (program_succ_typenv p E) i s2.


  (* Algebraic soundness with slicing *)

  Definition make_sndcond fE f p i :=
    let ef := bexp_rbexp f in
    let vs := depvars_rpre_rprogram (rvs_instr i) f p in
    let ep := bexp_program fE (slice_rprogram vs p) in
    let es := bexp_instr_algsnd fE i in
    qfbv_imp (qfbv_conj ef (qfbv_conjs_la ep)) es.

  Fixpoint algsnd_slice_la_rec fE (pre : program) (f : rbexp) (p : program) : seq QFBV.bexp :=
    match p with
    | [::] => [::]
    | hd::tl => (make_sndcond fE f pre hd)::
                  (algsnd_slice_la_rec fE (rcons pre hd) f tl)
    end.

  Definition algsnd_slice_la (s : rspec) : seq QFBV.bexp :=
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    algsnd_slice_la_rec fE [::] (rspre s) (rsprog s).

  Lemma slice_rbexp_eval_bexp vs r s :
    eval_bexp (bexp_rbexp r) s -> eval_bexp (bexp_rbexp (slice_rbexp vs r)) s.
  Proof.
    elim: r => //=.
    - move=> n e1 e2 Hev. by case Hs: (SSA.VSLemmas.disjoint vs (vars_rexp e1) &&
                                         SSA.VSLemmas.disjoint vs (vars_rexp e2)).
    - move=> n op e1 e2. by case Hs: (SSA.VSLemmas.disjoint vs (vars_rexp e1) &&
                                        SSA.VSLemmas.disjoint vs (vars_rexp e2)).
    - move=> e IH Hev. by case Hs: (SSA.VSLemmas.disjoint vs (vars_rbexp e)).
    - move=> e1 IH1 e2 IH2 /andP [H1 H2]. move: (IH1 H1) (IH2 H2) => {}IH1 {}IH2.
      (case Hs1: (slice_rbexp vs e1) IH1); (case Hs2: (slice_rbexp vs e2) IH2 => //=); intros;
        by rewrite IH1 IH2.
    - move=> e1 IH1 e2 IH2. by case: (SSA.VSLemmas.disjoint vs (vars_rbexp e1) &&
                                        SSA.VSLemmas.disjoint vs (vars_rbexp e2)).
  Qed.

  Lemma slice_instr_eval_bexp fE vs i i' s :
    slice_rinstr vs i = Some i' -> eval_bexp (bexp_instr fE i) s ->
    eval_bexp (bexp_instr fE i') s.
  Proof.
    (case: i => //=); intros; case_if; case_option; subst; simpl;
    repeat match goal with
           | H : ?e = true |- context c [?e] => rewrite H /=
           | H : ?e = false |- context c [?e] => rewrite H /=
           end; try assumption.
    case: b H H0 => [e r] /=. move=> [] ?; subst. rewrite /bexp_instr /=.
    exact: slice_rbexp_eval_bexp.
  Qed.

  Lemma slice_rprogram_eval_bexp fE vs p s :
    are_defined (lvs_program p) fE ->
    env_unchanged_program fE p ->
    eval_bexp (qfbv_conjs_la (bexp_program fE p)) s ->
    eval_bexp (qfbv_conjs_la (bexp_program fE (slice_rprogram vs p))) s.
  Proof.
    rewrite !qfbv_conj_la_eval. elim: p fE => [| i p IH] fE //=.
    rewrite are_defined_union => /andP [Hdefi Hdefp]. move/andP => [Huni Hunp].
    move/andP=> [Hvi Hvp]. case Hs: (slice_rinstr vs i) => /=.
    - rewrite (slice_instr_eval_bexp Hs Hvi) /=. rewrite -(slice_rinstr_some_succ_typenv _ Hs).
      apply: (IH _ (are_defined_instr_succ_typenv _ Hdefp) _ Hvp).
      exact: (env_unchanged_program_equal
                (SSATE.Lemmas.Equal_sym (env_unchanged_instr_succ_equal Hdefi Huni)) Hunp).
    - apply: (IH _ Hdefp Hunp).
      rewrite (env_unchanged_instr_succ_equal Hdefi Huni) in Hvp. exact: Hvp.
  Qed.

  Lemma algsnd_slice_la_algsnd_la s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    valid_bexps fE (algsnd_slice_la s) -> valid_qfbv_spec_algsnd_la s.
  Proof.
    case: s => [E f p g] /=. rewrite /algsnd_slice_la /valid_qfbv_spec_algsnd_la /=.
    rewrite /qfbv_spec_algsnd_la /=. rewrite /bexp_program_algsnd_split_fixed_final /=.
    rewrite /well_formed_ssa_rspec /=. rewrite /well_formed_rspec /=.
    move=> /andP [/andP [/andP [/andP [Hwff Hwfp] _] Hun] Hssa]. clear g.
    have: (are_defined (lvs_program ([::] ++ p)) (program_succ_typenv p E)).
    { rewrite cat0s. exact: are_defined_lvs_program_succ_typenv. }
    have: env_unchanged_program (program_succ_typenv p E) ([::] ++ p).
    { rewrite cat0s. apply: env_unchanged_program_succ. rewrite /well_formed_ssa_program.
      by rewrite Hwfp Hun Hssa. }
    clear Hwff Hwfp Hun Hssa.
    have: bexp_program (program_succ_typenv p E) [::] = [::] by reflexivity.
    move: [::] => pre. move: [::] => pre_es.
    elim: p E pre pre_es  => [| i p IH] E pre pre_es //= Hpre Hun Hdef.
    rewrite /make_sndcond /=. rewrite !valid_bexps_cons. move=> [Hvi Hvp].
    have Hdefpre: are_defined (lvs_program pre) (program_succ_typenv p (instr_succ_typenv i E)).
    { move: Hdef. apply: are_defined_subset. rewrite lvs_program_cat.
      exact: SSA.VSLemmas.union_subset_1. }
    have Hunpre: env_unchanged_program (program_succ_typenv p (instr_succ_typenv i E)) pre.
    { move: Hun. rewrite env_unchanged_program_cat. move/andP => [Hun _]. exact: Hun. }
    split.
    - move=> s Hco. move: (Hvi s Hco) => {Hvi} /=. case: (eval_bexp (bexp_rbexp f) s) => //=.
      case: (eval_bexp (bexp_instr_algsnd (program_succ_typenv p (instr_succ_typenv i E)) i) s);
        [by rewrite !orbT | rewrite !orbF]. move/negP=> Hvi. apply/negP => Hv.
      apply: Hvi. rewrite -Hpre in Hv. exact: (slice_rprogram_eval_bexp _ Hdefpre Hunpre Hv).
    - apply: (IH _ _ _ _ _ _ Hvp).
      + rewrite bexp_program_rcons Hpre. rewrite env_unchanged_program_cat in Hun.
        move/andP: Hun => [Hun _]. rewrite (env_unchanged_program_succ_equal Hdefpre Hun).
        reflexivity.
      + rewrite cat_rcons. assumption.
      + rewrite cat_rcons. assumption.
  Qed.

  Theorem algsnd_slice_la_sound s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    valid_bexps fE (algsnd_slice_la s) -> ssa_spec_algsnd s.
  Proof.
    move=> fE Hwf Hv. apply: (qfbv_spec_algsnd_la_sound Hwf).
    exact: (algsnd_slice_la_algsnd_la Hwf Hv).
  Qed.


  Lemma well_formed_bexp_slice_rbexp E vs e :
    well_formed_bexp (bexp_rbexp e) E ->
    well_formed_bexp (bexp_rbexp (slice_rbexp vs e)) E.
  Proof.
    elim: e => //=.
    - move=> n e1 e2. by case: (SSA.VSLemmas.disjoint vs (vars_rexp e1) &&
                                  SSA.VSLemmas.disjoint vs (vars_rexp e2)).
    - move=> n op e1 e2. by case: (SSA.VSLemmas.disjoint vs (vars_rexp e1) &&
                                     SSA.VSLemmas.disjoint vs (vars_rexp e2)).
    - move=> e IH. by case: (SSA.VSLemmas.disjoint vs (vars_rbexp e)).
    - move=> e1 IH1 e2 IH2 /andP [Hwf1 Hwf2]. move: (IH1 Hwf1) (IH2 Hwf2).
      case: (slice_rbexp vs e1); (case: (slice_rbexp vs e2) => //=); intros;
        by repeat match goal with
             | H : is_true ?e |- context c [?e] => rewrite H /=
             end.
    - move=> e1 IH1 e2 IH2. by case: (SSA.VSLemmas.disjoint vs (vars_rbexp e1) &&
                                        SSA.VSLemmas.disjoint vs (vars_rbexp e2)).
  Qed.

  Lemma well_formed_bexp_slice_rinstr fE vs i i' :
    well_formed_bexp (bexp_instr fE i) fE ->
    slice_rinstr vs i = Some i' ->
    well_formed_bexp (bexp_instr fE i') fE.
  Proof.
    (case: i => //=); intros; case_if; case_option; subst; simpl;
    repeat match goal with
      | H : ?e = true |- context c [?e] => rewrite H /=
      | H : ?e = false |- context c [?e] => rewrite H /=
      end; try assumption.
    case: b H H0 => [e r]. move=> H [] ?; subst; simpl.
    exact: (well_formed_bexp_slice_rbexp _ H).
  Qed.

  Lemma well_formed_bexp_slice_rprogram fE vs p :
    are_defined (lvs_program p) fE ->
    env_unchanged_program fE p ->
    well_formed_bexp (qfbv_conjs_la (bexp_program fE p)) fE ->
    well_formed_bexp (qfbv_conjs_la (bexp_program fE (slice_rprogram vs p))) fE.
  Proof.
    rewrite -!well_formed_bexp_ra_la. elim: p fE => [| i p IH] fE //=.
    rewrite are_defined_union => /andP [Hdefi Hdefp]. move/andP => [Huni Hunp].
    move/andP=> [Hi Hp]. case Hs: (slice_rinstr vs i) => /=.
    - rewrite (well_formed_bexp_slice_rinstr Hi Hs) /=.
      rewrite -(slice_rinstr_some_succ_typenv _ Hs).
      rewrite (env_unchanged_instr_succ_equal Hdefi Huni) in Hp *.
      exact: (IH _ Hdefp Hunp Hp).
    - rewrite (env_unchanged_instr_succ_equal Hdefi Huni) in Hp.
      exact: (IH _ Hdefp Hunp Hp).
  Qed.

  Lemma algsnd_slice_la_well_formed s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    well_formed_bexps (algsnd_slice_la s) fE.
  Proof.
    move=> fE Hwf. rewrite /fE => {fE}. move: Hwf (qfbv_spec_algsnd_la_well_formed Hwf).
    case: s => [E f p g] /=. rewrite /qfbv_spec_algsnd_la /algsnd_slice_la /=.
    rewrite /well_formed_ssa_rspec /=. rewrite /well_formed_rspec /=.
    move=> /andP [/andP [/andP [/andP [Hwff Hwfp] _] Hun] Hssa]. clear g.
    have: (are_defined (lvs_program ([::] ++ p)) (program_succ_typenv p E)).
    { rewrite cat0s. exact: are_defined_lvs_program_succ_typenv. }
    have: env_unchanged_program (program_succ_typenv p E) ([::] ++ p).
    { rewrite cat0s. apply: env_unchanged_program_succ. rewrite /well_formed_ssa_program.
      by rewrite Hwfp Hun Hssa. }
    clear Hwff Hwfp Hun Hssa. rewrite /bexp_program_algsnd_split_fixed_final.
    have: bexp_program (program_succ_typenv p E) [::] = [::] by reflexivity.
    move: [::] => pre. move: [::] => pre_es.
    elim: p E pre pre_es  => [| i p IH] E pre pre_es //= Hpre Hun Hdef.
    move/andP => [/andP [/andP [Hf Hpre_es] Hi] Hp].
    rewrite Hf /=. rewrite Hi andbT.
    have Hdefpre: are_defined (lvs_program pre) (program_succ_typenv p (instr_succ_typenv i E)).
    { move: Hdef. apply: are_defined_subset. rewrite lvs_program_cat.
      exact: SSA.VSLemmas.union_subset_1. }
    have Hunpre: env_unchanged_program (program_succ_typenv p (instr_succ_typenv i E)) pre.
    { move: Hun. rewrite env_unchanged_program_cat. move/andP => [Hun _]. exact: Hun. }
    apply/andP; split.
    - rewrite -Hpre in Hpre_es. exact: (well_formed_bexp_slice_rprogram _ Hdefpre Hunpre Hpre_es).
    - apply: (IH _ _ _ _ _ _ Hp).
      + rewrite bexp_program_rcons Hpre. rewrite env_unchanged_program_cat in Hun.
        move/andP: Hun => [Hun _]. rewrite (env_unchanged_program_succ_equal Hdefpre Hun).
        reflexivity.
      + rewrite cat_rcons. assumption.
      + rewrite cat_rcons. assumption.
  Qed.

End AlgsndSliceLeftAssoc.



(* Combine range reduction and algebraic soundness (version 1) *)

Section RngredAlgsnd.

  (* Combine range spec and safety conditions for bit-blasting *)

  Definition rngred_algsnd (s : rspec) :=
    (rngred_rspec s)::(qfbv_spec_algsnd s).

  Lemma valid_rngred_algsnd_rngred fE s :
    valid_bexps fE (rngred_algsnd s) -> QFBV.valid fE (rngred_rspec s).
  Proof. rewrite /rngred_algsnd. rewrite valid_bexps_cons. tauto. Qed.

  Lemma valid_rngred_algsnd_algsnd fE s :
    valid_bexps fE (rngred_algsnd s) -> valid_bexps fE (qfbv_spec_algsnd s).
  Proof. rewrite /rngred_algsnd. rewrite valid_bexps_cons. tauto. Qed.

  Lemma rngred_algsnd_valid_rspec s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    valid_bexps fE (rngred_algsnd s) ->
    valid_rspec s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hv. apply: (rngred_rspec_sound Hwf).
    exact: (valid_rngred_algsnd_rngred Hv).
  Qed.

  Lemma rngred_algsnd_valid_ssa_spec_algsnd s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    valid_bexps fE (rngred_algsnd s) ->
    ssa_spec_algsnd s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hv. apply: (qfbv_spec_algsnd_sound Hwf).
    exact: (valid_rngred_algsnd_algsnd Hv).
  Qed.

  Theorem rngred_algsnd_sound s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    valid_bexps fE (rngred_algsnd s) ->
    valid_rspec s /\ ssa_spec_algsnd s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hbb. split.
    - exact: (rngred_algsnd_valid_rspec Hwf Hbb).
    - exact: (rngred_algsnd_valid_ssa_spec_algsnd Hwf Hbb).
  Qed.

  Theorem rngred_algsnd_complete s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    is_rng_rspec s ->
    well_formed_ssa_rspec s ->
    valid_rspec s -> ssa_spec_algsnd s ->
    valid_bexps fE (rngred_algsnd s).
  Proof.
    move=> fE Hrs Hwf Hrng Hsnd. rewrite /rngred_algsnd. rewrite valid_bexps_cons. split.
    - exact: (rngred_rspec_complete Hrs Hwf Hrng).
    - exact: (qfbv_spec_algsnd_complete Hrs Hwf Hsnd).
  Qed.

  Theorem rngred_algsnd_well_formed s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    well_formed_bexps (rngred_algsnd s) fE.
  Proof.
    move=> fE Hwf. rewrite well_formed_bexps_cons.
    rewrite (well_formed_qfbv_rngred_rspec Hwf) andTb.
    exact: (qfbv_spec_algsnd_well_formed Hwf).
  Qed.

End RngredAlgsnd.


(* Combine range reduction and algebraic soundness (version 2) *)

Section RngredAlgsndLeftAssoc.

  (* Combine range spec and safety conditions for bit-blasting *)

  Definition rngred_algsnd_split_la (s : rspec) : seq QFBV.bexp :=
    (rngred_rspec_split_la s) ++ (qfbv_spec_algsnd_la s).

  Lemma valid_rngred_algsnd_split_la_rngred fE s :
    valid_bexps fE (rngred_algsnd_split_la s) -> valid_bexps fE (rngred_rspec_split_la s).
  Proof. rewrite /rngred_algsnd_split_la. rewrite valid_bexps_cat. tauto. Qed.

  Lemma valid_rngred_algsnd_split_la_algsnd fE s :
    valid_bexps fE (rngred_algsnd_split_la s) -> valid_bexps fE (qfbv_spec_algsnd_la s).
  Proof. rewrite /rngred_algsnd_split_la. rewrite valid_bexps_cat. tauto. Qed.

  Lemma rngred_algsnd_split_la_valid_rspec s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s -> valid_bexps fE (rngred_algsnd_split_la s) ->
    valid_rspec s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hv. apply: (rngred_rspec_split_la_sound Hwf).
    exact: (valid_rngred_algsnd_split_la_rngred Hv).
  Qed.

  Lemma rngred_algsnd_split_la_valid_ssa_spec_algsnd s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s -> valid_bexps fE (rngred_algsnd_split_la s) ->
    ssa_spec_algsnd s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hv. apply: (qfbv_spec_algsnd_la_sound Hwf).
    exact: (valid_rngred_algsnd_split_la_algsnd Hv).
  Qed.

  Theorem rngred_algsnd_split_la_sound s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    valid_bexps fE (rngred_algsnd_split_la s) ->
    valid_rspec s /\ ssa_spec_algsnd s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hbb. split.
    - exact: (rngred_algsnd_split_la_valid_rspec Hwf Hbb).
    - exact: (rngred_algsnd_split_la_valid_ssa_spec_algsnd Hwf Hbb).
  Qed.

  Theorem rngred_algsnd_split_la_complete s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    is_rng_rspec s ->
    well_formed_ssa_rspec s ->
    valid_rspec s -> ssa_spec_algsnd s ->
    valid_bexps fE (rngred_algsnd_split_la s).
  Proof.
    move=> fE Hrs Hwf Hrng Hsnd. rewrite /rngred_algsnd_split_la. rewrite valid_bexps_cat. split.
    - exact: (rngred_rspec_split_la_complete Hrs Hwf Hrng).
    - exact: (qfbv_spec_algsnd_la_complete Hrs Hwf Hsnd).
  Qed.

  Theorem rngred_algsnd_split_la_well_formed s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    well_formed_bexps (rngred_algsnd_split_la s) fE.
  Proof.
    move=> fE Hwf. rewrite /rngred_algsnd_split_la. rewrite well_formed_bexps_cat.
    rewrite (well_formed_qfbv_rngred_rspec_split_la Hwf) andTb.
    exact: (qfbv_spec_algsnd_la_well_formed Hwf).
  Qed.

End RngredAlgsndLeftAssoc.


(* Combine range reduction and algebraic soundness (version 3) *)

Section RngredAlgsndSlicing.

  (* Combine range spec and safety conditions for bit-blasting *)

  Definition rngred_algsnd_slice_split_la (s : rspec) : seq QFBV.bexp :=
    (rngred_rspec_slice_split_la s) ++ (algsnd_slice_la s).

  Lemma valid_rngred_algsnd_slice_split_la_rngred fE s :
    valid_bexps fE (rngred_algsnd_slice_split_la s) -> valid_bexps fE (rngred_rspec_slice_split_la s).
  Proof. rewrite /rngred_algsnd_slice_split_la. rewrite valid_bexps_cat. tauto. Qed.

  Lemma valid_rngred_algsnd_slice_split_la_algsnd fE s :
    valid_bexps fE (rngred_algsnd_slice_split_la s) -> valid_bexps fE (algsnd_slice_la s).
  Proof. rewrite /rngred_algsnd_slice_split_la. rewrite valid_bexps_cat. tauto. Qed.

  Lemma rngred_algsnd_slice_split_la_valid_rspec s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    is_rng_rspec s ->
    well_formed_ssa_rspec s -> valid_bexps fE (rngred_algsnd_slice_split_la s) ->
    valid_rspec s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hrng Hwf Hv. apply: (rngred_rspec_slice_split_la_sound Hrng Hwf).
    exact: (valid_rngred_algsnd_slice_split_la_rngred Hv).
  Qed.

  Lemma rngred_algsnd_slice_split_la_valid_ssa_spec_algsnd s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s -> valid_bexps fE (rngred_algsnd_slice_split_la s) ->
    ssa_spec_algsnd s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hwf Hv. apply: (algsnd_slice_la_sound Hwf).
    exact: (valid_rngred_algsnd_slice_split_la_algsnd Hv).
  Qed.

  Theorem rngred_algsnd_slice_split_la_sound s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    is_rng_rspec s ->
    well_formed_ssa_rspec s ->
    valid_bexps fE (rngred_algsnd_slice_split_la s) ->
    valid_rspec s /\ ssa_spec_algsnd s.
  Proof.
    move=> fE. rewrite /fE => {fE} Hrng Hwf Hbb. split.
    - exact: (rngred_algsnd_slice_split_la_valid_rspec Hrng Hwf Hbb).
    - exact: (rngred_algsnd_slice_split_la_valid_ssa_spec_algsnd Hwf Hbb).
  Qed.

  Theorem rngred_algsnd_slice_split_la_well_formed s :
    let fE := program_succ_typenv (rsprog s) (rsinputs s) in
    well_formed_ssa_rspec s ->
    well_formed_bexps (rngred_algsnd_slice_split_la s) fE.
  Proof.
    move=> fE Hwf. rewrite /rngred_algsnd_slice_split_la. rewrite well_formed_bexps_cat.
    rewrite (rngred_rspec_slice_split_la_well_formed Hwf) andTb.
    exact: (algsnd_slice_la_well_formed Hwf).
  Qed.

End RngredAlgsndSlicing.
