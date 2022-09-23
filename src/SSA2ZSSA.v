
(** Algebraic reduction.
    Convert an algebraic specification in SSA to a root entailment problem
    together with an algebraic soundness condition. *)

From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder Nats ZAriths Store Tactics FMaps Seqs.
From BitBlasting Require Import State Typ TypEnv.
From Cryptoline Require Import Options DSL SSA ZSSA.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module M2ZSSA := Map2Map SSAStore.M ZSSAStore.M.


(* Tactics *)

Ltac case_pairs :=
  match goal with
  | H : (_, _) = (_, _) |- _ => case: H; move=> ? ?; subst
  | H : (if ?e then _ else _) = _ |- _ => move: H; case: e; intros
  | H : (match ?t with | Tuint _ => _ | Tsint _ => _ end) = _ |- _ =>
    move: H; repeat (match goal with
                     | HH : context f [t] |- _ => move: HH
                     end); case: t; intros
  | H : (let (_, _) := Z.div_eucl ?e1 ?e2 in _) = (_, _) |- _ =>
    let q := fresh "q" in
    let r := fresh "r" in
    let Hqr := fresh in
    move: H; dcase (Z.div_eucl e1 e2) => [[q r] Hqr]; intros
  end.

Ltac case_svar_notin :=
  match goal with
  | H : svar_notin ?v (SSAVS.singleton _) |- _ =>
    move/svar_notin_singleton: H => H
  | H : svar_notin ?v (SSAVS.add _ _) |- _ =>
    let H1 := fresh in let H2 := fresh in
    move/svar_notin_add: H => [H1 H2]
  | H : svar_notin ?v (SSAVS.union _ _) |- _ =>
    let H1 := fresh in let H2 := fresh in
    move/svar_notin_union: H => [H1 H2]
  end.


(** Generate new SSA variable names *)

Section GenSvar.

  Import SSA.

  Definition max_svar (vs : SSAVS.t) : VarOrder.t :=
    match SSAVS.max_elt vs with
    | Some v => svar v
    | None => 0%num
    end.

  Definition new_svar (vs : SSAVS.t) : VarOrder.t :=
    N.succ (max_svar vs).

  Definition new_svar_program (p : program) : VarOrder.t :=
    N.succ (max_svar (vars_program p)).

  Lemma N_ltb_succ v : (v <? N.succ v)%num.
  Proof. apply: (proj2 (N.ltb_lt v (N.succ v))). exact: N.lt_succ_diag_r. Qed.

  Lemma V_ltb_succ v i j : SSAVarOrder.ltn (v, j) ((N.succ v), i).
  Proof.
    rewrite /SSAVarOrder.ltn /SSAVarOrder.M.ltn /VarOrder.ltn /NOrderMinimal.ltn /=.
    rewrite N_ltb_succ. exact: is_true_true.
  Qed.

  Lemma new_svar_notin vs : svar_notin (new_svar vs) vs.
  Proof.
    rewrite /new_svar /max_svar. set x := SSAVS.max_elt vs.
    have: SSAVS.max_elt vs = x by reflexivity. case x.
    - move=> v Hmax i. apply/negP => Hmem. apply: (VSLemmas.max_elt2 Hmax Hmem).
      exact: V_ltb_succ.
    - move=> Hnone i. apply: VSLemmas.is_empty_mem.
      exact: (VSLemmas.max_elt3 Hnone).
  Qed.

  Lemma new_svar_notin_program p :
    svar_notin (new_svar_program p) (vars_program p).
  Proof. exact: new_svar_notin. Qed.

End GenSvar.



(** Algebraic soundness conditions *)

Section AlgebraicSoundnessConditions.

  Import SSA.

  Definition uaddB_algsnd bs1 bs2 : bool := ~~ carry_addB bs1 bs2.

  Definition saddB_algsnd bs1 bs2 : bool := ~~ Saddo bs1 bs2.

  Definition addB_algsnd typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then uaddB_algsnd bs1 bs2
    else saddB_algsnd bs1 bs2.

  Definition adds_algsnd typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then true
    else saddB_algsnd bs1 bs2.

  Definition uadcB_algsnd bs1 bs2 c : bool :=
    ~~ carry_addB bs1 bs2 &&
    ~~ carry_addB (addB bs1 bs2) (zext (size bs1 - 1) c).

  Definition sadcB_algsnd bs1 bs2 c : bool :=
    ~~ Saddo bs1 bs2 &&
    ~~ Saddo (addB bs1 bs2) (zext (size bs1 - 1) c).

  Definition adcB_algsnd typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then uadcB_algsnd bs1 bs2 bsc
    else sadcB_algsnd bs1 bs2 bsc.

  Definition adcs_algsnd typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then true
    else sadcB_algsnd bs1 bs2 bsc.

  Definition usubB_algsnd bs1 bs2 : bool := ~~ borrow_subB bs1 bs2.

  Definition ssubB_algsnd bs1 bs2 : bool := ~~ Ssubo bs1 bs2.

  Definition subB_algsnd typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then usubB_algsnd bs1 bs2
    else ssubB_algsnd bs1 bs2.

  Definition subc_algsnd typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then true
    else ssubB_algsnd bs1 bs2.

  Definition subb_algsnd typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then true
    else ssubB_algsnd bs1 bs2.

  Definition usbbB_algsnd bs1 bs2 c : bool :=
    ~~ borrow_subB bs1 bs2 &&
    ~~ borrow_subB (subB bs1 bs2) (zext (size bs1 - 1) c).

  Definition ssbbB_algsnd bs1 bs2 c : bool :=
    ~~ Ssubo bs1 bs2 &&
    ~~ Ssubo (subB bs1 bs2) (zext (size bs1 - 1) c).

  Definition sbbB_algsnd typ_a bs1 bs2 bsb : bool :=
    if Typ.is_unsigned typ_a then usbbB_algsnd bs1 bs2 bsb
    else ssbbB_algsnd bs1 bs2 bsb.

  Definition sbbs_algsnd typ_a bs1 bs2 bsb : bool :=
    if Typ.is_unsigned typ_a then true
    else ssbbB_algsnd bs1 bs2 bsb.

  Definition usbcB_algsnd bs1 bs2 c : bool :=
    ~~ borrow_subB bs1 bs2 &&
    ~~ borrow_subB (subB bs1 bs2) (zext (size bs1 - 1) (subB (ones 1) c)).

  Definition ssbcB_algsnd bs1 bs2 c : bool :=
    ~~ Ssubo bs1 bs2 &&
    ~~ Ssubo (subB bs1 bs2) (zext (size bs1 - 1) (subB (ones 1) c)).

  Definition sbcB_algsnd typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then usbcB_algsnd bs1 bs2 bsc
    else ssbcB_algsnd bs1 bs2 bsc.

  Definition sbcs_algsnd typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then true
    else ssbcB_algsnd bs1 bs2 bsc.

  Definition umulB_algsnd bs1 bs2 : bool := ~~ Umulo bs1 bs2.

  Definition smulB_algsnd bs1 bs2 : bool := ~~ Smulo bs1 bs2.

  Definition mulB_algsnd typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then umulB_algsnd bs1 bs2
    else smulB_algsnd bs1 bs2.

  Definition ushlBn_algsnd bs n : bool := high n bs == zeros n.

  Definition sshlBn_algsnd bs n : bool :=
  (high (n + 1) bs == zeros (n + 1)) || (high (n + 1) bs == ones (n + 1)).

  Definition shlBn_algsnd typ_a bs n : bool :=
    if Typ.is_unsigned typ_a then ushlBn_algsnd bs n
    else sshlBn_algsnd bs n.

  Definition ucshlBn_algsnd (bsh bsl : bits) n : bool :=
    ushlBn_algsnd (cat bsl bsh) n.

  Definition scshlBn_algsnd (bsh bsl : bits) n : bool :=
    sshlBn_algsnd (cat bsl bsh) n.

  Definition cshlBn_algsnd typ_a (bs1 bs2 : bits) n : bool :=
    if Typ.is_unsigned typ_a then ucshlBn_algsnd bs1 bs2 n
    else scshlBn_algsnd bs1 bs2 n.

  Definition vpc_algsnd t a_typ bs : bool :=
    let 'a_size := Typ.sizeof_typ a_typ in
    let 't_size := Typ.sizeof_typ t in
    if Typ.is_unsigned a_typ then
      if Typ.is_unsigned t then
        (* from unsigned to unsigned *)
        if a_size <= t_size then true
        else (high (a_size - t_size) bs == zeros (a_size - t_size))
      else
        (* from unsigned to signed *)
        if a_size < t_size then true
        else (high (a_size - t_size + 1) bs == zeros (a_size - t_size + 1))
    else
      if Typ.is_unsigned t then
        (* from signed to unsigned *)
        if (a_size - 1 <= t_size) then (high 1 bs == zeros 1)
        else (high (a_size - t_size) bs == zeros (a_size - t_size))
      else
        (* from signed to signed *)
        if a_size <= t_size then true
        else sext (a_size - t_size) (low t_size bs) == bs.

  Definition ssa_instr_algsnd_at te (i : instr) (s : SSAStore.t) : bool :=
    match i with
    | Iadd _ a1 a2 =>
      addB_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s)
    | Iadds _ _ a1 a2 =>
      adds_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s)
    | Iadc _ a1 a2 ac =>
      adcB_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s)
    | Iadcs _ _ a1 a2 ac =>
      adcs_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s)
    | Isub _ a1 a2 =>
      subB_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s)
    | Isubc _ _ a1 a2 =>
      subc_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s)
    | Isubb _ _ a1 a2 =>
      subb_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s)
    | Isbc _ a1 a2 ac =>
      sbcB_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s)
    | Isbb _ a1 a2 ab =>
      sbbB_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ab s)
    | Isbcs _ _ a1 a2 ac =>
      sbcs_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ac s)
    | Isbbs _ _ a1 a2 ab =>
      sbbs_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s) (eval_atom ab s)
    | Imul _ a1 a2 =>
      mulB_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s)
    | Ishl _ a n =>
      shlBn_algsnd (atyp a te) (eval_atom a s) n
    | Icshl _ _ a1 a2 n =>
      cshlBn_algsnd (atyp a1 te) (eval_atom a1 s) (eval_atom a2 s) n
    | Ivpc _ t a =>
      vpc_algsnd t (atyp a te) (eval_atom a s)
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
    | Iassume _ => true
    end.

  Inductive ssa_program_algsnd_at : SSATE.env -> program -> SSAStore.t -> Prop :=
  | ssa_program_algsnd_at_nil te s :
      ssa_program_algsnd_at te [::] s
  | ssa_program_algsnd_at_cons te hd tl s :
      ssa_instr_algsnd_at te hd s ->
      (forall s', eval_instr te (rng_instr hd) s s' ->
                  ssa_program_algsnd_at (instr_succ_typenv hd te) tl s') ->
      ssa_program_algsnd_at te (hd::tl) s.

  Definition ssa_spec_algsnd sp :=
    forall s, SSAStore.conform s (sinputs sp) ->
              eval_rbexp (rng_bexp (spre sp)) s ->
              ssa_program_algsnd_at (sinputs sp) (sprog sp) s.


  Lemma ssa_instr_algsnd_at_eqn E i s :
    ssa_instr_algsnd_at E i s -> ssa_instr_algsnd_at E (eqn_instr i) s.
  Proof. case: i => //=. move=> [] e r _ /=. by trivial. Qed.

  Ltac rewrite_bvs_eqi_eval_atom :=
    repeat
    match goal with
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      move/andP: H => [H1 H2]
    | H1 : bvs_eqi ?E ?s1 ?s2,
      H2 : is_true (are_defined (vars_atom ?a) ?E) |-
      context f [eval_atom ?a ?s2] =>
      rewrite -(bvs_eqi_eval_atom H1 H2)
    end.

  Lemma bvs_eqi_ssa_instr_algsnd_at E i s1 s2 :
    bvs_eqi E s1 s2 -> well_defined_instr E i -> ssa_instr_algsnd_at E i s1 ->
    ssa_instr_algsnd_at E i s2.
  Proof.
    move=> Heqi. case: i => //=; by (move=> *; rewrite_bvs_eqi_eval_atom).
  Qed.

  Lemma bvs_eqi_ssa_program_algsnd_at E p s1 s2 :
    bvs_eqi E s1 s2 -> well_formed_program E p ->
    ssa_program_algsnd_at E p s1 -> ssa_program_algsnd_at E p s2.
  Proof.
    elim: p E s1 s2 => [| i p IH] /= E s1 s2 Heqi Hwf Hsafe.
    - exact: ssa_program_algsnd_at_nil.
    - inversion_clear Hsafe. move/andP: Hwf => [Hwf_Ei Hwf_Eip].
      move/andP: Hwf_Ei => [Hwd_Ei Hwt_Ei].
      apply: ssa_program_algsnd_at_cons.
      + exact: (bvs_eqi_ssa_instr_algsnd_at Heqi Hwd_Ei H).
      + move=> t2 Hev2.
        move: (well_defined_rng_instr Hwd_Ei) => Hwd_Eri.
        move: (bvs_eqi_eval_instr_eqi Hwd_Eri (bvs_eqi_sym Heqi) Hev2) =>
        [t1 [Hev1 Heqi_t]]. move: (bvs_eqi_sym Heqi_t) => {Heqi_t} Heqi_t.
        rewrite rng_instr_succ_typenv in Heqi_t.
        apply: (IH (instr_succ_typenv i E) t1 t2 Heqi_t Hwf_Eip).
        exact: (H0 _ Hev1).
  Qed.

  Lemma ssa_instr_algsnd_at_submap E1 E2 i s :
    TELemmas.submap E1 E2 -> well_defined_instr E1 i ->
    ssa_instr_algsnd_at E1 i s <-> ssa_instr_algsnd_at E2 i s.
  Proof.
    move=> Hsub. rewrite /ssa_instr_algsnd_at.
    rewrite /shlBn_algsnd /cshlBn_algsnd
            /addB_algsnd /adds_algsnd /adcB_algsnd /adcs_algsnd
            /subB_algsnd /subc_algsnd /subb_algsnd
            /sbcB_algsnd /sbcs_algsnd /sbbB_algsnd /sbbs_algsnd
            /mulB_algsnd /vpc_algsnd
            /ucshlBn_algsnd /scshlBn_algsnd
            /ushlBn_algsnd /sshlBn_algsnd
            /uaddB_algsnd /saddB_algsnd
            /uadcB_algsnd /sadcB_algsnd
            /usubB_algsnd /ssubB_algsnd
            /usbcB_algsnd /ssbcB_algsnd
            /usbbB_algsnd /ssbbB_algsnd
            /umulB_algsnd /smulB_algsnd.
    (case: i => //=); intros;
      by repeat
           match goal with
           | H : is_true (_ && _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             move/andP: H => [H1 H2]
           | Hdef : is_true (are_defined (vars_atom ?a) ?E1),
             Hsub : TELemmas.submap ?E1 ?E2
             |- context f [atyp ?a ?E1] =>
             rewrite (atyp_submap Hsub Hdef)
           | H : ?p |- ?p => assumption
           end.
  Qed.

  Lemma ssa_program_algsnd_at_submap E1 E2 p s :
    TELemmas.submap E1 E2 -> well_formed_program E1 p ->
    ssa_program_algsnd_at E1 p s <-> ssa_program_algsnd_at E2 p s.
  Proof.
    elim: p E1 E2 s => [| i p IH] E1 E2 s //=.
    - move=> *. split; move=> H; exact: ssa_program_algsnd_at_nil.
    - move=> Hsub /andP [Hwf_Ei Hwf_iEp].
      move: (well_formed_instr_well_defined Hwf_Ei) => Hwd_Ei.
      split; move=> Hsafe; inversion_clear Hsafe.
      + apply: ssa_program_algsnd_at_cons.
        * apply/(ssa_instr_algsnd_at_submap s Hsub Hwd_Ei). assumption.
        * move=> t Hev1.
          apply/(IH _ _ t (submap_instr_succ_typenv Hwf_Ei Hsub) Hwf_iEp).
          apply: H0.
          apply/(submap_eval_instr _ _ Hsub (well_defined_rng_instr Hwd_Ei)).
          exact: Hev1.
      + apply: ssa_program_algsnd_at_cons.
        * apply/(ssa_instr_algsnd_at_submap s Hsub Hwd_Ei). assumption.
        * move=> t Hev1.
          apply/(IH _ _ t (submap_instr_succ_typenv Hwf_Ei Hsub) Hwf_iEp).
          apply: H0.
          apply/(submap_eval_instr _ _ Hsub (well_defined_rng_instr Hwd_Ei)).
          exact: Hev1.
  Qed.


  (* Use the final typing environment *)

  Definition ssa_spec_algsnd_final sp :=
    let fE := (program_succ_typenv (sprog sp) (sinputs sp)) in
    forall s,
      SSAStore.conform s fE ->
      eval_rbexp (rng_bexp (spre sp)) s ->
      ssa_program_algsnd_at fE (sprog sp) s.

  Lemma ssa_spec_algsnd_init_final sp :
    well_formed_ssa_spec sp ->
    ssa_spec_algsnd sp -> ssa_spec_algsnd_final sp.
  Proof.
    rewrite /well_formed_ssa_spec /ssa_spec_algsnd /ssa_spec_algsnd_final.
    case: sp => [E f p g] /=. rewrite /well_formed_spec /=.
    move=> /andP [/andP [/andP [/andP [Hwf_Ef Hwf_Ep] Hwf_pEg] Hun_Ep] Hssa].
    move=> H s Hco Hf.
    move: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa) => Hsub.
    apply/(ssa_program_algsnd_at_submap s Hsub Hwf_Ep).
    exact: (H _ (conform_submap Hsub Hco) Hf).
  Qed.

  Lemma ssa_spec_algsnd_final_init sp :
    well_formed_ssa_spec sp ->
    ssa_spec_algsnd_final sp -> ssa_spec_algsnd sp.
  Proof.
    rewrite /well_formed_ssa_spec /ssa_spec_algsnd /ssa_spec_algsnd_final.
    case: sp => [E f p g] /=. rewrite /well_formed_spec /=.
    move=> /andP [/andP [/andP [/andP [Hwf_Ef Hwf_Ep] Hwf_pEg] Hun_Ep] Hssa].
    move=> H s Hco Hf.
    move: (ssa_unchanged_program_succ_typenv_submap Hun_Ep Hssa) => Hsub.
    move: (force_conform_conform Hsub Hco) => Hco_succ.
    move: (well_formed_rng_bexp Hwf_Ef) => /andP [Hwd_Erf Hwt_Erf].
    move/(force_conform_eval_rbexp s Hsub Hwd_Erf): Hf => Hwf.
    move: (H (force_conform E (program_succ_typenv p E) s) Hco_succ Hwf).
    move=> Hsafe. move/(ssa_program_algsnd_at_submap _ Hsub Hwf_Ep): Hsafe.
    apply: (bvs_eqi_ssa_program_algsnd_at _ Hwf_Ep).
    apply: bvs_eqi_sym. exact: (force_conform_bvs_eqi _ Hsub).
  Qed.

End AlgebraicSoundnessConditions.



(** Algebraic reduction: conversion from SSA specifications to algebraic predicates *)

Section AlgebraicReduction.

  Import SSA ZSSA.

  Variable options : options.


  Ltac split_disjoint :=
    match goal with
    | H : is_true (VSLemmas.disjoint _ (SSAVS.singleton _)) |- _ =>
      rewrite VSLemmas.disjoint_singleton in H
    | H : is_true (VSLemmas.disjoint _ (SSAVS.add _ _)) |- _ =>
      let H1 := fresh "Hdisj" in let H2 := fresh "Hdisj" in
      rewrite VSLemmas.disjoint_add in H;
      move/andP: H => [H1 H2]
    end.


  Definition algred_atom (a : atom) : zexp :=
    match a with
    | Avar v => evar v
    | Aconst ty bs => econst (bv2z ty bs)
    end.

  Definition algred_assign (v : ssavar) (e : SSA.eexp) := eeq (evar v) e.
  Definition algred_join (e h l : SSA.eexp) (p : nat) :=
    eeq (eadd l (emul2p h (Z.of_nat p))) e.
  Definition algred_split (vh vl : ssavar) (e : SSA.eexp) (p : nat) :=
    algred_join e (evar vh) (evar vl) p.
  Definition algred_is_carry (c : ssavar) :=
    eeq (emul (evar c) (esub (evar c) (econst 1)))
        (econst 0).
  Definition carry_constr (c : ssavar) :=
    if (add_carry_constraints options) then [:: algred_is_carry c] else [::].

  Definition algred_cast (avn : VarOrder.t) (g : N) v vtyp a atyp :=
    match vtyp, atyp with
    | Tuint wv, Tuint wa =>
      if wv >= wa then
        (g, [:: Eeq (evar v) (algred_atom a)])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: algred_split discarded v (algred_atom a) wv])
    | Tuint wv, Tsint wa =>
      (* a_sign and discarded have different meanings but
         the polynomial equation is equivalent. *)
      if wv >= wa then
        let a_sign := (avn, g) in
        let g' := N.succ g in
        (g', [:: algred_join (evar v) (evar a_sign) (algred_atom a) wv])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: algred_split discarded v (algred_atom a) wv])
    | Tsint wv, Tuint wa =>
      if wv > wa then
        (g, [:: Eeq (evar v) (algred_atom a)])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: algred_split discarded v (algred_atom a) wv])
    | Tsint wv, Tsint wa =>
      if wv >= wa then
        (g, [:: Eeq (evar v) (algred_atom a)])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: algred_split discarded v (algred_atom a) wv])
    end.

  Definition algred_vpc (avn : VarOrder.t) (g : N) (v : ssavar) a :=
    (g, [:: Eeq (evar v) (algred_atom a)]).

  (* avn: the name of auxiliary variables
     g: the SSA index of the next auxiliary variable *)
  Definition algred_instr (te : SSATE.env) (avn : VarOrder.t) (g : N) (i : instr) :
    (N * seq ebexp) :=
    match i with
    | Imov v a =>
      let za := algred_atom a in
      (g, [:: algred_assign v za])
    | Ishl v a n =>
      let za := algred_atom a in
      (g, [:: algred_assign v (emul2p za (Z.of_nat n))])
    | Icshl vh vl a1 a2 n =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let a2size := asize a2 te in
      (g, [:: algred_split
              vh vl
              (eadd (emul2p za1 (Z.of_nat a2size)) za2)
              (a2size - n)])
    | Inondet v t =>
      if t == Tbit then (g, carry_constr v)
      else (g, [::])
    | Icmov v c a1 a2 =>
      let zc := algred_atom c in
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      (g, [:: algred_assign
              v
              (eadd (emul zc za1)
                    (emul (esub (econst Z.one) zc) za2))])
    | Inop => (g, [::])
    | Inot v t a =>
      let za := algred_atom a in
      let ta := atyp a te in
      match t, ta with
      | Tuint w, Tuint _ =>
        (g, [:: algred_assign
                v
                (esub (econst (Z.sub (z2expn (Z.of_nat w)) Z.one)) za)])
      | Tsint w, Tsint _ =>
        (g, [:: algred_assign
                v
                (esub (eneg za) (econst Z.one))])
      | _, _ => (g, [::])
      end
    | Iadd v a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      (g, [:: algred_assign v (eadd za1 za2)])
    | Iadds c v a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: algred_split c v (eadd za1 za2) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: algred_assign v (eadd za1 za2)])
      end
    | Iadc v a1 a2 y =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let zy := algred_atom y in
      (g, [:: algred_assign v (eadd (eadd za1 za2) zy)])
    | Iadcs c v a1 a2 y =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let zy := algred_atom y in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: algred_split c v (eadd (eadd za1 za2) zy) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: algred_assign v (eadd (eadd za1 za2) zy)])
      end
    | Isub v a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      (g, [:: algred_assign v (esub za1 za2)])
    | Isubc c v a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: algred_join
                (evar v) (esub (econst Z.one) (evar c))
                (esub za1 za2) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: algred_assign v (esub za1 za2)])
      end
    | Isubb c v a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: algred_join (evar v) (evar c) (esub za1 za2) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: algred_assign v (esub za1 za2)])
      end
    | Isbc v a1 a2 y =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let zy := algred_atom y in
      (g, [:: algred_assign v (esub (esub za1 za2) (esub (econst Z.one) zy))])
    | Isbcs c v a1 a2 y =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let zy := algred_atom y in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: algred_join
                (evar v) (esub (econst Z.one) (evar c))
                (esub (esub za1 za2) (esub (econst Z.one) zy)) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: algred_assign v (esub (esub za1 za2) (esub (econst Z.one) zy))])
      end
    | Isbb v a1 a2 y =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let zy := algred_atom y in
      (g, [:: algred_assign v (esub (esub za1 za2) zy)])
    | Isbbs c v a1 a2 y =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let zy := algred_atom y in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: algred_join
                (esub (esub za1 za2) zy) (eneg (evar c))
                (evar v) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: algred_assign v (esub (esub za1 za2) zy)])
      end
    | Imul v a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      (g, [:: algred_assign v (emul za1 za2)])
    | Imull vh vl a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      let a2size := asize a2 te in
      (g, [:: algred_split vh vl (emul za1 za2) a2size])
    | Imulj v a1 a2 =>
      let za1 := algred_atom a1 in
      let za2 := algred_atom a2 in
      (g, [:: algred_assign v (emul za1 za2)])
    | Isplit vh vl a n =>
      let za := algred_atom a in
      (g, [:: algred_split vh vl za n])
    | Iand v t a1 a2 => (g, [::]) (* cannot be translated to polynomials *)
    | Ior v t a1 a2 => (g, [::]) (* cannot be translated to polynomials *)
    | Ixor v t a1 a2 => (g, [::]) (* cannot be translated to polynomials *)
    | Icast v t a => algred_cast avn g v t a (atyp a te)
    | Ivpc v t a => algred_vpc avn g v a
    | Ijoin v ah al =>
      let zah := algred_atom ah in
      let zal := algred_atom al in
      let alsize := asize al te in
      (g, [:: algred_join (evar v) zah zal alsize])
    | Iassume e => (g, split_eand (eqn_bexp e))
    end.

  Fixpoint algred_program (te : SSATE.env) (avn : VarOrder.t) (g : N) (p : program) :
    N * seq ebexp :=
    match p with
    | [::] => (g, [::])
    | hd::tl =>
      let (g_hd, zhd) := algred_instr te avn g hd in
      let (g_tl, ztl) := algred_program (instr_succ_typenv hd te) avn g_hd tl in
      (g_tl, zhd ++ ztl)
    end.

  Definition new_svar_espec (s : espec) : VarOrder.t :=
    new_svar (SSAVS.union (vars_env (esinputs s))
                          (SSAVS.union
                             (vars_bexp (espre s))
                             (SSAVS.union (vars_program (esprog s))
                                          (vars_ebexp (espost s))))).

  Definition new_svar_spec (s : spec) : VarOrder.t :=
    new_svar (SSAVS.union (vars_env (sinputs s))
                          (SSAVS.union
                             (vars_bexp (spre s))
                             (SSAVS.union (vars_program (sprog s))
                                          (vars_bexp (spost s))))).

  Fixpoint aux_vars_lt_nat (avn : VarOrder.t) (gn : nat) : SSAVS.t :=
    match gn with
    | O => SSAVS.empty
    | S n => SSAVS.add (avn, N.of_nat n) (aux_vars_lt_nat avn n)
    end.

  Definition aux_vars_lt (avn : VarOrder.t) (g : N) : SSAVS.t :=
    aux_vars_lt_nat avn (N.to_nat g).

  Definition algred_espec avn (s : espec) : rep :=
    let (g, eprogs) := algred_program (esinputs s)
                                    avn initial_index (esprog s) in
    {| premise := eand (eqn_bexp (espre s)) (eands eprogs);
       conseq := espost s |}.


  Lemma aux_vars_lt_nat_mem avn g n :
    (N.to_nat n < g)%N -> SSAVS.mem (avn, n) (aux_vars_lt_nat avn g).
  Proof.
    elim: g n => //=. move=> g IH n H. case Hn: (N.to_nat n == g).
    - rewrite -(eqP Hn) Nnat.N2Nat.id. exact: (SSAVS.Lemmas.mem_add_eq (eqxx _)).
    - rewrite ltnS leq_eqVlt Hn /= in H. apply: SSAVS.Lemmas.mem_add3.
      exact: (IH _ H).
  Qed.

  Lemma aux_vars_lt_mem avn g n :
    (n < g)%num -> SSAVS.mem (avn, n) (aux_vars_lt avn g).
  Proof.
    move=> H. apply: aux_vars_lt_nat_mem. apply/N2Nat_inj_lt. assumption.
  Qed.

  Lemma aux_vars_lt_nat_svar x avn g :
    SSAVS.mem x (aux_vars_lt_nat avn g) -> svar x = avn.
  Proof.
    elim: g => [| g IH] Hmem //=. rewrite /= in Hmem.
    case/SSAVS.Lemmas.mem_add1 : Hmem => Hmem.
    - rewrite (eqP Hmem); reflexivity.
    - exact: (IH Hmem).
  Qed.

  Lemma aux_vars_lt_svar x avn g :
    SSAVS.mem x (aux_vars_lt avn g) -> svar x = avn.
  Proof. exact: aux_vars_lt_nat_svar. Qed.

  Lemma aux_vars_lt_nat_sidx x avn g :
    SSAVS.mem x (aux_vars_lt_nat avn g) -> (sidx x < N.of_nat g)%num.
  Proof.
    elim: g => [| g IH] Hmem //=. rewrite /= in Hmem.
    case/SSAVS.Lemmas.mem_add1 : Hmem => Hmem.
    - rewrite (eqP Hmem) /=. rewrite Pos.of_nat_succ -positive_nat_N.
      rewrite Nat2Pos.id; last by done. apply/N2Nat_inj_lt.
      rewrite !Nnat.Nat2N.id. done.
    - rewrite Pos.of_nat_succ -positive_nat_N. rewrite Nat2Pos.id; last by done.
      apply: (N.lt_trans _ (N.of_nat g) _ (IH Hmem)).
      apply/N2Nat_inj_lt. rewrite !Nnat.Nat2N.id. exact: ltnSn.
  Qed.

  Lemma aux_vars_lt_sidx x avn g :
    SSAVS.mem x (aux_vars_lt avn g) -> (sidx x < g)%num.
  Proof.
    move=> H. move: (aux_vars_lt_nat_sidx H) => {H} H.
    rewrite Nnat.N2Nat.id in H. assumption.
  Qed.

  Lemma aux_vars_lt_nat_subset avn g1 g2 :
    (g1 <= g2)%N -> SSAVS.subset (aux_vars_lt_nat avn g1) (aux_vars_lt_nat avn g2).
  Proof.
    move=> H. apply: SSAVS.subset_1. move=> [vn vi] /SSAVS.Lemmas.memP Hmem.
    apply/SSAVS.Lemmas.memP. move: (aux_vars_lt_nat_svar Hmem) => /= ->.
    apply: aux_vars_lt_nat_mem. move: (aux_vars_lt_nat_sidx Hmem) => /= Hlt.
    move/N2Nat_inj_lt: Hlt. rewrite Nnat.Nat2N.id => Hlt.
    exact: (Nats.ltn_leq_trans Hlt H).
  Qed.

  Lemma aux_vars_lt_subset avn g1 g2 :
    (g1 <= g2)%num -> SSAVS.subset (aux_vars_lt avn g1) (aux_vars_lt avn g2).
  Proof.
    move=> H. rewrite /aux_vars_lt. apply: aux_vars_lt_nat_subset.
    apply/N2Nat_inj_le. assumption.
  Qed.

  Lemma vars_algred_atom a : vars_zexp (algred_atom a) = vars_atom a.
  Proof. by case: a. Qed.

  Lemma vars_carry_constr c :
    SSAVS.Equal
      (vars_zbexp (eands (carry_constr c)))
      (if add_carry_constraints options then SSAVS.singleton c else SSAVS.empty).
  Proof.
    rewrite /carry_constr. case: (add_carry_constraints options) => //=.
    rewrite !SSAVS.Lemmas.union_emptyr. rewrite SSAVS.Lemmas.union_same.
    reflexivity.
  Qed.


  Lemma algred_program_cons te avn g1 g2 i p zip :
    (g2, zip) = algred_program te avn g1 (i::p) ->
    exists g3, exists zi, exists zp,
          (g3, zi) = algred_instr te avn g1 i /\
          (g2, zp) = algred_program (instr_succ_typenv i te) avn g3 p /\
          zip = zi ++ zp.
  Proof.
    rewrite /=. dcase (algred_instr te avn g1 i) => [[g_hd zhd] Hhd].
    dcase (algred_program (instr_succ_typenv i te) avn g_hd p) => [[g_tl ztl] Htl].
    case=> ? ?; subst. exists g_hd; exists zhd; exists ztl. done.
  Qed.

  Lemma algred_eqn_instr te avn g i :
    algred_instr te avn g (eqn_instr i) = algred_instr te avn g i.
  Proof. case: i => //=. by case=> [e r]. Qed.

  Lemma algred_eqn_program te avn g p :
    algred_program te avn g (eqn_program p) = algred_program te avn g p.
  Proof.
    elim: p te avn g => [| i p IH] te avn g //=.
    dcase (algred_instr te avn g (eqn_instr i)) => [[g_hd zhd] Hhd].
    dcase (algred_program (instr_succ_typenv (eqn_instr i) te) avn g_hd (eqn_program p))
          => [[g_tl ztl] Htl]. dcase (algred_instr te avn g i) => [[g_hd0 zhd0] Hhd0].
    dcase (algred_program (instr_succ_typenv i te) avn g_hd0 p) => [[g_tl0 ztl0] Htl0].
    rewrite algred_eqn_instr Hhd0 in Hhd. case: Hhd => ? ?; subst.
    rewrite IH SSA.eqn_instr_succ_typenv Htl0 in Htl. case: Htl => ? ?; subst.
    reflexivity.
  Qed.

  Lemma algred_cast_idx_inc avn g1 g2 v t a ta zi :
    algred_cast avn g1 v t a ta = (g2, zi) ->
    (g1 <= g2)%num.
  Proof.
    rewrite /algred_cast. case: t; case: ta.
    - move=> wv wa; case: (wv <= wa); case=> ? ?; subst.
      + exact: N.le_refl.
      + exact: N.le_succ_diag_r.
    - move=> wv wa; case: (wv <= wa); case=> ? ?; subst.
      + exact: N.le_succ_diag_r.
      + exact: N.le_succ_diag_r.
    - move=> wv wa; case: (wv < wa); case=> ? ?; subst.
      + exact: N.le_refl.
      + exact: N.le_succ_diag_r.
    - move=> wv wa; case: (wv <= wa); case=> ? ?; subst.
      + exact: N.le_refl.
      + exact: N.le_succ_diag_r.
  Qed.

  Lemma algred_instr_idx_inc te avn g1 g2 i zi :
    algred_instr te avn g1 i = (g2, zi) -> (g1 <= g2)%num.
  Proof.
    ((case: i => /=); intros;
     (let rec tac :=
          match goal with
          | H : (_, _) = (_, _) |- _ => case: H => -> _; tac
          | H : (if ?b then _ else _) = (_, _) |- _ =>
            move: H; case: b; intro; tac
          | H : (match ?t with | Tuint _ => _ | Tsint _ => _ end) = _ |- _ =>
            move: H; case: t; intros; tac
          | H : algred_cast _ _ _ _ _ _ = _ |- _ =>
            exact: (algred_cast_idx_inc H)
          | H : algred_vpc _ _ _ _ = _ |- _ => rewrite /algred_vpc in H; tac
          | |- (?x <= ?x)%num => exact: N.le_refl
          | |- _ => idtac
          end in
      tac)).
  Qed.

  Lemma algred_program_idx_inc te avn g1 g2 p zp :
    algred_program te avn g1 p = (g2, zp) -> (g1 <= g2)%num.
  Proof.
    elim: p te g1 g2 zp => [te g1 g2 zp | hd tl IH te g1 g2 zp] /=.
    - case=> -> _. exact: N.le_refl.
    - dcase (algred_instr te avn g1 hd) => [[g_hd zhd] Hhd].
      dcase (algred_program (instr_succ_typenv hd te) avn g_hd tl) => [[g_tl ztl] Htl].
      case=> <- _. move: (algred_instr_idx_inc Hhd) => Hg1hd.
      move: (IH _ _ _ _ Htl) => Hghdtl. exact: (N.le_trans _ _ _ Hg1hd Hghdtl).
  Qed.



  Definition avars_newer_than_var (avn : N) (g : N) (v : ssavar) : Prop :=
    (svar v != avn) \/ (sidx v < g)%num.

  Definition avars_newer_than (avn : N) (g : N) (vs : SSAVS.t) :=
    forall v, SSAVS.mem v vs -> avars_newer_than_var avn g v.


  Lemma svar_notin_newer_than_singleton avn g v :
    svar_notin avn (SSAVS.singleton v) -> avars_newer_than_var avn g v.
  Proof.
    move=> H. move: (svar_notin_singleton1 H) => {H} H. rewrite /avars_newer_than_var.
    left; rewrite eq_sym; assumption.
  Qed.

  Lemma svar_notin_newer_than avn g vs :
    svar_notin avn vs -> avars_newer_than avn g vs.
  Proof.
    move=> H [vn vi] Hv. case Hvn: (vn == avn).
    - move: (H vi) => Hmem. rewrite -(eqP Hvn) Hv in Hmem. discriminate.
    - left. move/idP/negP: Hvn. by apply.
  Qed.


  Lemma avars_newer_than_var_le avn g1 g2 v :
    (g1 <= g2)%num -> avars_newer_than_var avn g1 v ->
    avars_newer_than_var avn g2 v.
  Proof.
    move=> Hle [] Hnew.
    - left. assumption.
    - right. exact: (N.lt_le_trans _ _ _ Hnew Hle).
  Qed.

  Lemma avars_newer_than_le avn g1 g2 vs :
    (g1 <= g2)%num -> avars_newer_than avn g1 vs ->
    avars_newer_than avn g2 vs.
  Proof.
    move=> Hle Hnew x Hx. move: (Hnew x Hx). exact: (avars_newer_than_var_le Hle).
  Qed.

  Lemma avars_newer_than_mem avn g1 g2 vs :
    avars_newer_than avn g1 vs -> SSAVS.mem (avn, g2) vs ->
    (g2 < g1)%num.
  Proof.
    move=> Hnew Hmem. move: (Hnew (avn, g2) Hmem). rewrite /avars_newer_than_var.
    case => /= H.
    - rewrite eqxx in H. discriminate.
    - assumption.
  Qed.

  Lemma avars_newer_than_empty avn g : avars_newer_than avn g SSAVS.empty.
  Proof. done. Qed.

  Lemma avars_newer_than_singleton avn g v :
    avars_newer_than avn g (SSAVS.singleton v) <->
    avars_newer_than_var avn g v.
  Proof.
    split.
    - move=> Hnew. apply: (Hnew v). apply: SSAVS.Lemmas.mem_singleton2. exact: eqxx.
    - move=> Hnew x Hmem. move: (SSAVS.Lemmas.mem_singleton1 Hmem) => {Hmem} /eqP Heq.
      rewrite Heq; assumption.
  Qed.

  Lemma avars_newer_than_add avn g v vs :
    avars_newer_than avn g (SSAVS.add v vs) <->
    (avars_newer_than_var avn g v /\ avars_newer_than avn g vs).
  Proof.
    split.
    - move=> H; split.
      + exact: (H v (SSAVS.Lemmas.mem_add2 vs (eqxx v))).
      + move=> x Hx. move: (SSAVS.Lemmas.mem_add3 v Hx) => Hmem. exact: (H x Hmem).
    - move=> [Hv Hvs] x Hx. case/SSAVS.Lemmas.mem_add1: Hx.
      + move=> Hxv. rewrite (eqP Hxv). assumption.
      + move=> Hx. exact: (Hvs x Hx).
  Qed.

  Lemma avars_newer_than_union avn g vs1 vs2 :
    avars_newer_than avn g (SSAVS.union vs1 vs2) <->
    (avars_newer_than avn g vs1 /\ avars_newer_than avn g vs2).
  Proof.
    split.
    - move=> Hun; split; move=> x Hx.
      + exact: (Hun x (SSAVS.Lemmas.mem_union2 vs2 Hx)).
      + exact: (Hun x (SSAVS.Lemmas.mem_union3 vs1 Hx)).
    - move=> [H1 H2] x Hx. case/SSAVS.Lemmas.mem_union1: Hx => Hx.
      + exact: (H1 x Hx).
      + exact: (H2 x Hx).
  Qed.

  Lemma avars_newer_than_equal avn g vs1 vs2 :
    SSAVS.Equal vs1 vs2 -> avars_newer_than avn g vs1 ->
    avars_newer_than avn g vs2.
  Proof.
    move=> Heq Hnew1 v Hmem. apply: Hnew1.
    move: (SSAVS.Lemmas.P.equal_sym Heq) => {Heq} Heq.
    exact: (SSAVS.Lemmas.mem_equal Hmem Heq).
  Qed.

  Lemma avars_newer_than_eqn avn g e :
    svar_notin avn (vars_bexp e) ->
    avars_newer_than avn g (vars_zbexp (eqn_bexp e)).
  Proof.
    case: e => [e r] /=. move/svar_notin_union => /= [He Hr].
    exact: (svar_notin_newer_than g He).
  Qed.

  Lemma avars_newer_than_split_eqn avn g e :
    svar_notin avn (vars_bexp e) ->
    avars_newer_than avn g (vars_zbexp (eands (split_eand (eqn_bexp e)))).
  Proof.
    move=> Hni.
    apply: (avars_newer_than_equal
              (SSAVS.Lemmas.P.equal_sym (vars_eands_split_eand (eqn_bexp e)))).
    exact: (avars_newer_than_eqn g).
  Qed.

  Lemma new_svar_newer_than vs g : avars_newer_than (new_svar vs) g vs.
  Proof.
    exact: (svar_notin_newer_than g (new_svar_notin vs)).
  Qed.


  Ltac split_avars_newer_than :=
    match goal with
    | |- avars_newer_than _ _ (SSAVS.union _ _) =>
      apply/avars_newer_than_union; split
    end.

  Ltac solve_avars_newer_than :=
    match goal with
    | |- avars_newer_than _ _ (SSAVS.singleton _) =>
      apply/avars_newer_than_singleton; solve_avars_newer_than
    | |- avars_newer_than _ _ (vars_zbexp (eands (carry_constr ?c))) =>
      apply: (avars_newer_than_equal
                (SSAVS.Lemmas.P.equal_sym (vars_carry_constr c)));
      case: (add_carry_constraints options); solve_avars_newer_than
    | H : is_true (?avn != Var.svar ?t) |- avars_newer_than_var ?avn _ ?t =>
      left; rewrite eq_sym; assumption
    | H : svar_notin ?avn (vars_atom ?a) |-
      avars_newer_than ?avn ?g (vars_zexp (algred_atom ?a)) =>
      rewrite vars_algred_atom; exact: (svar_notin_newer_than g H)
    | |- avars_newer_than _ _ SSAVS.empty =>
      exact: avars_newer_than_empty
    | |- avars_newer_than_var _ (N.succ ?g) (_, ?g) =>
      right; exact: N.lt_succ_diag_r
    end.

  Lemma algred_instr_newer_than E avn g1 g2 i zs :
    algred_instr E avn g1 i = (g2, zs) ->
    svar_notin avn (vars_instr i) ->
    avars_newer_than avn g2 (vars_zbexp (eands zs)).
  Proof.
    move=> H.
    case: i H => /=;

    try (intros; repeat case_pairs; rewrite /=;
    repeat case_svar_notin;
    repeat split_avars_newer_than;
    solve_avars_newer_than).

    (* algred_cast *)
    intros; repeat case_pairs; rewrite /=;
    repeat case_svar_notin;
    repeat split_avars_newer_than.
    move: H; rewrite /algred_cast => H.
    repeat case_pairs; rewrite /=; repeat split_avars_newer_than;
    solve_avars_newer_than.

    (* algred_vpc *)
    intros; repeat case_pairs; rewrite /=;
    repeat case_svar_notin;
    repeat split_avars_newer_than.
    move: H; rewrite /algred_vpc => H.
    repeat case_pairs; rewrite /=; repeat split_avars_newer_than;
    solve_avars_newer_than.

    intros; repeat case_pairs; rewrite /=.
    exact: (avars_newer_than_split_eqn g2 H0).
  Qed.

  Lemma algred_program_newer_than E avn g1 g2 p zs :
    algred_program E avn g1 p = (g2, zs) ->
    svar_notin avn (vars_program p) ->
    avars_newer_than avn g2 (vars_zbexp (eands zs)).
  Proof.
    elim: p E g1 g2 zs => [| i p IH] E g1 g2 zs /=.
    - move=> *; case_pairs. exact: avars_newer_than_empty.
    - dcase (algred_instr E avn g1 i) => [[g_hd zhd] Hhd].
      dcase (algred_program (instr_succ_typenv i E) avn g_hd p) => [[g_tl ztl] Htl].
      case=> ? ?; subst. move/svar_notin_union=> [Hi Hp].
      apply: (avars_newer_than_equal
                (SSAVS.Lemmas.P.equal_sym (vars_eands_cat zhd ztl))).
      apply/avars_newer_than_union; split.
      + apply: (avars_newer_than_le (algred_program_idx_inc Htl)).
        exact: (algred_instr_newer_than Hhd Hi).
      + exact: (IH _ _ _ _ Htl Hp).
  Qed.

End AlgebraicReduction.





(** Split a specification into algebraic soundness conditions, range specification,
    and algebraic specification *)
Section SplitSpec.

  Arguments Z.sub m n : simpl nomatch.

  Import SSA.

  Ltac split_disjoint :=
    match goal with
    | H : is_true (VSLemmas.disjoint _ (SSAVS.singleton _)) |- _ =>
      rewrite VSLemmas.disjoint_singleton in H
    | H : is_true (VSLemmas.disjoint _ (SSAVS.add _ _)) |- _ =>
      let H1 := fresh "Hdisj" in let H2 := fresh "Hdisj" in
      rewrite VSLemmas.disjoint_add in H;
      move/andP: H => [H1 H2]
    end.

  Ltac simplify_types :=
    repeat
    match goal with
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
    end.

  Ltac defined_dec :=
    match goal with
    | H : is_true (are_defined ?vs ?E) |-
      is_true (are_defined ?vs (SSATE.add _ _ (SSATE.add _ _ ?E))) =>
      apply: are_defined_addr; apply: are_defined_addr; exact: H
    | H : is_true (are_defined ?vs ?E) |-
      is_true (are_defined ?vs (SSATE.add _ _ ?E)) =>
      apply: are_defined_addr; exact: H
    end.

  Ltac ssa_vars_unchanged_instr_to_mem :=
    match goal with
    | H : is_true (ssa_vars_unchanged_instr ?vs ?i) |- _ =>
      let Hdisj := fresh "Hdisj" in
      (have: (ssa_vars_unchanged_instr vs i) by assumption);
      (rewrite ssa_unchanged_instr_disjoint_lvs => /= Hdisj);
      repeat split_disjoint
    end.

  (* State equivalence. *)

  Definition bvz_eq (E : SSATE.env) (sb : SSAStore.t) (sz : ZSSAStore.t) : Prop :=
    forall x, acc2z E x sb = ZSSAStore.acc x sz.

  Lemma bvz_eq_upd E v bv zv sb sz :
    bvz_eq E sb sz -> bv2z (SSATE.vtyp v E) bv = zv ->
    bvz_eq E (SSAStore.upd v bv sb) (ZSSAStore.upd v zv sz).
  Proof.
    move=> Heq Hbv x. case Hxv: (x == v).
    - rewrite (acc2z_upd_eq Hxv) (ZSSAStore.acc_upd_eq Hxv) (eqP Hxv). exact: Hbv.
    - move/idP/negP: Hxv => Hxv.
      rewrite (acc2z_upd_neq Hxv) (ZSSAStore.acc_upd_neq Hxv). exact: (Heq x).
  Qed.

  Lemma bvz_eq_upd2 E vh vl bvh bvl zvh zvl sb sz :
    bvz_eq E sb sz ->
    bv2z (SSATE.vtyp vh E) bvh = zvh -> bv2z (SSATE.vtyp vl E) bvl = zvl ->
    bvz_eq E (SSAStore.upd2 vh bvh vl bvl sb) (ZSSAStore.upd2 vh zvh vl zvl sz).
  Proof.
    move=> Heq Hbvh Hbvl x. case Hxvl: (x == vl).
    - rewrite (acc2z_upd_eq Hxvl) (ZSSAStore.acc_upd_eq Hxvl) (eqP Hxvl). exact: Hbvl.
    - move/idP/negP: Hxvl => Hxvl.
      rewrite (acc2z_upd_neq Hxvl) (ZSSAStore.acc_upd_neq Hxvl). case Hxvh: (x == vh).
      + rewrite (acc2z_upd_eq Hxvh) (ZSSAStore.acc_upd_eq Hxvh) (eqP Hxvh).
        exact: Hbvh.
      + move/idP/negP: Hxvh => Hxvh.
        rewrite (acc2z_upd_neq Hxvh) (ZSSAStore.acc_upd_neq Hxvh). exact: (Heq x).
  Qed.

  Lemma bvz_eq_eval_atom a E bs zs :
    bvz_eq E bs zs ->
    ZSSA.eval_zexp (algred_atom a) zs = bv2z (atyp a E) (eval_atom a bs).
  Proof.
    move=> Heq. case: a => /=.
    - move=> v. rewrite -Heq. reflexivity.
    - move=> t b. reflexivity.
  Qed.



  (* State equivalence except newly introduced variables. *)

  Definition bvz_eqm (E : SSATE.env) (tmp : VarOrder.t)
             (sb : SSAStore.t) (sz : ZSSAStore.t) : Prop :=
    forall x, tmp != svar x -> acc2z E x sb = ZSSAStore.acc x sz.

  Lemma bvz_eq_eqm E tmp sb sz : bvz_eq E sb sz -> bvz_eqm E tmp sb sz.
  Proof. move=> H x _. exact: H. Qed.

  Lemma bvz_eqm_upd E v bv zv tmp sb sz :
    bvz_eqm E tmp sb sz -> bv2z (SSATE.vtyp v E) bv = zv ->
    bvz_eqm E tmp (SSAStore.upd v bv sb) (ZSSAStore.upd v zv sz).
  Proof.
    move=> Heq Hbv x Hne. case Hxv: (x == v).
    - rewrite (acc2z_upd_eq Hxv) (ZSSAStore.acc_upd_eq Hxv) (eqP Hxv). exact: Hbv.
    - move/idP/negP: Hxv => Hxv.
      rewrite (acc2z_upd_neq Hxv) (ZSSAStore.acc_upd_neq Hxv). exact: (Heq _ Hne).
  Qed.

  Lemma bvz_eqm_upd2 E vh vl bvh bvl zvh zvl tmp sb sz :
    bvz_eqm E tmp sb sz ->
    bv2z (SSATE.vtyp vh E) bvh = zvh -> bv2z (SSATE.vtyp vl E) bvl = zvl ->
    bvz_eqm E tmp (SSAStore.upd2 vh bvh vl bvl sb) (ZSSAStore.upd2 vh zvh vl zvl sz).
  Proof.
    move=> Heq Hbvh Hbvl x Hne. case Hxvl: (x == vl).
    - rewrite (acc2z_upd_eq Hxvl) (ZSSAStore.acc_upd_eq Hxvl) (eqP Hxvl). exact: Hbvl.
    - move/idP/negP: Hxvl => Hxvl.
      rewrite (acc2z_upd_neq Hxvl) (ZSSAStore.acc_upd_neq Hxvl). case Hxvh: (x == vh).
      + rewrite (acc2z_upd_eq Hxvh) (ZSSAStore.acc_upd_eq Hxvh) (eqP Hxvh).
        exact: Hbvh.
      + move/idP/negP: Hxvh => Hxvh.
        rewrite (acc2z_upd_neq Hxvh) (ZSSAStore.acc_upd_neq Hxvh). exact: (Heq _ Hne).
  Qed.

  Lemma bvz_eqm_upd2_aux E c v bvc bvv zvc zvv zvt tmp idx sb sz :
  bvz_eqm E tmp sb sz ->
  bv2z (SSATE.vtyp c E) bvc = zvc -> bv2z (SSATE.vtyp v E) bvv = zvv ->
    tmp != svar c -> tmp != svar v ->
    bvz_eqm E tmp
            (SSAStore.upd2 v bvv c bvc sb)
            (ZSSAStore.upd c
                           zvc
                           (ZSSAStore.upd2 v zvv (tmp, idx) zvt sz)).
  Proof.
    move=> Heqm Hc Hv Hnec Hnev x Hnex. case Hxc: (x == c).
    - rewrite (acc2z_upd2_eq2 Hxc) (ZSSAStore.acc_upd2_eq2 Hxc) (eqP Hxc). exact: Hc.
    - move/idP/negP: Hxc => Hxc. rewrite (ZSSAStore.acc_upd_neq Hxc).
      have Hxtmp: x != (tmp, idx).
      { apply/negP => Heq. move/negP: Hnex; apply. by rewrite (eqP Heq). }
      case Hxv: (x == v).
      + rewrite (acc2z_upd2_eq1 Hxv Hxc) (ZSSAStore.acc_upd2_eq1 Hxv Hxtmp) (eqP Hxv).
        exact: Hv.
      + move/idP/negP: Hxv => Hxv.
        rewrite (acc2z_upd2_neq Hxv Hxc) (ZSSAStore.acc_upd2_neq Hxv Hxtmp).
        exact: (Heqm _ Hnex).
  Qed.


  (* State equivalence considering only variables in an environment. *)

  Definition bvz_eqi (E : SSATE.env) (sb : SSAStore.t) (sz : ZSSAStore.t) : Prop :=
    forall x, SSATE.mem x E -> acc2z E x sb = ZSSAStore.acc x sz.

  Lemma bvz_eq_eqi E sb sz : bvz_eq E sb sz -> bvz_eqi E sb sz.
  Proof. move=> Heq x _. exact: (Heq x). Qed.

  Lemma bvz_eqi_upd E v bv zv sb sz :
    bvz_eqi E sb sz -> bv2z (SSATE.vtyp v E) bv = zv ->
    bvz_eqi E (SSAStore.upd v bv sb) (ZSSAStore.upd v zv sz).
  Proof.
    move=> Heq Hbv x Hx. case Hxv: (x == v).
    - rewrite (acc2z_upd_eq Hxv) (ZSSAStore.acc_upd_eq Hxv) (eqP Hxv). exact: Hbv.
    - move/idP/negP: Hxv => Hxv.
      rewrite (acc2z_upd_neq Hxv) (ZSSAStore.acc_upd_neq Hxv). exact: (Heq x).
  Qed.

  Lemma bvz_eqi_upd2 E vh vl bvh bvl zvh zvl sb sz :
    bvz_eqi E sb sz ->
    bv2z (SSATE.vtyp vh E) bvh = zvh -> bv2z (SSATE.vtyp vl E) bvl = zvl ->
    bvz_eqi E (SSAStore.upd2 vh bvh vl bvl sb) (ZSSAStore.upd2 vh zvh vl zvl sz).
  Proof.
    move=> Heq Hbvh Hbvl x Hx. case Hxvl: (x == vl).
    - rewrite (acc2z_upd_eq Hxvl) (ZSSAStore.acc_upd_eq Hxvl) (eqP Hxvl). exact: Hbvl.
    - move/idP/negP: Hxvl => Hxvl.
      rewrite (acc2z_upd_neq Hxvl) (ZSSAStore.acc_upd_neq Hxvl). case Hxvh: (x == vh).
      + rewrite (acc2z_upd_eq Hxvh) (ZSSAStore.acc_upd_eq Hxvh) (eqP Hxvh).
        exact: Hbvh.
      + move/idP/negP: Hxvh => Hxvh.
        rewrite (acc2z_upd_neq Hxvh) (ZSSAStore.acc_upd_neq Hxvh). exact: (Heq x).
  Qed.

  Lemma bvz_eqi_eval_atom a E bs zs :
    bvz_eqi E bs zs -> are_defined (vars_atom a) E ->
    ZSSA.eval_zexp (algred_atom a) zs = bv2z (atyp a E) (eval_atom a bs).
  Proof.
    move=> Heq. case: a => /=.
    - move=> v; rewrite are_defined_singleton=> Hdef. rewrite -Heq; first reflexivity.
      exact: Hdef.
    - move=> t b _. reflexivity.
  Qed.

  Lemma bvz_eqi_eval_eexp E e bs zs :
    bvz_eqi E bs zs -> are_defined (ZSSA.vars_zexp e) E ->
    eval_eexp e E bs = ZSSA.eval_zexp e zs.
  Proof.
    move=> Heq. elim: e => //=.
    - move=> x; rewrite are_defined_singleton=> Hdef. exact: (Heq x Hdef).
    - move=> op e IH Hdef. rewrite (IH Hdef). reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite are_defined_union=> /andP [Hdef1 Hdef2].
      rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
    - move=> e IH n Hdef. rewrite (IH Hdef). reflexivity.
  Qed.

  Lemma bvz_eqi_eval_eexps E es bs zs :
    bvz_eqi E bs zs -> are_defined (ZSSA.vars_zexps es) E ->
    eval_eexps es E bs = ZSSA.eval_zexps es zs.
  Proof.
    elim: es => [| e es IH] //=. rewrite are_defined_union => Heqi /andP [Hdef1 Hdef2].
    rewrite (bvz_eqi_eval_eexp Heqi Hdef1) (IH Heqi Hdef2). reflexivity.
  Qed.

  Lemma bvz_eqi_eval_ebexp E e bs zs :
    bvz_eqi E bs zs -> are_defined (vars_ebexp e) E ->
    eval_ebexp e E bs <-> ZSSA.eval_zbexp (eands (split_eand e)) zs.
  Proof.
    move=> Heq. elim: e => //=.
    - move=> e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (bvz_eqi_eval_eexp Heq Hdef1) (bvz_eqi_eval_eexp Heq Hdef2). tauto.
    - move=> e1 e2 ms.
      rewrite !are_defined_union => /andP [Hdef1 /andP [Hdef2 Hdefms]].
      rewrite (bvz_eqi_eval_eexp Heq Hdef1) (bvz_eqi_eval_eexp Heq Hdef2)
              (bvz_eqi_eval_eexps Heq Hdefms). tauto.
    - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      move: (IH1 Hdef1) (IH2 Hdef2) => H1 H2. split.
      + move=> [He1 He2]. apply/ZSSA.eval_zbexp_eands_cat. tauto.
      + move/ZSSA.eval_zbexp_eands_cat=> [He1 He2]. tauto.
  Qed.

  Lemma submap_bvz_eqi E1 E2 bs zs :
    TELemmas.submap E1 E2 -> bvz_eqi E2 bs zs -> bvz_eqi E1 bs zs.
  Proof.
    move=> Hsub Heqi x Hx. move/defmemP: Hx => Hx.
    move: (TELemmas.submap_mem Hsub Hx) => Hx2. rewrite -(Heqi x Hx2).
    exact: (submap_acc2z Hsub Hx).
  Qed.


  (* Convert bit-vector stores to integer stores. *)

  Definition zssa_store_key (v : ssavar) : option ssavar := Some v.

  Definition zssa_store_value (E : SSATE.env) (v : ssavar) (bs : bits) : Z :=
    bv2z (SSATE.vtyp v E) bs.

  Lemma zssa_store_key_eq_none :
    forall k1 k2 : ssavar, k1 == k2 -> zssa_store_key k1 = None -> zssa_store_key k2 = None.
  Proof. move=> k1 k2 Heqk Hn. rewrite -(eqP Heqk). assumption. Qed.

  Lemma zssa_store_key_eq_some :
    forall (k1 k2 : ssavar) (fk1 : ssavar),
      k1 == k2 -> zssa_store_key k1 = Some fk1 ->
      exists fk2 : ssavar, zssa_store_key k2 = Some fk2 /\ fk1 == fk2.
  Proof. move=> k1 k2 fk1 Heqk Hfk1. exists fk1. rewrite -(eqP Heqk). done. Qed.

  Lemma zssa_store_key_some_inj k1 k2 v :
    zssa_store_key k1 = Some v -> zssa_store_key k2 = Some v -> k1 = k2.
  Proof.
    rewrite /zssa_store_key. case=> ?; case=> ?; subst. reflexivity.
  Qed.

  Lemma zssa_store_key_neq_some :
    forall (k1 k2 : ssavar) (fk1 fk2 : ssavar),
      ~ k1 == k2 -> zssa_store_key k1 = Some fk1 -> zssa_store_key k2 = Some fk2 ->
      ~ fk1 == fk2.
  Proof.
    move=> k1 k2 fk1 fk2 Hneqk Hfk1 Hfk2 Heqk. rewrite (eqP Heqk) in Hfk1.
    apply: Hneqk. apply/eqP. exact: (zssa_store_key_some_inj Hfk1 Hfk2).
  Qed.

  Lemma zssa_store_value_eq_key E :
    forall (k1 k2 : ssavar) (v : bits),
      k1 == k2 -> zssa_store_value E k1 v = zssa_store_value E k2 v.
  Proof. move=> ? ? ? /eqP H; subst. reflexivity. Qed.

  Definition algred_store (E : SSATE.env) (bs : SSAStore.t) : ZSSAStore.t :=
    M2ZSSA.map2map zssa_store_key (zssa_store_value E) bs.

  Lemma acc_algred_store E v s : ZSSAStore.acc v (algred_store E s) = acc2z E v s.
  Proof.
    rewrite /algred_store /acc2z /ZSSAStore.acc /SSAStore.acc.
    have Hfk: zssa_store_key v = Some v by reflexivity.
    dcase (SSAStore.M.find v s); case.
    - move=> bs Hf. rewrite (M2ZSSA.map2map_find_some zssa_store_key_eq_none
                                                      zssa_store_key_eq_some
                                                      zssa_store_key_neq_some
                                                      (zssa_store_value_eq_key E) Hfk Hf).
      reflexivity.
    - move=> Hf. rewrite (M2ZSSA.map2map_find_none zssa_store_key_eq_none
                                                   zssa_store_key_eq_some
                                                   zssa_store_key_neq_some
                                                   (zssa_store_value_eq_key E) Hfk Hf).
      rewrite /bv2z /BitsValueType.default /=. rewrite to_Z_nil.
      case: (SSATE.vtyp v E); reflexivity.
  Qed.

  Lemma algred_store_eq E bs : bvz_eq E bs (algred_store E bs).
  Proof. move=> x. symmetry. exact: acc_algred_store. Qed.

  Lemma algred_store_eqi E bs : bvz_eqi E bs (algred_store E bs).
  Proof. move=> x _. symmetry. exact: acc_algred_store. Qed.

  Lemma bvs_bvz_eqi E bs1 bs2 zs :
    bvs_eqi E bs1 bs2 -> bvz_eqi E bs1 zs -> bvz_eqi E bs2 zs.
  Proof.
    move=> Hseq Hzeq x Hx. rewrite -(Hzeq x Hx) /acc2z.
    rewrite (Hseq x Hx). reflexivity.
  Qed.

  Lemma bvz_bvs_eqi E bs1 bs2 zs :
    SSAStore.conform bs1 E -> SSAStore.conform bs2 E ->
    bvz_eqi E bs1 zs -> bvz_eqi E bs2 zs -> bvs_eqi E bs1 bs2.
  Proof.
    move=> Hcon1 Hcon2 Hzeq1 Hzeq2 x Hx. move: (Hzeq1 x Hx) (Hzeq2 x Hx).
    rewrite /acc2z /bv2z. case: (SSATE.vtyp x E) => wx.
    - move=> H1 H2; rewrite -H2 in H1.
      move: (Hcon1 x Hx) (Hcon2 x Hx) => Hs1 Hs2; rewrite Hs1 in Hs2.
      exact: (to_Zpos_inj_ss Hs2 H1).
    - move=> H1 H2; rewrite -H2 in H1.
      move: (Hcon1 x Hx) (Hcon2 x Hx) => Hs1 Hs2; rewrite Hs1 in Hs2.
      exact: (to_Z_inj_ss Hs2 H1).
  Qed.


  (* Assign auxiliary variables *)

  Definition algred_upd_avars_cast
             (avn : VarOrder.t) (g : N) (v : SSAVarOrder.t) vtyp a atyp
             (zs : ZSSAStore.t) : N * ZSSAStore.t :=
    match vtyp, atyp with
    | Tuint wv, Tuint wa =>
      if wv >= wa then
        (g, zs)
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (algred_atom a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd discarded q zs in
        (g', zs')
    | Tuint wv, Tsint wa =>
      if wv >= wa then
        let a_sign := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (algred_atom a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd a_sign (-q)%Z zs in
        (g', zs')
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (algred_atom a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd discarded q zs in
        (g', zs')
    | Tsint wv, Tuint wa =>
      if wv > wa then
        (g, zs)
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (algred_atom a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let (q', r') := Z.div_eucl r (z2expn (Z.of_nat wv - 1)) in
        let zs' := ZSSAStore.upd discarded (q + q')%Z zs in
        (g', zs')
    | Tsint wv, Tsint wa =>
      if wv >= wa then
        (g, zs)
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (algred_atom a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let (q', r') := Z.div_eucl r (z2expn (Z.of_nat wv - 1)) in
        let zs' := ZSSAStore.upd discarded (q + q')%Z zs in
        (g', zs')
    end.

  Definition algred_upd_avars_instr
             (E : SSATE.env) (avn : VarOrder.t) (g : N) (i : instr)
             (zs : ZSSAStore.t) : N * ZSSAStore.t :=
    match i with
    | Imov v a => (g, zs)
    | Ishl v a n => (g, zs)
    | Icshl vh vl a1 a2 n => (g, zs)
    | Inondet v t => (g, zs)
    | Icmov v c a1 a2 => (g, zs)
    | Inop => (g, zs)
    | Inot v t a => (g, zs)
    | Iadd v a1 a2 => (g, zs)
    | Iadds c v a1 a2 => (g, zs)
    | Iadc v a1 a2 y => (g, zs)
    | Iadcs c v a1 a2 y => (g, zs)
    | Isub v a1 a2 => (g, zs)
    | Isubc c v a1 a2 => (g, zs)
    | Isubb c v a1 a2 => (g, zs)
    | Isbc v a1 a2 y => (g, zs)
    | Isbcs c v a1 a2 y => (g, zs)
    | Isbb v a1 a2 y => (g, zs)
    | Isbbs c v a1 a2 y => (g, zs)
    | Imul v a1 a2 => (g, zs)
    | Imull vh vl a1 a2 => (g, zs)
    | Imulj v a1 a2 => (g, zs)
    | Isplit vh vl a n => (g, zs)
    | Iand v t a1 a2 => (g, zs)
    | Ior v t a1 a2 => (g, zs)
    | Ixor v t a1 a2 => (g, zs)
    | Icast v t a => algred_upd_avars_cast avn g v t a (atyp a E) zs
    | Ivpc v t a => (g, zs)
    | Ijoin v ah al => (g, zs)
    | Iassume e => (g, zs)
    end.

  Fixpoint algred_upd_avars_program
             (E : SSATE.env) (avn : VarOrder.t) (g : N) (p : program)
             (zs : ZSSAStore.t) : N * ZSSAStore.t :=
    match p with
    | [::] => (g, zs)
    | hd::tl =>
      let (g_hd, zs_hd) := algred_upd_avars_instr E avn g hd zs in
      let (g_tl, zs_tl) := algred_upd_avars_program
                             (instr_succ_typenv hd E) avn g_hd tl zs_hd in
      (g_tl, zs_tl)
    end.

  Definition algred_upd_avars
             (E : SSATE.env) (avn : VarOrder.t) (g : N) (p : program)
             (zs : ZSSAStore.t) : ZSSAStore.t :=
    snd (algred_upd_avars_program E avn g p zs).


  Lemma algred_upd_avars_instr_eqn E avn g i zs :
    algred_upd_avars_instr E avn g (eqn_instr i) zs =
    algred_upd_avars_instr E avn g i zs.
  Proof. case: i => //=. move=> [] e r /=. reflexivity. Qed.

  Lemma algred_upd_avars_program_eqn E avn g p zs :
    algred_upd_avars_program E avn g (eqn_program p) zs =
    algred_upd_avars_program E avn g p zs.
  Proof.
    elim: p E g zs => [| i p IH E g zs] //=.
    dcase (algred_upd_avars_instr E avn g (eqn_instr i) zs) => [[g_hde zs_hde] Hhde].
    dcase (algred_upd_avars_program
             (instr_succ_typenv (eqn_instr i) E) avn g_hde (eqn_program p) zs_hde) =>
    [[g_tle zs_tle] Htle].
    rewrite algred_upd_avars_instr_eqn in Hhde. rewrite IH eqn_instr_succ_typenv in Htle.
    rewrite Hhde Htle. reflexivity.
  Qed.

  Corollary algred_upd_avars_eqn E avn g p zs :
    algred_upd_avars E avn g (eqn_program p) zs = algred_upd_avars E avn g p zs.
  Proof.
    rewrite /algred_upd_avars algred_upd_avars_program_eqn. reflexivity.
  Qed.


  Lemma algred_upd_avars_cast_gen avn g1 v tv a ta g2 g3 zs zs1 zs2 :
    algred_cast avn g1 v tv a ta = (g2, zs) ->
    algred_upd_avars_cast avn g1 v tv a ta zs1 = (g3, zs2) ->
    g2 = g3.
  Proof.
    rewrite /algred_cast /algred_upd_avars_cast. case: tv => n.
    - case: ta => m; case: (m <= n); move=> *; repeat case_pairs; reflexivity.
    - case: ta => m.
      + case: (m < n); move=> *; repeat case_pairs; reflexivity.
      + case: (m <= n); move=> *; repeat case_pairs; reflexivity.
  Qed.

  Lemma algred_upd_avars_instr_gen o E avn i g1 g2 g3 zs zs1 zs2 :
    algred_instr o E avn g1 i = (g2, zs) ->
    algred_upd_avars_instr E avn g1 i zs1 = (g3, zs2) ->
    g2 = g3.
  Proof.
    case: i => /=; intros; repeat case_pairs; try reflexivity.
    (* algred_cast *)
    - exact: (algred_upd_avars_cast_gen H H0).
    (* algred_vpc *)
    - rewrite /algred_vpc in H. repeat case_pairs. reflexivity.
  Qed.

  Lemma algred_upd_avars_program_gen o E avn p g1 g2 g3 zs zs1 zs2 :
    algred_program o E avn g1 p = (g2, zs) ->
    algred_upd_avars_program E avn g1 p zs1 = (g3, zs2) ->
    g2 = g3.
  Proof.
    elim: p E g1 g2 g3 zs zs1 zs2 => [| i p IH] E g1 g2 g3 zs zs1 zs3 /=.
    - intros; repeat case_pairs. reflexivity.
    - dcase (algred_instr o E avn g1 i) => [[g_hd zhd] Hhd].
      dcase (algred_program o (instr_succ_typenv i E) avn g_hd p) => [[g_tl ztl] Htl].
      case=> ? ?; subst. dcase (algred_upd_avars_instr E avn g1 i zs1) =>
                         [[algred_g_hd algred_zs_hd] Halgred_hd].
      dcase (algred_upd_avars_program
               (instr_succ_typenv i E) avn algred_g_hd p algred_zs_hd) =>
      [[algred_g_tl  algred_zs_tl] Halgred_tl]. case=> ? ?; subst.
      rewrite (algred_upd_avars_instr_gen Hhd Halgred_hd) in Htl.
      rewrite (IH _ _ _ _ _ _ _ Htl Halgred_tl). reflexivity.
  Qed.

  Lemma algred_upd_avars_cast_idx_inc avn g1 v tv a ta g2 zs1 zs2 :
    algred_upd_avars_cast avn g1 v tv a ta zs1 = (g2, zs2) ->
    (g1 <= g2)%num.
  Proof.
    move=> Hupd. move: (Logic.eq_refl (algred_cast avn g1 v tv a ta)).
    move: {2}(algred_cast avn g1 v tv a ta) => [g3 zi] Hbvz.
    move: (algred_cast_idx_inc Hbvz) => Hg13.
    rewrite (algred_upd_avars_cast_gen Hbvz Hupd) in Hg13. assumption.
  Qed.

  Lemma algred_upd_avars_instr_idx_inc E avn i g1 g2 zs1 zs2 :
    algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    (g1 <= g2)%num.
  Proof.
    move=> Hupd. move: (Logic.eq_refl (algred_instr default_options E avn g1 i)).
    move: {2}(algred_instr default_options E avn g1 i) => [g3 zi] Hbvz.
    move: (algred_instr_idx_inc Hbvz) => Hg13.
    rewrite (algred_upd_avars_instr_gen Hbvz Hupd) in Hg13. assumption.
  Qed.

  Lemma algred_upd_avars_program_idx_inc E avn p g1 g2 zs1 zs2 :
    algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    (g1 <= g2)%num.
  Proof.
    move=> Hupd. move: (Logic.eq_refl (algred_program default_options E avn g1 p)).
    move: {2}(algred_program default_options E avn g1 p) => [g3 zp] Hbvz.
    move: (algred_program_idx_inc Hbvz) => Hg13.
    rewrite (algred_upd_avars_program_gen Hbvz Hupd) in Hg13. assumption.
  Qed.


  Lemma algred_upd_avars_instr_acc_ne E avn g1 i zs1 g2 zs2 v :
    svar v != avn -> algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    Ltac mytac :=
      (move=> *; match goal with
                 | H : (_, _) = (_, _) |- _ =>
                   case: H; move=> ? ?; subst; mytac
                 | H : is_true (?x != ?y) |-
                   ZSSAStore.acc ?x (ZSSAStore.upd ?y _ ?zs) = ZSSAStore.acc ?x ?zs =>
                   exact: (ZSSAStore.acc_upd_neq H)
                 | |- _ => idtac
                 end).
    move=> Hne. case: i => //=; try by mytac.
    (* Icast *)
    move=> x xt a Hupd. have: v != (avn, g1).
    { apply/negP=> Heq. move/negP: Hne; apply. case: v Heq. move=> ? ? /eqP [] -> _.
      exact: eqxx. } move=> {Hne} Hne. move: Hupd. rewrite /algred_upd_avars_cast.
    move=> *; repeat case_pairs; by mytac.
  Qed.

  Lemma algred_upd_avars_program_acc_ne E avn g1 p zs1 g2 zs2 v :
    svar v != avn -> algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    move=> Hne. elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 /=.
    - case=> _ ->. reflexivity.
    - dcase (algred_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (algred_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. case=> _ <-. rewrite (IH _ _ _ _ _ Htl).
      rewrite (algred_upd_avars_instr_acc_ne Hne Hhd). reflexivity.
  Qed.

  Corollary algred_upd_avars_acc_ne {E avn g p zs v} :
    svar v != avn ->
    ZSSAStore.acc v (algred_upd_avars E avn g p zs) = ZSSAStore.acc v zs.
  Proof.
    move=> Hne. rewrite /algred_upd_avars. dcase (algred_upd_avars_program E avn g p zs).
    case=> [g' zs'] H. exact: (algred_upd_avars_program_acc_ne Hne H).
  Qed.

  Lemma algred_upd_avars_instr_acc_lt E avn g1 i zs1 g2 zs2 v :
    (sidx v < g1)%num -> algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    Ltac mytac ::=
      (move=> *; match goal with
                 | H : (_, _) = (_, _) |- _ =>
                   case: H; move=> ? ?; subst; mytac
                 | H : is_true (?x != ?y) |-
                   ZSSAStore.acc ?x (ZSSAStore.upd ?y _ ?zs) = ZSSAStore.acc ?x ?zs =>
                   exact: (ZSSAStore.acc_upd_neq H)
                 | |- _ => idtac
                 end).
    move=> Hlt. case: i => //=; try by mytac.
    (* Icast *)
    move=> x xt a Hupd. have: v != (avn, g1).
    { apply/negP=> Heq. rewrite (eqP Heq) /= in Hlt. exact: (N.lt_irrefl _ Hlt). }
    move=> {Hlt} Hne. move: Hupd. rewrite /algred_upd_avars_cast.
    move=> *; repeat case_pairs; by mytac.
  Qed.

  Lemma algred_upd_avars_program_acc_lt E avn g1 p zs1 g2 zs2 v :
    (sidx v < g1)%num -> algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 Hlt /=.
    - case=> _ ->. reflexivity.
    - dcase (algred_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (algred_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. case=> Hg2 <-.
      move: (algred_upd_avars_instr_idx_inc Hhd) => Hg1.
      move: (N.lt_le_trans _ _ _ Hlt Hg1) => Hg_hd.
      rewrite (IH _ _ _ _ _ Hg_hd Htl). exact: (algred_upd_avars_instr_acc_lt Hlt Hhd).
  Qed.

  Corollary algred_upd_avars_acc_lt {E avn g p zs v} :
    (sidx v < g)%num ->
    ZSSAStore.acc v (algred_upd_avars E avn g p zs) = ZSSAStore.acc v zs.
  Proof.
    move=> Hlt. rewrite /algred_upd_avars. dcase (algred_upd_avars_program E avn g p zs).
    case=> [g' zs'] H. exact: (algred_upd_avars_program_acc_lt Hlt H).
  Qed.

  Corollary algred_upd_avars_instr_acc_newer E avn g1 i zs1 g2 zs2 v :
    avars_newer_than_var avn g1 v ->
    algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    case; [exact: algred_upd_avars_instr_acc_ne | exact: algred_upd_avars_instr_acc_lt].
  Qed.

  Corollary algred_upd_avars_program_acc_newer E avn g1 p zs1 g2 zs2 v :
    avars_newer_than_var avn g1 v ->
    algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    case; [exact: algred_upd_avars_program_acc_ne | exact: algred_upd_avars_program_acc_lt].
  Qed.

  Corollary algred_upd_avars_acc_newer {E avn g p zs v} :
    avars_newer_than_var avn g v ->
    ZSSAStore.acc v (algred_upd_avars E avn g p zs) = ZSSAStore.acc v zs.
  Proof.
    case; [exact: algred_upd_avars_acc_ne | exact: algred_upd_avars_acc_lt].
  Qed.


  Lemma algred_upd_avars_instr_eval_zexp E avn i g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zexp e) ->
    algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs1 = ZSSA.eval_zexp e zs2.
  Proof.
    move=> Hnew Hupd. elim: e Hnew => //=.
    - move=> v Hnew. move/avars_newer_than_singleton: Hnew => Hnew.
      rewrite (algred_upd_avars_instr_acc_newer Hnew Hupd). reflexivity.
    - move=> op e IH Hnew. rewrite (IH Hnew). reflexivity.
    - move=> op e1 IH1 e2 IH2 /avars_newer_than_union [] Hnew1 Hnew2.
      rewrite (IH1 Hnew1) (IH2 Hnew2). reflexivity.
    - move=> e IH n Hnew. rewrite (IH Hnew). reflexivity.
  Qed.

  Lemma algred_upd_avars_instr_eval_zexps E avn i g1 g2 zs1 zs2 es :
    avars_newer_than avn g1 (ZSSA.vars_zexps es) ->
    algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zexps es zs1 = ZSSA.eval_zexps es zs2.
  Proof.
    elim: es => [| e es IH] //=. rewrite avars_newer_than_union. move=> [Hnew1 Hnew2] Hupd.
    rewrite (algred_upd_avars_instr_eval_zexp Hnew1 Hupd) (IH Hnew2 Hupd). reflexivity.
  Qed.

  Lemma algred_upd_avars_program_eval_zexp E avn p g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zexp e) ->
    algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs1 = ZSSA.eval_zexp e zs2.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 /=.
    - move=> Hnew [] ? ?; subst. reflexivity.
    - move=> Hnew. dcase (algred_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (algred_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. move=> [] ? ?; subst.
      rewrite -(IH _ _ _ _ _
                   (avars_newer_than_le (algred_upd_avars_instr_idx_inc Hhd) Hnew) Htl).
      exact: (algred_upd_avars_instr_eval_zexp Hnew Hhd).
  Qed.

  Lemma algred_upd_avars_program_eval_zexps E avn p g1 g2 zs1 zs2 es :
    avars_newer_than avn g1 (ZSSA.vars_zexps es) ->
    algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSA.eval_zexps es zs1 = ZSSA.eval_zexps es zs2.
  Proof.
    elim: es => [| e es IH] //=. rewrite avars_newer_than_union. move=> [Hnew1 Hnew2] Hupd.
    rewrite (algred_upd_avars_program_eval_zexp Hnew1 Hupd) (IH Hnew2 Hupd). reflexivity.
  Qed.

  Lemma algred_upd_avars_eval_zexp E avn p g zs1 zs2 e :
    avars_newer_than avn g (ZSSA.vars_zexp e) ->
    algred_upd_avars E avn g p zs1 = zs2 ->
    ZSSA.eval_zexp e zs1 = ZSSA.eval_zexp e zs2.
  Proof.
    rewrite /algred_upd_avars. dcase (algred_upd_avars_program E avn g p zs1) =>
                             [[g2 zs2'] Hupd] /=. move=> Hnew ?; subst.
    exact: (algred_upd_avars_program_eval_zexp Hnew Hupd).
  Qed.

  Lemma algred_upd_avars_eval_zexps E avn p g zs1 zs2 es :
    avars_newer_than avn g (ZSSA.vars_zexps es) ->
    algred_upd_avars E avn g p zs1 = zs2 ->
    ZSSA.eval_zexps es zs1 = ZSSA.eval_zexps es zs2.
  Proof.
    elim: es => [| e es IH] //=. rewrite avars_newer_than_union. move=> [Hnew1 Hnew2] Hupd.
    rewrite (algred_upd_avars_eval_zexp Hnew1 Hupd) (IH Hnew2 Hupd). reflexivity.
  Qed.


  Lemma algred_upd_avars_instr_eval_zbexp E avn i g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zbexp e) ->
    algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zbexp e zs1 <-> ZSSA.eval_zbexp e zs2.
  Proof.
    move=> Hnew Hupd. elim: e Hnew => //=.
    - move=> e1 e2 /avars_newer_than_union [Hnew1 Hnew2].
      rewrite (algred_upd_avars_instr_eval_zexp Hnew1 Hupd)
              (algred_upd_avars_instr_eval_zexp Hnew2 Hupd). done.
    - move=> e1 e2 ms
                /avars_newer_than_union [Hnew1 /avars_newer_than_union [Hnew2 Hnewms]].
      rewrite (algred_upd_avars_instr_eval_zexp Hnew1 Hupd)
              (algred_upd_avars_instr_eval_zexp Hnew2 Hupd)
              (algred_upd_avars_instr_eval_zexps Hnewms Hupd). done.
    - move=> e1 IH1 e2 IH2 /avars_newer_than_union [Hnew1 Hnew2].
      move: (IH1 Hnew1) (IH2 Hnew2) => {IH1 IH2} H1 H2. tauto.
  Qed.

  Lemma algred_upd_avars_program_eval_zbexp E avn p g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zbexp e) ->
    algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSA.eval_zbexp e zs1 <-> ZSSA.eval_zbexp e zs2.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 /=.
    - move=> Hnew [] ? ?; subst. done.
    - move=> Hnew. dcase (algred_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (algred_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. move=> [] ? ?; subst.
      move: (algred_upd_avars_instr_idx_inc Hhd) => Hg1.
      move: (avars_newer_than_le Hg1 Hnew) => Hnew_hd.
      move: (IH _ _ _ _ _ Hnew_hd Htl) => Heval_tl.
      move: (algred_upd_avars_instr_eval_zbexp Hnew Hhd) => Heval_hd. tauto.
  Qed.

  Lemma algred_upd_avars_eval_zbexp E avn p g zs e :
    avars_newer_than avn g (ZSSA.vars_zbexp e) ->
    ZSSA.eval_zbexp e zs <-> ZSSA.eval_zbexp e (algred_upd_avars E avn g p zs).
  Proof.
    rewrite /algred_upd_avars. dcase (algred_upd_avars_program E avn g p zs) =>
                                       [[g2 zs2'] Hupd] /=. move=> Hnew.
    exact: (algred_upd_avars_program_eval_zbexp Hnew Hupd).
  Qed.


  Lemma svar_notin_eval_zexp {zs n g avn e} :
    svar_notin avn (ZSSA.vars_zexp e) ->
    ZSSA.eval_zexp e (ZSSAStore.upd (avn, g) n zs) = ZSSA.eval_zexp e zs.
  Proof.
    elim: e => //=.
    - move=> [vn vi]. move/svar_notin_singleton1=> Hni.
      rewrite ZSSAStore.acc_upd_neq; first by reflexivity.
      apply/negP=> /eqP [] ? ?; subst. move/negP: Hni; apply. exact: eqxx.
    - move=> op e IH Hni. rewrite (IH Hni). reflexivity.
    - move=> op e1 IH1 e2 IH2 /svar_notin_union [Hni1 Hni2].
      rewrite (IH1 Hni1) (IH2 Hni2). reflexivity.
    - move=> e IH m Hni. rewrite (IH Hni). reflexivity.
  Qed.

  Lemma svar_notin_eval_zexps {zs n g avn es} :
    svar_notin avn (ZSSA.vars_zexps es) ->
    ZSSA.eval_zexps es (ZSSAStore.upd (avn, g) n zs) = ZSSA.eval_zexps es zs.
  Proof.
    elim: es => [| e es IH] //=. rewrite svar_notin_union. move=> [Hni1 Hni2].
    rewrite (svar_notin_eval_zexp Hni1) (IH Hni2). reflexivity.
  Qed.

  Lemma svar_notin_eval_zbexp zs n g avn e :
    svar_notin avn (ZSSA.vars_zbexp e) ->
    ZSSA.eval_zbexp e (ZSSAStore.upd (avn, g) n zs) <-> ZSSA.eval_zbexp e zs.
  Proof.
    elim: e => //=.
    - move=> e1 e2 /svar_notin_union [Hni1 Hni2].
      rewrite (svar_notin_eval_zexp Hni1) (svar_notin_eval_zexp Hni2). done.
    - move=> e1 e2 ms /svar_notin_union [Hni1 /svar_notin_union [Hni2 Hnims]].
      rewrite (svar_notin_eval_zexp Hni1) (svar_notin_eval_zexp Hni2)
              (svar_notin_eval_zexps Hnims). done.
    - move=> e1 IH1 e2 IH2 /svar_notin_union [Hni1 Hni2].
      move: (IH1 Hni1) (IH2 Hni2) => H1 H2. tauto.
  Qed.

  Lemma svar_notin_algred_upd_avars_instr_eval_zexp E avn g1 i zs1 g2 zs2 e :
    svar_notin avn (ZSSA.vars_zexp e) ->
    algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs2 = ZSSA.eval_zexp e zs1.
  Proof.
    case: i => //=; try (intros; case_pairs; reflexivity).
    move=> v tv a Hni. rewrite /algred_upd_avars_cast.
    move=> *; repeat case_pairs; try rewrite (svar_notin_eval_zexp Hni); reflexivity.
  Qed.

  Lemma svar_notin_algred_upd_avars_instr_eval_zexps E avn g1 i zs1 g2 zs2 es :
    svar_notin avn (ZSSA.vars_zexps es) ->
    algred_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zexps es zs2 = ZSSA.eval_zexps es zs1.
  Proof.
    elim: es => [| e es IH] //=. rewrite svar_notin_union. move=> [Hni1 Hni2] Hupd.
    rewrite (svar_notin_algred_upd_avars_instr_eval_zexp Hni1 Hupd) (IH Hni2 Hupd).
    reflexivity.
  Qed.

  Lemma svar_notin_algred_upd_avars_program_eval_zexp E avn g1 p zs1 g2 zs2 e :
    svar_notin avn (ZSSA.vars_zexp e) ->
    algred_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs2 = ZSSA.eval_zexp e zs1.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 Hni /=.
    - case=> ? ?; subst. reflexivity.
    - dcase (algred_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (algred_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. case=> ? ?; subst. rewrite (IH _ _ _ _ _ Hni Htl).
      rewrite (svar_notin_algred_upd_avars_instr_eval_zexp Hni Hhd). reflexivity.
  Qed.


  Lemma bvz_zs_eqi zs1 zs2 E bs :
    bvz_eqi E bs zs1 -> ZSSA.zs_eqi (vars_env E) zs1 zs2 ->
    bvz_eqi E bs zs2.
  Proof.
    move=> Hbeq Hzeq x Hx. rewrite (Hbeq x Hx). move/memenvP: Hx => Hx.
    exact: (Hzeq x Hx).
  Qed.

  Lemma algred_upd_avars_instr_eqi E1 E2 avn g1 i zs1 g2 zs2 :
    algred_upd_avars_instr E1 avn g1 i zs1 = (g2, zs2) ->
    svar_notin avn (vars_env E2) ->
    ZSSA.zs_eqi (vars_env E2) zs1 zs2.
  Proof.
    case: i => /=; try (move=> *; case_pairs; exact: ZSSA.zs_eqi_refl).
    (* Icast *)
    move=> x tx a Hupd Hni.
    rewrite /algred_upd_avars_cast in Hupd;
      repeat case_pairs; try exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
  Qed.

  Lemma algred_upd_avars_program_eqi E1 E2 avn g1 p zs1 g2 zs2 :
    svar_notin avn (vars_env E2) ->
    algred_upd_avars_program E1 avn g1 p zs1 = (g2, zs2) ->
    ZSSA.zs_eqi (vars_env E2) zs1 zs2.
  Proof.
    move=> Hni. elim: p E1 g1 g2 zs1 zs2 => [| i p IH] E1 g1 g2 zs1 zs2 /=.
    - move=> [] ? ?; subst; exact: ZSSA.zs_eqi_refl.
    - dcase (algred_upd_avars_instr E1 avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (algred_upd_avars_program (instr_succ_typenv i E1) avn g_hd p zs_hd)
      => [[g_tl zs_tl] Htl]. case=> ? ?; subst.
      apply: (ZSSA.zs_eqi_trans (algred_upd_avars_instr_eqi Hhd Hni)).
      exact: (IH _ _ _ _ _  Htl).
  Qed.


  (* main theorem *)

  Lemma algred_carry_constraint n :
    size n = 1 -> (to_Zpos n * (to_Zpos n - 1))%Z = 0%Z.
  Proof. case: n => //. move=> a [] //=. move=> _. by case: a. Qed.

  Lemma algred_Ishl t bs n :
    size bs = sizeof_typ t -> shlBn_algsnd t bs n ->
    bv2z t (bs <<# n)%bits = (bv2z t bs * Cryptoline.DSL.z2expn (Z.of_nat n))%Z.
  Proof.
    rewrite /shlBn_algsnd /ushlBn_algsnd /sshlBn_algsnd /Cryptoline.DSL.z2expn.
    case: t => /=.
    - move=> _ _.  exact: bv2z_shl_unsigned.
    - move=> _ _. exact: bv2z_shl_signed.
  Qed.

  Lemma algred_Icshl th tl bsh bsl n :
    is_unsigned tl -> compatible th tl ->
    n <= size bsl ->
    size bsh = sizeof_typ th -> size bsl = sizeof_typ tl ->
    cshlBn_algsnd th bsh bsl n ->
    (bv2z tl (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits +
     bv2z th (high (size bsh) ((bsl ++ bsh) <<# n)%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat (size bsl - n)))%Z =
    (bv2z th bsh * Cryptoline.DSL.z2expn (Z.of_nat (size bsl)) + bv2z tl bsl)%Z.
  Proof.
    rewrite /compatible /cshlBn_algsnd /ucshlBn_algsnd /scshlBn_algsnd /ushlBn_algsnd
            /sshlBn_algsnd /Cryptoline.DSL.z2expn. case: th; case: tl => //=.
    - move=> ? ? _ /eqP -> Hs H1 H2. rewrite -H2 in H1. exact: bv2z_cshl_unsigned'.
    - move=> ? ? _ /eqP -> Hs H1 H2. rewrite -H2 in H1. exact: bv2z_cshl_signed'.
  Qed.

  Lemma algred_Icmov_true t c a1 a2 :
    size c = 1 ->
    to_bool c ->
    bv2z t a1 = (bv2z Tbit c * bv2z t a1 + (1 - bv2z Tbit c) * bv2z t a2)%Z.
  Proof.
    move=> Hs Hc. rewrite /bv2z /=.
    move: (Seqs.singleton_seq Hs) => {Hs} [b Hcb]. subst.
    rewrite /to_bool /= negb_and in Hc. case/orP: Hc => Hc; last by done.
    case: b Hc; last by done. move=> _. rewrite !Z.add_0_r /=.
    by case: t => wt; [case: (to_Zpos a1) | case: (to_Z a1)].
  Qed.

  Lemma algred_Icmov_false t c a1 a2 :
    size c = 1 ->
    ~~ to_bool c ->
    bv2z t a2 = (bv2z Tbit c * bv2z t a1 + (1 - bv2z Tbit c) * bv2z t a2)%Z.
  Proof.
    move=> Hs Hc. rewrite /bv2z /=.
    move: (Seqs.singleton_seq Hs) => {Hs} [b Hcb]. subst.
    rewrite /to_bool /= in Hc. move/negPn: Hc => /andP [/eqP -> _] /=.
    by case: t; [case: (to_Zpos a2) | case: (to_Z a2)].
  Qed.

  Lemma algred_Inot_unsigned bs n m :
    compatible (Tuint n) (Tuint m) -> size bs = m ->
    bv2z (Tuint n) (~~# bs)%bits = (z2expn (Z.of_nat n) - Z.one - bv2z (Tuint m) bs)%Z.
  Proof.
    rewrite /compatible /z2expn /Cryptoline.DSL.z2expn /=. move=> /eqP <- <-.
    exact: bv2z_not_unsigned.
  Qed.

  Lemma algred_Inot_signed bs n m :
    0 < size bs ->
    bv2z (Tsint n) (~~# bs)%bits = (- bv2z (Tsint m) bs - Z.one)%Z.
  Proof.
    rewrite /=. move=> Hs. exact: bv2z_not_signed.
  Qed.

  Lemma algred_Iadd t bs1 bs2 :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t ->
    addB_algsnd t bs1 bs2 ->
    bv2z t (bs1 +# bs2)%bits = (bv2z t bs1 + bv2z t bs2)%Z.
  Proof.
    rewrite /addB_algsnd /uaddB_algsnd /saddB_algsnd. case: t => /=.
    - move=> n H1 H2. rewrite -H2 in H1. exact: bv2z_add_unsigned.
    - move=> n H1 H2. rewrite -H2 in H1. exact: bv2z_add_signed.
  Qed.

  Lemma algred_Iadds_unsigned bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    (bv2z (Tuint n) (bs1 +# bs2)%bits +
     bv2z Tbit (1) -bits of bool (carry_addB bs1 bs2)%bits *
                    Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    (bv2z (Tuint n) bs1 + bv2z (Tuint n) bs2)%Z.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. move=> H1 H2. rewrite -H1.
    rewrite -H2 in H1. rewrite Z.add_0_r. exact: bv2z_adds_unsigned.
  Qed.

  Lemma algred_Iadds_signed bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    adds_algsnd (Tsint n) bs1 bs2 ->
    bv2z (Tsint n) (bs1 +# bs2)%bits = (bv2z (Tsint n) bs1 + bv2z (Tsint n) bs2)%Z.
  Proof.
    rewrite /adds_algsnd /saddB_algsnd /=. move=> H1 H2. rewrite -H2 in H1.
    exact: bv2z_adds_signed.
  Qed.

  Lemma algred_Iadc_unsigned bs1 bs2 bsc n :
    0 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    adcB_algsnd (Tuint n) bs1 bs2 bsc ->
    bv2z (Tuint n) (adcB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tuint n) bs1 + bv2z (Tuint n) bs2 + bv2z Tbit bsc)%Z.
  Proof.
    rewrite /adcB_algsnd /uadcB_algsnd /=.
    move=> Hs1 H1 H2 Hc. rewrite -H2 in H1. exact: bv2z_adc_unsigned.
  Qed.

  Lemma algred_Iadc_signed bs1 bs2 bsc n :
    1 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    adcB_algsnd (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (adcB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tsint n) bs1 + bv2z (Tsint n) bs2 + bv2z Tbit bsc)%Z.
  Proof.
    rewrite /adcB_algsnd /sadcB_algsnd /=.
    move=> Hs1 H1 H2 Hc. rewrite -H2 in H1. exact: bv2z_adc_signed.
  Qed.

  Lemma algred_Iadcs_unsigned bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    (bv2z (Tuint n) (adcB (to_bool bsc) bs1 bs2).2 +
     bv2z Tbit (1)-bits of bool
                        ((adcB (to_bool bsc) bs1 bs2).1)%bits *
                   Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
  (bv2z (Tuint n) bs1 + bv2z (Tuint n) bs2 + bv2z Tbit bsc)%Z.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. rewrite Z.add_0_r.
    move=> H1 H2 Hc. rewrite -H1. rewrite -H2 in H1.
    exact: bv2z_adcs_unsigned.
  Qed.

  Lemma algred_Iadcs_signed bs1 bs2 bsc n :
    1 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    adcs_algsnd (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (adcB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tsint n) bs1 + bv2z (Tsint n) bs2 + bv2z Tbit bsc)%Z.
  Proof.
    rewrite /adcs_algsnd /sadcB_algsnd /=. move=> Hs H1 H2 Hc. rewrite -H2 in H1.
    exact: bv2z_adcs_signed.
  Qed.

  Lemma algred_Isub t bs1 bs2 :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t ->
    subB_algsnd t bs1 bs2 ->
    bv2z t (bs1 -# bs2)%bits = (bv2z t bs1 - bv2z t bs2)%Z.
  Proof.
    rewrite /subB_algsnd /usubB_algsnd /ssubB_algsnd. case: t => /=.
    - move=> n H1 H2. rewrite -H2 in H1. exact: bv2z_sub_unsigned.
    - move=> n H1 H2. rewrite -H2 in H1. exact: bv2z_sub_signed.
  Qed.

  Lemma algred_Isubc_unsigned bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 +
     (1 - bv2z Tbit
               (1) -bits of bool ((adcB true bs1 (~~# bs2)).1)%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    bv2z (Tuint n) (adcB true bs1 (~~# bs2)%bits).2.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. rewrite Z.add_0_r. move=> H1 H2.
    rewrite -H1. rewrite -H2 in H1. exact: bv2z_subc_unsigned.
  Qed.

  Lemma algred_Isubc_signed bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    subc_algsnd (Tsint n) bs1 bs2 ->
    bv2z (Tsint n) (adcB true bs1 (~~# bs2)%bits).2 =
    (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2)%Z.
  Proof.
    rewrite /subc_algsnd /ssubB_algsnd /=. move=> H1 H2. rewrite -H2 in H1.
    exact: bv2z_subc_signed.
  Qed.

  Lemma algred_Isubb_unsigned bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 +
     bv2z Tbit (1) -bits of bool (borrow_subB bs1 bs2)%bits *
                    Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    bv2z (Tuint n) (bs1 -# bs2)%bits.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. move=> H1 H2. rewrite -H1 Z.add_0_r.
    rewrite -H2 in H1. exact: bv2z_subb_unsigned.
  Qed.

  Lemma algred_Isubb_signed bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    subb_algsnd (Tsint n) bs1 bs2 ->
    bv2z (Tsint n) (bs1 -# bs2)%bits = (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2)%Z.
  Proof.
    rewrite /subb_algsnd /ssubB_algsnd /=. move=> H1 H2. rewrite -H2 in H1.
    exact: bv2z_subb_signed.
  Qed.

  Lemma algred_Isbc_unsigned bs1 bs2 bsc n :
    0 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbcB_algsnd (Tuint n) bs1 bs2 bsc ->
    bv2z (Tuint n) (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 - (1 - bv2z Tbit bsc))%Z.
  Proof.
    rewrite /sbcB_algsnd /usbcB_algsnd /=.
    move=> Hs H1 H2 Hc. rewrite -H2 in H1. exact: bv2z_sbc_unsigned.
  Qed.

  Lemma algred_Isbc_signed bs1 bs2 bsc n :
    1 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbcB_algsnd (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2 - (1 - bv2z Tbit bsc))%Z.
  Proof.
    rewrite /sbcB_algsnd /ssbcB_algsnd /=.
    move=> Hs H1 H2 Hc. rewrite -H2 in H1. exact: bv2z_sbc_signed.
  Qed.

  Lemma algred_Isbcs_unsigned bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 - (1 - bv2z Tbit bsc) +
     (1 - bv2z Tbit (1)-bits of bool
                             ((adcB (to_bool bsc) bs1 (~~# bs2)).1)%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    bv2z (Tuint n) (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. rewrite Z.add_0_r. move=> H1 H2 Hc.
    rewrite -H1. rewrite -H2 in H1. exact: bv2z_sbcs_unsigned.
  Qed.

  Lemma algred_Isbcs_signed bs1 bs2 bsc n :
    1 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbcs_algsnd (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2 - (1 - bv2z Tbit bsc))%Z.
  Proof.
    rewrite /sbcs_algsnd /ssbcB_algsnd /=. move=> Hs H1 H2 Hc. rewrite -H2 in H1.
    exact: bv2z_sbcs_signed.
  Qed.

  Lemma algred_Isbb_unsigned bs1 bs2 bsc n :
    0 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbbB_algsnd (Tuint n) bs1 bs2 bsc ->
    bv2z (Tuint n) (sbbB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 - bv2z Tbit bsc)%Z.
  Proof.
    rewrite /sbbB_algsnd /usbbB_algsnd /=.
    move=> Hs H1 H2 Hc. rewrite -H2 in H1. exact: bv2z_sbb_unsigned.
  Qed.

  Lemma algred_Isbb_signed bs1 bs2 bsc n :
    1 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbbB_algsnd (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (sbbB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2 - bv2z Tbit bsc)%Z.
  Proof.
    rewrite /sbbB_algsnd /ssbbB_algsnd /=.
    move=> Hs H1 H2 Hc. rewrite -H2 in H1. exact: bv2z_sbb_signed.
  Qed.

  Lemma algred_Isbbs_unsigned bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    (bv2z (Tuint n) (sbbB (to_bool bsc) bs1 bs2).2 +
     - bv2z Tbit (1)-bits of bool ((sbbB (to_bool bsc) bs1 bs2).1)%bits *
                     Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 - bv2z Tbit bsc)%Z.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. move=> H1 H2 Hc. rewrite Z.add_0_r.
    rewrite -H1. rewrite -H2 in H1. exact: bv2z_sbbs_unsigned.
  Qed.

  Lemma algred_Isbbs_signed bs1 bs2 bsc n :
    1 < size bs1 ->
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbbs_algsnd (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (sbbB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2 - bv2z Tbit bsc)%Z.
  Proof.
    rewrite /sbbs_algsnd /ssbbB_algsnd /=. move=> Hs H1 H2 Hc. rewrite -H2 in H1.
    exact: bv2z_sbbs_signed.
  Qed.

  Lemma algred_Imul t bs1 bs2 :
    0 < size bs1 ->
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t ->
    mulB_algsnd t bs1 bs2 ->
    bv2z t (bs1 *# bs2)%bits = (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
    rewrite /mulB_algsnd /umulB_algsnd /smulB_algsnd. case: t => /=.
    - move=> n Hsz H1 H2. rewrite -H2 in H1. exact: bv2z_mul_unsigned.
    - move=> n Hsz H1 H2. rewrite -H2 in H1. exact: bv2z_mul_signed.
  Qed.

  Lemma algred_Imull_unsigned t bs1 bs2 :
    is_unsigned t ->
    size bs1 = sizeof_typ t ->
    size bs2 = sizeof_typ t ->
    (bv2z (unsigned_typ t)
          (low (size bs2) (zext (size bs1) bs1 *# zext (size bs1) bs2)%bits) +
     bv2z t (high (size bs1) (zext (size bs1) bs1 *# zext (size bs1) bs2)%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat (size bs2)))%Z =
    (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. case: t => //=.
    move=> n _ H1 H2. rewrite -H2 in H1. exact: bv2z_mull_unsigned.
  Qed.

  Lemma algred_Imull_signed t bs1 bs2 :
    is_signed t ->
    0 < size bs1 ->
    size bs1 = sizeof_typ t ->
    size bs2 = sizeof_typ t ->
    (bv2z (unsigned_typ t)
          (low (size bs2) (sext (size bs1) bs1 *# sext (size bs1) bs2)%bits) +
     bv2z t (high (size bs1) (sext (size bs1) bs1 *# sext (size bs1) bs2)%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat (size bs2)))%Z =
    (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. case: t => //=.
    move=> n _ Hs H1 H2. rewrite -H2 in H1. exact: bv2z_mull_signed.
  Qed.

  Lemma algred_Imulj_unsigned t bs1 bs2 :
    is_unsigned t ->
    size bs1 = sizeof_typ t ->
    size bs2 = sizeof_typ t ->
    bv2z (double_typ t) (zext (size bs1) bs1 *# zext (size bs1) bs2)%bits =
    (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
    case: t => //=. move=> n _ H1 H2. rewrite -H2 in H1. exact: bv2z_mulj_unsigned.
  Qed.

  Lemma algred_Imulj_signed t bs1 bs2 :
    is_signed t ->
    0 < size bs1 ->
    size bs1 = sizeof_typ t ->
    size bs2 = sizeof_typ t ->
    bv2z (double_typ t) (sext (size bs1) bs1 *# sext (size bs1) bs2)%bits =
    (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
    case: t => //=. move=> n _ Hsz H1 H2. rewrite -H2 in H1. exact: bv2z_mulj_signed.
  Qed.

  Lemma algred_Isplit_unsigned t bs n :
    is_unsigned t -> size bs = sizeof_typ t ->
    (bv2z (unsigned_typ t) (bs <<# (size bs - n) >># (size bs - n))%bits +
     bv2z t (bs >># n)%bits * Cryptoline.DSL.z2expn (Z.of_nat n))%Z = bv2z t bs.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. case: t => //=.
    move=> _ _ _. exact: bv2z_split_unsigned.
  Qed.

  Lemma algred_Isplit_signed t bs n :
    is_signed t -> size bs = sizeof_typ t -> n <= size bs ->
    (bv2z (unsigned_typ t) (bs <<# (size bs - n) >># (size bs - n))%bits +
     bv2z t (sarB n bs) * Cryptoline.DSL.z2expn (Z.of_nat n))%Z = bv2z t bs.
  Proof.
    rewrite /Cryptoline.DSL.z2expn /=. case: t => //=.
    move=> _ _ _ Hn. exact: bv2z_split_signed.
  Qed.

  (* Upcast from unsigned to unsigned*)
  Lemma algred_Icast_uuu wt wa bs :
    wa <= wt -> size bs = wa ->
    bv2z (Tuint wt) (tcast bs (Tuint wa) (Tuint wt)) = bv2z (Tuint wa) bs.
  Proof.
    rewrite /tcast /ucastB /=. move=> H1 H2. rewrite -H2 in H1.
    rewrite leq_eqVlt in H1. case H: (wt == size bs).
    - reflexivity.
    - rewrite eq_sym H orFb in H1. move/ltn_geF: (H1). rewrite leq_eqVlt H orFb.
      move=> ->. exact: bv2z_cast_uuu.
  Qed.

  (* Downcast from unsigned to unsigned *)
  Lemma algred_Icast_duu wt wa bs q r :
    (wa <= wt) = false -> size bs = wa ->
    Z.div_eucl (to_Zpos bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tuint wt) (tcast bs (Tuint wa) (Tuint wt)) +
     q * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tuint wa) bs.
  Proof.
    rewrite /tcast /ucastB /z2expn /Cryptoline.DSL.z2expn /=. move=> H1 H2.
    rewrite -H2 in H1. rewrite leq_eqVlt in H1. case H: (wt == size bs).
    - rewrite eq_sym H orTb in H1. discriminate.
    - rewrite eq_sym H orFb in H1. move/idP/negP: H1.
      rewrite -leqNgt leq_eqVlt H orFb. move=> H1; rewrite H1.
      exact: bv2z_cast_duu.
  Qed.

  (* Upcast from signed to unsigned *)
  Lemma algred_Icast_usu wt wa bs q r :
    (wa <= wt) = true -> size bs = wa ->
    Z.div_eucl (to_Z bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tsint wa) bs + (-q) * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z =
    bv2z (Tuint wt) (tcast bs (Tsint wa) (Tuint wt)).
  Proof.
    rewrite /tcast /scastB /z2expn /Cryptoline.DSL.z2expn /=. move=> H1 H2.
    rewrite -H2 in H1. case H: (wt == size bs).
    - rewrite (eqP H). exact: bv2z_cast_usu_eq.
    - rewrite leq_eqVlt eq_sym H orFb in H1. move/ltn_geF: (H1).
      rewrite leq_eqVlt H orFb. move=> ->. exact: bv2z_cast_usu_gt.
  Qed.

  (* Downcast from signed to unsigned *)
  Lemma algred_Icast_dsu wt wa bs q r :
    (wa <= wt) = false -> size bs = wa ->
    Z.div_eucl (to_Z bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tuint wt) (tcast bs (Tsint wa) (Tuint wt)) +
     q * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tsint wa) bs.
  Proof.
    rewrite /z2expn /Cryptoline.DSL.z2expn /tcast /scastB /=. move=> H1 H2.
    rewrite -H2 in H1. rewrite leq_eqVlt in H1. case H: (wt == size bs).
    - rewrite eq_sym H orTb in H1. discriminate.
    - rewrite eq_sym H orFb in H1. move/idP/negP: H1.
      rewrite -leqNgt leq_eqVlt H orFb. move=> H1; rewrite H1.
      exact: bv2z_cast_dsu.
  Qed.

  (* Upcast from unsigned to signed *)
  Lemma algred_Icast_uus wt wa bs :
    (wa < wt) = true -> size bs = wa ->
    bv2z (Tsint wt) (tcast bs (Tuint wa) (Tsint wt)) = bv2z (Tuint wa) bs.
  Proof.
    rewrite /tcast /ucastB /=. move=> H1 H2. rewrite -H2 in H1.
    move/ltn_geF: H1. rewrite leq_eqVlt. case H: (wt == size bs).
    - rewrite orTb. discriminate.
    - rewrite orFb. move=> H1; rewrite H1. move/idP/negP: H1.
      rewrite -leqNgt leq_eqVlt eq_sym H orFb. move=> H1.
      exact: bv2z_cast_uus.
  Qed.

  (* Downcast from unsigned to signed *)
  Lemma algred_Icast_dus wt wa bs q r q' r' :
    (wa < wt) = false -> size bs = wa ->
    Z.div_eucl (to_Zpos bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    Z.div_eucl r (z2expn (Z.of_nat wt - 1)) = (q', r') ->
    (bv2z (Tsint wt) (tcast bs (Tuint wa) (Tsint wt)) +
     (q + q') * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tuint wa) bs.
  Proof.
    rewrite /tcast /ucastB /z2expn /Cryptoline.DSL.z2expn /=.
    move=> H1 H2; rewrite -H2 in H1. case H: (wt == size bs).
    - rewrite (eqP H). exact: bv2z_cast_dus_eq.
    - move/idP/negP: H1. rewrite -leqNgt leq_eqVlt H orFb. move=> H1; rewrite H1.
      exact: bv2z_cast_dus_lt.
  Qed.

  (* Upcast from signed to signed *)
  Lemma algred_Icast_uss wt wa bs :
    (wa <= wt) = true -> size bs = wa ->
    bv2z (Tsint wt) (tcast bs (Tsint wa) (Tsint wt)) = bv2z (Tsint wa) bs.
  Proof.
    rewrite /tcast /scastB /=. move=> H1 H2; rewrite -H2 in H1.
    case H: (wt == size bs).
    - reflexivity.
    - rewrite leq_eqVlt eq_sym H orFb in H1. move/ltn_geF: (H1).
      rewrite leq_eqVlt H orFb. move=> ->. exact: bv2z_cast_uss.
  Qed.

  (* Downcast from signed to signed *)
  Lemma algred_Icast_dss wt wa bs q r q' r' :
    (wa <= wt) = false -> size bs = wa ->
    Z.div_eucl (to_Z bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    Z.div_eucl r (z2expn (Z.of_nat wt - 1)) = (q', r') ->
    (bv2z (Tsint wt) (tcast bs (Tsint wa) (Tsint wt)) +
     (q + q') * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tsint wa) bs.
  Proof.
    rewrite /tcast /scastB /z2expn /Cryptoline.DSL.z2expn /=.
    move=> H1 H2; rewrite -H2 in H1. case H: (wt == size bs).
    - rewrite leq_eqVlt eq_sym H orTb in H1. discriminate.
    - rewrite leq_eqVlt eq_sym H orFb in H1. move/idP/negP: H1.
      rewrite -leqNgt leq_eqVlt H orFb. move=> H1; rewrite H1.
      exact: bv2z_cast_dss.
  Qed.

  Lemma algred_Ivpc tv ta bs :
    size bs = sizeof_typ ta -> vpc_algsnd tv ta bs ->
    bv2z tv (tcast bs ta tv) = bv2z ta bs.
  Proof.
    rewrite /vpc_algsnd /tcast /ucastB /scastB. case: ta => wa; case: tv => wv /=.
    - move=> <-. case/orP: (Nats.eqn_ltn_gtn_cases wv (size bs)); [case/orP | idtac]
                 => H.
      + rewrite (eqP H) leqnn eqxx. reflexivity.
      + deduce_compare_cases H. rewrite H0 (eq_sym wv) H1 H4 H.
        move/eqP=> Heq. exact: (high_zeros_to_Zpos_low_eq Heq).
      + deduce_compare_cases H. rewrite H3 H1 H2. rewrite to_Zpos_zext. reflexivity.
    - move=> <-. case/orP: (Nats.eqn_ltn_gtn_cases wv (size bs)); [case/orP | idtac]
                 => H.
      + rewrite (eqP H) ltnn eqxx. rewrite subnn add0n.
        rewrite /zeros /=. move/eqP=> Heq. exact: (high1_0_to_Z Heq).
      + deduce_compare_cases H. rewrite H2 (eq_sym wv) H1 H.
        move/eqP=> Heq. exact: (high_zeros_to_Z_low Heq).
      + deduce_compare_cases H. rewrite H H1 H2. move=> _.
        apply: to_Z_zext. rewrite subn_gt0. exact: H.
    - move=> <-. case/orP: (Nats.eqn_ltn_gtn_cases wv (size bs)); [case/orP | idtac]
                 => H.
      + rewrite (eqP H) eqxx leq_subr. move/eqP=> Heq. apply: Logic.eq_sym.
        exact: (high1_0_to_Z Heq).
      + deduce_compare_cases H. rewrite (eq_sym wv) H1 H.
        case Hs: (size bs - 1 <= wv).
        * rewrite leq_eqVlt in Hs. case/orP: Hs => Hs.
          -- rewrite -(eqP Hs). move/eqP=> Heq. rewrite (high1_0_to_Z Heq).
             move: (ltn_predK H). rewrite -addn1 -subn1 => Hs'.
             rewrite -{3}(cat_low_high Hs') Heq.
             rewrite to_Zpos_cat /= Z.add_0_r. reflexivity.
          -- move: (Nats.ltn_lt Hs) => {Hs} Hs. rewrite subn1 in Hs.
             move: (Nat.lt_pred_le _ _ Hs) => {Hs} /Nats.le_leq Hs.
             rewrite H0 in Hs. discriminate.
        * move/eqP=> Heq. rewrite (high_zeros_to_Zpos_low_eq Heq).
          apply: Logic.eq_sym. apply: (highn_0_to_Z _ Heq).
          rewrite subn_gt0. assumption.
      + deduce_compare_cases H. rewrite H1 H2. case Hs: (size bs - 1 <= wv).
        * move/eqP=> Heq. rewrite (high1_0_to_Zpos_sext _ Heq).
          rewrite (high1_0_to_Z Heq). reflexivity.
        * move=> _. move/idP/negP: Hs => Hs. rewrite -ltnNge in Hs.
          move: (ltn_trans H Hs) => {Hs} Hs. rewrite ltnNge leq_subr in Hs.
          discriminate.
    - move=> <-. case/orP: (Nats.eqn_ltn_gtn_cases wv (size bs)); [case/orP | idtac]
                 => H.
      + rewrite (eqP H) eqxx leqnn. reflexivity.
      + deduce_compare_cases H. rewrite H0 (eq_sym wv) H1 H.
        move/eqP=> Heq. rewrite -{2}Heq. rewrite to_Z_sext. reflexivity.
      + deduce_compare_cases H. rewrite H3 H1 H2. move=> _. exact: to_Z_sext.
  Qed.

  Lemma algred_Ijoin th tl bsh bsl :
    (0 < size bsh) -> is_unsigned tl -> compatible th tl ->
    size bsh = sizeof_typ th -> size bsl = sizeof_typ tl ->
    (bv2z tl bsl + bv2z th bsh * Cryptoline.DSL.z2expn (Z.of_nat (size bsl)))%Z =
    bv2z (double_typ th) (bsl ++ bsh).
  Proof.
    rewrite /compatible /Cryptoline.DSL.z2expn /=. case: th; case: tl => //=.
    - move=> n m _ _ /eqP -> <- H. rewrite to_Zpos_cat. reflexivity.
    - move=> n m Hlt _ /eqP Heq Hh Hl. subst. rewrite (to_Z_cat _ Hlt). reflexivity.
  Qed.


  Derive Inversion_clear eval_program_cons_inv with
      (forall E i p s1 s2, eval_program E (i::p) s1 s2) Sort Prop.

  Ltac acc_zs_to_bs :=
    repeat
    match goal with
    | Heq : bvz_eqi (SSATE.add ?v ?t ?E) ?bs ?zs |- context f [ZSSAStore.acc ?v ?zs] =>
      rewrite -(Heq v (SSATE.Lemmas.mem_add_eq (eqxx v)))
    | Heq : bvz_eqi (SSATE.add ?vh ?th (SSATE.add ?vl ?tl ?E)) ?bs ?zs,
      Hneq : is_true (?vh != ?vl) |-
      context f [ZSSAStore.acc ?vl ?zs] =>
      let Hneq' := fresh in
      rewrite -(Heq vl); last by
      (move: (negP Hneq) => Hneq'; rewrite eq_sym in Hneq';
      rewrite (SSATE.Lemmas.mem_add_neq Hneq'));
      exact (SSATE.Lemmas.mem_add_eq (eqxx vl))
    | Hupd : SSAStore.Upd ?v ?e ?bs1 ?bs2 |- context f [acc2z ?E ?v ?bs2] =>
      rewrite (acc2z_Upd_eq (eqxx v) Hupd)
    | Heq : is_true (?x == ?v), Hupd : SSAStore.Upd ?v ?e ?bs1 ?bs2 |-
      context f [acc2z ?E ?x ?bs2] =>
      rewrite (acc2z_Upd_eq Heq Hupd)
    | Hneq : is_true (?x != ?v), Hupd : SSAStore.Upd ?v ?e ?bs1 ?bs2 |-
      context f [acc2z ?E ?x ?bs2] =>
      rewrite (acc2z_Upd_neq Hneq Hupd)
    | Hupd : SSAStore.Upd2 ?vl ?el ?vh ?eh ?bs1 ?bs2 |-
      context f [acc2z ?E ?vh ?bs2] =>
      rewrite (acc2z_Upd2_eq2 (eqxx vh) Hupd)
    | Hneq : is_true (?vh != ?vl), Hupd : SSAStore.Upd2 ?vl ?el ?vh ?eh ?bs1 ?bs2 |-
      context f [acc2z ?E ?vl ?bs2] =>
      rewrite eq_sym in Hneq; rewrite (acc2z_Upd2_eq1 (eqxx vl) Hneq Hupd)
    | Hni : svar_notin ?avn _, Hne : is_true (?avn != Var.svar ?v) |-
      context f [ZSSAStore.acc ?v (ZSSAStore.upd (?avn, _) _ _)] =>
      let H := fresh in
      rewrite ZSSAStore.acc_upd_neq;
      last by (apply/eqP=> H; rewrite H /= eqxx in Hne; discriminate)
    | |- context f [ZSSAStore.acc ?v (ZSSAStore.upd ?v _ _)] =>
      rewrite ZSSAStore.acc_upd_eq; last exact: eqxx
    end.

  Ltac eval_zs_to_bs :=
    repeat
    match goal with
    | H : svar_notin ?avn (vars_atom ?a) |-
      (* remove the update of auxiliary variables *)
      context f [ZSSAStore.upd (?avn, _) _ ?zs] =>
      rewrite svar_notin_eval_zexp; last by (rewrite vars_algred_atom; exact: H)
    | Heq : bvz_eqi (SSATE.add ?v ?t ?E) ?bs ?zs
      |- context f [ZSSA.eval_zexp (algred_atom ?a) ?zs] =>
      rewrite (bvz_eqi_eval_atom Heq); last by defined_dec
    | Heq : bvz_eqi (SSATE.add ?v ?t ?E) ?bs ?zs,
      H : context f [ZSSA.eval_zexp (algred_atom ?a) ?zs] |- _ =>
      rewrite (bvz_eqi_eval_atom Heq) in H; last by defined_dec
    end.

  (* rewrite (eval_atom a bs2) to (eval_atom a bs1) where bs1 is a
     predecessor of bs2 *)
  Ltac eval_atom_to_prev :=
    repeat
    match goal with
    | Hun : is_true (ssa_vars_unchanged_instr ?vs ?i),
      Hsub : is_true (SSAVS.subset (vars_atom ?a) ?vs),
      Heval : eval_instr ?E ?i ?bs1 ?bs2 |-
      context f [eval_atom ?a ?bs2] =>
      rewrite -(ssa_unchanged_instr_eval_atom
                  (ssa_unchanged_instr_subset Hun Hsub) Heval)
    | Hun : is_true (ssa_vars_unchanged_instr ?vs ?i),
      Hsub : is_true (SSAVS.subset (vars_atom ?a) ?vs),
      Heval : eval_instr ?E ?i ?bs1 ?bs2,
      H : context f [eval_atom ?a ?bs2] |- _ =>
      rewrite -(ssa_unchanged_instr_eval_atom
                  (ssa_unchanged_instr_subset Hun Hsub) Heval) in H
    end.

  (* If the type of an atom a is Tbit in some typing environment E, and
     some state s conforms to E, introduce size (eval_atom a s) = 1. *)
  Ltac intro_size_carry :=
    match goal with
    | Hco : SSAStore.conform ?bs1 ?E,
      H : is_true (atyp ?c ?E == Tbit),
      Hsub : is_true (SSAVS.subset (vars_atom ?c) (vars_env ?E)),
      Hsm : is_true (size_matched_atom ?c) |- _ =>
      let Hsc := fresh "Hsc" in
      (move: (size_eval_atom_asize Hsub Hco Hsm) => Hsc);
      rewrite /asize (eqP H) /= in Hsc
    end.

  (* Unfold well_formed_instr and split all the Boolean conjunction. *)
  Ltac unfold_well_formed_instr :=
    match goal with
    | H : is_true (well_formed_instr _ _) |- _ =>
      let Hdef := fresh "Hdef" in
      let Hwt := fresh "Hwt" in
      move/andP: H=> [Hdef Hwt]; repeat unfold_well_formed_instr
    | H : is_true (well_defined_instr _ _) |- _ =>
      rewrite /well_defined_instr in H; hyps_splitb
    | H : is_true (well_typed_instr _ _) |- _ =>
      rewrite /well_typed_instr in H; hyps_splitb
    | H : is_true (well_typed_atom _ _) |- _ =>
      let H1 := fresh "Hwta" in
      let H2 := fresh "Hwta" in
      move/andP: H=> [H1 H2]
    end.

  (* For each are_defined vs E, introduce SSAVS.subset vs (vars_env E). *)
  Ltac intro_subset_from_are_defined :=
    match goal with
    | H : is_true (are_defined _ _) |- _ =>
      let Hsub := fresh "Hsub" in
      move: (H) => /defsubP Hsub; move: H; intro_subset_from_are_defined
    | |- _ => intros
    end.

  (* Introduce size (eval_atom a s) = sizeof_typ (atyp a E) and
     rewrite asize a E. *)
  Ltac intro_atom_size :=
    match goal with
    | Hco : SSAStore.conform ?bs ?E,
      Hsub : is_true (SSAVS.subset (vars_atom ?a) (vars_env ?E)),
      Hsm : is_true (size_matched_atom ?a) |- _ =>
      let Hsize := fresh "Hsize" in
      (move: (conform_size_eval_atom Hsub Hco Hsm) => Hsize);
      move: Hsub; intro_atom_size
    |  Hs : _ = sizeof_typ (atyp ?a ?E),
       Hsign : atyp ?a ?E = Tsint ?n,
       Hws : is_true (well_sized_atom ?E ?a) |- _ =>
       let H := fresh in
       (have: is_signed (atyp a E) by rewrite Hsign);
       (move=> H); move: (well_sized_atom_signed H Hws);
       move: (well_sized_atom_gt0 Hws); rewrite /asize;
       rewrite -Hs; move: Hws; intro_atom_size
    |  Hs : _ = sizeof_typ (atyp ?a ?E),
       Hsign : is_true (is_signed (atyp ?a ?E)),
       Hws : is_true (well_sized_atom ?E ?a) |- _ =>
       move: (well_sized_atom_signed Hsign Hws); move: (well_sized_atom_gt0 Hws);
       rewrite /asize; rewrite -Hs; move: Hws; intro_atom_size
    |  Hs : _ = sizeof_typ (atyp ?a ?E),
       Hws : is_true (well_sized_atom ?E ?a) |- _ =>
       move: (well_sized_atom_gt0 Hws); rewrite /asize;
       rewrite -Hs; move: Hws; intro_atom_size
    | |- _ =>
      intros; try rewrite /asize;
      repeat (match goal with
              | H : _ = sizeof_typ (atyp ?a ?E)
                |- context f [sizeof_typ (atyp ?a ?E)] =>
                rewrite -H
              end)
    end.

  Ltac rewrite_types :=
    match goal with
    | H : is_true (atyp _ _ == _) |- _ => move/eqP: H => H; rewrite_types
    | H : is_true (_ == atyp _ _) |- _ => move/eqP: H => H; rewrite_types
    | H1 : atyp ?a1 ?E = atyp ?a2 ?E |- _ =>
      repeat (match goal with
              | H2 : context f [atyp a2 E] |- _ => rewrite -H1 /= in H2
              | |- context f [atyp a2 E] => rewrite -H1
              end); clear H1; rewrite_types
    | H1 : atyp ?a1 ?E = _ |- _ =>
      repeat (match goal with
              | H2 : context f [atyp a1 E] |- _ => rewrite H1 /= in H2
              | |- context f [atyp a1 E] => rewrite H1
              end); clear H1; rewrite_types
    | |- _ => idtac
    end.

  (* Prove carry_constr. *)
  Ltac prove_carry_constr :=
    match goal with
    | |- context f [carry_constr ?o ?v] =>
      rewrite /carry_constr; (case: (add_carry_constraints o) => /=; last by trivial);
      (split; last by trivial); acc_zs_to_bs; simplify_types;
      exact: algred_carry_constraint
    end.

  Lemma algred_upd_avars_sat_instr o E avn i bs1 bs2 g1 g2 g2' zes zs1 zs2 :
    well_formed_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    svar_notin avn (vars_instr i) ->
    SSAStore.conform bs1 E ->
    ssa_instr_algsnd_at E i bs1 ->
    eval_instr E i bs1 bs2 ->
    algred_instr o E avn g1 i = (g2, zes) ->
    algred_upd_avars_instr E avn g1 i zs1 = (g2', zs2) ->
    bvz_eqi (instr_succ_typenv i E) bs2 zs1 ->
    ZSSA.eval_zbexp (eands zes) zs2.
  Proof.
    Ltac mytac ::=
      match goal with
      | Hev : eval_instr _ _ _ _ |- _ =>
        unfold_well_formed_instr; ssa_vars_unchanged_instr_to_mem;
        intro_subset_from_are_defined;
        (* rewrite the RHS *)
        repeat case_svar_notin; eval_zs_to_bs;
        eval_atom_to_prev; simplify_types;
        (* rewrite the LHS *)
        inversion_clear Hev; acc_zs_to_bs; simplify_types;
        (* *)
        intro_atom_size; rewrite_types
      end.
    case: i => /=.
    (* Imov *)
    - move=> v a Hwf Hun Hni Hco _ Hev [] ? ? [] ? ? Heq; subst; rewrite /=.
      split; last by trivial. mytac. reflexivity.
    (* Ishl *)
    - move=> v a n Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst; rewrite /=.
      split; last by trivial. mytac. exact: (algred_Ishl _ Hsa).
    (* Icshl *)
    - move=> vh vl ah al n Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst;
               rewrite /=. split; last by trivial. mytac.
      apply: (algred_Icshl _ _ _ _ _ Hsa) => //=. rewrite Hsize. assumption.
    (* Inondet *)
    - move=> v t Hwf Hun Hni Hco _ Hev.
      case Ht: (t == Tbit); (move=> [] ? ? [] ? ? Heq; subst; rewrite /=);
        last by trivial. ssa_vars_unchanged_instr_to_mem. move/eqP: Ht => ?; subst.
      inversion_clear Hev. by prove_carry_constr.
    (* Icmov *)
    - move=> v c a1 a2 Hwf Hun Hni Hco _ Hev [] ? ? [] ? ? Heq; subst; rewrite /=.
      split; last by trivial. mytac.
      + exact: (algred_Icmov_true _ _ _ _ _).
      + exact: (algred_Icmov_false _ _ _ _ _).
    (* Inop *)
    - move=> Hwf Hun Hni Hco _ Hev [] ? ? [] ? ? Heq; subst; rewrite /=. done.
    (* Inot *)
    - move=> v t a Hwf Hun Hni Hco _ Hev. (case: t Hwf Hun Hev => n Hwf Hun Hev);
                                            case Hta: (atyp a E) => /=.
      + move=> [] ? ? [] ? ? Heq; subst; rewrite /=. split; last by trivial.
        mytac. exact: (algred_Inot_unsigned _ _).
      + move=> [] ? ? [] ? ? Heq; subst; rewrite /=. by trivial.
      + move=> [] ? ? [] ? ? Heq; subst; rewrite /=. by trivial.
      + move=> [] ? ? [] ? ? Heq; subst; rewrite /=. split; last by trivial.
        mytac. exact: (algred_Inot_signed _).
    (* Iadd *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (algred_Iadd _ _ Hsa).
    (* Iadds *)
    - move=> y v a1 a2 Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case => n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (algred_Iadds_unsigned _ _).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by trivial.
        mytac. exact: (algred_Iadds_signed _ _ Hsa).
    (* Iadc *)
    - move=> v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Iadc_unsigned _ _ _ _ Hsa).
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Iadc_signed _ _ _ _ Hsa).
    (* Iadcs *)
    - move=> c v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (algred_Iadcs_unsigned _ _ _).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Iadcs_signed _ _ _ _ Hsa).
    (* Isub *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst.
      rewrite /=. split; last by done. mytac. exact: (algred_Isub _ _ Hsa).
    (* Isubc *)
    - move=> c v a1 a2 Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (algred_Isubc_unsigned _ _).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isubc_signed _ _ Hsa).
    (* Isubb *)
    - move=> c v a1 a2 Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (algred_Isubb_unsigned _ _).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isubb_signed _ _ Hsa).
    (* Isbc *)
    - move=> v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isbc_unsigned _ _ _ _ Hsa).
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isbc_signed _ _ _ _ Hsa).
    (* Isbcs *)
    - move=> c v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (algred_Isbcs_unsigned _ _ _).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isbcs_signed _ _ _ _ Hsa).
    (* Isbb *)
    - move=> v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isbb_unsigned _ _ _ _ Hsa).
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isbb_signed _ _ _ _ Hsa).
    (* Isbbs *)
    - move=> c v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (algred_Isbbs_unsigned _ _ _).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (algred_Isbbs_signed _ _ _ _ Hsa).
    (* Imul *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (algred_Imul _ _ _ Hsa).
    (* Imull *)
    - move=> vh vl a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac.
      + exact: (algred_Imull_unsigned _ _ _).
      + exact: (algred_Imull_signed _ _ _).
    (* Imulj *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac.
      + exact: (algred_Imulj_unsigned _ _).
      + exact: (algred_Imulj_signed _ _).
    (* Isplit *)
    - move=> vh vl a n Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac.
      + exact: (algred_Isplit_unsigned _ _ _).
      + rewrite /asize -Hsize in H2. move: (ltnW H2) => {H2} H2.
        exact: (algred_Isplit_signed _ _ H2).
    (* Iand *)
    - move=> v t a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. done.
    (* Ior *)
    - move=> v t a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. done.
    (* Ixor *)
    - move=> v t a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. done.
    (* Icast *)
    - move=> v t a. rewrite /algred_cast /algred_upd_avars_cast.
      case: t => wt; dcase (atyp a E); case => wa Hta Hwf Hun Hni Hco Hsa Hev.
      + case Hwa: (wa <= wt).
        * move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_uuu Hwa Hsize).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_duu Hwa Hsize H0).
      + case Hwa: (wa <= wt).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_usu Hwa Hsize H0).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_dsu Hwa Hsize H0).
      + case Hwa: (wa < wt).
        * move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_uus Hwa Hsize).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_dus Hwa Hsize H0 H2).
      + case Hwa: (wa <= wt).
        * move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_uss Hwa Hsize).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (algred_Icast_dss Hwa Hsize H0 H2).
    (* Ivpc *)
    - move=> v t a Hwf Hni Hun Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (algred_Ivpc Hsize Hsa).
    (* Ijoin *)
    - move=> v a1 a2 Hwf Hni Hun Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (algred_Ijoin _ _ _ Hsize0 Hsize).
    (* Iassume *)
    - move=> [e r] /= Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst.
      mytac. rewrite are_defined_union /= in Hdef. move/andP: Hdef => [Hdef _].
      move: H => [/= He _]. apply/(bvz_eqi_eval_ebexp Heq Hdef). exact: He.
  Qed.

  Lemma algred_upd_avars_sat_program o E avn g1 p g2 eprogs bs1 bs2 :
    well_formed_program E p ->
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p ->
    svar_notin avn (vars_env E) -> svar_notin avn (vars_program p) ->
    SSAStore.conform bs1 E ->
    ssa_program_algsnd_at E p bs1 ->
    eval_program E p bs1 bs2 ->
    algred_program o E avn g1 p = (g2, eprogs) ->
    ZSSA.eval_zbexp (eands eprogs)
                    (algred_upd_avars E avn g1 p
                                    (algred_store (program_succ_typenv p E) bs2)).
  Proof.
    rewrite /algred_upd_avars. move: (@algred_store_eqi (program_succ_typenv p E) bs2).
    move: (algred_store (program_succ_typenv p E) bs2) => zs2.

    elim: p E g1 g2 eprogs bs1 bs2 zs2 =>
    [| i p IH] E g1 g2 eprogs bs1 bs2 zs2 /= Heqi2 Hwf Hun Hssa
               Hni_E Hni_p Hco Hsa Hev Hbv2z.
    - case: Hbv2z => ? ?; subst => /=. by trivial.
    - move: Hbv2z. inversion Hev using eval_program_cons_inv => {Hev} bs3 Hi Hp.
      dcase (algred_instr o E avn g1 i) => [[g_hd zhd] Hhd].
      dcase (algred_program o (instr_succ_typenv i E) avn g_hd p) => [[g_tl ztl] Htl].
      case=> ? ?; subst. move/andP: Hwf => [Hwf_i Hwf_p].
      move/andP: Hssa => [Hssa_i Hssa_p]. rewrite ssa_unchanged_program_cons in Hun.
      move/andP: Hun=> [Hun_i Hun_p]. move/svar_notin_union: Hni_p => [Hni_i Hni_p].
      inversion_clear Hsa. move: H H0 => Hsa_i Hsa_p. rewrite /algred_upd_avars /=.
      dcase (algred_upd_avars_instr E avn g1 i zs2) => [[g_hd' zs_hd] Hupd_hd].
      dcase (algred_upd_avars_program (instr_succ_typenv i E) avn g_hd' p zs_hd) =>
      [[g_tl' zs_tl] Hupd_tl].
      move: (algred_upd_avars_instr_gen Hhd Hupd_hd) => ?; subst.
      move: (algred_upd_avars_program_gen Htl Hupd_tl) => ?; subst.
      rewrite /=.

      have Hun_iep: ssa_vars_unchanged_program (vars_env (instr_succ_typenv i E)) p.
      { apply: (ssa_unchanged_program_replace
                  (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          by rewrite ssa_unchanged_program_union Hun_p Hssa_i. }

      have Hni_lvi: svar_notin avn (lvs_instr i).
      { apply: (svar_notin_subset _ Hni_i). rewrite vars_instr_split.
        exact: SSAVS.Lemmas.union_subset_1. }
      have Hni_lvp: svar_notin avn (lvs_program p).
      { apply: (svar_notin_subset _ Hni_p). rewrite vars_program_split.
        exact: SSAVS.Lemmas.union_subset_1. }

      have Hni_ie: svar_notin avn (vars_env (instr_succ_typenv i E)).
      { apply: (svar_notin_replace
                  (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
        apply/svar_notin_union. split; [exact: Hni_E | exact: Hni_lvi]. }

      apply/ZSSA.eval_zbexp_eands_cat. split.
      + apply/(algred_upd_avars_program_eval_zbexp _ Hupd_tl).
        * exact: (algred_instr_newer_than Hhd Hni_i).
        * apply: (algred_upd_avars_sat_instr
                    Hwf_i Hun_i Hni_i Hco Hsa_i Hi Hhd Hupd_hd).
          apply: (@bvs_bvz_eqi (instr_succ_typenv i E) bs2 bs3 zs2).
          -- apply: bvs_eqi_sym. exact: (bvs_eqi_eval_program Hun_iep Hssa_p Hp).
          -- apply: (submap_bvz_eqi _ Heqi2).
             exact: (ssa_unchanged_program_succ_typenv_submap Hun_iep Hssa_p).
      + have ->: (zs_tl =
                  (algred_upd_avars_program (instr_succ_typenv i E) avn g_hd' p zs_hd).2)
          by rewrite Hupd_tl; reflexivity.
        move: (conform_instr_succ_typenv Hwf_i Hco Hi) => Hco_3succi.
        apply: (IH _ _ _ _ _ _ _ _ Hwf_p Hun_iep Hssa_p Hni_ie Hni_p
                   Hco_3succi (Hsa_p bs3 (eval_rng_instr Hi)) Hp Htl).
        apply: (bvz_zs_eqi Heqi2). apply: (algred_upd_avars_instr_eqi Hupd_hd).
        apply: (svar_notin_replace
                  (SSAVS.Lemmas.P.equal_sym
                     (vars_env_program_succ_typenv p (instr_succ_typenv i E)))).
        apply/svar_notin_union; split.
        * apply: (svar_notin_replace
                    (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          apply/svar_notin_union. split; [exact: Hni_E | exact: Hni_lvi].
        * exact: Hni_lvp.
  Qed.

  Lemma algred_upd_avars_eval_eexp {E avn g p bs e} :
    svar_notin avn (vars_eexp e) ->
    ZSSA.eval_zexp e (algred_upd_avars
                        E avn g p (algred_store (program_succ_typenv p E) bs)) =
    eval_eexp e (program_succ_typenv p E) bs.
  Proof.
    elim: e E g p bs => //=.
    - move=> v E g p bs Hnotin. move: (svar_notin_singleton1 Hnotin) => Hne.
      rewrite eq_sym in Hne. rewrite (algred_upd_avars_acc_ne Hne).
      rewrite acc_algred_store. reflexivity.
    - move=> op e IH E g p bs Hnotin. rewrite (IH _ _ _ _ Hnotin). reflexivity.
    - move=> op e1 IH1 e2 IH2 E g p bs Hnotin.
      rewrite (IH1 _ _ _ _ (svar_notin_union1 Hnotin))
              (IH2 _ _ _ _ (svar_notin_union2 Hnotin)). reflexivity.
    - move=> e IH n E g p bs Hni. rewrite (IH _ _ _ _ Hni). reflexivity.
  Qed.

  Lemma algred_upd_avars_eval_eexps {E avn g p bs es} :
    svar_notin avn (vars_eexps es) ->
    ZSSA.eval_zexps es (algred_upd_avars
                          E avn g p (algred_store (program_succ_typenv p E) bs)) =
    eval_eexps es (program_succ_typenv p E) bs.
  Proof.
    elim: es => [| e es IH] //=. rewrite svar_notin_union. move=> [Hni1 Hni2].
    rewrite (algred_upd_avars_eval_eexp Hni1) (IH Hni2). reflexivity.
  Qed.

  Lemma algred_upd_avars_eval_ebexp {E avn g p bs e} :
    svar_notin avn (vars_ebexp e) ->
    ZSSA.eval_zbexp e (algred_upd_avars
                         E avn g p (algred_store (program_succ_typenv p E) bs)) <->
    eval_ebexp e (program_succ_typenv p E) bs.
  Proof.
    elim: e E g p bs => //=.
    - move=> e1 e2 E g p bs Hnotin.
      rewrite (algred_upd_avars_eval_eexp (svar_notin_union1 Hnotin))
              (algred_upd_avars_eval_eexp (svar_notin_union2 Hnotin)). done.
    - move=> e1 e2 ms E g p bs Hnotin.
      move: (svar_notin_union2 Hnotin) => Hnotin2m.
      rewrite (algred_upd_avars_eval_eexp (svar_notin_union1 Hnotin))
              (algred_upd_avars_eval_eexp (svar_notin_union1 Hnotin2m))
              (algred_upd_avars_eval_eexps (svar_notin_union2 Hnotin2m)). done.
    - move=> e1 IH1 e2 IH2 E g p bs Hnotin.
      rewrite (IH1 _ _ _ _ (svar_notin_union1 Hnotin))
              (IH2 _ _ _ _ (svar_notin_union2 Hnotin)). done.
  Qed.


  (* Soundness *)

  Ltac decompose_svar_notin_union :=
    repeat
      (match goal with
       | H : svar_notin _ (SSAVS.union _ _) |- _ =>
         let H1 := fresh "Hni" in let H2 := fresh "Hni" in
         move/svar_notin_union: H => /= [H1 H2]
       end).

  Definition fresh_var_spec v s :=
    svar_notin v (SSAVS.union (vars_env (sinputs s))
                              (SSAVS.union (vars_bexp (spre s))
                                           (SSAVS.union (vars_program (sprog s))
                                                        (vars_bexp (spost s))))).

  Definition fresh_var_espec v s :=
    svar_notin v (SSAVS.union (vars_env (esinputs s))
                              (SSAVS.union (vars_bexp (espre s))
                                           (SSAVS.union (vars_program (esprog s))
                                                        (vars_ebexp (espost s))))).

  Lemma new_svar_spec_fresh s :
    fresh_var_spec (new_svar_spec s) s .
  Proof. exact: new_svar_notin. Qed.

  Lemma new_svar_espec_fresh s :
    fresh_var_espec (new_svar_espec s) s .
  Proof. exact: new_svar_notin. Qed.

  Ltac mytac ::=
    repeat
      match goal with
      | H : svar_notin _ (SSAVS.union _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move: (svar_notin_union1 H) (svar_notin_union2 H) => {H} H1 H2
      | |- svar_notin _ (SSAVS.union _ _) =>
          apply: svar_notin_union3
      | H : ?e |- ?e => assumption
      | H: svar_notin ?v (vars_bexp ?g) |-
          svar_notin ?v (ZSSA.vars_zbexp (eqn_bexp ?g)) =>
          exact: (svar_notin_subset (vars_ebexp_subset g) H)
      end.

  Lemma fresh_var_spec_espec v s :
    fresh_var_spec v s -> fresh_var_espec v (SSA.espec_of_spec s).
  Proof.
    case: s => E f p g. rewrite /fresh_var_spec /fresh_var_espec /SSA.espec_of_spec /=.
    move=> ?; by mytac.
  Qed.

  Lemma algred_espec_sound (o : options) (avn : var) (s : spec) :
    well_formed_ssa_spec s ->
    ssa_spec_algsnd s ->
    fresh_var_espec avn (espec_of_spec s) ->
    ZSSA.valid_rep (algred_espec o avn (espec_of_spec s)) ->
    valid_espec (SSA.espec_of_spec s).
  Proof.
    destruct s as [E f p g] => /=. rewrite /well_formed_ssa_spec /algred_espec /=.
    rewrite /well_formed_spec /=.
    move/andP=> [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hunch] Hssa].
    set g1 := initial_index.
    dcase (algred_program o E avn g1 (eqn_program p)) => [[g2 eprogs] Hzp].
    rewrite /new_svar_espec_fresh /fresh_var_espec.
    move=> Hsafe Hnotin Heqn bs1 bs2 /= Hcon [Hpre_eqn Hpre_rng] Hprog.

    rewrite /ZSSA.valid_rep /= in Heqn.

    decompose_svar_notin_union.
    move: (svar_notin_subset (vars_ebexp_subset f) Hni1) => Hni_eqn_f.
    move: Hni3 => /= Hni_eqn_g.

    move: (SSA.well_formed_eqn_bexp Hwf_f) => Hwf_ef.
    move/andP: Hwf_ef => [Hdef_ef Hwt_ef].
    rewrite are_defined_subset_env in Hdef_ef.
    move: (SSA.ssa_unchanged_program_subset Hunch Hdef_ef) => Hunch_ef.
    rewrite -ssa_vars_unchanged_eqn_program in Hunch_ef.
    move: (SSA.ssa_unchanged_program_eval_ebexp1
             Hunch_ef (eval_eqn_program Hprog) Hpre_eqn) => Heval_ef.
    move: (@algred_upd_avars_eval_ebexp
             E
             avn g1 (eqn_program p) bs2 (eqn_bexp f) Hni_eqn_f) => Hiff.
    move: (ssa_unchanged_program_succ_typenv_submap Hunch Hssa) => Hsubmap.
    move/andP: Hwf_f => [Hdef_f Hwt_f]. rewrite are_defined_union in Hdef_f.
    move/andP: Hdef_f => [Hdef_eqn_f Hdef_rng_f].
    move: (@SSA.submap_eval_ebexp _ _ _ bs2 Hsubmap Hdef_eqn_f).
    rewrite -eqn_program_succ_typenv => H.
    move/H/Hiff: Heval_ef => {H} Hzf.

    move: (Hsafe bs1 Hcon Hpre_rng) => /= => Hsafe_at.
    rewrite algred_eqn_program in Hzp.
    move: (algred_upd_avars_sat_program
             Hwf_p Hunch Hssa Hni Hni0 Hcon Hsafe_at Hprog Hzp) => Hzprog.
    rewrite -eqn_program_succ_typenv in Hzprog.
    rewrite -algred_upd_avars_eqn in Hzprog.

    move: Hzf Hzprog.
    set zbs2 := algred_upd_avars
                  E avn g1 (eqn_program p)
                  (algred_store (program_succ_typenv (eqn_program p) E) bs2).
    move=> Hzf Hzprog.
    move: (Heqn zbs2). rewrite Hzp /= => Hzg.
    move: (Hzg (conj Hzf Hzprog)) => {} Hzg.

    apply/(algred_upd_avars_eval_ebexp Hni_eqn_g). exact: Hzg.
  Qed.

  Theorem algred_spec_sound (o : options) avn (s : spec) :
    well_formed_ssa_spec s ->
    ssa_spec_algsnd s ->
    valid_rspec (rspec_of_spec s) ->
    fresh_var_espec avn (espec_of_spec s) ->
    ZSSA.valid_rep (algred_espec o avn (espec_of_spec s)) ->
    valid_spec s.
  Proof.
    move=> Hwf Hsafe Hvr Hnotin Hvz. apply: valid_spec_split.
    - apply: (algred_espec_sound Hwf Hsafe Hnotin Hvz).
    - exact: Hvr.
  Qed.











  (* With slicing *)

  Lemma algred_spec_split o s avn :
    ZSSA.valid_reps (tmap (algred_espec o avn) (split_espec s)) ->
    ZSSA.valid_rep (algred_espec o avn s).
  Proof.
    case: s => E f p g /=. rewrite tmap_map. elim: g E f p => //=.
    - move=> E f p. apply. exact: mem_head.
    - move=> e1 e2 E f p. apply. exact: mem_head.
    - move=> e1 e2 ms E f p. apply. exact: mem_head.
    - move=> e1 IH1 e2 IH2 E f p Hreps.

      rewrite /algred_espec /=.
      dcase (algred_program o E avn initial_index p) => [[n eprogs] Hap].
      rewrite split_espec_eand /= in Hreps.
      rewrite map_cat in Hreps. move/ZSSA.valid_reps_cat: Hreps => [Hreps1 Hreps2].
      move=> st /=. move=> [Hef Hep]. split.
      + move: (IH1 _ _ _ Hreps1 st). rewrite /algred_espec /=. rewrite Hap /=. apply. tauto.
      + move: (IH2 _ _ _ Hreps2 st). rewrite /algred_espec /=. rewrite Hap /=. apply. tauto.
  Qed.

  Section StorePvareq.

    Variable avn : var.

    Definition store_pvareq s1 s2 :=
      forall v, avn != svar v -> ZSSAStore.acc v s1 = ZSSAStore.acc v s2.

    Global Instance store_pvareq_refl : RelationClasses.Reflexive store_pvareq.
    Proof. move=> s v Hnotin. reflexivity. Qed.

    Global Instance store_pvareq_sym : RelationClasses.Symmetric store_pvareq.
    Proof.
      move=> s1 s2 Heq v Hnotin. rewrite (Heq _ Hnotin). reflexivity.
    Qed.

    Instance store_pvareq_trans : RelationClasses.Transitive store_pvareq.
    Proof.
      move=> s1 s2 s3 Heq12 Heq23 v Hnotin. rewrite (Heq12 _ Hnotin).
      exact: (Heq23 _ Hnotin).
    Qed.

    Instance store_pvareq_equiv : RelationClasses.Equivalence store_pvareq :=
      { Equivalence_Reflexive := store_pvareq_refl;
        Equivalence_Symmetric := store_pvareq_sym;
        Equivalence_Transitive := store_pvareq_trans }.

    Lemma store_pvareq_eval_zexp s1 s2 e :
      svar_notin avn (ZSSA.vars_zexp e) -> store_pvareq s1 s2 ->
      ZSSA.eval_zexp e s1 = ZSSA.eval_zexp e s2.
    Proof.
      elim: e => //=.
      - move=> v /svar_notin_singleton Hnotin Heq. exact: (Heq _ Hnotin).
      - move=> op e IH Hnotin Heq. rewrite (IH Hnotin Heq). reflexivity.
      - move=> op e1 IH1 e2 IH2 /svar_notin_union [Hnotin1 Hnotin2] Heq.
        rewrite (IH1 Hnotin1 Heq) (IH2 Hnotin2 Heq). reflexivity.
      - move=> e IH n Hnotin Heq. rewrite (IH Hnotin Heq). reflexivity.
    Qed.

    Lemma store_pvareq_eval_zexps s1 s2 es :
      svar_notin avn (ZSSA.vars_zexps es) -> store_pvareq s1 s2 ->
      ZSSA.eval_zexps es s1 = ZSSA.eval_zexps es s2.
    Proof.
      elim: es => [| e es IH] //=. move => /svar_notin_union [Hnotin1 Hnotin2] Heq.
      rewrite (store_pvareq_eval_zexp Hnotin1 Heq) (IH Hnotin2 Heq). reflexivity.
    Qed.

    Lemma store_pvareq_eval_zbexp s1 s2 e :
      svar_notin avn (ZSSA.vars_zbexp e) -> store_pvareq s1 s2 ->
      ZSSA.eval_zbexp e s1 -> ZSSA.eval_zbexp e s2.
    Proof.
      elim: e => //=.
      - move=> e1 e2 /svar_notin_union [Hnotin1 Hnotin2] Heq.
        rewrite (store_pvareq_eval_zexp Hnotin1 Heq) (store_pvareq_eval_zexp Hnotin2 Heq).
        by apply.
      - move=> e1 e2 ms /svar_notin_union [Hnotin1 /svar_notin_union [Hnotin2 Hnotin3]] Heq.
        rewrite (store_pvareq_eval_zexp Hnotin1 Heq) (store_pvareq_eval_zexp Hnotin2 Heq)
                (store_pvareq_eval_zexps Hnotin3 Heq). by apply.
      - move=> e1 IH1 e2 IH2 /svar_notin_union [Hnotin1 Hnotin2] Heq.
        move: (IH1 Hnotin1 Heq) (IH2 Hnotin2 Heq). tauto.
    Qed.

    Lemma store_pvareq_upd_l g v s1 s2 :
      store_pvareq s1 s2 -> store_pvareq (ZSSAStore.upd (avn, g) v s1) s2.
    Proof.
      move=> Heq x Hne. rewrite ZSSAStore.acc_upd_neq.
      - exact: (Heq _ Hne).
      - case: x Hne => [x gx] Hne. apply/negP => /eqP [] ? ?; subst.
        move/negP: Hne; apply. exact: eqxx.
    Qed.

    Lemma store_pvareq_upd_r g v s1 s2 :
      store_pvareq s1 s2 -> store_pvareq s1 (ZSSAStore.upd (avn, g) v s2).
    Proof.
      move=> Heq x Hne. rewrite ZSSAStore.acc_upd_neq.
      - exact: (Heq _ Hne).
      - case: x Hne => [x gx] Hne. apply/negP => /eqP [] ? ?; subst.
        move/negP: Hne; apply. exact: eqxx.
    Qed.

  End StorePvareq.

  Definition succ_gen avn vs i gs g s t :=
    match slice_einstr vs i with
    | None => (gs, N.succ g, t)
    | Some _ => (N.succ gs, N.succ g, ZSSAStore.upd (avn, gs) (ZSSAStore.acc (avn, g) s) t)
    end.

  Definition algred_instr_upd_avn E avn vs i gs g s t :=
    match i with
    | Icast v tv a =>
        match tv, atyp a E with
        | Tuint wv, Tuint wa =>
            if wv >= wa then (gs, g, t)
            else succ_gen avn vs i gs g s t
        | Tuint wv, Tsint wa => succ_gen avn vs i gs g s t
        | Tsint wv, Tuint wa =>
            if wv > wa then (gs, g, t)
            else succ_gen avn vs i gs g s t
        | Tsint wv, Tsint wa =>
            if wv >= wa then (gs, g, t)
            else succ_gen avn vs i gs g s t
        end
    | _ => (gs, g, t)
    end.

  Fixpoint algred_program_upd_avn E avn vs p gs g s t :=
    match p with
    | [::] => (gs, g, t)
    | hd::tl => let '(gs', g', t') := algred_instr_upd_avn E avn vs hd gs g s t in
                algred_program_upd_avn (instr_succ_typenv hd E) avn vs tl gs' g' s t'
    end.

  Ltac case_if' :=
    repeat
      case_if ||
        match goal with
        | |- context c [let (_, _) := ?b in _] =>
            let e := fresh in
            let r := fresh in
            case: b => e r
        end.

  Ltac mysimpl :=
    repeat (case_option; case_if'; case_tuples;
            (try match goal with
                 | H : algred_instr _ _ _ _ _ = _ |- _ => simpl in H
                 | H : MA.agree (vars_instr _) _ _ |- _ => simpl in H
                 end);
            MA.simpl_agree; intros; subst).

  Ltac mytac ::=
    repeat (mysimpl;
            match goal with
            | H : context c [algred_cast] |- _ =>
                move: H; rewrite /algred_cast /=
            | H : context c [algred_vpc] |- _ =>
                move: H; rewrite /algred_vpc /=
            | H1 : MA.agree (vars_atom ?a) ?E1 ?E2,
                H2 : context c [atyp ?a ?E1] |- _ =>
                rewrite !(agree_atyp H1) in H2
            | H : MA.agree (vars_atom ?a) ?E1 ?E2 |- context c [atyp ?a ?E1] =>
                rewrite !(agree_atyp H)
            | H : match ?t with
                  | Tuint _ => _
                  | Tsint _ => _
                  end = _ |- _ =>
                repeat match goal with
                       | H0 : context c [t] |- _ => move: H0
                       end;
                let w := fresh in
                case: t; move=> w
            end);
    mysimpl;
    repeat match goal with
           | |- ?e1 = ?e1 /\ ?e2 = ?e2 => split; reflexivity
           | |- ?e = ?e => reflexivity
           | H1 : VSLemmas.disjoint ?vs1 ?vs2 = false,
               H2 : VSLemmas.disjoint ?vs1 ?vs2 = true |- _ =>
               rewrite H1 in H2; discriminate
           | H1 : (?a <= ?b)%N = true,
               H2 : (?a <= ?b)%N = false |- _ =>
               rewrite H1 in H2; discriminate
           end.

  Lemma slice_einstr_none_upd_avn_gen E avn vs i g1 g2 g1' g2' s1 s2 t :
    slice_einstr vs i = None ->
    algred_instr_upd_avn E avn vs i g1 g2 s1 s2 = (g1', g2', t) ->
    g1 = g1'.
  Proof.
    rewrite /algred_instr_upd_avn /succ_gen. case: i => //=; intros; by mytac.
  Qed.

  Lemma slice_einstr_some_upd_avn_gen o E1 E2 avn vs i i' g1 g2 eg1 ei1 g1' g2' s1 s2 t :
    slice_einstr vs i = Some i' ->
    MA.agree (vars_instr i') E1 E2 ->
    algred_instr o E1 avn g1 i' = (eg1, ei1) ->
    algred_instr_upd_avn E2 avn vs i g1 g2 s1 s2 = (g1', g2', t) ->
    eg1 = g1'.
  Proof.
    rewrite /algred_instr_upd_avn /succ_gen.
    case: i => //=; intros; mytac. move: H. case_if'.
    case=> ?; subst. case: H1 => ? ?; subst. reflexivity.
  Qed.

  Lemma algred_instr_upd_avn_gen_le E avn vs i g1 g2 g1' g2' s1 s2 t :
    algred_instr_upd_avn E avn vs i g1 g2 s1 s2 = (g1', g2', t) ->
    (g1 <= g1')%num /\ (g2 <= g2')%num.
  Proof.
    rewrite /algred_instr_upd_avn /succ_gen.
    (case: i => //=); intros; mytac; split;
    by match goal with
       | |- (?a <= ?a)%num => exact: N.le_refl
       | |- (?a <= N.succ ?a)%num => exact: N.le_succ_diag_r
       end.
  Qed.

  Lemma algred_instr_upd_avn_gen o E2 avn vs i g1 g2 eg2 ei2 g1' g2' s1 s2 t :
    algred_instr o E2 avn g2 i = (eg2, ei2) ->
    algred_instr_upd_avn E2 avn vs i g1 g2 s1 s2 = (g1', g2', t) ->
    eg2 = g2'.
  Proof.
    rewrite /algred_instr_upd_avn /succ_gen. case: i => //=; intros; by mytac.
  Qed.

  Lemma slice_einstr_none_upd_avn_store vs i E avn g1 g2 s1 s2 g1' g2' t2 :
    slice_einstr vs i = None ->
    algred_instr_upd_avn E avn vs i g1 g2 s1 s2 = (g1', g2', t2) ->
    s2 = t2.
  Proof.
    rewrite /algred_instr_upd_avn /succ_gen. case: i => /=; by mytac.
  Qed.

  Lemma algred_instr_upd_avn_eval o vs E1 E2 avn i i' g1 g2 eg1 ei1 eg2 ei2 eg1' eg2' s1 s2 t2 :
    slice_einstr vs i = Some i' ->
    svar_notin avn (vars_instr i) ->
    MA.agree (vars_instr i') E1 E2 ->
    algred_instr o E1 avn g1 i' = (eg1, ei1) ->
    algred_instr o E2 avn g2 i = (eg2, ei2) ->
    ZSSA.eval_zbexp (eands ei2) s1 ->
    algred_instr_upd_avn E2 avn vs i g1 g2 s1 s2 = (eg1', eg2', t2) ->
    store_pvareq avn s1 s2 ->
    store_pvareq avn s1 t2 /\ ZSSA.eval_zbexp (eands ei1) t2.
  Proof.
    case: i => //=; intros; mytac;
    repeat
      ((try case_svar_notin);
       match goal with
       | H : ZSSA.eval_zbexp (eands [:: _]) _ |- _ => case: H; move=> /= H _
       | H : _ /\ _ |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           case: H; move=> H1 H2
       | |- _ /\ _ => split
       | H : context c [succ_gen] |- _ => rewrite /succ_gen /= in H
       | H1 : context c [if ?e then _ else _],
           H2 : ?e = _ |- _ =>
           rewrite H2 /= in H1
       | H : (_, _, _) = (_, _, _) |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           let H3 := fresh in
           case: H; intros H1 H2 H3; subst
       | H : ?e |- ?e => assumption
       | |- ZSSA.eval_zbexp (eands [:: _]) _ => split; [simpl | by trivial]
       | H : context c [carry_constr ?o ?t] |- context d [carry_constr ?o ?t] =>
           move: H; rewrite /carry_constr /algred_is_carry; case_if
       | H : context c [algred_split] |- _ => rewrite /algred_split /= in H
       | |- context c [algred_split] => rewrite /algred_split /=
       | H : context c [algred_join] |- _ => rewrite /algred_join /= in H
       | |- context c [algred_join] => rewrite /algred_join /=
       | H1 : store_pvareq ?avn _ ?t2,
           H2 : is_true (?avn != Var.svar ?t) |-
           context c [ZSSAStore.acc _ ?t2] =>
           rewrite -(H1 t H2)
       | H : svar_notin ?avn (vars_atom ?a) |- _ =>
           rewrite -vars_algred_atom in H
       | H : MA.agree (vars_atom ?a) ?E1 ?E2 |- context [asize ?a ?E1] =>
           rewrite !(agree_asize H)
       | H1 : store_pvareq ?avn ?s1 ?t2,
           H2 : svar_notin ?avn (ZSSA.vars_zexp (algred_atom ?a))
         |- context c [ZSSA.eval_zexp (algred_atom ?a) ?t2] =>
           rewrite -(store_pvareq_eval_zexp H2 H1)
       | H1 : store_pvareq ?avn ?s1 ?s2,
           H2 : is_true (?avn != Var.svar ?t) |-
           context f [ZSSAStore.acc ?t (ZSSAStore.upd (?avn, ?g1) ?v ?s2)] =>
           rewrite -((store_pvareq_upd_r g1 v H1) t H2)
       |  H1 : store_pvareq ?avn ?s1 ?s2,
           H2 : svar_notin ?avn (ZSSA.vars_zexp (algred_atom ?a))
          |- context c [ZSSA.eval_zexp (algred_atom ?a) (ZSSAStore.upd (?avn, ?g1) ?v ?s2)] =>
            rewrite -(store_pvareq_eval_zexp H2 (store_pvareq_upd_r g1 v H1))
       | |- context c [ZSSAStore.acc ?x (ZSSAStore.upd ?x _ _)] =>
           rewrite ZSSAStore.acc_upd_eq
       | |- context c [ZSSAStore.acc (?avn, ?g) (ZSSAStore.upd (?anv, ?g) _ _)] =>
           rewrite (ZSSAStore.acc_upd_eq (eqxx (avn, g)))
       | |- store_pvareq avn _ (ZSSAStore.upd (avn, _) _ _) =>
           apply: store_pvareq_upd_r
       | |- True => by trivial
       | |- ZSSA.eval_zbexp (eands [::]) _ => by trivial
       | H1 : ?e = true, H2 : ?e = false |- _ =>
           rewrite H2 in H1; discriminate
       | H : true = false |- _ => discriminate
       end).
    case: b H H0 H4 => [e r] /=. case=> ?; subst. rewrite /vars_bexp /=.
    move/svar_notin_union => [Hnotin_e Hnotin_r]. move=> H. rewrite /= in H1 H2.
    case: H2 => ? ?; subst. apply: (store_pvareq_eval_zbexp _ H6).
    - rewrite SSA.vars_eands_split_eand.
      exact: (svar_notin_subset (slice_ebexp_vars_subset vs e) Hnotin_e).
    - apply/ZSSA.eval_zbexp_eands_split_eand. move/ZSSA.eval_zbexp_eands_split_eand: H.
      exact: ZSSA.slice_zbexp_eval.
  Qed.

  Lemma newer_than_pvareq_eval_zeexp avn e g t1 t2 :
    avars_newer_than avn g (ZSSA.vars_zexp e) ->
    store_pvareq avn t1 t2 ->
    (forall g', (g' < g)%num -> ZSSAStore.acc (avn, g') t1 = ZSSAStore.acc (avn, g') t2) ->
    ZSSA.eval_zexp e t1 = ZSSA.eval_zexp e t2.
  Proof.
    elim: e => //=.
    - move=> [] v gv Hnew Heq Hacc. case Hv: (avn == v).
      + move/eqP: Hv => ?; subst. apply: Hacc.
        move: (Hnew (v, gv) (SSA.VSLemmas.mem_singleton2 (eqxx (v, gv)))).
        rewrite /avars_newer_than_var /=. rewrite eqxx /=. case; first discriminate.
        by apply.
      + move/idP/negP: Hv => Hv. apply: Heq. exact: Hv.
    - move=> op e IH Hnew Heq Hacc. rewrite (IH Hnew Heq Hacc). reflexivity.
    - move=> op e1 IH1 e2 IH2 /avars_newer_than_union [Hnew1 Hnew2] Heq Hacc.
      rewrite (IH1 Hnew1 Heq Hacc) (IH2 Hnew2 Heq Hacc). reflexivity.
    - move=> e IH n Hnew Heq Hacc. rewrite (IH Hnew Heq Hacc). reflexivity.
  Qed.

  Lemma newer_than_pvareq_eval_zeexps avn es g t1 t2 :
    avars_newer_than avn g (ZSSA.vars_zexps es) ->
    store_pvareq avn t1 t2 ->
    (forall g', (g' < g)%num -> ZSSAStore.acc (avn, g') t1 = ZSSAStore.acc (avn, g') t2) ->
    ZSSA.eval_zexps es t1 = ZSSA.eval_zexps es t2.
  Proof.
    elim: es => [| e es IH] //=. move=> /avars_newer_than_union [Hnew1 Hnew2] Heq Hacc.
    rewrite (newer_than_pvareq_eval_zeexp Hnew1 Heq Hacc)
            (IH Hnew2 Heq Hacc). reflexivity.
  Qed.

  Lemma newer_than_pvareq_eval_zbexp avn e g t1 t2 :
    avars_newer_than avn g (ZSSA.vars_zbexp e) ->
    store_pvareq avn t1 t2 ->
    (forall g', (g' < g)%num -> ZSSAStore.acc (avn, g') t1 = ZSSAStore.acc (avn, g') t2) ->
    ZSSA.eval_zbexp e t1 ->
    ZSSA.eval_zbexp e t2.
  Proof.
    elim: e => //=.
    - move=> e1 e2 /avars_newer_than_union [Hnew1 Hnew2] Heq Hacc Hev.
      rewrite -(newer_than_pvareq_eval_zeexp Hnew1 Heq Hacc)
              -(newer_than_pvareq_eval_zeexp Hnew2 Heq Hacc). assumption.
    - move=> e1 e2 ms /avars_newer_than_union [Hnew1 /avars_newer_than_union [Hnew2 Hnew3]]
                Heq Hacc Hev.
      rewrite -(newer_than_pvareq_eval_zeexp Hnew1 Heq Hacc)
              -(newer_than_pvareq_eval_zeexp Hnew2 Heq Hacc)
              -(newer_than_pvareq_eval_zeexps Hnew3 Heq Hacc). assumption.
    - move=> e1 IH1 e2 IH2 /avars_newer_than_union [Hnew1 Hnew2] Heq Hacc [H1 H2].
      exact: (conj (IH1 Hnew1 Heq Hacc H1) (IH2 Hnew2 Heq Hacc H2)).
  Qed.

  Lemma algred_instr_upd_avn_newer_than E avn vs i g1 g2 g1' g2' s1 s2 t2 g' :
    algred_instr_upd_avn E avn vs i g1 g2 s1 s2 = (g1', g2', t2) ->
    (g' < g1)%num ->
    ZSSAStore.acc (avn, g') s2 = ZSSAStore.acc (avn, g') t2.
  Proof.
    rewrite /algred_instr_upd_avn /succ_gen.
    case: i => //=; intros; mytac.
    - rewrite ZSSAStore.acc_upd_neq;
        [ reflexivity |
          apply/negP => /eqP [] ?; subst; exact: (N.lt_irrefl _ H0)].
    - rewrite ZSSAStore.acc_upd_neq;
        [ reflexivity |
          apply/negP => /eqP [] ?; subst; exact: (N.lt_irrefl _ H0)].
    - rewrite ZSSAStore.acc_upd_neq;
        [ reflexivity |
          apply/negP => /eqP [] ?; subst; exact: (N.lt_irrefl _ H0)].
    - rewrite ZSSAStore.acc_upd_neq;
        [ reflexivity |
          apply/negP => /eqP [] ?; subst; exact: (N.lt_irrefl _ H0)].
  Qed.

  Lemma algred_program_upd_avn_newer_than E avn vs p g1 g2 g1' g2' s1 s2 t2 g' :
    algred_program_upd_avn E avn vs p g1 g2 s1 s2 = (g1', g2', t2) ->
    (g' < g1)%num ->
    ZSSAStore.acc (avn, g') s2 = ZSSAStore.acc (avn, g') t2.
  Proof.
    elim: p E avn vs g1 g2 g1' g2' s1 s2 t2 g'
        => [| i p IH] E avn vs g1 g2 g1' g2' s1 s2 t2 g' //=.
    - case => ? ? ?; subst. move=> Hg. reflexivity.
    - dcase (algred_instr_upd_avn E avn vs i g1 g2 s1 s2) => [[[g1_hd g2_hd] t_hd] Hhd].
      move=> Htl Hg. rewrite (algred_instr_upd_avn_newer_than Hhd Hg).
      apply: (IH _ _ _ _ _ _ _ _ _ _ _ Htl).
      move: (algred_instr_upd_avn_gen_le Hhd) => [Hg1 Hg2].
      exact: (N.lt_le_trans _ _  _ Hg Hg1).
  Qed.

  Lemma algred_program_upd_avn_eval o vs E1 E2 avn p g1 g2 eg1 ep1 eg2 ep2 eg1' eg2' s1 s2 t2 :
    svar_notin avn (vars_program p) ->
    SSAVS.subset (vars_program (slice_eprogram vs p)) vs ->
    MA.agree (vars_program (slice_eprogram vs p)) E1 E2 ->
    algred_program o E1 avn g1 (slice_eprogram vs p) = (eg1, ep1) ->
    algred_program o E2 avn g2 p = (eg2, ep2) ->
    ZSSA.eval_zbexp (eands ep2) s1 ->
    algred_program_upd_avn E2 avn vs p g1 g2 s1 s2 = (eg1', eg2', t2) ->
    store_pvareq avn s1 s2 ->
    store_pvareq avn s1 t2 /\ ZSSA.eval_zbexp (eands ep1) t2.
  Proof.
    elim: p o vs E1 E2 avn g1 g2 eg1 ep1 eg2 ep2 eg1' eg2' s1 s2
        => [| i p IH]  o vs E1 E2 avn g1 g2 eg1 ep1 eg2 ep2 eg1' eg2' s1 s2 /=.
    - move=> _ _ Hag [] ? ? [] ? ? Hev [] ? ? ?; subst. move=> Heq.
      split; [assumption | done].
    - move=> /svar_notin_union [Hnotin_i Hnotin_p]. dcase (slice_einstr vs i); case.
      + move=> i' Hsi /=. rewrite SSA.VSLemmas.subset_union6 => /andP [Hsub_i Hsub_p].
        move/MA.agree_union_set => [Hag_i Hag_p].
        dcase (algred_instr o E1 avn g1 i') => [[g_hd1 zhd1] Hhd1].
        dcase (algred_program o (instr_succ_typenv i' E1) avn g_hd1 (slice_eprogram vs p))
              => [[g_tl1 ztl1] Htl1].
        dcase (algred_instr o E2 avn g2 i) => [[g_hd2 zhd2] Hhd2].
        dcase (algred_program o (instr_succ_typenv i E2) avn g_hd2 p)
              => [[g_tl2 ztl2] Htl2].
        dcase (algred_instr_upd_avn E2 avn vs i g1 g2 s1 s2) => [[[g_hd1' g_hd2'] t] Hupd_hd].
        move=> [] ? ? [] ? ?; subst. move/ZSSA.eval_zbexp_eands_cat => [Hev1 Hev2].
        move=> Hupd_tl Heq.
        move: (algred_instr_upd_avn_eval Hsi Hnotin_i Hag_i Hhd1 Hhd2 Hev1 Hupd_hd Heq)
            => [Heq1t Hev1t].
        move: (slice_einstr_some_upd_avn_gen Hsi Hag_i Hhd1 Hupd_hd) => ?; subst.
        move: (algred_instr_upd_avn_gen Hhd2 Hupd_hd) => ?; subst.

        move: (IH o vs (instr_succ_typenv i E1) (instr_succ_typenv i E2)
                  avn g_hd1' g_hd2' eg1 ztl1 eg2 ztl2 eg1' eg2' s1 t Hnotin_p).
        rewrite -(slice_einstr_some_succ_typenv _ Hsi) in Htl1 *.
        have Hag_succ: MA.agree (vars_program (slice_eprogram vs p)) (instr_succ_typenv i E1) (instr_succ_typenv i E2).
        { rewrite !(slice_einstr_some_succ_typenv _ Hsi).
          exact: (agree_instr_succ_typenv Hag_p Hag_i). }
        move=> H. move: (H Hsub_p Hag_succ Htl1 Htl2 Hev2 Hupd_tl Heq1t) => {H} [Heq12 Hevztl1].
        split; first assumption. apply/ZSSA.eval_zbexp_eands_cat.
        split; last assumption.
        move: (svar_notin_subset (slice_einstr_vars_subset Hsi) Hnotin_i) => Hnotin_i'.
        apply: (newer_than_pvareq_eval_zbexp
                  (algred_instr_newer_than Hhd1 Hnotin_i')
                  (store_pvareq_trans (store_pvareq_sym Heq1t) Heq12)).
        * move=> g'.
          exact: (algred_program_upd_avn_newer_than Hupd_tl).
        * assumption.
      + move=> Hsi Hsub Hag.
        dcase (algred_instr o E2 avn g2 i) => [[g_hd2 zhd2] Hhd2].
        dcase (algred_program o (instr_succ_typenv i E2) avn g_hd2 p) => [[g_tl2 ztl2] Htl2].
        dcase (algred_instr_upd_avn E2 avn vs i g1 g2 s1 s2) => [[[g_hd1' g_hd2'] t] Hupd_hd].
        move=> Htl1 [] ? ?; subst. move /ZSSA.eval_zbexp_eands_cat => [Hev_hd Hev_tl].
        move=> Hupd_tl Heq.
        move: (slice_einstr_none_upd_avn_gen Hsi Hupd_hd) => ?; subst.
        move: (algred_instr_upd_avn_gen Hhd2 Hupd_hd) => ?; subst.

        have Hag_succ: MA.agree (vars_program (slice_eprogram vs p)) E1 (instr_succ_typenv i E2).
        { apply: (MA.agree_trans Hag).
          exact: (MA.subset_set_agree Hsub (MA.agree_sym (slice_einstr_none_agree E2 Hsi))). }

        apply: (IH o vs E1 (instr_succ_typenv i E2) _ _ _ _ _ _ _ _ _ _ _ Hnotin_p Hsub Hag_succ
               Htl1 Htl2 Hev_tl Hupd_tl).
        move: (slice_einstr_none_upd_avn_store Hsi Hupd_hd) => ?; subst.
        assumption.
  Qed.

  Lemma algred_program_exists o avn vs E1 E2 p g1 g2 eg1 ep1 eg2 ep2 st  :
    svar_notin avn (vars_program p) ->
    SSAVS.subset (vars_program (slice_eprogram vs p)) vs ->
    MA.agree vs E1 E2 ->
    algred_program o E1 avn g1 (slice_eprogram vs p) = (eg1, ep1) ->
    algred_program o E2 avn g2 p = (eg2, ep2) ->
    ZSSA.eval_zbexp (eands ep2) st ->
    exists st', store_pvareq avn st st' /\ ZSSA.eval_zbexp (eands ep1) st'.
  Proof.
    move=> Hnotin Hsub Hag Har1 Har2 Hev.
    dcase (algred_program_upd_avn E2 avn vs p g1 g2 st st) => [[[g1' g'] t] Hupd].
    exists t.
    apply: (algred_program_upd_avn_eval Hnotin Hsub (MA.subset_set_agree Hsub Hag)
           Har1 Har2 Hev Hupd).
    exact: store_pvareq_refl.
  Qed.

  Lemma algred_spec_slice_espec o avn s :
    fresh_var_espec avn s ->
    ZSSA.valid_rep (algred_espec o avn (slice_espec s)) ->
    ZSSA.valid_rep (algred_espec o avn s).
  Proof.
    case: s => E f p g. rewrite /fresh_var_espec /slice_espec /algred_espec /=.
    dcase (algred_program
             o E avn initial_index
             (slice_eprogram (depvars_epre_eprogram_sat (eqn_bexp f) p (ZSSA.vars_zbexp g)) p))
          => [[eg1 ep1] Har1].
    dcase (algred_program o E avn initial_index p) => [[eg2 ep2] Har2].
    rewrite /ZSSA.valid_rep /=. move=> Hnotin Hent st /ZSSA.eval_zbexp_eands_cons [Hef Hep].

    move: (@MA.agree_refl _ (depvars_epre_eprogram_sat (eqn_bexp f) p (ZSSA.vars_zbexp g)) E)
        => Hag.
    move/svar_notin_union: Hnotin.
    move=> [Hnotin_E /svar_notin_union [Hnotin_f /svar_notin_union [Hnotin_p Hnotin_g]]].

    move: (algred_program_exists
             Hnotin_p (depvars_epre_eprogram_sat_slice_subset (eqn_bexp f) p (ZSSA.vars_zbexp g))
             Hag Har1 Har2 Hep) => [st' [Hseq Hevp1]].
    apply: (store_pvareq_eval_zbexp Hnotin_g (store_pvareq_sym Hseq)).
    apply: Hent. split.
    - apply: ZSSA.slice_zbexp_eval. apply: (store_pvareq_eval_zbexp _ Hseq Hef).
      apply: (svar_notin_subset _ Hnotin_f). exact: vars_ebexp_subset.
    - exact: Hevp1.
  Qed.

  Lemma svar_notin_avars_newer_than g avn vs :
    svar_notin avn vs -> avars_newer_than avn g vs.
  Proof.
    move=> Hnotin x Hmem. left. apply/eqP => Heq; subst.
    move: (Hnotin (sidx x)) => /=. apply/idP. clear Hnotin. case: x Hmem => /=. done.
  Qed.


  Lemma fresh_var_espec_split avn s s' :
    fresh_var_espec avn s ->
    In s' (split_espec s) -> fresh_var_espec avn s'.
  Proof.
    case: s => E f p g. rewrite /fresh_var_espec /=. elim: g => //=.
    - move=> Hnotin. case=> //=. move=> <- /=. by dp_svar_notin.
    - move=> e1 e2 Hnotin. case=> //=. move=> <-. by dp_svar_notin.
    - move=> e1 e2 ms Hnotin. case=> //=. move=> <-. by dp_svar_notin.
    - move=> e1 IH1 e2 IH2 Hnotin. rewrite split_espec_eand. move=> Hin.
      case: (in_cat Hin) => {}Hin.
      + apply: (IH1 _ Hin). by dp_svar_notin.
      + apply: (IH2 _ Hin). by dp_svar_notin.
  Qed.

  Lemma algred_spec_slice_especs o avn ss :
    (forall s, In s ss -> fresh_var_espec avn s) ->
    ZSSA.valid_reps (tmap (algred_espec o avn) (tmap slice_espec ss)) ->
    ZSSA.valid_reps (tmap (algred_espec o avn) ss).
  Proof.
    rewrite !tmap_map. elim: ss => [| s ss IH] Hnotins //=.
    move/ZSSA.valid_reps_cons=> [Hreps Hrepss].
    apply/ZSSA.valid_reps_cons. split.
    - apply: (algred_spec_slice_espec _ Hreps). apply: Hnotins. by left.
    - apply: (IH _ Hrepss). move=> s' Hin. apply: Hnotins. right. assumption.
  Qed.

  Theorem algred_spec_slice_sound (o : options) (avn : var) (s : spec) :
    well_formed_ssa_spec s ->
    ssa_spec_algsnd s ->
    fresh_var_espec avn (espec_of_spec s) ->
    valid_rspec (rspec_of_spec s) ->
    ZSSA.valid_reps (tmap (algred_espec o avn)
                          (tmap slice_espec (split_espec (espec_of_spec s)))) ->
    valid_spec s.
  Proof.
    move=> Hwf Hsnd Hnotin Hvr Hrep.
    apply: (algred_spec_sound (o:=o) Hwf Hsnd Hvr Hnotin).
    apply: algred_spec_split. apply: (algred_spec_slice_especs _ Hrep).
    move=> s'. exact: (fresh_var_espec_split Hnotin).
  Qed.

End SplitSpec.
