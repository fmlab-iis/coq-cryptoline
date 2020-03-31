
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder ZAriths Store Tactics.
From BitBlasting Require Import State Typ TypEnv.
From Cryptoline Require Import DSL SSA ZSSA.
From nbits Require Import NBits.

(** Conversion from a specification to a range specification, an algebraic specification, and a safety condition. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Record options : Set :=
  mkOptions { add_carry_constraints : bool }.

Definition default_options : options :=
  {| add_carry_constraints := false |}.



(* Tactics *)

Ltac case_pairs :=
  match goal with
  | H : (_, _) = (_, _) |- _ => case: H; move=> ? ?; subst
  | H : (if ?e then _ else _) = _ |- _ => move: H; case: e; intros
  | H : (match ?t with | Tuint _ => _ | Tsint _ => _ end) = _ |- _ =>
    move: H; case: t; intros
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



(** Safety conditions *)

Section Safety.

  Import SSA.

  Definition uaddB_safe bs1 bs2 : bool := ~~ carry_addB bs1 bs2.

  Definition saddB_safe bs1 bs2 : bool := ~~ Saddo bs1 bs2.

  Definition addB_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then uaddB_safe bs1 bs2
    else saddB_safe bs1 bs2.

  Definition adds_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then true
    else saddB_safe bs1 bs2.

  Definition uadcB_safe bs1 bs2 c : bool :=
    ~~ carry_addB bs1 bs2 && ~~ carry_addB (addB bs1 bs2) c.

  Definition sadcB_safe bs1 bs2 c : bool :=
    ~~ Saddo bs1 bs2 && ~~ Saddo (addB bs1 bs2) c.

  Definition adcB_safe typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then uadcB_safe bs1 bs2 bsc
    else sadcB_safe bs1 bs2 bsc.

  Definition adcs_safe typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then true
    else sadcB_safe bs1 bs2 bsc.

  Definition usubB_safe bs1 bs2 : bool := ~~ borrow_subB bs1 bs2.

  Definition ssubB_safe bs1 bs2 : bool := ~~ Ssubo bs1 bs2.

  Definition subB_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then usubB_safe bs1 bs2
    else ssubB_safe bs1 bs2.

  Definition subc_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then true
    else ssubB_safe bs1 bs2.

  Definition subb_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then true
    else ssubB_safe bs1 bs2.

  Definition usbbB_safe bs1 bs2 c : bool :=
    ~~ borrow_subB bs1 bs2 && ~~ borrow_subB (subB bs1 bs2) c.

  Definition ssbbB_safe bs1 bs2 c : bool :=
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (subB bs1 bs2) c.

  Definition sbbB_safe typ_a bs1 bs2 bsb : bool :=
    if Typ.is_unsigned typ_a then usbbB_safe bs1 bs2 bsb
    else ssbbB_safe bs1 bs2 bsb.

  Definition sbbs_safe typ_a bs1 bs2 bsb : bool :=
    if Typ.is_unsigned typ_a then true
    else ssbbB_safe bs1 bs2 bsb.

  Definition usbcB_safe bs1 bs2 c : bool :=
    ~~ borrow_subB bs1 bs2 && ~~ borrow_subB (subB bs1 bs2) (subB (ones 1) c).

  Definition ssbcB_safe bs1 bs2 c : bool :=
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (subB bs1 bs2) (subB (ones 1) c).

  Definition sbcB_safe typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then usbcB_safe bs1 bs2 bsc
    else ssbcB_safe bs1 bs2 bsc.

  Definition sbcs_safe typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then true
    else ssbcB_safe bs1 bs2 bsc.

  Definition umulB_safe bs1 bs2 : bool := ~~ Umulo bs1 bs2.

  Definition smulB_safe bs1 bs2 : bool := ~~ Smulo bs1 bs2.

  Definition mulB_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then umulB_safe bs1 bs2
    else smulB_safe bs1 bs2.

  Definition ushlBn_safe bs n : bool := high n bs == zeros n.

  Definition sshlBn_safe bs n : bool :=
  (high (n + 1) bs == zeros n) || (high (n + 1) bs == ones n).

  Definition shlBn_safe typ_a bs n : bool :=
    if Typ.is_unsigned typ_a then ushlBn_safe bs n
    else sshlBn_safe bs n.

  Definition ucshlBn_safe (bs1 bs2 : bits) n : bool :=
    ushlBn_safe (cat bs1 bs2) n.

  Definition scshlBn_safe (bs1 bs2 : bits) n : bool :=
    sshlBn_safe (cat bs1 bs2) n.

  Definition cshlBn_safe typ_a (bs1 bs2 : bits) n : bool :=
    if Typ.is_unsigned typ_a then ucshlBn_safe bs1 bs2 n
    else scshlBn_safe bs1 bs2 n.

  Definition vpc_safe t a_typ bs : bool :=
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

  Definition ssa_instr_safe_at te (i : instr) (s : SSAStore.t) : bool :=
    match i with
    | Iadd _ a1 a2 =>
      addB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s)
    | Iadds _ _ a1 a2 =>
      adds_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s)
    | Iadc _ a1 a2 ac =>
      adcB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s)
    | Iadcs _ _ a1 a2 ac =>
      adcs_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s)
    | Isub _ a1 a2 =>
      subB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s)
    | Isubc _ _ a1 a2 =>
      subc_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s)
    | Isubb _ _ a1 a2 =>
      subb_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s)
    | Isbc _ a1 a2 ac =>
      sbcB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s)
    | Isbb _ a1 a2 ab =>
      sbbB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ab s)
    | Isbcs _ _ a1 a2 ac =>
      sbcs_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s)
    | Isbbs _ _ a1 a2 ab =>
      sbbs_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ab s)
    | Imul _ a1 a2 =>
      mulB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s)
    | Ishl _ a n =>
      shlBn_safe (atyp a te) (eval_atomic a s) n
    | Icshl _ _ a1 a2 n =>
      cshlBn_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) n
    | Ivpc _ t a =>
      vpc_safe t (atyp a te) (eval_atomic a s)
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

  Inductive ssa_program_safe_at : SSATE.env -> program -> SSAStore.t -> Prop :=
  | ssa_program_safe_at_nil te s :
      ssa_program_safe_at te [::] s
  | ssa_program_safe_at_cons te hd tl s :
      ssa_instr_safe_at te hd s ->
      (forall s', eval_instr te hd s s' ->
                  ssa_program_safe_at (instr_succ_typenv hd te) tl s') ->
      ssa_program_safe_at te (hd::tl) s.

  Definition ssa_program_safe te p : Prop :=
    forall s, ssa_program_safe_at te p s.

  Definition ssa_spec_safe sp :=
    forall s, eval_rbexp (rng_bexp (spre sp)) s ->
              ssa_program_safe_at (sinputs sp) (sprog sp) s.


  Lemma ssa_instr_safe_at_eqn E i s :
    ssa_instr_safe_at E i s -> ssa_instr_safe_at E (eqn_instr i) s.
  Proof. case: i => //=. move=> [] e r _ /=. by trivial. Qed.

End Safety.



(** Conversion from SSA programs to algebraic expressions *)

Section SSA2Algebra.

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


  Definition bv2z_atomic (a : atomic) : zexp :=
    match a with
    | Avar v => evar v
    | Aconst ty bs => econst (bv2z ty bs)
    end.

  Definition bv2z_assign (v : ssavar) (e : SSA.eexp) := eeq (evar v) e.
  Definition bv2z_join (e h l : SSA.eexp) (p : nat) :=
    eeq (eadd l (emul2p h (Z.of_nat p))) e.
  Definition bv2z_split (vh vl : ssavar) (e : SSA.eexp) (p : nat) :=
    bv2z_join e (evar vh) (evar vl) p.
  Definition bv2z_is_carry (c : ssavar) :=
    eeq (emul (evar c) (esub (evar c) (econst 1)))
        (econst 0).
  Definition carry_constr (c : ssavar) :=
    if (add_carry_constraints options) then [:: bv2z_is_carry c] else [::].

  Definition bv2z_cast (avn : VarOrder.t) (g : N) v vtyp a atyp :=
    match vtyp, atyp with
    | Tuint wv, Tuint wa =>
      if wv >= wa then
        (g, [:: Eeq (evar v) (bv2z_atomic a)])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: bv2z_split discarded v (bv2z_atomic a) wv])
    | Tuint wv, Tsint wa =>
      (* a_sign and discarded have different meanings but
         the polynomial equation is equivalent. *)
      if wv >= wa then
        let a_sign := (avn, g) in
        let g' := N.succ g in
        (g', [:: bv2z_join (evar v) (evar a_sign) (bv2z_atomic a) wv])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: bv2z_split discarded v (bv2z_atomic a) wv])
    | Tsint wv, Tuint wa =>
      if wv > wa then
        (g, [:: Eeq (evar v) (bv2z_atomic a)])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: bv2z_split discarded v (bv2z_atomic a) wv])
    | Tsint wv, Tsint wa =>
      if wv >= wa then
        (g, [:: Eeq (evar v) (bv2z_atomic a)])
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        (g', [:: bv2z_split discarded v (bv2z_atomic a) wv])
    end.

  Definition bv2z_vpc (avn : VarOrder.t) (g : N) (v : ssavar) a :=
    (g, [:: Eeq (evar v) (bv2z_atomic a)]).

  (* avn: the name of auxiliary variables
     g: the SSA index of the next auxiliary variable *)
  Definition bv2z_instr (te : SSATE.env) (avn : VarOrder.t) (g : N) (i : instr) :
    (N * seq ebexp) :=
    match i with
    | Imov v a =>
      let za := bv2z_atomic a in
      (g, [:: bv2z_assign v za])
    | Ishl v a n =>
      let za := bv2z_atomic a in
      (g, [:: bv2z_assign v (emul2p za (Z.of_nat n))])
    | Icshl vh vl a1 a2 n =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let a2size := asize a2 te in
      (g, [:: bv2z_split vh vl (eadd (emul2p za1 (Z.of_nat a2size)) za2)
              (a2size - n)])
    | Inondet v t =>
      if t == Tbit then (g, carry_constr v)
      else (g, [::])
    | Icmov v c a1 a2 =>
      let zc := bv2z_atomic c in
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      (g, [:: bv2z_assign
              v
              (eadd (emul zc za1)
                    (emul (esub (econst Z.one) zc) za2))])
    | Inop => (g, [::])
    | Inot v t a =>
      let za := bv2z_atomic a in
      match t with
      | Tuint w =>
        (g, [:: bv2z_assign
                v
                (esub (econst (Z.sub (z2expn (Z.of_nat w)) Z.one)) za)])
      | Tsint w =>
        (g, [:: bv2z_assign
                v
                (esub (eneg za) (econst Z.one))])
      end
    | Iadd v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      (g, [:: bv2z_assign v (eadd za1 za2)])
    | Iadds c v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: bv2z_split c v (eadd za1 za2) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: bv2z_assign v (eadd za1 za2)])
      end
    | Iadc v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      (g, [:: bv2z_assign v (eadd (eadd za1 za2) zy)])
    | Iadcs c v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: bv2z_split c v (eadd (eadd za1 za2) zy) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: bv2z_assign v (eadd (eadd za1 za2) zy)])
      end
    | Isub v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      (g, [:: bv2z_assign v (esub za1 za2)])
    | Isubc c v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: bv2z_join
                (evar v) (esub (econst Z.one) (evar c))
                (esub za1 za2) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: bv2z_assign v (esub za1 za2)])
      end
    | Isubb c v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: bv2z_join (evar v) (evar c) (esub za1 za2) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: bv2z_assign v (esub za1 za2)])
      end
    | Isbc v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      (g, [:: bv2z_assign v (esub (esub za1 za2) (esub (econst Z.one) zy))])
    | Isbcs c v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: bv2z_join
                (evar v) (esub (econst Z.one) (evar c))
                (esub (esub za1 za2) (esub (econst Z.one) zy)) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: bv2z_assign v (esub (esub za1 za2) (esub (econst Z.one) zy))])
      end
    | Isbb v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      (g, [:: bv2z_assign v (esub (esub za1 za2) (esub (econst Z.one) zy))])
    | Isbbs c v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      match atyp a1 te with
      | Tuint w =>
        (g, [:: bv2z_join
                (esub (esub za1 za2) zy) (eneg (evar c))
                (evar v) w]
              ++ (carry_constr c))
      | Tsint w =>
        (g, [:: bv2z_assign v (esub (esub za1 za2) zy)])
      end
    | Imul v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      (g, [:: bv2z_assign v (emul za1 za2)])
    | Imull vh vl a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let a2size := asize a2 te in
      (g, [:: bv2z_split vh vl (emul za1 za2) a2size])
    | Imulj v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      (g, [:: bv2z_assign v (emul za1 za2)])
    | Isplit vh vl a n =>
      let za := bv2z_atomic a in
      (g, [:: bv2z_split vh vl za n])
    | Iand v t a1 a2 => (g, [::]) (* cannot be translated to polynomials *)
    | Ior v t a1 a2 => (g, [::]) (* cannot be translated to polynomials *)
    | Ixor v t a1 a2 => (g, [::]) (* cannot be translated to polynomials *)
    | Icast v t a => bv2z_cast avn g v t a (atyp a te)
    | Ivpc v t a => bv2z_vpc avn g v a
    | Ijoin v ah al =>
      let zah := bv2z_atomic ah in
      let zal := bv2z_atomic al in
      let alsize := asize al te in
      (g, [:: bv2z_join (evar v) zah zal alsize])
    | Iassume e => (g, split_eand (eqn_bexp e))
    end.

  Fixpoint bv2z_program (te : SSATE.env) (avn : VarOrder.t) (g : N) (p : program) :
    N * seq ebexp :=
    match p with
    | [::] => (g, [::])
    | hd::tl =>
      let (g_hd, zhd) := bv2z_instr te avn g hd in
      let (g_tl, ztl) := bv2z_program (instr_succ_typenv hd te) avn g_hd tl in
      (g_tl, zhd ++ ztl)
    end.

  Definition new_svar_espec (s : espec) : VarOrder.t :=
    new_svar (SSAVS.union (vars_env (esinputs s))
                          (SSAVS.union
                             (vars_ebexp (espre s))
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

  Definition bv2z_espec avn (s : espec) : zspec :=
    let (g, eprogs) := bv2z_program (esinputs s)
                                    avn initial_index (esprog s) in
    {| zsinputs := SSAVS.union
                     (aux_vars_lt avn g)
                     (vars_env (program_succ_typenv (esprog s) (esinputs s)));
       zspre := eand (espre s) (eands eprogs);
       zsprog := [::];
       zspost := espost s |}.


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

  Lemma vars_bv2z_atomic a : vars_zexp (bv2z_atomic a) = vars_atomic a.
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


  Lemma bv2z_program_cons te avn g1 g2 i p zip :
    (g2, zip) = bv2z_program te avn g1 (i::p) ->
    exists g3, exists zi, exists zp,
          (g3, zi) = bv2z_instr te avn g1 i /\
          (g2, zp) = bv2z_program (instr_succ_typenv i te) avn g3 p /\
          zip = zi ++ zp.
  Proof.
    rewrite /=. dcase (bv2z_instr te avn g1 i) => [[g_hd zhd] Hhd].
    dcase (bv2z_program (instr_succ_typenv i te) avn g_hd p) => [[g_tl ztl] Htl].
    case=> ? ?; subst. exists g_hd; exists zhd; exists ztl. done.
  Qed.

  Lemma bv2z_eqn_instr te avn g i :
    bv2z_instr te avn g (eqn_instr i) = bv2z_instr te avn g i.
  Proof. case: i => //=. by case=> [e r]. Qed.

  Lemma bv2z_eqn_program te avn g p :
    bv2z_program te avn g (eqn_program p) = bv2z_program te avn g p.
  Proof.
    elim: p te avn g => [| i p IH] te avn g //=.
    dcase (bv2z_instr te avn g (eqn_instr i)) => [[g_hd zhd] Hhd].
    dcase (bv2z_program (instr_succ_typenv (eqn_instr i) te) avn g_hd (eqn_program p))
          => [[g_tl ztl] Htl]. dcase (bv2z_instr te avn g i) => [[g_hd0 zhd0] Hhd0].
    dcase (bv2z_program (instr_succ_typenv i te) avn g_hd0 p) => [[g_tl0 ztl0] Htl0].
    rewrite bv2z_eqn_instr Hhd0 in Hhd. case: Hhd => ? ?; subst.
    rewrite IH SSA.eqn_instr_succ_typenv Htl0 in Htl. case: Htl => ? ?; subst.
    reflexivity.
  Qed.

  Lemma bv2z_cast_idx_inc avn g1 g2 v t a ta zi :
    bv2z_cast avn g1 v t a ta = (g2, zi) ->
    (g1 <= g2)%num.
  Proof.
    rewrite /bv2z_cast. case: t; case: ta.
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

  Lemma bv2z_instr_idx_inc te avn g1 g2 i zi :
    bv2z_instr te avn g1 i = (g2, zi) -> (g1 <= g2)%num.
  Proof.
    ((case: i => /=); intros;
     (let rec tac :=
          match goal with
          | H : (_, _) = (_, _) |- _ => case: H => -> _; tac
          | H : (if ?b then _ else _) = (_, _) |- _ =>
            move: H; case: b; intro; tac
          | H : (match ?t with | Tuint _ => _ | Tsint _ => _ end) = _ |- _ =>
            move: H; case: t; intros; tac
          | H : bv2z_cast _ _ _ _ _ _ = _ |- _ =>
            exact: (bv2z_cast_idx_inc H)
          | H : bv2z_vpc _ _ _ _ = _ |- _ => rewrite /bv2z_vpc in H; tac
          | |- (?x <= ?x)%num => exact: N.le_refl
          | |- _ => idtac
          end in
      tac)).
  Qed.

  Lemma bv2z_program_idx_inc te avn g1 g2 p zp :
    bv2z_program te avn g1 p = (g2, zp) -> (g1 <= g2)%num.
  Proof.
    elim: p te g1 g2 zp => [te g1 g2 zp | hd tl IH te g1 g2 zp] /=.
    - case=> -> _. exact: N.le_refl.
    - dcase (bv2z_instr te avn g1 hd) => [[g_hd zhd] Hhd].
      dcase (bv2z_program (instr_succ_typenv hd te) avn g_hd tl) => [[g_tl ztl] Htl].
      case=> <- _. move: (bv2z_instr_idx_inc Hhd) => Hg1hd.
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
    | H : svar_notin ?avn (vars_atomic ?a) |-
      avars_newer_than ?avn ?g (vars_zexp (bv2z_atomic ?a)) =>
      rewrite vars_bv2z_atomic; exact: (svar_notin_newer_than g H)
    | |- avars_newer_than _ _ SSAVS.empty =>
      exact: avars_newer_than_empty
    | |- avars_newer_than_var _ (N.succ ?g) (_, ?g) =>
      right; exact: N.lt_succ_diag_r
    end.

  Lemma bv2z_instr_newer_than E avn g1 g2 i zs :
    bv2z_instr E avn g1 i = (g2, zs) ->
    svar_notin avn (vars_instr i) ->
    avars_newer_than avn g2 (vars_zbexp (eands zs)).
  Proof.
    move=> H.
    case: i H => /=;

    try (intros; repeat case_pairs; rewrite /=;
    repeat case_svar_notin;
    repeat split_avars_newer_than;
    solve_avars_newer_than).

    (* bv2z_cast *)
    intros; repeat case_pairs; rewrite /=;
    repeat case_svar_notin;
    repeat split_avars_newer_than.
    move: H; rewrite /bv2z_cast => H.
    repeat case_pairs; rewrite /=; repeat split_avars_newer_than;
    solve_avars_newer_than.

    (* bv2z_vpc *)
    intros; repeat case_pairs; rewrite /=;
    repeat case_svar_notin;
    repeat split_avars_newer_than.
    move: H; rewrite /bv2z_vpc => H.
    repeat case_pairs; rewrite /=; repeat split_avars_newer_than;
    solve_avars_newer_than.

    intros; repeat case_pairs; rewrite /=.
    exact: (avars_newer_than_split_eqn g2 H0).
  Qed.

  Lemma bv2z_program_newer_than E avn g1 g2 p zs :
    bv2z_program E avn g1 p = (g2, zs) ->
    svar_notin avn (vars_program p) ->
    avars_newer_than avn g2 (vars_zbexp (eands zs)).
  Proof.
    elim: p E g1 g2 zs => [| i p IH] E g1 g2 zs /=.
    - move=> *; case_pairs. exact: avars_newer_than_empty.
    - dcase (bv2z_instr E avn g1 i) => [[g_hd zhd] Hhd].
      dcase (bv2z_program (instr_succ_typenv i E) avn g_hd p) => [[g_tl ztl] Htl].
      case=> ? ?; subst. move/svar_notin_union=> [Hi Hp].
      apply: (avars_newer_than_equal
                (SSAVS.Lemmas.P.equal_sym (vars_eands_cat zhd ztl))).
      apply/avars_newer_than_union; split.
      + apply: (avars_newer_than_le (bv2z_program_idx_inc Htl)).
        exact: (bv2z_instr_newer_than Hhd Hi).
      + exact: (IH _ _ _ _ Htl Hp).
  Qed.

End SSA2Algebra.



(** Split a specification into safety conditions, range specification,
    and algebraic specification *)
Section SplitSpec.

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
      Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E))
      |- context f [atyp ?a (SSATE.add ?v ?t _)] =>
      rewrite (atyp_add_not_mem _ _ (SSAVS.Lemmas.not_mem_subset Hmem Hsub))
    | Hmem : is_true (~~ SSAVS.mem ?v (vars_env ?E)),
      Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)),
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

  Lemma bvz_eq_eval_atomic a E bs zs :
    bvz_eq E bs zs ->
    ZSSA.eval_zexp (bv2z_atomic a) zs = bv2z (atyp a E) (eval_atomic a bs).
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

  Lemma bvz_eqi_eval_atomic a E bs zs :
    bvz_eqi E bs zs -> are_defined (vars_atomic a) E ->
    ZSSA.eval_zexp (bv2z_atomic a) zs = bv2z (atyp a E) (eval_atomic a bs).
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
  Qed.

  Lemma bvz_eqi_eval_ebexp E e bs zs :
    bvz_eqi E bs zs -> are_defined (vars_ebexp e) E ->
    eval_ebexp e E bs <-> ZSSA.eval_zbexp (eands (split_eand e)) zs.
  Proof.
    move=> Heq. elim: e => //=.
    - move=> e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (bvz_eqi_eval_eexp Heq Hdef1) (bvz_eqi_eval_eexp Heq Hdef2). tauto.
    - move=> e1 e2 e3.
      rewrite !are_defined_union => /andP [Hdef1 /andP [Hdef2 Hdef3]].
      rewrite (bvz_eqi_eval_eexp Heq Hdef1) (bvz_eqi_eval_eexp Heq Hdef2)
              (bvz_eqi_eval_eexp Heq Hdef3). tauto.
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

  Definition bv2z_store (E : SSATE.env) (bs : SSAStore.t) : ZSSAStore.t :=
    fun v => acc2z E v bs.

  Lemma acc_bv2z_store E v bs : ZSSAStore.acc v (bv2z_store E bs) = acc2z E v bs.
  Proof. reflexivity. Qed.

  Lemma bv2z_store_eq E bs : bvz_eq E bs (bv2z_store E bs).
  Proof. move=> x; reflexivity. Qed.

  Lemma bv2z_store_eqi E bs : bvz_eqi E bs (bv2z_store E bs).
  Proof. move=> x _. reflexivity. Qed.

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

  Definition bv2z_upd_avars_cast
             (avn : VarOrder.t) (g : N) (v : SSAVarOrder.t) vtyp a atyp
             (zs : ZSSAStore.t) : N * ZSSAStore.t :=
    match vtyp, atyp with
    | Tuint wv, Tuint wa =>
      if wv >= wa then
        (g, zs)
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd discarded q zs in
        (g', zs')
    | Tuint wv, Tsint wa =>
      (* a_sign and discarded have different meanings but
         the polynomial equation is equivalent. *)
      (*if wv >= wa then
        let a_sign := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd a_sign q zs in
        (g', zs')
      else*)
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd discarded q zs in
        (g', zs')
    | Tsint wv, Tuint wa =>
      if wv > wa then
        (g, zs)
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd discarded q zs in
        (g', zs')
    | Tsint wv, Tsint wa =>
      if wv >= wa then
        (g, zs)
      else
        let discarded := (avn, g) in
        let g' := N.succ g in
        let (q, r) := Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs)
                                 (z2expn (Z.of_nat wv)) in
        let zs' := ZSSAStore.upd discarded q zs in
        (g', zs')
    end.

  Definition bv2z_upd_avars_instr
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
    | Icast v t a => bv2z_upd_avars_cast avn g v t a (atyp a E) zs
    | Ivpc v t a => (g, zs)
    | Ijoin v ah al => (g, zs)
    | Iassume e => (g, zs)
    end.

  Fixpoint bv2z_upd_avars_program
             (E : SSATE.env) (avn : VarOrder.t) (g : N) (p : program)
             (zs : ZSSAStore.t) : N * ZSSAStore.t :=
    match p with
    | [::] => (g, zs)
    | hd::tl =>
      let (g_hd, zs_hd) := bv2z_upd_avars_instr E avn g hd zs in
      let (g_tl, zs_tl) := bv2z_upd_avars_program
                             (instr_succ_typenv hd E) avn g_hd tl zs_hd in
      (g_tl, zs_tl)
    end.

  Definition bv2z_upd_avars
             (E : SSATE.env) (avn : VarOrder.t) (g : N) (p : program)
             (zs : ZSSAStore.t) : ZSSAStore.t :=
    snd (bv2z_upd_avars_program E avn g p zs).


  Lemma bv2z_upd_avars_instr_eqn E avn g i zs :
    bv2z_upd_avars_instr E avn g (eqn_instr i) zs =
    bv2z_upd_avars_instr E avn g i zs.
  Proof. case: i => //=. move=> [] e r /=. reflexivity. Qed.

  Lemma bv2z_upd_avars_program_eqn E avn g p zs :
    bv2z_upd_avars_program E avn g (eqn_program p) zs =
    bv2z_upd_avars_program E avn g p zs.
  Proof.
    elim: p E g zs => [| i p IH E g zs] //=.
    dcase (bv2z_upd_avars_instr E avn g (eqn_instr i) zs) => [[g_hde zs_hde] Hhde].
    dcase (bv2z_upd_avars_program
             (instr_succ_typenv (eqn_instr i) E) avn g_hde (eqn_program p) zs_hde) =>
    [[g_tle zs_tle] Htle].
    rewrite bv2z_upd_avars_instr_eqn in Hhde. rewrite IH eqn_instr_succ_typenv in Htle.
    rewrite Hhde Htle. reflexivity.
  Qed.

  Corollary bv2z_upd_avars_eqn E avn g p zs :
    bv2z_upd_avars E avn g (eqn_program p) zs = bv2z_upd_avars E avn g p zs.
  Proof.
    rewrite /bv2z_upd_avars bv2z_upd_avars_program_eqn. reflexivity.
  Qed.


  Lemma bv2z_upd_avars_cast_gen avn g1 v tv a ta g2 g3 zs zs1 zs2 :
    bv2z_cast avn g1 v tv a ta = (g2, zs) ->
    bv2z_upd_avars_cast avn g1 v tv a ta zs1 = (g3, zs2) ->
    g2 = g3.
  Proof.
    rewrite /bv2z_cast /bv2z_upd_avars_cast. case: tv => n.
    - dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat n)))
      => [[q r] H]. case: ta => m; case: (m <= n).
      + intros; repeat case_pairs. reflexivity.
      + intros; repeat case_pairs. reflexivity.
      + intros; repeat case_pairs. reflexivity.
      + intros; repeat case_pairs. reflexivity.
    - dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat n)))
      => [[q r] H]. case: ta => m.
      + case: (m < n).
        * intros; repeat case_pairs. reflexivity.
        * intros; repeat case_pairs. reflexivity.
      + case: (m <= n).
        * intros; repeat case_pairs. reflexivity.
        * intros; repeat case_pairs. reflexivity.
  Qed.

  Lemma bv2z_upd_avars_instr_gen o E avn i g1 g2 g3 zs zs1 zs2 :
    bv2z_instr o E avn g1 i = (g2, zs) ->
    bv2z_upd_avars_instr E avn g1 i zs1 = (g3, zs2) ->
    g2 = g3.
  Proof.
    case: i => /=; intros; repeat case_pairs; try reflexivity.
    (* bv2z_cast *)
    - exact: (bv2z_upd_avars_cast_gen H H0).
    (* bv2z_vpc *)
    - rewrite /bv2z_vpc in H. repeat case_pairs. reflexivity.
  Qed.

  Lemma bv2z_upd_avars_program_gen o E avn p g1 g2 g3 zs zs1 zs2 :
    bv2z_program o E avn g1 p = (g2, zs) ->
    bv2z_upd_avars_program E avn g1 p zs1 = (g3, zs2) ->
    g2 = g3.
  Proof.
    elim: p E g1 g2 g3 zs zs1 zs2 => [| i p IH] E g1 g2 g3 zs zs1 zs3 /=.
    - intros; repeat case_pairs. reflexivity.
    - dcase (bv2z_instr o E avn g1 i) => [[g_hd zhd] Hhd].
      dcase (bv2z_program o (instr_succ_typenv i E) avn g_hd p) => [[g_tl ztl] Htl].
      case=> ? ?; subst. dcase (bv2z_upd_avars_instr E avn g1 i zs1) =>
                         [[bv2z_g_hd bv2z_zs_hd] Hbv2z_hd].
      dcase (bv2z_upd_avars_program
               (instr_succ_typenv i E) avn bv2z_g_hd p bv2z_zs_hd) =>
      [[bv2z_g_tl  bv2z_zs_tl] Hbv2z_tl]. case=> ? ?; subst.
      rewrite (bv2z_upd_avars_instr_gen Hhd Hbv2z_hd) in Htl.
      rewrite (IH _ _ _ _ _ _ _ Htl Hbv2z_tl). reflexivity.
  Qed.

  Lemma bv2z_upd_avars_cast_idx_inc avn g1 v tv a ta g2 zs1 zs2 :
    bv2z_upd_avars_cast avn g1 v tv a ta zs1 = (g2, zs2) ->
    (g1 <= g2)%num.
  Proof.
    move=> Hupd. move: (Logic.eq_refl (bv2z_cast avn g1 v tv a ta)).
    move: {2}(bv2z_cast avn g1 v tv a ta) => [g3 zi] Hbvz.
    move: (bv2z_cast_idx_inc Hbvz) => Hg13.
    rewrite (bv2z_upd_avars_cast_gen Hbvz Hupd) in Hg13. assumption.
  Qed.

  Lemma bv2z_upd_avars_instr_idx_inc E avn i g1 g2 zs1 zs2 :
    bv2z_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    (g1 <= g2)%num.
  Proof.
    move=> Hupd. move: (Logic.eq_refl (bv2z_instr default_options E avn g1 i)).
    move: {2}(bv2z_instr default_options E avn g1 i) => [g3 zi] Hbvz.
    move: (bv2z_instr_idx_inc Hbvz) => Hg13.
    rewrite (bv2z_upd_avars_instr_gen Hbvz Hupd) in Hg13. assumption.
  Qed.

  Lemma bv2z_upd_avars_program_idx_inc E avn p g1 g2 zs1 zs2 :
    bv2z_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    (g1 <= g2)%num.
  Proof.
    move=> Hupd. move: (Logic.eq_refl (bv2z_program default_options E avn g1 p)).
    move: {2}(bv2z_program default_options E avn g1 p) => [g3 zp] Hbvz.
    move: (bv2z_program_idx_inc Hbvz) => Hg13.
    rewrite (bv2z_upd_avars_program_gen Hbvz Hupd) in Hg13. assumption.
  Qed.


  Lemma bv2z_upd_avars_instr_acc_ne E avn g1 i zs1 g2 zs2 v :
    svar v != avn -> bv2z_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
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
      exact: eqxx. } move=> {Hne} Hne. move: Hupd. rewrite /bv2z_upd_avars_cast.
    case: xt; case: (atyp a E) => /=.
    - move=> wx wa. case: (wx <= wa); [by mytac |].
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
    - move=> wx wa.
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
    - move=> wx wa. case: (wx < wa); [by mytac |].
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
    - move=> wx wa. case: (wx <= wa); [by mytac |].
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
  Qed.

  Lemma bv2z_upd_avars_program_acc_ne E avn g1 p zs1 g2 zs2 v :
    svar v != avn -> bv2z_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    move=> Hne. elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 /=.
    - case=> _ ->. reflexivity.
    - dcase (bv2z_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (bv2z_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. case=> _ <-. rewrite (IH _ _ _ _ _ Htl).
      rewrite (bv2z_upd_avars_instr_acc_ne Hne Hhd). reflexivity.
  Qed.

  Corollary bv2z_upd_avars_acc_ne {E avn g p zs v} :
    svar v != avn ->
    ZSSAStore.acc v (bv2z_upd_avars E avn g p zs) = ZSSAStore.acc v zs.
  Proof.
    move=> Hne. rewrite /bv2z_upd_avars. dcase (bv2z_upd_avars_program E avn g p zs).
    case=> [g' zs'] H. exact: (bv2z_upd_avars_program_acc_ne Hne H).
  Qed.

  Lemma bv2z_upd_avars_instr_acc_lt E avn g1 i zs1 g2 zs2 v :
    (sidx v < g1)%num -> bv2z_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
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
    move=> {Hlt} Hne. move: Hupd. rewrite /bv2z_upd_avars_cast.
    case: xt; case: (atyp a E) => /=.
    - move=> wx wa. case: (wx <= wa); [by mytac |].
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
    - move=> wx wa.
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
    - move=> wx wa. case: (wx < wa); [by mytac |].
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
    - move=> wx wa. case: (wx <= wa); [by mytac |].
      dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1) (z2expn (Z.of_nat wa))).
      case; by mytac.
  Qed.

  Lemma bv2z_upd_avars_program_acc_lt E avn g1 p zs1 g2 zs2 v :
    (sidx v < g1)%num -> bv2z_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 Hlt /=.
    - case=> _ ->. reflexivity.
    - dcase (bv2z_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (bv2z_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. case=> Hg2 <-.
      move: (bv2z_upd_avars_instr_idx_inc Hhd) => Hg1.
      move: (N.lt_le_trans _ _ _ Hlt Hg1) => Hg_hd.
      rewrite (IH _ _ _ _ _ Hg_hd Htl). exact: (bv2z_upd_avars_instr_acc_lt Hlt Hhd).
  Qed.

  Corollary bv2z_upd_avars_acc_lt {E avn g p zs v} :
    (sidx v < g)%num ->
    ZSSAStore.acc v (bv2z_upd_avars E avn g p zs) = ZSSAStore.acc v zs.
  Proof.
    move=> Hlt. rewrite /bv2z_upd_avars. dcase (bv2z_upd_avars_program E avn g p zs).
    case=> [g' zs'] H. exact: (bv2z_upd_avars_program_acc_lt Hlt H).
  Qed.

  Corollary bv2z_upd_avars_instr_acc_newer E avn g1 i zs1 g2 zs2 v :
    avars_newer_than_var avn g1 v ->
    bv2z_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    case; [exact: bv2z_upd_avars_instr_acc_ne | exact: bv2z_upd_avars_instr_acc_lt].
  Qed.

  Corollary bv2z_upd_avars_program_acc_newer E avn g1 p zs1 g2 zs2 v :
    avars_newer_than_var avn g1 v ->
    bv2z_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSAStore.acc v zs2 = ZSSAStore.acc v zs1.
  Proof.
    case; [exact: bv2z_upd_avars_program_acc_ne | exact: bv2z_upd_avars_program_acc_lt].
  Qed.

  Corollary bv2z_upd_avars_acc_newer {E avn g p zs v} :
    avars_newer_than_var avn g v ->
    ZSSAStore.acc v (bv2z_upd_avars E avn g p zs) = ZSSAStore.acc v zs.
  Proof.
    case; [exact: bv2z_upd_avars_acc_ne | exact: bv2z_upd_avars_acc_lt].
  Qed.


  Lemma bv2z_upd_avars_instr_eval_zexp E avn i g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zexp e) ->
    bv2z_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs1 = ZSSA.eval_zexp e zs2.
  Proof.
    move=> Hnew Hupd. elim: e Hnew => //=.
    - move=> v Hnew. move/avars_newer_than_singleton: Hnew => Hnew.
      rewrite (bv2z_upd_avars_instr_acc_newer Hnew Hupd). reflexivity.
    - move=> op e IH Hnew. rewrite (IH Hnew). reflexivity.
    - move=> op e1 IH1 e2 IH2 /avars_newer_than_union [] Hnew1 Hnew2.
      rewrite (IH1 Hnew1) (IH2 Hnew2). reflexivity.
  Qed.

  Lemma bv2z_upd_avars_program_eval_zexp E avn p g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zexp e) ->
    bv2z_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs1 = ZSSA.eval_zexp e zs2.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 /=.
    - move=> Hnew [] ? ?; subst. reflexivity.
    - move=> Hnew. dcase (bv2z_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (bv2z_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. move=> [] ? ?; subst.
      rewrite -(IH _ _ _ _ _
                   (avars_newer_than_le (bv2z_upd_avars_instr_idx_inc Hhd) Hnew) Htl).
      exact: (bv2z_upd_avars_instr_eval_zexp Hnew Hhd).
  Qed.

  Lemma bv2z_upd_avars_eval_zexp E avn p g zs1 zs2 e :
    avars_newer_than avn g (ZSSA.vars_zexp e) ->
    bv2z_upd_avars E avn g p zs1 = zs2 ->
    ZSSA.eval_zexp e zs1 = ZSSA.eval_zexp e zs2.
  Proof.
    rewrite /bv2z_upd_avars. dcase (bv2z_upd_avars_program E avn g p zs1) =>
                             [[g2 zs2'] Hupd] /=. move=> Hnew ?; subst.
    exact: (bv2z_upd_avars_program_eval_zexp Hnew Hupd).
  Qed.

  Lemma bv2z_upd_avars_instr_eval_zbexp E avn i g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zbexp e) ->
    bv2z_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zbexp e zs1 <-> ZSSA.eval_zbexp e zs2.
  Proof.
    move=> Hnew Hupd. elim: e Hnew => //=.
    - move=> e1 e2 /avars_newer_than_union [Hnew1 Hnew2].
      rewrite (bv2z_upd_avars_instr_eval_zexp Hnew1 Hupd)
              (bv2z_upd_avars_instr_eval_zexp Hnew2 Hupd). done.
    - move=> e1 e2 e3
                /avars_newer_than_union [Hnew1 /avars_newer_than_union [Hnew2 Hnew3]].
      rewrite (bv2z_upd_avars_instr_eval_zexp Hnew1 Hupd)
              (bv2z_upd_avars_instr_eval_zexp Hnew2 Hupd)
              (bv2z_upd_avars_instr_eval_zexp Hnew3 Hupd). done.
    - move=> e1 IH1 e2 IH2 /avars_newer_than_union [Hnew1 Hnew2].
      move: (IH1 Hnew1) (IH2 Hnew2) => {IH1 IH2} H1 H2. tauto.
  Qed.

  Lemma bv2z_upd_avars_program_eval_zbexp E avn p g1 g2 zs1 zs2 e :
    avars_newer_than avn g1 (ZSSA.vars_zbexp e) ->
    bv2z_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSA.eval_zbexp e zs1 <-> ZSSA.eval_zbexp e zs2.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 /=.
    - move=> Hnew [] ? ?; subst. done.
    - move=> Hnew. dcase (bv2z_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (bv2z_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. move=> [] ? ?; subst.
      move: (bv2z_upd_avars_instr_idx_inc Hhd) => Hg1.
      move: (avars_newer_than_le Hg1 Hnew) => Hnew_hd.
      move: (IH _ _ _ _ _ Hnew_hd Htl) => Heval_tl.
      move: (bv2z_upd_avars_instr_eval_zbexp Hnew Hhd) => Heval_hd. tauto.
  Qed.

  Lemma bv2z_upd_avars_eval_zbexp E avn p g zs1 zs2 e :
    avars_newer_than avn g (ZSSA.vars_zbexp e) ->
    bv2z_upd_avars E avn g p zs1 = zs2 ->
    ZSSA.eval_zbexp e zs1 <-> ZSSA.eval_zbexp e zs2.
  Proof.
    rewrite /bv2z_upd_avars. dcase (bv2z_upd_avars_program E avn g p zs1) =>
                             [[g2 zs2'] Hupd] /=. move=> Hnew ?; subst.
    exact: (bv2z_upd_avars_program_eval_zbexp Hnew Hupd).
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
  Qed.

  Lemma svar_notin_eval_zbexp zs n g avn e :
    svar_notin avn (ZSSA.vars_zbexp e) ->
    ZSSA.eval_zbexp e (ZSSAStore.upd (avn, g) n zs) <-> ZSSA.eval_zbexp e zs.
  Proof.
    elim: e => //=.
    - move=> e1 e2 /svar_notin_union [Hni1 Hni2].
      rewrite (svar_notin_eval_zexp Hni1) (svar_notin_eval_zexp Hni2). done.
    - move=> e1 e2 e3 /svar_notin_union [Hni1 /svar_notin_union [Hni2 Hni3]].
      rewrite (svar_notin_eval_zexp Hni1) (svar_notin_eval_zexp Hni2)
              (svar_notin_eval_zexp Hni3). done.
    - move=> e1 IH1 e2 IH2 /svar_notin_union [Hni1 Hni2].
      move: (IH1 Hni1) (IH2 Hni2) => H1 H2. tauto.
  Qed.

  Lemma svar_notin_bv2z_upd_avars_instr_eval_zexp E avn g1 i zs1 g2 zs2 e :
    svar_notin avn (ZSSA.vars_zexp e) ->
    bv2z_upd_avars_instr E avn g1 i zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs2 = ZSSA.eval_zexp e zs1.
  Proof.
    case: i => //=; try (intros; case_pairs; reflexivity).
    move=> v tv a Hni. rewrite /bv2z_upd_avars_cast. case: tv.
    - move=> wv. dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1)
                                   (z2expn (Z.of_nat wv))) => [[q r] Hdiv].
      case: (atyp a E).
      + move=> wa. case: (wa <= wv).
        * case=> ? ?; subst. reflexivity.
        * case=> ? ?; subst. rewrite (svar_notin_eval_zexp Hni). reflexivity.
      + move=> _. case=> ? ?; subst. rewrite (svar_notin_eval_zexp Hni). reflexivity.
    - move=> wv. dcase (Z.div_eucl (ZSSA.eval_zexp (bv2z_atomic a) zs1)
                                   (z2expn (Z.of_nat wv))) => [[q r] Hdiv].
      case: (atyp a E).
      + move=> wa. case: (wa < wv).
        * case=> ? ?; subst. reflexivity.
        * case=> ? ?; subst. rewrite (svar_notin_eval_zexp Hni). reflexivity.
      + move=> wa. case: (wa <= wv).
        * case=> ? ?; subst. reflexivity.
        * case=> ? ?; subst. rewrite (svar_notin_eval_zexp Hni). reflexivity.
  Qed.

  Lemma svar_notin_bv2z_upd_avars_program_eval_zexp E avn g1 p zs1 g2 zs2 e :
    svar_notin avn (ZSSA.vars_zexp e) ->
    bv2z_upd_avars_program E avn g1 p zs1 = (g2, zs2) ->
    ZSSA.eval_zexp e zs2 = ZSSA.eval_zexp e zs1.
  Proof.
    elim: p E g1 zs1 g2 zs2 => [| i p IH] E g1 zs1 g2 zs2 Hni /=.
    - case=> ? ?; subst. reflexivity.
    - dcase (bv2z_upd_avars_instr E avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (bv2z_upd_avars_program (instr_succ_typenv i E) avn g_hd p zs_hd) =>
      [[g_tl zs_tl] Htl]. case=> ? ?; subst. rewrite (IH _ _ _ _ _ Hni Htl).
      rewrite (svar_notin_bv2z_upd_avars_instr_eval_zexp Hni Hhd). reflexivity.
  Qed.


  Lemma bvz_zs_eqi zs1 zs2 E bs :
    bvz_eqi E bs zs1 -> ZSSA.zs_eqi (vars_env E) zs1 zs2 ->
    bvz_eqi E bs zs2.
  Proof.
    move=> Hbeq Hzeq x Hx. rewrite (Hbeq x Hx). move/memenvP: Hx => Hx.
    exact: (Hzeq x Hx).
  Qed.

  Lemma bv2z_upd_avars_instr_eqi E1 E2 avn g1 i zs1 g2 zs2 :
    bv2z_upd_avars_instr E1 avn g1 i zs1 = (g2, zs2) ->
    svar_notin avn (vars_env E2) ->
    ZSSA.zs_eqi (vars_env E2) zs1 zs2.
  Proof.
    case: i => /=; try (move=> *; case_pairs; exact: ZSSA.zs_eqi_refl).
    (* Icast *)
    move=> x tx a Hupd Hni.
    rewrite /bv2z_upd_avars_cast in Hupd;
      repeat case_pairs; try exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
    - apply: (ZSSA.zs_eqi_upd _ (Hni g1)). exact: ZSSA.zs_eqi_refl.
  Qed.

  Lemma bv2z_upd_avars_program_eqi E1 E2 avn g1 p zs1 g2 zs2 :
    svar_notin avn (vars_env E2) ->
    bv2z_upd_avars_program E1 avn g1 p zs1 = (g2, zs2) ->
    ZSSA.zs_eqi (vars_env E2) zs1 zs2.
  Proof.
    move=> Hni. elim: p E1 g1 g2 zs1 zs2 => [| i p IH] E1 g1 g2 zs1 zs2 /=.
    - move=> [] ? ?; subst; exact: ZSSA.zs_eqi_refl.
    - dcase (bv2z_upd_avars_instr E1 avn g1 i zs1) => [[g_hd zs_hd] Hhd].
      dcase (bv2z_upd_avars_program (instr_succ_typenv i E1) avn g_hd p zs_hd)
      => [[g_tl zs_tl] Htl]. case=> ? ?; subst.
      apply: (ZSSA.zs_eqi_trans (bv2z_upd_avars_instr_eqi Hhd Hni)).
      exact: (IH _ _ _ _ _  Htl).
  Qed.


  (* main theorem *)

  Lemma bv2z_carry_constraint n :
    size n = 1 -> (to_Zpos n * (to_Zpos n - 1))%Z = 0%Z.
  Proof. case: n => //. move=> a [] //=. move=> _. by case: a. Qed.

  Lemma bv2z_Ishl t bs n :
    size bs = sizeof_typ t -> shlBn_safe t bs n ->
    bv2z t (bs <<# n)%bits = (bv2z t bs * Cryptoline.DSL.z2expn (Z.of_nat n))%Z.
  Proof.
  Admitted.

  Lemma bv2z_Icshl th tl bsh bsl n :
    is_unsigned tl -> compatible th tl ->
    size bsh = sizeof_typ th -> size bsl = sizeof_typ tl ->
    cshlBn_safe th bsh bsl n ->
    (bv2z tl (low (size bsl) ((bsl ++ bsh) <<# n) >># n)%bits +
     bv2z th (high (size bsh) ((bsl ++ bsh) <<# n)%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat (size bsl - n)))%Z =
    (bv2z th bsh * Cryptoline.DSL.z2expn (Z.of_nat (size bsl)) + bv2z tl bsl)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Icmov_true t c a1 a2 :
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

  Lemma bv2z_Icmov_false t c a1 a2 :
    size c = 1 ->
    ~~ to_bool c ->
    bv2z t a2 = (bv2z Tbit c * bv2z t a1 + (1 - bv2z Tbit c) * bv2z t a2)%Z.
  Proof.
    move=> Hs Hc. rewrite /bv2z /=.
    move: (Seqs.singleton_seq Hs) => {Hs} [b Hcb]. subst.
    rewrite /to_bool /= in Hc. move/negPn: Hc => /andP [/eqP -> _] /=.
    by case: t; [case: (to_Zpos a2) | case: (to_Z a2)].
  Qed.

  Lemma bv2z_Inot_unsigned t bs n :
    compatible (Tuint n) t -> size bs = sizeof_typ t ->
    bv2z (Tuint n) (~~# bs)%bits = (z2expn (Z.of_nat n) - Z.one - bv2z t bs)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Inot_signed t bs n :
    compatible (Tsint n) t -> size bs = sizeof_typ t ->
    bv2z (Tsint n) (~~# bs)%bits = (- bv2z t bs - Z.one)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Iadd t bs1 bs2 :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t ->
    addB_safe t bs1 bs2 ->
    bv2z t (bs1 +# bs2)%bits = (bv2z t bs1 + bv2z t bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Iadds_unsigned bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    (bv2z (Tuint n) (bs1 +# bs2)%bits +
     bv2z Tbit (1) -bits of bool (carry_addB bs1 bs2)%bits *
                    Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    (bv2z (Tuint n) bs1 + bv2z (Tuint n) bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Iadds_signed bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    adds_safe (Tsint n) bs1 bs2 ->
    bv2z (Tsint n) (bs1 +# bs2)%bits = (bv2z (Tsint n) bs1 + bv2z (Tsint n) bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Iadc t bs1 bs2 bsc :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t -> size bsc = 1 ->
    adcB_safe t bs1 bs2 bsc ->
    bv2z t (adcB (to_bool bsc) bs1 bs2).2 =
    (bv2z t bs1 + bv2z t bs2 + bv2z Tbit bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Iadcs_unsigned bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    (bv2z (Tuint n) (adcB (to_bool bsc) bs1 bs2).2 +
     bv2z Tbit (1)-bits of bool
                        ((adcB (to_bool bsc) bs1 bs2).1)%bits *
                   Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
  (bv2z (Tuint n) bs1 + bv2z (Tuint n) bs2 + bv2z Tbit bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Iadcs_signed bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    adcs_safe (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (adcB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tsint n) bs1 + bv2z (Tsint n) bs2 + bv2z Tbit bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isub t bs1 bs2 :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t ->
    subB_safe t bs1 bs2 ->
    bv2z t (bs1 -# bs2)%bits = (bv2z t bs1 - bv2z t bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isubc_unsigned bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 +
     (1 -  bv2z Tbit (1)-bits of bool (carry_addB bs1 (-# bs2))%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    bv2z (Tuint n) (bs1 +# -# bs2)%bits.
  Proof.
  Admitted.

  Lemma bv2z_Isubc_signed bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    subc_safe (Tsint n) bs1 bs2 ->
    bv2z (Tsint n) (bs1 +# -# bs2)%bits = (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isubb_unsigned bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 +
     bv2z Tbit (1) -bits of bool (borrow_subB bs1 bs2)%bits *
                    Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    bv2z (Tuint n) (bs1 -# bs2)%bits.
  Proof.
  Admitted.

  Lemma bv2z_Isubb_signed bs1 bs2 n :
    size bs1 = n -> size bs2 = n ->
    subb_safe (Tsint n) bs1 bs2 ->
    bv2z (Tsint n) (bs1 -# bs2)%bits = (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isbc t bs1 bs2 bsc :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t -> size bsc = 1 ->
    sbcB_safe t bs1 bs2 bsc ->
    bv2z t (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (bv2z t bs1 - bv2z t bs2 - (1 - bv2z Tbit bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isbcs_unsigned bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 - (1 - bv2z Tbit bsc) +
     (1 - bv2z Tbit (1)-bits of bool
                             ((adcB (to_bool bsc) bs1 (~~# bs2)).1)%bits) *
     Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    bv2z (Tuint n) (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2.
  Proof.
  Admitted.

  Lemma bv2z_Isbcs_signed bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbcs_safe (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (adcB (to_bool bsc) bs1 (~~# bs2)%bits).2 =
    (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2 - (1 - bv2z Tbit bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isbb t bs1 bs2 bsc :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t -> size bsc = 1 ->
    sbbB_safe t bs1 bs2 bsc ->
    bv2z t (sbbB (to_bool bsc) bs1 bs2).2 =
    (bv2z t bs1 - bv2z t bs2 - (1 - bv2z Tbit bsc))%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isbbs_unsigned bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    (bv2z (Tuint n) (sbbB (to_bool bsc) bs1 bs2).2 +
     - bv2z Tbit (1)-bits of bool ((sbbB (to_bool bsc) bs1 bs2).1)%bits *
                     Cryptoline.DSL.z2expn (Z.of_nat n))%Z =
    (bv2z (Tuint n) bs1 - bv2z (Tuint n) bs2 - bv2z Tbit bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isbbs_signed bs1 bs2 bsc n :
    size bs1 = n -> size bs2 = n -> size bsc = 1 ->
    sbbs_safe (Tsint n) bs1 bs2 bsc ->
    bv2z (Tsint n) (sbbB (to_bool bsc) bs1 bs2).2 =
    (bv2z (Tsint n) bs1 - bv2z (Tsint n) bs2 - bv2z Tbit bsc)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Imul t bs1 bs2 :
    size bs1 = sizeof_typ t -> size bs2 = sizeof_typ t ->
    mulB_safe t bs1 bs2 ->
    bv2z t (bs1 *# bs2)%bits = (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Imull t bs1 bs2 :
    size bs1 = sizeof_typ t ->
    size bs2 = sizeof_typ t ->
    (bv2z (unsigned_typ t) (low (size bs2) (full_mul bs1 bs2)) +
     bv2z t (high (size bs1) (full_mul bs1 bs2)) *
     Cryptoline.DSL.z2expn (Z.of_nat (size bs2)))%Z =
    (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Imulj t bs1 bs2 :
    size bs1 = sizeof_typ t ->
    size bs2 = sizeof_typ t ->
    bv2z (double_typ t) (full_mul bs1 bs2) = (bv2z t bs1 * bv2z t bs2)%Z.
  Proof.
  Admitted.

  Lemma bv2z_Isplit_unsigned t bs n :
    size bs = sizeof_typ t ->
    (bv2z (unsigned_typ t) (bs <<# (size bs - n) >># (size bs - n))%bits +
     bv2z t (bs >># n)%bits * Cryptoline.DSL.z2expn (Z.of_nat n))%Z = bv2z t bs.
  Proof.
  Admitted.

  Lemma bv2z_Isplit_signed t bs n :
    size bs = sizeof_typ t ->
    (bv2z (unsigned_typ t) (bs <<# (size bs - n) >># (size bs - n))%bits +
     bv2z t (sarB n bs) * Cryptoline.DSL.z2expn (Z.of_nat n))%Z = bv2z t bs.
  Proof.
  Admitted.

  (* Upcast from unsigned to unsigned*)
  Lemma bv2z_Icast_uuu wt wa bs :
    wa <= wt -> size bs = wa ->
    bv2z (Tuint wt) (tcast bs (Tuint wa) (Tuint wt)) = bv2z (Tuint wa) bs.
  Proof.
  Admitted.

  (* Downcast from unsigned to unsigned *)
  Lemma bv2z_Icast_duu wt wa bs q r :
    (wa <= wt) = false -> size bs = wa ->
    Z.div_eucl (to_Zpos bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tuint wt) (tcast bs (Tuint wa) (Tuint wt)) +
     q * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tuint wa) bs.
  Proof.
  Admitted.

  (* Upcast from signed to unsigned *)
  Lemma bv2z_Icast_usu wt wa bs q r :
    (wa <= wt) = true -> size bs = wa ->
    Z.div_eucl (to_Z bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tsint wa) bs + q * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z =
    bv2z (Tuint wt) (tcast bs (Tsint wa) (Tuint wt)).
  Proof.
  Admitted.

  (* Downcast from signed to unsigned *)
  Lemma bv2z_Icast_dsu wt wa bs q r :
    (wa <= wt) = false -> size bs = wa ->
    Z.div_eucl (to_Z bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tuint wt) (tcast bs (Tsint wa) (Tuint wt)) +
     q * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tsint wa) bs.
  Proof.
  Admitted.

  (* Upcast from unsigned to signed *)
  Lemma bv2z_Icast_uus wt wa bs :
    (wa < wt) = true -> size bs = wa ->
    bv2z (Tsint wt) (tcast bs (Tuint wa) (Tsint wt)) = bv2z (Tuint wa) bs.
  Proof.
  Admitted.

  (* Downcast from unsigned to signed *)
  Lemma bv2z_Icast_dus wt wa bs q r :
    (wa < wt) = false -> size bs = wa ->
    Z.div_eucl (to_Zpos bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tsint wt) (tcast bs (Tuint wa) (Tsint wt)) +
     q * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tuint wa) bs.
  Proof.
  Admitted.

  (* Upcast from signed to signed *)
  Lemma bv2z_Icast_uss wt wa bs :
    (wa <= wt) = true -> size bs = wa ->
    bv2z (Tsint wt) (tcast bs (Tsint wa) (Tsint wt)) = bv2z (Tsint wa) bs.
  Proof.
  Admitted.

  (* Downcast from signed to signed *)
  Lemma bv2z_Icast_dss wt wa bs q r :
    (wa <= wt) = false -> size bs = wa ->
    Z.div_eucl (to_Z bs) (z2expn (Z.of_nat wt)) = (q, r) ->
    (bv2z (Tsint wt) (tcast bs (Tsint wa) (Tsint wt)) +
     q * Cryptoline.DSL.z2expn (Z.of_nat wt))%Z = bv2z (Tsint wa) bs.
  Proof.
  Admitted.

  Lemma bv2z_Ivpc tv ta bs :
    size bs = sizeof_typ ta -> vpc_safe tv ta bs ->
    bv2z tv (tcast bs ta tv) = bv2z ta bs.
  Proof.
  Admitted.

  Lemma bv2z_Ijoin th tl bsh bsl :
    compatible th tl ->
    size bsh = sizeof_typ th -> size bsl = sizeof_typ tl ->
    (bv2z tl bsl + bv2z th bsh * Cryptoline.DSL.z2expn (Z.of_nat (size bsl)))%Z =
    bv2z (double_typ th) (bsl ++ bsh).
  Proof.
  Admitted.


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
    | H : svar_notin ?avn (vars_atomic ?a) |-
      (* remove the update of auxiliary variables *)
      context f [ZSSAStore.upd (?avn, _) _ ?zs] =>
      rewrite svar_notin_eval_zexp; last by (rewrite vars_bv2z_atomic; exact: H)
    | Heq : bvz_eqi (SSATE.add ?v ?t ?E) ?bs ?zs
      |- context f [ZSSA.eval_zexp (bv2z_atomic ?a) ?zs] =>
      rewrite (bvz_eqi_eval_atomic Heq); last by defined_dec
    | Heq : bvz_eqi (SSATE.add ?v ?t ?E) ?bs ?zs,
      H : context f [ZSSA.eval_zexp (bv2z_atomic ?a) ?zs] |- _ =>
      rewrite (bvz_eqi_eval_atomic Heq) in H; last by defined_dec
    end.

  (* rewrite (eval_atomic a bs2) to (eval_atomic a bs1) where bs1 is a
     predecessor of bs2 *)
  Ltac eval_atomic_to_prev :=
    repeat
    match goal with
    | Hun : is_true (ssa_vars_unchanged_instr ?vs ?i),
      Hsub : is_true (SSAVS.subset (vars_atomic ?a) ?vs),
      Heval : eval_instr ?E ?i ?bs1 ?bs2 |-
      context f [eval_atomic ?a ?bs2] =>
      rewrite -(ssa_unchanged_instr_eval_atomic
                  (ssa_unchanged_instr_subset Hun Hsub) Heval)
    | Hun : is_true (ssa_vars_unchanged_instr ?vs ?i),
      Hsub : is_true (SSAVS.subset (vars_atomic ?a) ?vs),
      Heval : eval_instr ?E ?i ?bs1 ?bs2,
      H : context f [eval_atomic ?a ?bs2] |- _ =>
      rewrite -(ssa_unchanged_instr_eval_atomic
                  (ssa_unchanged_instr_subset Hun Hsub) Heval) in H
    end.

  (* If the type of an atomic a is Tbit in some typing environment E, and
     some state s conforms to E, introduce size (eval_atomic a s) = 1. *)
  Ltac intro_size_carry :=
    match goal with
    | Hco : SSAStore.conform ?bs1 ?E,
      H : is_true (atyp ?c ?E == Tbit),
      Hsub : is_true (SSAVS.subset (vars_atomic ?c) (vars_env ?E)) |- _ =>
      let Hsc := fresh "Hsc" in
      (move: (size_eval_atomic_asize Hsub Hco) => Hsc);
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
    end.

  (* For each are_defined vs E, introduce SSAVS.subset vs (vars_env E). *)
  Ltac intro_subset_from_are_defined :=
    match goal with
    | H : is_true (are_defined _ _) |- _ =>
      let Hsub := fresh "Hsub" in
      move: (H) => /defsubP Hsub; move: H; intro_subset_from_are_defined
    | |- _ => intros
    end.

  (* Introduce size (eval_atomic a s) = sizeof_typ (atyp a E) and
     rewrite asize a E. *)
  Ltac intro_atomic_size :=
    match goal with
    | Hco : SSAStore.conform ?bs ?E,
      Hsub : is_true (SSAVS.subset (vars_atomic ?a) (vars_env ?E)) |- _ =>
      let Hsize := fresh "Hsize" in
      move: (conform_size_eval_atomic Hsub Hco) => Hsize; move: Hsub; intro_atomic_size
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
      exact: bv2z_carry_constraint
    end.

  Lemma bv2z_upd_avars_sat_instr o E avn i bs1 bs2 g1 g2 g2' zes zs1 zs2 :
    well_formed_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    svar_notin avn (vars_instr i) ->
    SSAStore.conform bs1 E ->
    ssa_instr_safe_at E i bs1 ->
    eval_instr E i bs1 bs2 ->
    bv2z_instr o E avn g1 i = (g2, zes) ->
    bv2z_upd_avars_instr E avn g1 i zs1 = (g2', zs2) ->
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
        eval_atomic_to_prev; simplify_types;
        (* rewrite the LHS *)
        inversion_clear Hev; acc_zs_to_bs; simplify_types;
        (* *)
        intro_atomic_size; rewrite_types
      end.
    case: i => /=.
    (* Imov *)
    - move=> v a Hwf Hun Hni Hco _ Hev [] ? ? [] ? ? Heq; subst; rewrite /=.
      split; last by trivial. mytac. reflexivity.
    (* Ishl *)
    - move=> v a n Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst; rewrite /=.
      split; last by trivial. mytac. exact: (bv2z_Ishl Hsize Hsa).
    (* Icshl *)
    - move=> vh vl ah al n Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst;
               rewrite /=. split; last by trivial. mytac.
      exact: (bv2z_Icshl H H3 Hsize0 Hsize Hsa).
    (* Inondet *)
    - move=> v t Hwf Hun Hni Hco _ Hev.
      case Ht: (t == Tbit); (move=> [] ? ? [] ? ? Heq; subst; rewrite /=);
        last by trivial. ssa_vars_unchanged_instr_to_mem. move/eqP: Ht => ?; subst.
      inversion_clear Hev. by prove_carry_constr.
    (* Icmov *)
    - move=> v c a1 a2 Hwf Hun Hni Hco _ Hev [] ? ? [] ? ? Heq; subst; rewrite /=.
      split; last by trivial. mytac.
      + exact: (bv2z_Icmov_true _ _ _ Hsize0 H7).
      + exact: (bv2z_Icmov_false _ _ _ Hsize0 H7).
    (* Inop *)
    - move=> Hwf Hun Hni Hco _ Hev [] ? ? [] ? ? Heq; subst; rewrite /=. done.
    (* Inot *)
    - move=> v t a Hwf Hun Hni Hco _ Hev. case: t Hwf Hun Hev => n Hwf Hun Hev.
      + move=> [] ? ? [] ? ? Heq; subst; rewrite /=. split; last by trivial.
        mytac. exact: (bv2z_Inot_unsigned Hwt Hsize).
      + move=> [] ? ? [] ? ? Heq; subst; rewrite /=. split; last by trivial.
        mytac. exact: (bv2z_Inot_signed Hwt Hsize).
    (* Iadd *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (bv2z_Iadd Hsize Hsize0 Hsa).
    (* Iadds *)
    - move=> y v a1 a2 Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case => n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (bv2z_Iadds_unsigned Hsize0 Hsize).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by trivial.
        mytac. exact: (bv2z_Iadds_signed Hsize0 Hsize Hsa).
    (* Iadc *)
    - move=> v a1 a2 ac Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst.
      rewrite /=. split; last by done. mytac.
      exact: (bv2z_Iadc Hsize0 Hsize1 Hsize Hsa).
    (* Iadcs *)
    - move=> c v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (bv2z_Iadcs_unsigned Hsize1 Hsize0 Hsize).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (bv2z_Iadcs_signed Hsize1 Hsize0 Hsize Hsa).
    (* Isub *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst.
      rewrite /=. split; last by done. mytac. exact: (bv2z_Isub Hsize Hsize0 Hsa).
    (* Isubc *)
    - move=> c v a1 a2 Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (bv2z_Isubc_unsigned Hsize0 Hsize).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (bv2z_Isubc_signed Hsize0 Hsize Hsa).
    (* Isubb *)
    - move=> c v a1 a2 Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (bv2z_Isubb_unsigned Hsize0 Hsize).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (bv2z_Isubb_signed Hsize0 Hsize Hsa).
    (* Isbc *)
    - move=> v a1 a2 ac Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst.
      rewrite /=. split; last by done. mytac.
      exact: (bv2z_Isbc Hsize0 Hsize1 Hsize Hsa).
    (* Isbcs *)
    - move=> c v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (bv2z_Isbcs_unsigned Hsize1 Hsize0 Hsize).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (bv2z_Isbcs_signed Hsize1 Hsize0 Hsize Hsa).
    (* Isbb *)
    - move=> v a1 a2 ac Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst.
      rewrite /=. split; last by done. mytac.
      exact: (bv2z_Isbb Hsize0 Hsize1 Hsize Hsa).
    (* Isbbs *)
    - move=> c v a1 a2 ac Hwf Hun Hni Hco Hsa Hev. dcase (atyp a1 E). case=> n Hta1.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split.
        * mytac. exact: (bv2z_Isbbs_unsigned Hsize1 Hsize0 Hsize).
        * inversion_clear Hev. by prove_carry_constr.
      + move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
        mytac. exact: (bv2z_Isbbs_signed Hsize1 Hsize0 Hsize Hsa).
    (* Imul *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (bv2z_Imul Hsize Hsize0 Hsa).
    (* Imull *)
    - move=> vh vl a1 a2 Hwf Hni Hun Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (bv2z_Imull Hsize0 Hsize).
    (* Imulj *)
    - move=> v a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (bv2z_Imulj Hsize Hsize0).
    (* Isplit *)
    - move=> vh vl a n Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac.
      + exact: (bv2z_Isplit_unsigned _ Hsize).
      + exact: (bv2z_Isplit_signed _ Hsize).
    (* Iand *)
    - move=> v t a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. done.
    (* Ior *)
    - move=> v t a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. done.
    (* Ixor *)
    - move=> v t a1 a2 Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst. done.
    (* Icast *)
    - move=> v t a. rewrite /bv2z_cast /bv2z_upd_avars_cast.
      case: t => wt; dcase (atyp a E); case => wa Hta Hwf Hun Hni Hco Hsa Hev.
      + case Hwa: (wa <= wt).
        * move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_uuu Hwa Hsize).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_duu Hwa Hsize H0).
      + case Hwa: (wa <= wt).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_usu Hwa Hsize H0).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_dsu Hwa Hsize H0).
      + case Hwa: (wa < wt).
        * move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_uus Hwa Hsize).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_dus Hwa Hsize H0).
      + case Hwa: (wa <= wt).
        * move=> [] ? ? [] ? ? Heq; subst. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_uss Hwa Hsize).
        * move=> [] ? ? H; subst. repeat case_pairs. rewrite /=. split; last by done.
          mytac. exact: (bv2z_Icast_dss Hwa Hsize H0).
    (* Ivpc *)
    - move=> v t a Hwf Hni Hun Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (bv2z_Ivpc Hsize Hsa).
    (* Ijoin *)
    - move=> v a1 a2 Hwf Hni Hun Hco Hsa Hev [] ? ? [] ? ? Heq; subst. rewrite /=.
      split; last by trivial. mytac. exact: (bv2z_Ijoin H2 Hsize Hsize0).
    (* Iassume *)
    - move=> [e r] /= Hwf Hun Hni Hco Hsa Hev [] ? ? [] ? ? Heq; subst.
      mytac. rewrite are_defined_union /= in Hdef. move/andP: Hdef => [Hdef _].
      move: H => [/= He _]. apply/(bvz_eqi_eval_ebexp Heq Hdef). exact: He.
  Qed.

  Lemma bv2z_upd_avars_sat_program o E avn g1 p g2 eprogs bs1 bs2 :
    well_formed_program E p ->
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p ->
    svar_notin avn (vars_env E) -> svar_notin avn (vars_program p) ->
    SSAStore.conform bs1 E ->
    ssa_program_safe_at E p bs1 ->
    eval_program E p bs1 bs2 ->
    bv2z_program o E avn g1 p = (g2, eprogs) ->
    ZSSA.eval_zbexp (eands eprogs)
                    (bv2z_upd_avars E avn g1 p
                                    (bv2z_store (program_succ_typenv p E) bs2)).
  Proof.
    rewrite /bv2z_upd_avars. move: (@bv2z_store_eqi (program_succ_typenv p E) bs2).
    move: (bv2z_store (program_succ_typenv p E) bs2) => zs2.

    elim: p E g1 g2 eprogs bs1 bs2 zs2 =>
    [| i p IH] E g1 g2 eprogs bs1 bs2 zs2 /= Heqi2 Hwf Hun Hssa
               Hni_E Hni_p Hco Hsa Hev Hbv2z.
    - case: Hbv2z => ? ?; subst => /=. by trivial.
    - move: Hbv2z. inversion Hev using eval_program_cons_inv => {Hev} bs3 Hi Hp.
      dcase (bv2z_instr o E avn g1 i) => [[g_hd zhd] Hhd].
      dcase (bv2z_program o (instr_succ_typenv i E) avn g_hd p) => [[g_tl ztl] Htl].
      case=> ? ?; subst. move/andP: Hwf => [Hwf_i Hwf_p].
      move/andP: Hssa => [Hssa_i Hssa_p]. rewrite ssa_unchanged_program_cons in Hun.
      move/andP: Hun=> [Hun_i Hun_p]. move/svar_notin_union: Hni_p => [Hni_i Hni_p].
      inversion_clear Hsa. move: H H0 => Hsa_i Hsa_p. rewrite /bv2z_upd_avars /=.
      dcase (bv2z_upd_avars_instr E avn g1 i zs2) => [[g_hd' zs_hd] Hupd_hd].
      dcase (bv2z_upd_avars_program (instr_succ_typenv i E) avn g_hd' p zs_hd) =>
      [[g_tl' zs_tl] Hupd_tl].
      move: (bv2z_upd_avars_instr_gen Hhd Hupd_hd) => ?; subst.
      move: (bv2z_upd_avars_program_gen Htl Hupd_tl) => ?; subst.
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
      + apply/(bv2z_upd_avars_program_eval_zbexp _ Hupd_tl).
        * exact: (bv2z_instr_newer_than Hhd Hni_i).
        * apply: (bv2z_upd_avars_sat_instr
                    Hwf_i Hun_i Hni_i Hco Hsa_i Hi Hhd Hupd_hd).
          apply: (@bvs_bvz_eqi (instr_succ_typenv i E) bs2 bs3 zs2).
          -- apply: bvs_eqi_sym. exact: (bvs_eqi_eval_program Hun_iep Hssa_p Hp).
          -- apply: (submap_bvz_eqi _ Heqi2).
             exact: (ssa_unchanged_program_succ_typenv_submap Hun_iep Hssa_p).
      + have ->: (zs_tl =
                  (bv2z_upd_avars_program (instr_succ_typenv i E) avn g_hd' p zs_hd).2)
          by rewrite Hupd_tl; reflexivity.
        move: (conform_eval_succ_typenv Hwf_i Hco Hi) => Hco_3succi.
        apply: (IH _ _ _ _ _ _ _ _ Hwf_p Hun_iep Hssa_p Hni_ie Hni_p
                   Hco_3succi (Hsa_p bs3 Hi) Hp Htl).
        apply: (bvz_zs_eqi Heqi2). apply: (bv2z_upd_avars_instr_eqi Hupd_hd).
        apply: (svar_notin_replace
                  (SSAVS.Lemmas.P.equal_sym
                     (vars_env_program_succ_typenv p (instr_succ_typenv i E)))).
        apply/svar_notin_union; split.
        * apply: (svar_notin_replace
                    (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          apply/svar_notin_union. split; [exact: Hni_E | exact: Hni_lvi].
        * exact: Hni_lvp.
  Qed.

  Lemma bv2z_upd_avars_eval_eexp {E avn g p bs e} :
    svar_notin avn (vars_eexp e) ->
    ZSSA.eval_zexp e (bv2z_upd_avars
                        E avn g p (bv2z_store (program_succ_typenv p E) bs)) =
    eval_eexp e (program_succ_typenv p E) bs.
  Proof.
    elim: e E g p bs => //=.
    - move=> v E g p bs Hnotin. move: (svar_notin_singleton1 Hnotin) => Hne.
      rewrite eq_sym in Hne. rewrite (bv2z_upd_avars_acc_ne Hne).
      rewrite acc_bv2z_store. reflexivity.
    - move=> op e IH E g p bs Hnotin. rewrite (IH _ _ _ _ Hnotin). reflexivity.
    - move=> op e1 IH1 e2 IH2 E g p bs Hnotin.
      rewrite (IH1 _ _ _ _ (svar_notin_union1 Hnotin))
              (IH2 _ _ _ _ (svar_notin_union2 Hnotin)). reflexivity.
  Qed.

  Lemma bv2z_upd_avars_eval_ebexp {E avn g p bs e} :
    svar_notin avn (vars_ebexp e) ->
    ZSSA.eval_zbexp e (bv2z_upd_avars
                         E avn g p (bv2z_store (program_succ_typenv p E) bs)) <->
    eval_ebexp e (program_succ_typenv p E) bs.
  Proof.
    elim: e E g p bs => //=.
    - move=> e1 e2 E g p bs Hnotin.
      rewrite (bv2z_upd_avars_eval_eexp (svar_notin_union1 Hnotin))
              (bv2z_upd_avars_eval_eexp (svar_notin_union2 Hnotin)). done.
    - move=> e1 e2 em E g p bs Hnotin.
      move: (svar_notin_union2 Hnotin) => Hnotin2m.
      rewrite (bv2z_upd_avars_eval_eexp (svar_notin_union1 Hnotin))
              (bv2z_upd_avars_eval_eexp (svar_notin_union1 Hnotin2m))
              (bv2z_upd_avars_eval_eexp (svar_notin_union2 Hnotin2m)). done.
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
         move/svar_notin_union: H => [H1 H2]
       end).

  Theorem bv2z_spec_sound (o : options) (s : spec) :
    well_formed_ssa_spec s ->
    ssa_spec_safe s ->
    valid_rspec (rspec_of_spec s) ->
    ZSSA.valid_zspec (bv2z_espec o (new_svar_spec s) (espec_of_spec s)) ->
    valid_spec s.
  Proof.
    destruct s as [E f p g] => /=. rewrite /well_formed_ssa_spec /bv2z_espec /=.
    rewrite /well_formed_spec /=.
    move/andP=> [/andP [/andP [/andP [Hwf_f Hwf_p] Hwf_g] Hunch] Hssa].
    dcase (new_svar_spec {| sinputs := E; spre := f; sprog := p; spost := g |}) =>
    avn Havn. set g1 := initial_index.
    dcase (bv2z_program o E avn g1 (eqn_program p)) => [[g2 eprogs] Hzp].
    move=> Hsafe Hrng Heqn bs1 bs2 /= Hcon [Hpre_eqn Hpre_rng] Hprog.

    split; last exact: (Hrng _ _ Hcon Hpre_rng (eval_rng_program Hprog)). 
    rewrite /ZSSA.valid_zspec /= in Heqn.

    rewrite /new_svar_spec /= in Havn.
    move: (new_svar_notin
             (SSAVS.union (vars_env E)
                          (SSAVS.union (vars_bexp f)
                                       (SSAVS.union (vars_program p)
                                                    (vars_bexp g))))).
    rewrite Havn => Hnotin. decompose_svar_notin_union.
    move: (svar_notin_subset (vars_ebexp_subset f) Hni1) => Hni_eqn_f.
    move: (svar_notin_subset (vars_ebexp_subset g) Hni3) => Hni_eqn_g.

    move: (SSA.well_formed_eqn_bexp Hwf_f) => Hwf_ef.
    move/andP: Hwf_ef => [Hdef_ef Hwt_ef].
    rewrite are_defined_subset_env in Hdef_ef.
    move: (SSA.ssa_unchanged_program_subset Hunch Hdef_ef) => Hunch_ef.
    rewrite -ssa_vars_unchanged_eqn_program in Hunch_ef.
    move: (SSA.ssa_unchanged_program_eval_ebexp1
             Hunch_ef (eval_eqn_program Hprog) Hpre_eqn) => Heval_ef.
    move: (@bv2z_upd_avars_eval_ebexp
             E
             avn g1 (eqn_program p) bs2 (eqn_bexp f) Hni_eqn_f) => Hiff.
    move: (ssa_unchanged_program_succ_typenv_submap Hunch Hssa) => Hsubmap.
    move/andP: Hwf_f => [Hdef_f Hwt_f]. rewrite are_defined_union in Hdef_f.
    move/andP: Hdef_f => [Hdef_eqn_f Hdef_rng_f].
    move: (@SSA.submap_eval_ebexp _ _ _ bs2 Hsubmap Hdef_eqn_f).
    rewrite -eqn_program_succ_typenv => H.
    move/H/Hiff: Heval_ef => {H} Hzf.

    move: (Hsafe bs1 Hpre_rng) => /= => Hsafe_at.
    rewrite bv2z_eqn_program in Hzp.
    move: (bv2z_upd_avars_sat_program
             Hwf_p Hunch Hssa Hni Hni0 Hcon Hsafe_at Hprog Hzp) => Hzprog.
    rewrite -eqn_program_succ_typenv in Hzprog.
    rewrite -bv2z_upd_avars_eqn in Hzprog.

    move: Hzf Hzprog.
    set zbs2 := bv2z_upd_avars
                  E avn g1 (eqn_program p)
                  (bv2z_store (program_succ_typenv (eqn_program p) E) bs2).
    move=> Hzf Hzprog.
    move: (Heqn zbs2 zbs2 (conj Hzf Hzprog) (Logic.eq_refl zbs2)) => Hzg.

    apply/(bv2z_upd_avars_eval_ebexp Hni_eqn_g). exact: Hzg.
  Qed.

  (* Well-formedness of bv2z_spec *)

  Lemma bv2z_instr_vars_subset E o avn g1 i g2 zes :
    well_defined_instr E i ->
    bv2z_instr o E avn g1 i = (g2, zes) ->
    SSAVS.subset (ZSSA.vars_zbexp (eands zes))
                 (SSAVS.union (aux_vars_lt avn g2)
                              (vars_env (instr_succ_typenv i E))).
  Proof.
    Ltac mytac ::=
      repeat
        match goal with
        | H : is_true (_ && _) |- _ => hyps_splitb
        | H : is_true (are_defined _ _) |- _ => move/defsubP: H => H
        | |- context f [carry_constr ?o] =>
          rewrite /carry_constr; case: (add_carry_constraints o) => /=
        | H : bv2z_cast _ _ _ _ _ _ = _ |- _ =>
          rewrite /bv2z_cast in H; repeat case_pairs; rewrite /=
        | H : bv2z_vpc _ _ _ _ = _ |- _ =>
          rewrite /bv2z_vpc in H; repeat case_pairs; rewrite /=
        | |- context f [vars_env (SSATE.add _ _ _)] =>
          rewrite vars_env_add_union
        | |- context f [ZSSA.vars_zexp (bv2z_atomic _)] =>
          rewrite vars_bv2z_atomic
        | |- context f [ZSSA.vars_zbexp (eands (split_eand _))] =>
          rewrite vars_eands_split_eand
    end.
    (case: i; rewrite /=; intros; repeat case_pairs; rewrite /=);
      mytac; try match goal with
                 | |- context f [aux_vars_lt ?avn (N.succ ?g)] =>
                   let H := fresh in
                   move/SSAVS.Lemmas.subset_singleton2:
                     (aux_vars_lt_mem avn (N.lt_succ_diag_r g)) => H
                 | |- context f [ZSSA.vars_zbexp (eqn_bexp ?e)] =>
                   let H := fresh in
                   move: (vars_ebexp_subset e) => H
                 end;
      by (t_auto with SSAVS.Lemmas.dp_subset).
  Qed.

  Lemma bv2z_program_vars_subset E o avn g1 p g2 eprogs :
    well_formed_program E p ->
    bv2z_program o E avn g1 p = (g2, eprogs) ->
    SSAVS.subset (ZSSA.vars_zbexp (eands eprogs))
                 (SSAVS.union (aux_vars_lt avn g2)
                              (vars_env (program_succ_typenv p E))).
  Proof.
    elim: p E g1 g2 eprogs => /=.
    - move=> ? ? ? ? _ [] _ <- /=. exact: SSAVS.Lemmas.subset_empty.
    - move=> i p IH E g1 g2 eprogs /andP [Hwf_i Hwf_p].
      dcase (bv2z_instr o E avn g1 i) => [[g_hd zhd] Hhd].
      dcase (bv2z_program o (instr_succ_typenv i E) avn g_hd p) => [[g_tl ztl] Htl].
      case=> ? ?; subst. rewrite vars_eands_cat. apply: SSAVS.Lemmas.subset_union3.
      + rewrite vars_env_program_succ_typenv. move: (bv2z_program_idx_inc Htl) => Hg.
        move: (aux_vars_lt_subset avn Hg) => Hsub1.
        move/andP: Hwf_i => [Hdef_i Hwt_i].
        move: (bv2z_instr_vars_subset Hdef_i Hhd) => Hsub2.
        rewrite -SSAVS.Lemmas.P.union_assoc. apply: SSAVS.Lemmas.subset_union1.
        apply: (SSAVS.Lemmas.subset_trans Hsub2). apply: SSAVS.Lemmas.subset_union3.
        * apply: SSAVS.Lemmas.subset_union1. exact: Hsub1.
        * apply: SSAVS.Lemmas.subset_union2. exact: SSAVS.Lemmas.subset_refl.
      + exact: (IH _ _ _ _ Hwf_p Htl).
  Qed.

  Lemma bv2z_spec_well_formed o s :
    well_formed_ssa_spec s ->
    ZSSA.well_formed_zspec (bv2z_espec o (new_svar_spec s) (espec_of_spec s)).
  Proof.
    case: s => E f p g.
    move=> /andP [/= /andP [/= /andP [/= /andP [Hwf_f Hwf_p] Hwf_g] Hun] Hssa].
    rewrite /bv2z_espec /=.
    dcase (bv2z_program
             o E (new_svar_spec {| sinputs := E; spre := f; sprog := p; spost := g |})
             initial_index (eqn_program p)) => [[g' eprogs] Hbvz].
    rewrite /ZSSA.well_formed_zspec /=. rewrite andbT eqn_program_succ_typenv.
    apply/andP; split.
    - apply: SSAVS.Lemmas.subset_union3.
      + apply: SSAVS.Lemmas.subset_union2.
        move/andP: Hwf_f => [Hdef Hwt]. move/defsubP: Hdef => Hsub.
        apply: (SSAVS.Lemmas.subset_trans (vars_ebexp_subset f)).
        apply: (SSAVS.Lemmas.subset_trans Hsub).
        rewrite vars_env_program_succ_typenv.
        apply: SSAVS.Lemmas.subset_union1. exact: SSAVS.Lemmas.subset_refl.
      + rewrite bv2z_eqn_program in Hbvz.
        exact: (bv2z_program_vars_subset Hwf_p Hbvz).
    - apply: SSAVS.Lemmas.subset_union1. apply: SSAVS.Lemmas.subset_union2.
      apply: (SSAVS.Lemmas.subset_trans (vars_ebexp_subset g)).
      move/andP: Hwf_g => [/defsubP H _]. exact: H.
  Qed.

End SplitSpec.
