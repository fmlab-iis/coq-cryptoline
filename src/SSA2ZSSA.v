
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder ZAriths Store Tactics.
From BitBlasting Require Import State Typ TypEnv.
From Cryptoline Require Import DSL SSA ZSSA.
From nbits Require Import NBits.

(** Conversion from a specification to a range specification, an algebraic specification, and a safety condition. *)



(* Safety conditions *)

Section Safety.

  Import SSA.

  Definition uaddB_safe bs1 bs2 : bool := ~~ carry_addB bs1 bs2 .

  Definition saddB_safe bs1 bs2 : bool := ~~ Saddo bs1 bs2 .

  Definition addB_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then uaddB_safe bs1 bs2
    else saddB_safe bs1 bs2 .

  Definition uadcB_safe bs1 bs2 c : bool :=
    ~~ carry_addB bs1 bs2 && ~~ carry_addB (addB bs1 bs2) c .

  Definition sadcB_safe bs1 bs2 c : bool :=
    ~~ Saddo bs1 bs2 && ~~ Saddo (addB bs1 bs2) c .

  Definition adcB_safe typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then uadcB_safe bs1 bs2 bsc
    else sadcB_safe bs1 bs2 bsc .

  Definition usubB_safe bs1 bs2 : bool := ~~ borrow_subB bs1 bs2 .

  Definition ssubB_safe bs1 bs2 : bool := ~~ Ssubo bs1 bs2 .

  Definition subB_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then usubB_safe bs1 bs2
    else ssubB_safe bs1 bs2 .

  Definition usbbB_safe bs1 bs2 c : bool :=
    ~~ borrow_subB bs1 bs2 && ~~ borrow_subB (subB bs1 bs2) c .

  Definition ssbbB_safe bs1 bs2 c : bool :=
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (subB bs1 bs2) c .

  Definition sbbB_safe typ_a bs1 bs2 bsb : bool :=
    if Typ.is_unsigned typ_a then usbbB_safe bs1 bs2 bsb
    else ssbbB_safe bs1 bs2 bsb .

  Definition usbcB_safe bs1 bs2 c : bool :=
    ~~ borrow_subB bs1 bs2 && ~~ borrow_subB (subB bs1 bs2) (subB (ones 1) c) .

  Definition ssbcB_safe bs1 bs2 c : bool :=
    ~~ Ssubo bs1 bs2 && ~~ Ssubo (subB bs1 bs2) (subB (ones 1) c) .

  Definition sbcB_safe typ_a bs1 bs2 bsc : bool :=
    if Typ.is_unsigned typ_a then usbcB_safe bs1 bs2 bsc
    else ssbcB_safe bs1 bs2 bsc .

  Definition umulB_safe bs1 bs2 : bool := ~~ Umulo bs1 bs2 .

  Definition smulB_safe bs1 bs2 : bool := ~~ Smulo bs1 bs2 .

  Definition mulB_safe typ_a bs1 bs2 : bool :=
    if Typ.is_unsigned typ_a then umulB_safe bs1 bs2
    else smulB_safe bs1 bs2 .

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
    | Iadc _ a1 a2 ac =>
      adcB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s)
    | Isub _ a1 a2 =>
      subB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s)
    | Isbc _ a1 a2 ac =>
      sbcB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ac s)
    | Isbb _ a1 a2 ab =>
      sbbB_safe (atyp a1 te) (eval_atomic a1 s) (eval_atomic a2 s) (eval_atomic ab s)
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
    | Iassume _ => true
    end .

  Inductive ssa_program_safe_at : SSATE.env -> program -> SSAStore.t -> Prop :=
  | ssa_program_safe_at_nil te s :
      ssa_program_safe_at te [::] s
  | ssa_program_safe_at_cons te hd tl s :
      ssa_instr_safe_at te hd s ->
      (forall s', eval_instr te hd s s' ->
                  ssa_program_safe_at (instr_succ_typenv hd te) tl s') ->
      ssa_program_safe_at te (hd::tl) s .

  Definition ssa_program_safe te p : Prop :=
    forall s, ssa_program_safe_at te p s .

  Definition ssa_spec_safe sp :=
    forall s, eval_rbexp (rng_bexp (spre sp)) s ->
              ssa_program_safe_at (sinputs sp) (sprog sp) s .

End Safety.



(* Convert a bit-vector program to an integer program *)

Section SSA2ZSSA.

  Import SSA ZSSA.

  Definition bv2z_atomic (a : atomic) : zexp :=
    match a with
    | Avar v => evar v
    | Aconst ty bs =>
      match ty with
      | Tuint _ => econst (to_Zpos bs)
      | Tsint _ => econst (to_Z bs)
      end
    end.

  Definition bv2z_assign v e := eeq (evar v) e.
  Definition bv2z_join e h l p := eeq (eadd l (emul2p h p)) e.
  Definition bv2z_split vh vl e p := bv2z_join e (evar vh) (evar vl) p.
  Definition bv2z_is_carry c := eeq (emul (evar c) (esub (evar c) (econst 1)))
                                    (econst 0).
  Definition carry_constr b c := if b then [:: bv2z_is_carry c] else [::].

  Definition bv2z_instr (te : SSATE.env) (nvar : N) (g : N) (i : instr) :
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
              (Z.of_nat (a2size - n))])
    | Inondet v t => (g, [::])
    | Icmov v c a1 a2 =>
      (g, [::])
    | Inop => (g, [::])
    | Inot v t a => (g, [::])
    | Iadd v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      (g, [:: bv2z_assign v (eadd za1 za2)])
    | Iadds c v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let a2size := asize a2 te in
      (g, [:: bv2z_split c v (eadd za1 za2) (Z.of_nat a2size)])
    | Iadc v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      (g, [:: bv2z_assign v (eadd (eadd za1 za2) zy)])
    | Iadcs c v a1 a2 y =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      let zy := bv2z_atomic y in
      let a2size := asize a2 te in
      (g, [::])
    | Isub v a1 a2 =>
      let za1 := bv2z_atomic a1 in
      let za2 := bv2z_atomic a2 in
      (g, [:: bv2z_assign v (esub za1 za2)])
    | Isubc c v a1 a2 => (g, [::])
    | Isubb c v a1 a2 => (g, [::])
    | Isbc v a1 a2 y => (g, [::])
    | Isbcs c v a1 a2 y => (g, [::])
    | Isbb v a1 a2 y => (g, [::])
    | Isbbs c v a1 a2 y => (g, [::])
    | Imul v a1 a2 => (g, [::])
    | Imull vh vl a1 a2 => (g, [::])
    | Imulj v a1 a2 => (g, [::])
    | Isplit vh vl a n => (g, [::])
    | Iand v t a1 a2 => (g, [::])
    | Ior v t a1 a2 => (g, [::])
    | Ixor v t a1 a2 => (g, [::])
    | Icast v t a => (g, [::])
    | Ivpc v t a => (g, [::])
    | Ijoin v ah al => (g, [::])
    | Iassume e => (g, [::])
    end.

  (* TODO: see bv2z_program in certified_qhasm_vcg/mqhasm/bvSSA2zSSA.v *)
  Definition bv2z_program (nvar : N) (idx : N) (p : program) : N * ZSSA.zprogram :=
    (nvar, [::]).

End SSA2ZSSA.
