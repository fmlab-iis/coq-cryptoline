
(** * Conversion from SSA to SSALite *)

From Coq Require Import List ZArith FSets OrderedType String Decimal DecimalString Btauto.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State BBCommon.
From ssrlib Require Import EqVar EqOrder EqFMaps ZAriths Tactics Lists EqFSets Seqs Strings.
From Cryptoline Require Import Options DSLRaw SSALite SSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** ** Rewrite mov statements *)

Section RewriteMov.

  Import SSA.

  (** Variable substitution *)

  Definition eexp_of_atom (a : atom) : eexp :=
    match a with
    | Avar v => evar v
    | Aconst ty n => econst (bv2z ty n)
    end.

  Definition rexp_of_atom (a : atom) : rexp :=
    match a with
    | Avar v => rvar v
    | Aconst ty n => rconst (sizeof_typ ty) n
    end.

  Fixpoint subst_eexp (m : SSAVM.t atom) (e : eexp) : eexp :=
    match e with
    | Evar v => match SSAVM.find v m with
                | None => e
                | Some a => eexp_of_atom a
                end
    | Econst _ => e
    | Eunop op e => eunary op (subst_eexp m e)
    | Ebinop op e1 e2 => ebinary op (subst_eexp m e1) (subst_eexp m e2)
    | Epow e n => epow (subst_eexp m e) n
    end.

  Fixpoint subst_rexp (m : SSAVM.t atom) (e : rexp) : rexp :=
    match e with
    | Rvar v => match SSAVM.find v m with
                | None => e
                | Some a => rexp_of_atom a
                end
    | Rconst _ _ => e
    | Runop w op e => runary w op (subst_rexp m e)
    | Rbinop w op e1 e2 => rbinary w op (subst_rexp m e1) (subst_rexp m e2)
    | Ruext w e i => ruext w (subst_rexp m e) i
    | Rsext w e i => rsext w (subst_rexp m e) i
    end.

  Definition subst_eexps (m : SSAVM.t atom) (es : seq eexp) : seq eexp :=
    tmap (subst_eexp m) es.

  Fixpoint subst_ebexp (m : SSAVM.t atom) (e : ebexp) : ebexp :=
    match e with
    | Etrue => e
    | Eeq e1 e2 => Eeq (subst_eexp m e1) (subst_eexp m e2)
    | Eeqmod e1 e2 ms => Eeqmod (subst_eexp m e1) (subst_eexp m e2) (subst_eexps m ms)
    | Eand e1 e2 => Eand (subst_ebexp m e1) (subst_ebexp m e2)
    end.

  Fixpoint subst_rbexp (m : SSAVM.t atom) (e : rbexp) : rbexp :=
    match e with
    | Rtrue => e
    | Req w e1 e2 => Req w (subst_rexp m e1) (subst_rexp m e2)
    | Rcmp w op e1 e2 => Rcmp w op (subst_rexp m e1) (subst_rexp m e2)
    | Rneg e => Rneg (subst_rbexp m e)
    | Rand e1 e2 => Rand (subst_rbexp m e1) (subst_rbexp m e2)
    | Ror e1 e2 => Ror (subst_rbexp m e1) (subst_rbexp m e2)
    end.

  Definition subst_bexp (m : SSAVM.t atom) (e : bexp) : bexp :=
    (subst_ebexp m (fst e), subst_rbexp m (snd e)).

  Definition subst_atom (m : SSAVM.t atom) (a : atom) : atom :=
    match a with
    | Avar v => match SSAVM.find v m with
                | None => a
                | Some a' => a'
                end
    | Aconst _ _ => a
    end.

  Definition subst_instr (m : SSAVM.t atom) (i : instr) : instr :=
    match i with
    | Imov v a => Imov v (subst_atom m a)
    | Ishl v a n => Ishl v (subst_atom m a) n
    | Icshl v1 v2 a1 a2 n => Icshl v1 v2 (subst_atom m a1) (subst_atom m a2) n
    | Inondet v t => i
    | Icmov v c a1 a2 => Icmov v c (subst_atom m a1) (subst_atom m a2)
    | Inop => i
    | Inot v t a => Inot v t (subst_atom m a)
    | Iadd v a1 a2 => Iadd v (subst_atom m a1) (subst_atom m a2)
    | Iadds c v a1 a2 => Iadds c v (subst_atom m a1) (subst_atom m a2)
    | Iadc v a1 a2 y => Iadc v (subst_atom m a1) (subst_atom m a2) y
    | Iadcs c v a1 a2 y => Iadcs c v (subst_atom m a1) (subst_atom m a2) y
    | Isub v a1 a2 => Isub v (subst_atom m a1) (subst_atom m a2)
    | Isubc c v a1 a2 => Isubc c v (subst_atom m a1) (subst_atom m a2)
    | Isubb c v a1 a2 => Isubb c v (subst_atom m a1) (subst_atom m a2)
    | Isbc v a1 a2 y => Isbc v (subst_atom m a1) (subst_atom m a2) y
    | Isbcs c v a1 a2 y => Isbcs c v (subst_atom m a1) (subst_atom m a2) y
    | Isbb v a1 a2 y => Isbb v (subst_atom m a1) (subst_atom m a2) y
    | Isbbs c v a1 a2 y => Isbbs c v (subst_atom m a1) (subst_atom m a2) y
    | Imul v a1 a2 => Imul v (subst_atom m a1) (subst_atom m a2)
    | Imull vh vl a1 a2 => Imull vh vl (subst_atom m a1) (subst_atom m a2)
    | Imulj v a1 a2 => Imulj v (subst_atom m a1) (subst_atom m a2)
    | Isplit vh vl a n => Isplit vh vl (subst_atom m a) n
    | Iand v t a1 a2 => Iand v t (subst_atom m a1) (subst_atom m a2)
    | Ior v t a1 a2 => Ior v t (subst_atom m a1) (subst_atom m a2)
    | Ixor v t a1 a2 => Ixor v t (subst_atom m a1) (subst_atom m a2)
    | Icast v t a => Icast v t (subst_atom m a)
    | Ivpc v t a => Ivpc v t (subst_atom m a)
    | Ijoin v ah al => Ijoin v (subst_atom m ah) (subst_atom m al)
    | Icut e => Icut (subst_bexp m e)
    | Iassert e => Iassert (subst_bexp m e)
    | Iassume e => Iassume (subst_bexp m e)
    end.

  Definition subst_program (m : SSAVM.t atom) (p : program) : program :=
    tmap (subst_instr m) p.

  Definition subst_spec (m : SSAVM.t atom) (s : spec) : spec :=
    {| sinputs := sinputs s;
       spre := subst_bexp m (spre s);
       sprog := subst_program m (sprog s);
       spost := subst_bexp m (spost s) |}.


  (** Rewrite mov statements *)

  Definition subst_map_instr (m : SSAVM.t atom) (i : instr) : SSAVM.t atom :=
    match i with
    | Imov v a =>
        (* v <- a *)
        match a with
        | Avar u => match SSAVM.find u m with
                    | None =>
                        (* v <- u *)
                        SSAVM.add v a m
                    | Some ua =>
                        (* v <- u <- ... <- ua *)
                        SSAVM.add v ua m
                    end
        | Aconst _ _ => SSAVM.add v a m
        end
    | _ => m
    end.

  Fixpoint subst_map_program_rec (m : SSAVM.t atom) (p : program) : SSAVM.t atom :=
    match p with
    | [::] => m
    | i::p => subst_map_program_rec (subst_map_instr m i) p
    end.

  Definition subst_map_program (p : program) : SSAVM.t atom :=
    subst_map_program_rec (SSAVM.empty atom) p.

  Definition subst_map_spec (s : spec) : SSAVM.t atom :=
    subst_map_program (sprog s).

  Definition rewrite_mov (s : spec) : spec :=
    subst_spec (subst_map_spec s) s.

End RewriteMov.


(** ** Conversion from SSA.spec to SSALite.spec *)

(** It is assumed that in the SSA specification, there is neither
    cut, assert, nor assume statement. *)

Section SSA2SSALite.

  Import SSA.

  Definition ssa2lite_instr (i : SSA.instr) : SSALite.instr :=
    match i with
    | Imov v a => SSALite.Imov v a
    | Ishl v a n => SSALite.Ishl v a n
    | Icshl v1 v2 a1 a2 n => SSALite.Icshl v1 v2 a1 a2 n
    | Inondet v t => SSALite.Inondet v t
    | Icmov v c a1 a2 => SSALite.Icmov v c a1 a2
    | Inop => SSALite.Inop
    | Inot v t a => SSALite.Inot v t a
    | Iadd v a1 a2 => SSALite.Iadd v a1 a2
    | Iadds c v a1 a2 => SSALite.Iadds c v a1 a2
    | Iadc v a1 a2 y => SSALite.Iadc v a1 a2 y
    | Iadcs c v a1 a2 y => SSALite.Iadcs c v a1 a2 y
    | Isub v a1 a2 => SSALite.Isub v a1 a2
    | Isubc c v a1 a2 => SSALite.Isubc c v a1 a2
    | Isubb c v a1 a2 => SSALite.Isubb c v a1 a2
    | Isbc v a1 a2 y => SSALite.Isbc v a1 a2 y
    | Isbcs c v a1 a2 y => SSALite.Isbcs c v a1 a2 y
    | Isbb v a1 a2 y => SSALite.Isbb v a1 a2 y
    | Isbbs c v a1 a2 y => SSALite.Isbbs c v a1 a2 y
    | Imul v a1 a2 => SSALite.Imul v a1 a2
    | Imull vh vl a1 a2 => SSALite.Imull vh vl a1 a2
    | Imulj v a1 a2 => SSALite.Imulj v a1 a2
    | Isplit vh vl a n => SSALite.Isplit vh vl a n
    | Iand v t a1 a2 => SSALite.Iand v t a1 a2
    | Ior v t a1 a2 => SSALite.Ior v t a1 a2
    | Ixor v t a1 a2 => SSALite.Ixor v t a1 a2
    | Icast v t a => SSALite.Icast v t a
    | Ivpc v t a => SSALite.Ivpc v t a
    | Ijoin v ah al => SSALite.Ijoin v ah al
    | Icut e => SSALite.Inop
    | Iassert e => SSALite.Inop
    | Iassume e => SSALite.Iassume e
    end.

  Definition ssa2lite_program (p : SSA.program) : SSALite.program :=
    tmap ssa2lite_instr p.

  Definition ssa2lite_spec (s : SSA.spec) : SSALite.spec :=
    {| SSALite.sinputs := sinputs s;
       SSALite.spre := spre s;
       SSALite.sprog := ssa2lite_program (sprog s);
       SSALite.spost := spost s |}.

End SSA2SSALite.


(** ** Properties of variable substitution *)

Section VarSubst.

  Import SSA.

  Lemma vars_eexp_of_atom a : vars_eexp (eexp_of_atom a) = vars_atom a.
  Proof. by case: a => [ v | ty bs ] //=. Qed.

  Lemma vars_rexp_of_atom a : vars_rexp (rexp_of_atom a) = vars_atom a.
  Proof. by case: a => [ v | ty bs ] //=. Qed.

  Lemma subst_eexps_cons m e es :
    subst_eexps m (e::es) = (subst_eexp m e)::(subst_eexps m es).
  Proof. rewrite /subst_eexps !tmap_map /=. reflexivity. Qed.

  Lemma subst_eexps_rcons m es e :
    subst_eexps m (rcons es e) = rcons (subst_eexps m es) (subst_eexp m e).
  Proof. rewrite /subst_eexps !tmap_map. rewrite map_rcons. reflexivity. Qed.

  Lemma subst_eexps_cat m es1 es2 :
    subst_eexps m (es1 ++ es2) = subst_eexps m es1 ++ subst_eexps m es2.
  Proof.
    elim: es1 => [| e1 es1 IH1] //=. rewrite !subst_eexps_cons IH1.
    rewrite cat_cons. reflexivity.
  Qed.

  Lemma subst_program_cons m i p :
    subst_program m (i::p) = (subst_instr m i)::(subst_program m p).
  Proof. rewrite /subst_program !tmap_map /=. reflexivity. Qed.

  Lemma subst_program_rcons m p i :
    subst_program m (rcons p i) = rcons (subst_program m p) (subst_instr m i).
  Proof. rewrite /subst_program !tmap_map. rewrite map_rcons. reflexivity. Qed.

  Lemma subst_program_cat m p1 p2 :
    subst_program m (p1 ++ p2) = subst_program m p1 ++ subst_program m p2.
  Proof.
    elim: p1 => [| i1 p1 IH1] //=. rewrite !subst_program_cons IH1.
    rewrite cat_cons. reflexivity.
  Qed.


  (* Unchanged substitution *)

  Lemma disjoint_subst_eexp m e :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (vars_eexp e) ->
    subst_eexp m e = e.
  Proof.
    elim: e => //=.
    - move=> v Hdisj. rewrite SSAVS.Lemmas.disjoint_singleton_r in Hdisj.
      rewrite (TEKS.not_mem_key_set_find Hdisj). reflexivity.
    - move=> op e IH Hdisj. rewrite (IH Hdisj). reflexivity.
    - move=> op e1 IH1 e2 IH2 Hdisj. rewrite SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2]. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
    - move=> e IH n Hdisj. rewrite (IH Hdisj). reflexivity.
  Qed.

  Lemma disjoint_subst_rexp m e :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (vars_rexp e) ->
    subst_rexp m e = e.
  Proof.
    elim: e => //=.
    - move=> v Hdisj. rewrite SSAVS.Lemmas.disjoint_singleton_r in Hdisj.
      rewrite (TEKS.not_mem_key_set_find Hdisj). reflexivity.
    - move=> w op e IH Hdisj. rewrite (IH Hdisj). reflexivity.
    - move=> w op e1 IH1 e2 IH2 Hdisj. rewrite SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2]. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
    - move=> w e IH n Hdisj. rewrite (IH Hdisj). reflexivity.
    - move=> w e IH n Hdisj. rewrite (IH Hdisj). reflexivity.
  Qed.

  Lemma disjoint_subst_eexps m es :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (vars_eexps es) ->
    subst_eexps m es = es.
  Proof.
    elim: es => [| e es IH] //=. move=> Hdisj.
    rewrite SSAVS.Lemmas.disjoint_union_r in Hdisj. move/andP: Hdisj => [Hdisj1 Hdisj2].
    rewrite subst_eexps_cons. rewrite (disjoint_subst_eexp Hdisj1) (IH Hdisj2).
    reflexivity.
  Qed.

  Lemma disjoint_subst_ebexp m e :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (vars_ebexp e) ->
    subst_ebexp m e = e.
  Proof.
    elim: e => //=.
    - move=> e1 e2 Hdisj. rewrite SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2].
      rewrite (disjoint_subst_eexp Hdisj1) (disjoint_subst_eexp Hdisj2).
      reflexivity.
    - move=> e1 e2 ms Hdisj. rewrite !SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 /andP [Hdisj2 Hdisj3]].
      rewrite (disjoint_subst_eexp Hdisj1) (disjoint_subst_eexp Hdisj2)
              (disjoint_subst_eexps Hdisj3).
      reflexivity.
    - move=> e1 IH1 e2 IH2 Hdisj. rewrite SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2]. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
  Qed.

  Lemma disjoint_subst_rbexp m e :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (vars_rbexp e) ->
    subst_rbexp m e = e.
  Proof.
    elim: e => //=.
    - move=> w e1 e2 Hdisj. rewrite SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2].
      rewrite (disjoint_subst_rexp Hdisj1) (disjoint_subst_rexp Hdisj2).
      reflexivity.
    - move=> w op e1 e2 Hdisj. rewrite !SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2].
      rewrite (disjoint_subst_rexp Hdisj1) (disjoint_subst_rexp Hdisj2).
      reflexivity.
    - move=> e IH Hdisj. rewrite (IH Hdisj). reflexivity.
    - move=> e1 IH1 e2 IH2 Hdisj. rewrite !SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2]. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
    - move=> e1 IH1 e2 IH2 Hdisj. rewrite !SSAVS.Lemmas.disjoint_union_r in Hdisj.
      move/andP: Hdisj => [Hdisj1 Hdisj2]. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
  Qed.

  Lemma disjoint_subst_bexp m e :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (vars_bexp e) ->
    subst_bexp m e = e.
  Proof.
    case: e => [e r]. rewrite /vars_bexp /subst_bexp /=.
    rewrite SSAVS.Lemmas.disjoint_union_r => /andP [Hdisj1 Hdisj2].
    rewrite (disjoint_subst_ebexp Hdisj1) (disjoint_subst_rbexp Hdisj2).
    reflexivity.
  Qed.

  Lemma disjoint_subst_atom m a :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (vars_atom a) ->
    subst_atom m a = a.
  Proof.
    case: a => //=. move=> v Hdisj. rewrite SSAVS.Lemmas.disjoint_singleton_r in Hdisj.
    rewrite (TEKS.not_mem_key_set_find Hdisj). reflexivity.
  Qed.

  Lemma disjoint_subst_instr m i :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (rvs_instr i) ->
    subst_instr m i = i.
  Proof.
    (case: i => //=); intros;
    repeat
      match goal with
      | H : is_true (SSAVS.Lemmas.disjoint _ (SSAVS.union _ _)) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          rewrite SSAVS.Lemmas.disjoint_union_r in H;
          move/andP: H => [H1 H2]
      | H : is_true (SSAVS.Lemmas.disjoint _ (vars_atom ?a)) |- context [subst_atom _ ?a] =>
          rewrite (disjoint_subst_atom H)
      | H : is_true (SSAVS.Lemmas.disjoint _ (vars_bexp ?e)) |- context [subst_bexp _ ?e] =>
          rewrite (disjoint_subst_bexp H)
      end; reflexivity.
  Qed.

  Lemma disjoint_subst_program m p :
    SSAVS.Lemmas.disjoint (TEKS.key_set m) (rvs_program p) ->
    subst_program m p = p.
  Proof.
    elim: p => [| i p IH] //=. rewrite SSAVS.Lemmas.disjoint_union_r.
    move/andP=> [Hdisj1 Hdisj2]. rewrite subst_program_cons.
    rewrite (disjoint_subst_instr Hdisj1) (IH Hdisj2). reflexivity.
  Qed.


  (* Unchanged evaluation *)

  Definition consistent_value (m : SSAVM.t atom) (s : SSAStore.t) : Prop :=
    forall x a, SSAVM.find x m = Some a -> SSAStore.acc x s = eval_atom a s.

  Definition consistent_type (m : SSAVM.t atom) (E : SSATE.env) : Prop :=
    forall x a, SSAVM.find x m = Some a ->
                is_defined x E
                /\ are_defined (vars_atom a) E
                /\ well_typed_atom E a
                /\ SSATE.vtyp x E = atyp a E.


  Lemma consistent_value_empty s : consistent_value (SSAVM.empty _) s.
  Proof.
    move=> x a Hx. rewrite SSAVM.Lemmas.empty_o in Hx. discriminate.
  Qed.

  Lemma consistent_value_upd E m s1 s2 v a :
    consistent_value m s1 ->
    consistent_type m E ->
    SSAStore.Upd v a s1 s2 ->
    ~~ SSAVS.mem v (vars_env E) ->
    consistent_value m s2.
  Proof.
    move=> Hco Hty Hupd Hnotin x ax Hx. move: (Hty _ _ Hx) => [Hdv [Hdav _]].
    case Hxv: (x == v).
    - move/eqP: Hxv => ?; subst. move/memdefP: Hdv => Hdv. move/memenvP: Hdv => Hdv.
      rewrite Hdv in Hnotin. discriminate.
    - move/idP/negP: Hxv => Hxv. rewrite (SSAStore.acc_Upd_neq Hxv Hupd).
      rewrite (Hco _ _ Hx). symmetry. apply: (Upd_disjoint_eval_atom Hupd).
      move/defsubP: Hdav => Hsub. move: (VSLemmas.not_mem_subset Hnotin Hsub).
      rewrite VSLemmas.disjoint_singleton_l. by apply.
  Qed.

  Lemma consistent_value_upd2 E m s1 s2 v1 a1 v2 a2 :
    consistent_value m s1 ->
    consistent_type m E ->
    SSAStore.Upd2 v1 a1 v2 a2 s1 s2 ->
    ~~ SSAVS.mem v1 (vars_env E) ->
    ~~ SSAVS.mem v2 (vars_env E) ->
    consistent_value m s2.
  Proof.
    move=> Hco Hty Hupd Hnotin1 Hnotin2 x ax Hx. move: (Hty _ _ Hx) => [Hdv [Hdav _]].
    case Hxv2: (x == v2).
    - move/eqP: Hxv2 => ?; subst. move/memdefP: Hdv => Hdv. move/memenvP: Hdv => Hdv.
      rewrite Hdv in Hnotin2. discriminate.
    - move/idP/negP: Hxv2 => Hxv2. case Hxv1: (x == v1).
      + move/eqP: Hxv1 => ?; subst. move/memdefP: Hdv => Hdv. move/memenvP: Hdv => Hdv.
        rewrite Hdv in Hnotin1. discriminate.
      + move/idP/negP: Hxv1 => Hxv1. rewrite (SSAStore.acc_Upd2_neq Hxv1 Hxv2 Hupd).
        rewrite (Hco _ _ Hx). move/defsubP: Hdav => Hsub. symmetry.
        apply: (Upd2_disjoint_eval_atom Hupd).
        * rewrite VSLemmas.disjoint_singleton_l.
          exact: (VSLemmas.not_mem_subset Hnotin1 Hsub).
        * rewrite VSLemmas.disjoint_singleton_l.
          exact: (VSLemmas.not_mem_subset Hnotin2 Hsub).
  Qed.

  Lemma consistent_add m v a s :
    SSAStore.acc v s = eval_atom a s ->
    consistent_value m s ->
    consistent_value (SSAVM.add v a m) s.
  Proof.
    move=> Hacc Hco x ax Hx. case Hxv: (x == v).
    - move/eqP: Hxv => ?; subst. rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx.
      case: Hx => ?; subst. assumption.
    - move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv) in Hx.
      rewrite (Hco _ _ Hx). reflexivity.
  Qed.

  Lemma consistent_value_add_upd E m v a bs s1 s2 :
    eval_atom a s2 = bs ->
    SSAStore.Upd v bs s1 s2 ->
    consistent_type m E ->
    ~~ SSAVS.mem v (vars_env E) ->
    consistent_value m s1 ->
    consistent_value (SSAVM.add v a m) s2.
  Proof.
    move=> Heva Hupd Hty Hnotin Hco x ax Hx. case Hxv: (x == v).
    - move/eqP: Hxv => ?; subst. rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx.
      case: Hx => ?; subst. rewrite (SSAStore.acc_Upd_eq (eqxx _) Hupd). reflexivity.
    - move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv) in Hx.
      move/negP: Hxv => Hxv. rewrite (SSAStore.acc_Upd_neq Hxv Hupd).
      rewrite (Hco _ _ Hx). symmetry. apply: (Upd_disjoint_eval_atom Hupd).
      rewrite VSLemmas.disjoint_singleton_l. apply/negP=> Hmem.
      apply/idP: Hnotin. apply: (VSLemmas.mem_subset Hmem).
      apply/defsubP. exact: (proj1 (proj2 (Hty _ _ Hx))).
  Qed.

  Lemma consistent_type_empty E : consistent_type (SSAVM.empty _) E.
  Proof.
    move=> x a Hx. rewrite SSAVM.Lemmas.empty_o in Hx. discriminate.
  Qed.

  Lemma consistent_type_subst_atom E m a :
    consistent_type m E ->
    atyp (subst_atom m a) E = atyp a E.
  Proof.
    move=> Hco. case: a => //=. move=> v. case Hv: (SSAVM.find v m) => //=.
    move: (proj2 (proj2 (proj2 (Hco _ _ Hv)))). symmetry. assumption.
  Qed.

  Lemma eval_eexp_of_atom E a s :
    eval_eexp (eexp_of_atom a) E s = bv2z (atyp a E) (eval_atom a s).
  Proof. by case: a => //=. Qed.

  Lemma eval_rexp_of_atom a s :
    eval_rexp (rexp_of_atom a) s = eval_atom a s.
  Proof. by case: a => //=. Qed.

  Lemma subst_eexp_eval_unchanged E m e s :
    consistent_value m s ->
    consistent_type m E ->
    eval_eexp (subst_eexp m e) E s = eval_eexp e E s.
  Proof.
    move=> Hev Hty. elim: e => //=.
    - move=> v. case Hv: (SSAVM.find v m).
      + rewrite eval_eexp_of_atom. rewrite /acc2z.
        rewrite (Hev _ _ Hv) (proj2 (proj2 (proj2 (Hty _ _ Hv)))). reflexivity.
      + reflexivity.
    - move=> op e IH. rewrite IH. reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> e IH n. rewrite IH. reflexivity.
  Qed.

  Lemma subst_rexp_eval_unchanged m e s :
    consistent_value m s ->
    eval_rexp (subst_rexp m e) s = eval_rexp e s.
  Proof.
    move=> Hev. elim: e => //=.
    - move=> v. case Hv: (SSAVM.find v m).
      + rewrite eval_rexp_of_atom. rewrite /acc2z.
        rewrite (Hev _ _ Hv). reflexivity.
      + reflexivity.
    - move=> _ op e IH. rewrite IH. reflexivity.
    - move=> _ op e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> _ e IH n. rewrite IH. reflexivity.
    - move=> _ e IH n. rewrite IH. reflexivity.
  Qed.

  Lemma subst_eexps_eval_unchanged E m es s :
    consistent_value m s ->
    consistent_type m E ->
    eval_eexps (subst_eexps m es) E s = eval_eexps es E s.
  Proof.
    move=> Hev Hty. elim: es => [| e es IH] //=. rewrite subst_eexps_cons /=.
    rewrite (subst_eexp_eval_unchanged _ Hev Hty) IH. reflexivity.
  Qed.

  Lemma subst_ebexp_eval_unchanged E m e s :
    consistent_value m s ->
    consistent_type m E ->
    eval_ebexp (subst_ebexp m e) E s <-> eval_ebexp e E s.
  Proof.
    move=> Hev Hty. elim: e => //=.
    - move=> e1 e2. rewrite !(subst_eexp_eval_unchanged _ Hev Hty). tauto.
    - move=> e1 e2 ms. rewrite !(subst_eexp_eval_unchanged _ Hev Hty)
                               (subst_eexps_eval_unchanged _ Hev Hty). tauto.
    - move=> e1 IH1 e2 IH2. tauto.
  Qed.

  Lemma subst_rbexp_eval_unchanged m e s :
    consistent_value m s ->
    eval_rbexp (subst_rbexp m e) s = eval_rbexp e s.
  Proof.
    move=> Hev. elim: e => //=.
    - move=> _ e1 e2. rewrite !(subst_rexp_eval_unchanged _ Hev). reflexivity.
    - move=> _ op e1 e2. rewrite !(subst_rexp_eval_unchanged _ Hev). reflexivity.
    - move=> e IH. rewrite IH. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
  Qed.

  Lemma subst_bexp_eval_unchanged E m e s :
    consistent_value m s ->
    consistent_type m E ->
    eval_bexp (subst_bexp m e) E s <-> eval_bexp e E s.
  Proof.
    move=> Hev Hty. case: e => [e r] /=. rewrite /subst_bexp /eval_bexp /=.
    rewrite (subst_ebexp_eval_unchanged _ Hev Hty) (subst_rbexp_eval_unchanged _ Hev).
    tauto.
  Qed.

  Global Instance add_proper_consistent_value_map :
    Proper (SSAVM.Equal ==> eq ==> iff) consistent_value.
  Proof.
    move=> m1 m2 Heq s1 s2 ?; subst. split => Hco x a Hx.
    - rewrite -Heq in Hx. exact: (Hco _ _ Hx).
    - rewrite Heq in Hx. exact: (Hco _ _ Hx).
  Qed.

  Global Instance add_proper_consistent_value_store :
    Proper (eq ==> SSAStore.Equal ==> iff) consistent_value.
  Proof.
    move=> m1 m2 ? s1 s2 Heq; subst. split => Hco x a Hx.
    - move: (Hco _ _ Hx). rewrite Heq. by apply.
    - move: (Hco _ _ Hx). rewrite Heq. by apply.
  Qed.

  Global Instance add_proper_consistent_type_map :
    Proper (SSAVM.Equal ==> eq ==> iff) consistent_type.
  Proof.
    move=> m1 m2 Heq s1 s2 ?; subst. split => Hco x a Hx.
    - rewrite -Heq in Hx. exact: (Hco _ _ Hx).
    - rewrite Heq in Hx. exact: (Hco _ _ Hx).
  Qed.

  Global Instance add_proper_consistent_type_env :
    Proper (eq ==> SSATE.Equal ==> iff) consistent_type.
  Proof.
    move=> m1 m2 ? E1 E2 Heq; subst. split => Hco x a Hx.
    - move: (Hco _ _ Hx). rewrite Heq. tauto.
    - move: (Hco _ _ Hx). rewrite Heq. tauto.
  Qed.


  (* Well-formedness *)

  Lemma consistent_type_size_of_subst_rexp E m e :
    consistent_type m E ->
    well_formed_rexp E e ->
    size_of_rexp (subst_rexp m e) E = size_of_rexp e E.
  Proof.
    move=> Hco. elim: e => //=. move=> v. rewrite /well_formed_rexp /=.
    rewrite are_defined_singleton => /andP [Hdv Hsv].
    dcase (SSAVM.find v m); case.
    - move=> a. case: a => /=.
      + move=> u Hv. move: (Hco _ _ Hv) => [_ [_ [_ H]]].
        rewrite 2!SSATE.vtyp_vsize. rewrite H. reflexivity.
      + move=> ty bs Hv. move: (Hco _ _ Hv) => [_ [_ [_ H]]].
        rewrite SSATE.vtyp_vsize H. reflexivity.
    - move=> Hv. rewrite /size_of_rexp /=. reflexivity.
  Qed.

  Lemma disjoint_well_formed_eexp E m e :
    VSLemmas.disjoint (vars_eexp e) (TEKS.key_set m) ->
    well_formed_eexp E (subst_eexp m e) = well_formed_eexp E e.
  Proof.
    elim: e => //=.
    - move=> v Hdisj. rewrite VSLemmas.disjoint_singleton_l in Hdisj.
      rewrite (TEKS.not_mem_key_set_find Hdisj). reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l.
      move/andP=> [Hdisj1 Hdisj2]. rewrite /ebinary.
      rewrite !well_formed_eexp_ebinopb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
  Qed.

  Lemma consistent_type_disjoint_well_formed_rexp E m e :
    consistent_type m E ->
    VSLemmas.disjoint (vars_rexp e) (TEKS.key_set m) ->
    well_formed_rexp E (subst_rexp m e) = well_formed_rexp E e.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> v Hdisj. rewrite VSLemmas.disjoint_singleton_l in Hdisj.
      rewrite (TEKS.not_mem_key_set_find Hdisj). reflexivity.
    - move=> w op e IH Hdisj. rewrite /runary.
      rewrite !well_formed_rexp_runopb. rewrite (IH Hdisj).
      case Hwf: (well_formed_rexp E e) => //=.
      rewrite (consistent_type_size_of_subst_rexp Hco Hwf). reflexivity.
    - move=> w op e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l.
      move/andP=> [Hdisj1 Hdisj2]. rewrite /rbinary.
      rewrite !well_formed_rexp_rbinopb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=.
      case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (consistent_type_size_of_subst_rexp Hco Hwf1)
              (consistent_type_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> w e IH n Hdisj. rewrite /ruext. rewrite 2!well_formed_rexp_ruextb /=.
      rewrite (IH Hdisj). case Hwf: (well_formed_rexp E e) => //=.
      rewrite (consistent_type_size_of_subst_rexp Hco Hwf). reflexivity.
    - move=> w e IH n Hdisj. rewrite /rsext. rewrite 2!well_formed_rexp_rsextb /=.
      rewrite (IH Hdisj). case Hwf: (well_formed_rexp E e) => //=.
      rewrite (consistent_type_size_of_subst_rexp Hco Hwf). reflexivity.
  Qed.

  Lemma disjoint_well_formed_eexps E m es :
    VSLemmas.disjoint (vars_eexps es) (TEKS.key_set m) ->
    well_formed_eexps E (subst_eexps m es) = well_formed_eexps E es.
  Proof.
    elim: es => [| e es IH] //=. rewrite VSLemmas.disjoint_union_l.
    move/andP => [Hdisje Hdisjes]. rewrite subst_eexps_cons /=.
    rewrite (disjoint_well_formed_eexp _ Hdisje) (IH Hdisjes). reflexivity.
  Qed.

  Lemma disjoint_well_formed_ebexp E m e :
    VSLemmas.disjoint (vars_ebexp e) (TEKS.key_set m) ->
    well_formed_ebexp E (subst_ebexp m e) = well_formed_ebexp E e.
  Proof.
    elim: e => //=.
    - move=> e1 e2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite !well_formed_ebexp_eeqb.
      rewrite (disjoint_well_formed_eexp _ Hdisj1) (disjoint_well_formed_eexp _ Hdisj2).
      reflexivity.
    - move=> e1 e2 ms. rewrite 2!VSLemmas.disjoint_union_l => /andP [Hdisj1 /andP [Hdisj2 Hdisjms]].
      rewrite !well_formed_ebexp_eeqmodb.
      rewrite (disjoint_well_formed_eexp _ Hdisj1) (disjoint_well_formed_eexp _ Hdisj2)
              (disjoint_well_formed_eexps _ Hdisjms).
      reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l.
      move/andP=> [Hdisj1 Hdisj2]. rewrite 2!well_formed_ebexp_eandb.
      rewrite (IH1 Hdisj1) (IH2 Hdisj2). reflexivity.
  Qed.

  Lemma consistent_type_disjoint_well_formed_rbexp E m e :
    consistent_type m E ->
    VSLemmas.disjoint (vars_rbexp e) (TEKS.key_set m) ->
    well_formed_rbexp E (subst_rbexp m e) = well_formed_rbexp E e.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> w e1 e2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_reqb.
      rewrite (consistent_type_disjoint_well_formed_rexp Hco Hdisj1)
              (consistent_type_disjoint_well_formed_rexp Hco Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=. case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (consistent_type_size_of_subst_rexp Hco Hwf1)
              (consistent_type_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> w op e1 e2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_rcmpb.
      rewrite (consistent_type_disjoint_well_formed_rexp Hco Hdisj1)
              (consistent_type_disjoint_well_formed_rexp Hco Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=. case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (consistent_type_size_of_subst_rexp Hco Hwf1)
              (consistent_type_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_randb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_rorb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
  Qed.

  Lemma disjoint_well_formed_bexp E m e :
    consistent_type m E ->
    VSLemmas.disjoint (vars_bexp e) (TEKS.key_set m) ->
    well_formed_bexp E (subst_bexp m e) = well_formed_bexp E e.
  Proof.
    move=> Hco. case: e => [e r]. rewrite /vars_bexp /=.
    rewrite VSLemmas.disjoint_union_l => /andP [Hdisje Hdisjr].
    rewrite /subst_bexp 2!well_formed_bexp_split /=.
    rewrite (disjoint_well_formed_ebexp _ Hdisje)
            (consistent_type_disjoint_well_formed_rbexp Hco Hdisjr).
    reflexivity.
  Qed.

End VarSubst.


(** ** Properties of rewriting mov statements *)

Section RewriteMov.

  Import SSA.

  Lemma subst_map_program_rec_cons m i p :
    subst_map_program_rec m (i::p) = subst_map_program_rec (subst_map_instr m i) p.
  Proof. reflexivity. Qed.

  Lemma subst_map_program_rec_rcons m p i :
    subst_map_program_rec m (rcons p i) = subst_map_instr (subst_map_program_rec m p) i.
  Proof. by elim: p m i => [| j p IH] m i //=. Qed.

  Lemma subst_map_program_rec_cat m p1 p2 :
    subst_map_program_rec m (p1 ++ p2) = subst_map_program_rec (subst_map_program_rec m p1) p2.
  Proof. by elim: p1 m p2 => [| i1 p1 IH1] m p2 //=. Qed.

  Lemma subst_map_instr_unchanged_find x m i :
    ssa_vars_unchanged_instr (SSAVS.singleton x) i ->
    SSAVM.find x (subst_map_instr m i) = SSAVM.find x m.
  Proof.
    (case i => //=). move=> v a Hun.
    rewrite ssa_unchanged_instr_disjoint_lvs /= in Hun.
    rewrite VSLemmas.disjoint_singleton_l in Hun.
    move: (VSLemmas.not_mem_singleton1 Hun) => {Hun}Hne.
    case: a => [ u | ty bs ] //=.
    - case Hu: (SSAVM.find u m).
      + rewrite (SSAVM.Lemmas.find_add_neq Hne). reflexivity.
      + rewrite (SSAVM.Lemmas.find_add_neq Hne). reflexivity.
    - rewrite (SSAVM.Lemmas.find_add_neq Hne). reflexivity.
  Qed.

  Lemma subst_map_program_rec_unchanged_find x m p :
    ssa_vars_unchanged_program (SSAVS.singleton x) p ->
    SSAVM.find x (subst_map_program_rec m p) = SSAVM.find x m.
  Proof.
    elim: p m => [| i p IH] m //=. move=> Hun.
    rewrite (IH _ (ssa_unchanged_program_tl Hun)).
    exact: (subst_map_instr_unchanged_find _ (ssa_unchanged_program_hd Hun)).
  Qed.


  (* Variables of subst_map_instr and subst_map_program *)

  Lemma subst_map_instr_keys_subset m i :
    SSAVS.subset (SSA.TEKS.key_set (subst_map_instr m i))
                 (SSAVS.union (SSA.TEKS.key_set m) (lvs_instr i)).
  Proof.
    (case: i => //=); intros;
    repeat
      match goal with
      | |- context [match ?a with | Avar _ => _ | Aconst _ _ => _ end] =>
          case: a; simpl; intros
      | |- context [match SSAVM.find ?v ?m with | Some _ => _ | None => _ end] =>
          case: (SSAVM.find v m); simpl; intros
      | |- context [TEKS.key_set (SSAVM.add ?v ?a ?m)] =>
          rewrite TEKS.key_set_add /=
      end; by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma subst_map_program_rec_keys_subset m p :
    SSAVS.subset (SSA.TEKS.key_set (subst_map_program_rec m p))
                 (SSAVS.union (SSA.TEKS.key_set m) (lvs_program p)).
  Proof.
    elim: p m => [| i p IH] m //=.
    - by SSAVS.Lemmas.dp_subset.
    - move: (IH (subst_map_instr m i)) => Hsub1.
      move: (subst_map_instr_keys_subset m i) => Hsub2.
      move: (VSLemmas.union_subsets Hsub2 (SSAVS.Lemmas.subset_refl (lvs_program p))) => {}Hsub2.
      apply: (SSAVS.Lemmas.subset_trans Hsub1).
      apply: (SSAVS.Lemmas.subset_trans Hsub2).
      by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma subst_map_program_keys_subset p :
    SSAVS.subset (SSA.TEKS.key_set (subst_map_program p))
                 (lvs_program p).
  Proof.
    apply: (SSAVS.Lemmas.subset_trans (subst_map_program_rec_keys_subset _ _)).
    rewrite TEKS.key_set_empty. by SSAVS.Lemmas.dp_subset.
  Qed.

  Lemma subst_map_program_keys_disjoint E p :
    well_formed_ssa_program E p ->
    VSLemmas.disjoint (TEKS.key_set (subst_map_program p)) (vars_env E).
  Proof.
    move=> Hwf.
    apply: (VSLemmas.disjoint_subset_l _ (subst_map_program_keys_subset p)).
    rewrite VSLemmas.disjoint_sym. rewrite -ssa_unchanged_program_disjoint_lvs.
    exact: (well_formed_ssa_unchanged_env Hwf).
  Qed.


  (* Unchanged substitution *)

  Lemma subst_map_instr_find_unchanged m v i :
    ssa_vars_unchanged_instr (SSAVS.singleton v) i ->
    SSAVM.find v (subst_map_instr m i) = SSAVM.find v m.
  Proof.
    rewrite /subst_map_instr. (case: i => //=).
    move=> u a. (case: a => //=).
    - move=> x Hun. rewrite ssa_unchanged_instr_disjoint_lvs /= in Hun.
      rewrite VSLemmas.disjoint_singleton in Hun.
      move: (VSLemmas.not_mem_singleton1 Hun) => {Hun} Hne.
      case Hx: (SSAVM.find x m).
      + rewrite SSAVM.Lemmas.find_add_neq; first reflexivity.
        move=> Heq. apply: Hne. symmetry. assumption.
      + rewrite SSAVM.Lemmas.find_add_neq; first reflexivity.
        move=> Heq. apply: Hne. symmetry. assumption.
    - move=> ty bs Hun. rewrite ssa_unchanged_instr_disjoint_lvs /= in Hun.
      rewrite VSLemmas.disjoint_singleton in Hun.
      move: (VSLemmas.not_mem_singleton1 Hun) => {Hun} Hne.
      rewrite SSAVM.Lemmas.find_add_neq; first reflexivity.
      move=> Heq. apply: Hne. symmetry. assumption.
  Qed.

  Lemma subst_eexp_subst_map_instr_unchanged m e i :
    ssa_vars_unchanged_instr (vars_eexp e) i ->
    subst_eexp (subst_map_instr m i) e = subst_eexp m e.
  Proof.
    elim: e => //=.
    - move=> v Hun. rewrite (subst_map_instr_find_unchanged _ Hun).
      reflexivity.
    - move=> op e IH Hun. rewrite (IH Hun). reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (IH1 Hun1) (IH2 Hun2). reflexivity.
    - move=> e IH n Hun. rewrite (IH Hun). reflexivity.
  Qed.

  Lemma subst_rexp_subst_map_instr_unchanged m e i :
    ssa_vars_unchanged_instr (vars_rexp e) i ->
    subst_rexp (subst_map_instr m i) e = subst_rexp m e.
  Proof.
    elim: e => //=.
    - move=> v Hun. rewrite (subst_map_instr_find_unchanged _ Hun).
      reflexivity.
    - move=> w op e IH Hun. rewrite (IH Hun). reflexivity.
    - move=> w op e1 IH1 e2 IH2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (IH1 Hun1) (IH2 Hun2). reflexivity.
    - move=> w e IH n Hun. rewrite (IH Hun). reflexivity.
    - move=> w e IH n Hun. rewrite (IH Hun). reflexivity.
  Qed.

  Lemma subst_eexps_subst_map_instr_unchanged m es i :
    ssa_vars_unchanged_instr (vars_eexps es) i ->
    subst_eexps (subst_map_instr m i) es = subst_eexps m es.
  Proof.
    elim: es => [| e es IH] //=. rewrite !subst_eexps_cons.
    rewrite ssa_unchanged_instr_union. move/andP => [Hun1 Hun2].
    rewrite (subst_eexp_subst_map_instr_unchanged _ Hun1) (IH Hun2). reflexivity.
  Qed.

  Lemma subst_ebexp_subst_map_instr_unchanged m e i :
    ssa_vars_unchanged_instr (vars_ebexp e) i ->
    subst_ebexp (subst_map_instr m i) e = subst_ebexp m e.
  Proof.
    elim: e => //=.
    - move=> e1 e2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (subst_eexp_subst_map_instr_unchanged _ Hun1)
                                        (subst_eexp_subst_map_instr_unchanged _ Hun2).
      reflexivity.
    - move=> e1 e2 ms. rewrite !ssa_unchanged_instr_union.
      move/andP => [Hun1 /andP [Hun2 Hun3]].
      rewrite (subst_eexp_subst_map_instr_unchanged _ Hun1)
              (subst_eexp_subst_map_instr_unchanged _ Hun2)
              (subst_eexps_subst_map_instr_unchanged _ Hun3).
      reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (IH1 Hun1) (IH2 Hun2). reflexivity.
  Qed.

  Lemma subst_rbexp_subst_map_instr_unchanged m e i :
    ssa_vars_unchanged_instr (vars_rbexp e) i ->
    subst_rbexp (subst_map_instr m i) e = subst_rbexp m e.
  Proof.
    elim: e => //=.
    - move=> w e1 e2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (subst_rexp_subst_map_instr_unchanged _ Hun1)
                                        (subst_rexp_subst_map_instr_unchanged _ Hun2).
      reflexivity.
    - move=> w op e1 e2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (subst_rexp_subst_map_instr_unchanged _ Hun1)
                                        (subst_rexp_subst_map_instr_unchanged _ Hun2).
      reflexivity.
    - move=> e IH Hun. rewrite (IH Hun). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (IH1 Hun1) (IH2 Hun2). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite ssa_unchanged_instr_union.
      move/andP => [Hun1 Hun2]. rewrite (IH1 Hun1) (IH2 Hun2). reflexivity.
  Qed.

  Lemma subst_bexp_subst_map_instr_unchanged m e i :
    ssa_vars_unchanged_instr (vars_bexp e) i ->
    subst_bexp (subst_map_instr m i) e = subst_bexp m e.
  Proof.
    case: e => [e r]. rewrite /vars_bexp /subst_bexp /=.
    rewrite ssa_unchanged_instr_union. move/andP => [Hun1 Hun2].
    rewrite (subst_ebexp_subst_map_instr_unchanged _ Hun1)
            (subst_rbexp_subst_map_instr_unchanged _ Hun2).
    reflexivity.
  Qed.

  Lemma subst_atom_subst_map_instr_unchanged m a i :
    ssa_vars_unchanged_instr (vars_atom a) i ->
    subst_atom (subst_map_instr m i) a = subst_atom m a.
  Proof.
    case: a => //=. move=> v Hun.
    rewrite (subst_map_instr_find_unchanged _ Hun). reflexivity.
  Qed.

  Lemma subst_instr_subst_map_instr_unchanged m i j :
    ssa_vars_unchanged_instr (rvs_instr i) j ->
    subst_instr (subst_map_instr m j) i = subst_instr m i.
  Proof.
    (case: i => //=); intros;
      by repeat match goal with
                | H : is_true (ssa_vars_unchanged_instr (SSAVS.union _ _) _) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    rewrite ssa_unchanged_instr_union in H;
                    move/andP: H => [H1 H2]
                | H : is_true (ssa_vars_unchanged_instr (vars_atom ?a) ?j)
                  |- context [subst_atom (subst_map_instr ?m ?j) ?a] =>
                    rewrite (subst_atom_subst_map_instr_unchanged _ H)
                | H : is_true (ssa_vars_unchanged_instr (vars_bexp ?a) ?j)
                  |- context [subst_bexp (subst_map_instr ?m ?j) ?a] =>
                    rewrite (subst_bexp_subst_map_instr_unchanged _ H)
                | |- ?e = ?e => reflexivity
                end.
  Qed.

  Lemma subst_instr_subst_map_program_rec_unchanged m i p :
    ssa_vars_unchanged_program (rvs_instr i) p ->
    subst_instr (subst_map_program_rec m p) i = subst_instr m i.
  Proof.
    elim: p i m => [| j p IH] i m //=. rewrite ssa_unchanged_program_cons.
    move/andP => [Hunj Hunp]. rewrite (IH _ _ Hunp).
    exact: (subst_instr_subst_map_instr_unchanged _ Hunj).
  Qed.


  (* consistent_type after subst_map_instr or subst_map_program *)

  Lemma subst_map_instr_consistent_type E m i :
    well_formed_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    consistent_type m E ->
    consistent_type (subst_map_instr m i) (instr_succ_typenv i E).
  Proof.
    (case: i => //=); intros;
    repeat match goal with
           | H : is_true (well_formed_instr _ _) |- _ =>
               rewrite /well_formed_instr /= in H
           | H : is_true (_ && _) |- _ =>
               let H1 := fresh in
               let H2 := fresh in
               move/andP: H => [H1 H2]
           | H : is_true (ssa_vars_unchanged_instr _ _) |- _ =>
               rewrite ssa_unchanged_instr_disjoint_lvs /= in H
           | H : is_true (VSLemmas.disjoint _ (SSAVS.singleton _)) |- _ =>
               rewrite VSLemmas.disjoint_singleton_r in H
           | H : is_true (VSLemmas.disjoint _ (SSAVS.add _ _)) |- _ =>
               let H1 := fresh in
               let H2 := fresh in
               (rewrite VSLemmas.disjoint_add_r /= in H);
               move/andP: H => [H1 H2]
           | H1 : consistent_type ?m ?E,
               H0 : is_true (~~ SSAVS.mem ?t (vars_env ?E)) |-
               consistent_type ?m (SSATE.add ?t _ ?E) =>
               (move => x ax Hx); simpl; (move: (H1 _ _ Hx) => [Hdefx [Hdefax [Hsmax Htyx]]]); repeat split;
               [ by rewrite is_defined_add Hdefx orbT
               | apply: are_defined_addr; exact: Hdefax
               | (rewrite well_typed_atom_notin_add; first assumption);
                 apply: (VSLemmas.not_mem_subset H0);
                 move/defsubP: Hdefax; by apply
               | rewrite is_defined_mem_vars_env in Hdefx;
                 (have Hxt: x != t
                   by apply/negP => /eqP ?; subst; rewrite Hdefx in H0; discriminate);
                 rewrite (SSATE.vtyp_add_neq Hxt) Htyx;
                 rewrite atyp_add_not_mem; first reflexivity;
                 (apply/negP => Hmemt); (move/negP: H0; apply);
                 (move/defsubP: Hdefax => Hsub); exact: (VSLemmas.mem_subset Hmemt Hsub) ]
           | H1 : consistent_type ?m ?E,
               H : is_true (~~ SSAVS.mem ?t (vars_env ?E)),
                 H10 : is_true (~~ SSAVS.mem ?t0 (vars_env ?E)) |-
               consistent_type ?m (SSATE.add ?t _ (SSATE.add ?t0 _ ?E)) =>
               (move => x ax Hx); simpl; (move: (H1 _ _ Hx) => [Hdefx [Hdefax [Hsmax Htyx]]]); repeat split;
               [ by rewrite !is_defined_add Hdefx !orbT
               | repeat apply: are_defined_addr; exact: Hdefax
               | (rewrite well_typed_atom_notin_add;
                  last by (apply: (VSLemmas.not_mem_subset H); move/defsubP: Hdefax; apply));
                 (rewrite well_typed_atom_notin_add;
                  last by (apply: (VSLemmas.not_mem_subset H10); move/defsubP: Hdefax; apply));
                 assumption
               | rewrite is_defined_mem_vars_env in Hdefx;
                 (have Hxt: x != t
                   by apply/negP => /eqP ?; subst; rewrite Hdefx in H; discriminate);
                 (have Hxt0: x != t0
                   by apply/negP => /eqP ?; subst; rewrite Hdefx in H10; discriminate);
                 rewrite (SSATE.vtyp_add_neq Hxt) (SSATE.vtyp_add_neq Hxt0) Htyx;
                 rewrite atyp_add_not_mem; [ rewrite atyp_add_not_mem |]; first reflexivity;
                 [ (apply/negP => Hmemt); (move/negP: H10; apply);
                   (move/defsubP: Hdefax => Hsub); exact: (VSLemmas.mem_subset Hmemt Hsub)
                 | (apply/negP => Hmemt); (move/negP: H; apply);
                   (move/defsubP: Hdefax => Hsub); exact: (VSLemmas.mem_subset Hmemt Hsub) ] ]
           end.
    (* Imov *)
    move: H0 H1 H2 H3 => Hmemt Hty Hdefa Hwta.
    case: a Hdefa Hwta => //=.
    - move=> v Hdefv Hwtv. case Hvm: (SSAVM.find v m).
      + move=> x ax Hx. move: (Hty _ _ Hvm) => [Hdefv' [Hdefa [Hwta Htyv]]].
        case Hxt: (x == t).
        * move/eqP: Hxt => ?; subst.
          rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
          repeat split.
          -- by rewrite is_defined_add eqxx.
          -- repeat apply: are_defined_addr. exact: Hdefa.
          -- rewrite well_typed_atom_notin_add; first assumption.
             apply: (VSLemmas.not_mem_subset Hmemt). move/defsubP: Hdefa. by apply.
          -- rewrite (SSATE.vtyp_add_eq (eqxx _)). rewrite atyp_add_not_mem; first exact: Htyv.
             apply/negP=> Hmem. move/negP: Hmemt; apply. move/defsubP: Hdefa => Hsub.
             exact: (VSLemmas.mem_subset Hmem Hsub).
        * move/negP: Hxt => Hxt. rewrite (SSAVM.Lemmas.find_add_neq Hxt) in Hx.
          move: (Hty _ _ Hx) => [Hdefx [Hdefax [Hwtax Htyx]]]. repeat split.
          -- by rewrite !is_defined_add Hdefx !orbT.
          -- repeat apply: are_defined_addr; exact: Hdefax.
          -- rewrite well_typed_atom_notin_add; first assumption.
             apply: (VSLemmas.not_mem_subset Hmemt). move/defsubP: Hdefax. by apply.
          -- move/negP: Hxt => Hxt. rewrite (SSATE.vtyp_add_neq Hxt).
             rewrite atyp_add_not_mem; first exact: Htyx.
             apply/negP=> Hmem. move/negP: Hmemt; apply. move/defsubP: Hdefax => Hsub.
             exact: (VSLemmas.mem_subset Hmem Hsub).
      + move=> x ax Hx. case Hxt: (x == t).
        * move/eqP: Hxt => ?; subst; simpl.
          rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst; simpl.
          repeat split.
          -- by rewrite is_defined_add eqxx.
          -- repeat apply: are_defined_addr. exact: Hdefv.
          -- rewrite well_typed_atom_notin_add; first assumption.
             apply: (VSLemmas.not_mem_subset Hmemt). move/defsubP: Hdefv. by apply.
          -- rewrite (SSATE.vtyp_add_eq (eqxx _)). rewrite SSATE.vtyp_add_neq; first reflexivity.
             apply/negP=> /eqP ?; subst. rewrite are_defined_singleton in Hdefv.
             move/memdefP: Hdefv => Hmem. rewrite mem_vars_env Hmem in Hmemt. discriminate.
        * move/negP: Hxt => Hxt. rewrite (SSAVM.Lemmas.find_add_neq Hxt) in Hx.
          move: (Hty _ _ Hx) => [Hdefx [Hdefax [Hsmax Htyx]]]. repeat split.
          -- by rewrite !is_defined_add Hdefx !orbT.
          -- repeat apply: are_defined_addr; exact: Hdefax.
          -- rewrite well_typed_atom_notin_add; first assumption.
             apply: (VSLemmas.not_mem_subset Hmemt). move/defsubP: Hdefax. by apply.
          -- move/negP: Hxt => Hxt. rewrite (SSATE.vtyp_add_neq Hxt).
             rewrite atyp_add_not_mem; first exact: Htyx.
             apply/negP=> Hmem. move/negP: Hmemt; apply. move/defsubP: Hdefax => Hsub.
             exact: (VSLemmas.mem_subset Hmem Hsub).
    - move=> ty bs _ Hwf. move=> x ax Hx. case Hxt: (x == t).
      + move/eqP: Hxt => ?; subst.
        rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
        repeat split.
        * by rewrite is_defined_add eqxx.
        * exact: Hwf.
        * rewrite (SSATE.vtyp_add_eq (eqxx _)). reflexivity.
      + move/negP: Hxt => Hxt. rewrite (SSAVM.Lemmas.find_add_neq Hxt) in Hx.
        move: (Hty _ _ Hx) => [Hdefx [Hdefax [Hsmax Htyx]]]. repeat split.
        * by rewrite !is_defined_add Hdefx !orbT.
        * repeat apply: are_defined_addr; exact: Hdefax.
        * rewrite well_typed_atom_notin_add; first assumption.
          apply: (VSLemmas.not_mem_subset Hmemt). move/defsubP: Hdefax. by apply.
        * move/negP: Hxt => Hxt. rewrite (SSATE.vtyp_add_neq Hxt).
          rewrite atyp_add_not_mem; first exact: Htyx.
          apply/negP=> Hmem. move/negP: Hmemt; apply. move/defsubP: Hdefax => Hsub.
          exact: (VSLemmas.mem_subset Hmem Hsub).
  Qed.

  Lemma subst_map_program_rec_consistent_type E p m :
    well_formed_ssa_program E p ->
    consistent_type m E ->
    consistent_type (subst_map_program_rec m p) (program_succ_typenv p E).
  Proof.
    elim: p E m => [| i p IH] E m //=. move=> Hwf Hty.
    apply: (IH _ _ (well_formed_ssa_tl Hwf)) => {IH}.
    exact: (subst_map_instr_consistent_type
              (well_formed_ssa_hd Hwf)
              (well_formed_ssa_unchanged_env_hd Hwf) Hty).
  Qed.

  Lemma subst_map_program_consistent_type E p :
    well_formed_ssa_program E p ->
    consistent_type (subst_map_program p) (program_succ_typenv p E).
  Proof.
    move=> Hwf. exact: (subst_map_program_rec_consistent_type Hwf (consistent_type_empty _)).
  Qed.


  (* Typing environments after subst_instr or subst_program *)

  Lemma consistent_type_instr_succ_typenv E m i :
    consistent_type m E ->
    SSATE.Equal (instr_succ_typenv (subst_instr m i) E)
                (instr_succ_typenv i E).
  Proof.
    move=> Hco.
    (case: i => //=); intros;
      by repeat match goal with
                | |- SSATE.Equal _ _ => move=> x
                | |- context [SSAVM.find ?x (SSATE.add ?t _ _)] =>
                    let Hxt := fresh in
                    dcase (x == t); case; intro Hxt;
                    [ (move/eqP: Hxt => ?); subst; rewrite !(SSATE.Lemmas.find_add_eq (eqxx _))
                    | (move/negP: Hxt => Hxt); rewrite !(SSATE.Lemmas.find_add_neq Hxt) ]
                | Hco : consistent_type ?m ?E
                  |- context [atyp (subst_atom ?m ?a) ?E] =>
                    rewrite (consistent_type_subst_atom _ Hco)
                | |- ?e = ?e => reflexivity
                end.
  Qed.

  Lemma subst_map_program_succ_typenv E p :
    well_formed_ssa_program E p ->
    SSATE.Equal (program_succ_typenv (subst_program (subst_map_program p) p) E)
                (program_succ_typenv p E).
  Proof.
    move=> Hwf. rewrite /subst_map_program.
    move: (consistent_type_empty E). move: (SSAVM.empty atom).
    elim: p E Hwf => [| i p IH] E Hwf m Hty //=. rewrite subst_program_cons /=.
    have ->: (subst_instr (subst_map_program_rec (subst_map_instr m i) p) i) =
           (subst_instr m i).
    { move: (well_formed_ssa_vars_unchanged_hd Hwf) => Hun.
      move: (ssa_unchanged_program_subset Hun (rvs_instr_subset i)) => {}Hun.
      rewrite (subst_instr_subst_map_program_rec_unchanged _ Hun).
      apply: subst_instr_subst_map_instr_unchanged.
      exact: (well_formed_ssa_lvs_unchanged_hd Hwf). }
    rewrite (consistent_type_instr_succ_typenv _ Hty). apply: (IH _ (well_formed_ssa_tl Hwf)).
    exact: (subst_map_instr_consistent_type
              (well_formed_ssa_hd Hwf)
              (well_formed_ssa_unchanged_env_hd Hwf) Hty).
  Qed.

  Lemma rewrite_mov_succ_typenv s :
    well_formed_ssa_spec s ->
    SSATE.Equal
             (program_succ_typenv (sprog (rewrite_mov s)) (sinputs (rewrite_mov s)))
             (program_succ_typenv (sprog s) (sinputs s)).
  Proof.
    move=> Hwf. apply: (subst_map_program_succ_typenv (well_formed_ssa_spec_program Hwf)).
  Qed.


  (* Consistent evaluation after subst_map_instr or subst_map_program *)

  Lemma subst_map_instr_consistent_value E i m s1 s2 :
    consistent_type m E ->
    consistent_value m s1 ->
    eval_instr E i (OK s1) (OK s2) ->
    well_formed_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    consistent_value (subst_map_instr m i) s2.
  Proof.
    (move=> Hty Hco Hevi). inversion_clear Hevi; simpl; intros;
      repeat match goal with
             | H : is_true (ssa_vars_unchanged_instr _ _) |- _ =>
                 rewrite ssa_unchanged_instr_disjoint_lvs /= in H
             | H : is_true (VSLemmas.disjoint _ (SSAVS.singleton _)) |- _ =>
                 rewrite VSLemmas.disjoint_singleton_r in H
             | H : is_true (VSLemmas.disjoint _ (SSAVS.add _ _)) |- _ =>
                 let H1 := fresh in
                 let H2 := fresh in
                 rewrite VSLemmas.disjoint_add_r in H;
                 move/andP: H => [H1 H2]
             | Hty : consistent_type ?m ?E,
                 Hco : consistent_value ?m ?s1,
                   Hupd : SSAStore.Upd ?v _ ?s1 ?s2,
                     Hnotin : is_true (~~ SSAVS.mem ?v (vars_env ?E))
               |- consistent_value ?m ?s2 =>
                 apply: (consistent_value_upd Hco Hty Hupd Hnotin)
             | Hty : consistent_type ?m ?E,
                 Hco : consistent_value ?m ?s1,
                   Hupd : SSAStore.Upd2 ?v1 _ ?v2 _ ?s1 ?s2,
                     Hnotin1 : is_true (~~ SSAVS.mem ?v1 (vars_env ?E)),
                       Hnotin2 : is_true (~~ SSAVS.mem ?v2 (vars_env ?E))
               |- consistent_value ?m ?s2 =>
                 apply: (consistent_value_upd2 Hco Hty Hupd Hnotin1 Hnotin2)
             |  Hco : consistent_value ?m ?s1,
                 Heq : SSAStore.Equal ?s1 ?s2
                |- consistent_value ?m ?s2 =>
                  rewrite -Heq; exact: Hco
             end.
    (* Imov *)
    case: a H H0 => //=.
    - move=> u Hupd Hwf. case Hu: (SSAVM.find u m).
      + apply: (consistent_value_add_upd _ Hupd Hty H1 Hco).
        rewrite (Hco _ _ Hu). apply: (Upd_disjoint_eval_atom Hupd).
        rewrite VSLemmas.disjoint_singleton_l. apply/negP => Hmem.
        apply/idP: H1. apply: (VSLemmas.mem_subset Hmem). apply/defsubP.
        exact: (proj1 (proj2 (Hty _ _ Hu))).
      + apply: (consistent_value_add_upd _ Hupd Hty H1 Hco). simpl.
        apply: (SSAStore.acc_Upd_neq _ Hupd).
        apply/negP => /eqP Huv; subst. move/andP: Hwf => /= [Hdef _].
        move/defsubP: Hdef => Hsub. apply/idP: H1. rewrite SSAVS.Lemmas.subset_singleton in Hsub.
        exact: Hsub.
    - move=> ty bs Hupd Hwf. apply: (consistent_value_add_upd _ Hupd Hty H1 Hco).
      reflexivity.
  Qed.

  Lemma subst_map_instr_consistent_value' E i m s1 s2 :
    consistent_type m E ->
    consistent_value m s1 ->
    eval_instr E (subst_instr m i) (OK s1) (OK s2) ->
    well_formed_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    consistent_value (subst_map_instr m i) s2.
  Proof.
    (move=> Hty Hco).
    (case: i => //=); intros;
    repeat match goal with
           | H : eval_instr _ _ _ _ |- _ =>
               inversion_clear H
           | H : is_true (ssa_vars_unchanged_instr _ _) |- _ =>
               rewrite ssa_unchanged_instr_disjoint_lvs /= in H
           | H : is_true (VSLemmas.disjoint _ (SSAVS.singleton _)) |- _ =>
               rewrite VSLemmas.disjoint_singleton_r in H
           | H : is_true (VSLemmas.disjoint _ (SSAVS.add _ _)) |- _ =>
               let H1 := fresh in
               let H2 := fresh in
               rewrite VSLemmas.disjoint_add_r in H;
               move/andP: H => [H1 H2]
           | Hty : consistent_type ?m ?E,
               Hco : consistent_value ?m ?s1,
                 Hupd : SSAStore.Upd ?v _ ?s1 ?s2,
                   Hnotin : is_true (~~ SSAVS.mem ?v (vars_env ?E))
             |- consistent_value ?m ?s2 =>
               apply: (consistent_value_upd Hco Hty Hupd Hnotin)
           | Hty : consistent_type ?m ?E,
               Hco : consistent_value ?m ?s1,
                 Hupd : SSAStore.Upd2 ?v1 _ ?v2 _ ?s1 ?s2,
                   Hnotin1 : is_true (~~ SSAVS.mem ?v1 (vars_env ?E)),
                     Hnotin2 : is_true (~~ SSAVS.mem ?v2 (vars_env ?E))
             |- consistent_value ?m ?s2 =>
               apply: (consistent_value_upd2 Hco Hty Hupd Hnotin1 Hnotin2)
           |  Hco : consistent_value ?m ?s1,
               Heq : SSAStore.Equal ?s1 ?s2
              |- consistent_value ?m ?s2 =>
                rewrite -Heq; exact: Hco
           end.
    (* Imov *)
    case: a H0 H2 => //=.
    - move=> u Hwf. case Hu: (SSAVM.find u m) => Hupd.
      + apply: (consistent_value_add_upd _ Hupd Hty H1 Hco).
        apply: (Upd_disjoint_eval_atom Hupd).
        rewrite VSLemmas.disjoint_singleton_l. apply/negP => Hmem.
        apply/idP: H1. apply: (VSLemmas.mem_subset Hmem). apply/defsubP.
        exact: (proj1 (proj2 (Hty _ _ Hu))).
      + apply: (consistent_value_add_upd _ Hupd Hty H1 Hco). simpl.
        apply: (SSAStore.acc_Upd_neq _ Hupd).
        apply/negP => /eqP Huv; subst. move/andP: Hwf => /= [Hdef _].
        move/defsubP: Hdef => Hsub. apply/idP: H1. rewrite SSAVS.Lemmas.subset_singleton in Hsub.
        exact: Hsub.
    - move=> ty bs Hwf Hupd. apply: (consistent_value_add_upd _ Hupd Hty H1 Hco).
      reflexivity.
  Qed.

  Lemma subst_map_program_consistent_value E p s1 s2 :
    well_formed_ssa_program E p ->
    eval_program E p (OK s1) (OK s2) ->
    consistent_value (subst_map_program p) s2.
  Proof.
    rewrite /subst_map_program. move: (consistent_value_empty s1).
    move: (consistent_type_empty E).
    move: (SSAVM.empty atom). elim: p E s1 s2 => [| i p IH] E s1 s2 m Hty Hco Hwf Hev //=.
    - inversion_clear Hev. move: H => Heq. simpl in Heq. rewrite -Heq. exact: Hco.
    - inversion_clear Hev. move: H H0 => Hevi Hevp.
      move: (well_formed_ssa_hd Hwf) => Hwfi.
      move: (well_formed_ssa_unchanged_env_hd Hwf) => HunEi.
      case: t Hevi Hevp => [ t |] Hevi Hevp.
      + apply: (IH _ t _ _
                   (subst_map_instr_consistent_type Hwfi HunEi Hty)
                   _ (well_formed_ssa_tl Hwf) Hevp).
        exact: (subst_map_instr_consistent_value Hty Hco Hevi Hwfi HunEi).
      + apply: False_ind. exact: (eval_program_err_ok Hevp).
  Qed.

  Lemma subst_map_program_consistent_value' E p s1 s2 :
    well_formed_ssa_program E p ->
    eval_program E (subst_program (subst_map_program p) p) (OK s1) (OK s2) ->
    consistent_value (subst_map_program p) s2.
  Proof.
    rewrite /subst_map_program. move: (consistent_value_empty s1).
    move: (consistent_type_empty E).
    move: (SSAVM.empty atom). elim: p E s1 s2 => [| i p IH] E s1 s2 m Hty Hco Hwf Hev //=.
    - inversion_clear Hev. move: H => Heq. simpl in Heq. rewrite -Heq. exact: Hco.
    - rewrite subst_program_cons in Hev.
      inversion_clear Hev. move: H H0 => Hevi Hevp.
      move: (well_formed_ssa_hd Hwf) => Hwfi.
      move: (well_formed_ssa_unchanged_env_hd Hwf) => HunEi.
      move: (well_formed_ssa_vars_unchanged_hd Hwf) => Hun.
      move: (ssa_unchanged_program_subset Hun (rvs_instr_subset i)) => {}Hun.
      rewrite (subst_instr_subst_map_program_rec_unchanged _ Hun) in Hevi Hevp.
      rewrite (subst_instr_subst_map_instr_unchanged _ (well_formed_ssa_lvs_unchanged_hd Hwf)) in Hevi Hevp.
      rewrite (consistent_type_instr_succ_typenv _ Hty) in Hevp.
      case: t Hevi Hevp => [ t |] Hevi Hevp.
      + apply: (IH _ t _ _ (subst_map_instr_consistent_type Hwfi HunEi Hty)
                   _ (well_formed_ssa_tl Hwf) Hevp).
        exact: (subst_map_instr_consistent_value' Hty Hco Hevi Hwfi HunEi).
      + apply: False_ind. exact: (eval_program_err_ok Hevp).
  Qed.


  (* A combination of consistent_value and consistent_type *)

  Definition consistent_map E m s : Prop :=
    forall x a, SSAVM.find x m = Some a ->
                is_defined x E ->
                are_defined (vars_atom a) E
                /\ well_typed_atom E a
                /\ SSATE.vtyp x E = atyp a E
                /\ (match s with
                    | OK t => SSAStore.acc x t = eval_atom a t
                    | ERR => True
                    end).

  Fixpoint consistent_map_chain E m s p :=
    match p with
    | [::] => consistent_map E m s
    | i::p => consistent_map E m s
              /\ (forall t, eval_instr E i s t ->
                            consistent_map_chain (instr_succ_typenv i E) m t p)
    end.


  Lemma consistent_map_chain_consistent E m s p :
    consistent_map_chain E m s p -> consistent_map E m s.
  Proof. case: p => [| i p] => //=. tauto. Qed.


  Global Instance add_proper_consistent_map_env :
    Proper (SSATE.Equal ==> eq ==> eq ==> iff) consistent_map.
  Proof.
    move=> E1 E2 Heq m1 m2 ? s1 s2 ?; subst. split => Hco x a Hx Hdx.
    - rewrite -Heq in Hdx *. exact: (Hco _ _ Hx Hdx).
    - rewrite Heq in Hdx *. exact: (Hco _ _ Hx Hdx).
  Qed.

  Global Instance add_proper_consistent_map_map :
    Proper (eq ==> SSAVM.Equal ==> eq ==> iff) consistent_map.
  Proof.
    move=> E1 E2 ? m1 m2 Heq s1 s2 ?; subst. split => Hco x a Hx Hdx.
    - rewrite -Heq in Hx. exact: (Hco _ _ Hx Hdx).
    - rewrite Heq in Hx. exact: (Hco _ _ Hx Hdx).
  Qed.

  Global Instance add_proper_consistent_map_state :
    Proper (eq ==> eq ==> state_equal ==> iff) consistent_map.
  Proof.
    move=> E1 E2 ? m1 m2 ? s1 s2 Heq; subst. split => Hco x a Hx Hdx.
    - move: (Hco _ _ Hx Hdx) => {Hco} H. caseb H. move=> Hdefa Hsma Htyx Hvx.
      repeat split; try assumption. move: Heq Hvx. case: s1; case: s2 => //=.
      move=> s1 s2 ->. by apply.
    - move: (Hco _ _ Hx Hdx) => {Hco} H. caseb H. move=> Hdefa Hsma Htyx Hvx.
      repeat split; try assumption. move: Heq Hvx. case: s1; case: s2 => //=.
      move=> s1 s2 ->. by apply.
  Qed.

  Global Instance add_proper_consistent_map_chain_env :
    Proper (SSATE.Equal ==> eq ==> eq ==> eq ==> iff) consistent_map_chain.
  Proof.
    move=> E1 E2 Heq m1 m2 ? s1 s2 ? p1 p2 ?; subst.
    elim: p2 E1 E2 m2 s2 Heq => [| i p IH] E1 E2 m s Heq //=.
    - rewrite Heq. tauto.
    - move: (add_proper_instr_succ_typenv (Logic.eq_refl i) Heq) => Heq'.
      split; move => [Hco Hsucc].
      + split; first by rewrite -Heq. move=> t Hevi. rewrite -Heq in Hevi.
        move: (IH _ _ m t Heq') => [IH1 IH2]. exact: (IH1 (Hsucc _ Hevi)).
      + split; first by rewrite Heq. move=> t Hevi. rewrite Heq in Hevi.
        move: (IH _ _ m t Heq') => [IH1 IH2]. exact: (IH2 (Hsucc _ Hevi)).
  Qed.

  Global Instance add_proper_consistent_map_chain_map :
    Proper (eq ==> SSAVM.Equal ==> eq ==> eq ==> iff) consistent_map_chain.
  Proof.
    move=> E1 E2 ? m1 m2 Heq s1 s2 ? p1 p2 ?; subst.
    elim: p2 E2 m1 m2 s2 Heq => [| i p IH] E m1 m2 s Heq //=.
    - rewrite Heq. tauto.
    - split; move => [Hco Hsucc].
      + rewrite Heq in Hco. split; first assumption. move=> t Hevi.
        apply/(IH _ _ _ _ Heq). exact: (Hsucc _ Hevi).
      + rewrite -Heq in Hco. split; first assumption. move=> t Hevi.
        apply/(IH _ _ _ _ Heq). exact: (Hsucc _ Hevi).
  Qed.

  Global Instance add_proper_consistent_map_chain_state :
    Proper (eq ==> eq ==> state_equal ==> eq ==> iff) consistent_map_chain.
  Proof.
    move=> E1 E2 ? m1 m2 ? s1 s2 Heq p1 p2 ?; subst.
    elim: p2 E2 m2 s1 s2 Heq => [| i p IH] E m s1 s2 Heq //=.
    - rewrite Heq. tauto.
    - split; move => [Hco Hsucc].
      + split; first by rewrite -Heq. move=> t Hevi.
        rewrite -Heq in Hevi. exact: (Hsucc _ Hevi).
      + split; first by rewrite Heq. move=> t Hevi.
        rewrite Heq in Hevi. exact: (Hsucc _ Hevi).
  Qed.


  Lemma disjoint_consistent_map E m s :
    VSLemmas.disjoint (TEKS.key_set m) (vars_env E) ->
    consistent_map E m s.
  Proof.
    move=> Hdisj x a Hx Hdx. move: (SSAVM.Lemmas.find_some_mem Hx) => Hmem.
    move: (TEKS.mem_key_set1 Hmem) => {}Hmem. move: (VSLemmas.mem_disjoint1 Hdisj Hmem).
    move/memdefP: Hdx. rewrite mem_vars_env. move=> ->. discriminate.
  Qed.


  Lemma consistent_map_eval_eexp E m s e :
    consistent_map E m (OK s) ->
    are_defined (vars_eexp e) E ->
    eval_eexp (subst_eexp m e) E s = eval_eexp e E s.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> v Hwd. rewrite are_defined_singleton in Hwd.
      dcase (SSAVM.find v m); case => /=.
      + move=> a. case: a => [ u | ty bs ] /= Hv.
        * move: (Hco _ _ Hv Hwd) => [Hdefa [Hsma [Htyp Hacc]]].
          rewrite /acc2z. rewrite Hacc /=. rewrite Htyp /=. reflexivity.
        * move: (Hco _ _ Hv Hwd) => [Hdefa [Hsma [Htyp Hacc]]].
          rewrite /acc2z. rewrite Htyp Hacc /=. reflexivity.
      + reflexivity.
    - move=> op e IH Hwd. rewrite (IH Hwd). reflexivity.
    - move=> op e1 IH1 e2 IH2 Hwd. rewrite are_defined_union in Hwd.
      move/andP: Hwd => [Hwd1 Hwd2]. rewrite (IH1 Hwd1) (IH2 Hwd2). reflexivity.
    - move=> e IH n Hwd. rewrite (IH Hwd). reflexivity.
  Qed.

  Lemma consistent_map_eval_rexp E m s e :
    consistent_map E m (OK s) ->
    are_defined (vars_rexp e) E ->
    eval_rexp (subst_rexp m e) s = eval_rexp e s.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> v Hwd. rewrite are_defined_singleton in Hwd.
      dcase (SSAVM.find v m); case => /=.
      + move=> a. case: a => [ u | ty bs ] /= Hv.
        * move: (Hco _ _ Hv Hwd) => [Hdefa [Hsma [Htyp Hacc]]].
          rewrite /acc2z. rewrite Hacc /=. reflexivity.
        * move: (Hco _ _ Hv Hwd) => [Hdefa [Hsma [Htyp Hacc]]].
          rewrite /acc2z. rewrite Hacc /=. reflexivity.
      + reflexivity.
    - move=> w op e IH Hwd. rewrite (IH Hwd). reflexivity.
    - move=> w op e1 IH1 e2 IH2 Hwd. rewrite are_defined_union in Hwd.
      move/andP: Hwd => [Hwd1 Hwd2]. rewrite (IH1 Hwd1) (IH2 Hwd2). reflexivity.
    - move=> w e IH n Hwd. rewrite (IH Hwd). reflexivity.
    - move=> w e IH n Hwd. rewrite (IH Hwd). reflexivity.
  Qed.

  Lemma consistent_map_eval_eexps E m s es :
    consistent_map E m (OK s) ->
    are_defined (vars_eexps es) E ->
    eval_eexps (subst_eexps m es) E s = eval_eexps es E s.
  Proof.
    move=> Hco. elim: es => [| e es IH] //=. rewrite are_defined_union.
    move/andP=> [Hwde Hwdes]. rewrite subst_eexps_cons /=.
    rewrite (consistent_map_eval_eexp Hco Hwde) (IH Hwdes). reflexivity.
  Qed.

  Lemma consistent_map_eval_ebexp E m s e :
    consistent_map E m (OK s) ->
    are_defined (vars_ebexp e) E ->
    eval_ebexp (subst_ebexp m e) E s <-> eval_ebexp e E s.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> e1 e2 Hwd. rewrite are_defined_union in Hwd. move/andP: Hwd => [Hwd1 Hwd2].
      rewrite (consistent_map_eval_eexp Hco Hwd1) (consistent_map_eval_eexp Hco Hwd2). tauto.
    - move=> e1 e2 ms Hwd. rewrite !are_defined_union in Hwd.
      move/andP: Hwd => [Hwd1 /andP [Hwd2 Hwdms]].
      rewrite (consistent_map_eval_eexp Hco Hwd1) (consistent_map_eval_eexp Hco Hwd2)
              (consistent_map_eval_eexps Hco Hwdms). tauto.
    - move=> e1 IH1 e2 IH2 Hwd. rewrite are_defined_union in Hwd.
      move/andP: Hwd => [Hwd1 Hwd2]. rewrite (IH1 Hwd1) (IH2 Hwd2). tauto.
  Qed.

  Lemma consistent_map_eval_rbexp E m s e :
    consistent_map E m (OK s) ->
    are_defined (vars_rbexp e) E ->
    eval_rbexp (subst_rbexp m e) s = eval_rbexp e s.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> w e1 e2 Hwd. rewrite are_defined_union in Hwd. move/andP: Hwd => [Hwd1 Hwd2].
      rewrite (consistent_map_eval_rexp Hco Hwd1) (consistent_map_eval_rexp Hco Hwd2).
      reflexivity.
    - move=> w op e1 e2 Hwd. rewrite are_defined_union in Hwd. move/andP: Hwd => [Hwd1 Hwd2].
      rewrite (consistent_map_eval_rexp Hco Hwd1) (consistent_map_eval_rexp Hco Hwd2).
      reflexivity.
    - move=> e IH Hwd. rewrite (IH Hwd). reflexivity.
    - move=> e1 IH1 e2 IH2 Hwd. rewrite are_defined_union in Hwd. move/andP: Hwd => [Hwd1 Hwd2].
      rewrite (IH1 Hwd1) (IH2 Hwd2). reflexivity.
    - move=> e1 IH1 e2 IH2 Hwd. rewrite are_defined_union in Hwd. move/andP: Hwd => [Hwd1 Hwd2].
      rewrite (IH1 Hwd1) (IH2 Hwd2). reflexivity.
  Qed.

  Lemma consistent_map_eval_bexp E m s e :
    consistent_map E m (OK s) ->
    are_defined (vars_bexp e) E ->
    eval_bexp (subst_bexp m e) E s <-> eval_bexp e E s.
  Proof.
    case: e => [e r] Hco. rewrite /vars_bexp /subst_bexp /eval_bexp /= => Hwd.
    rewrite are_defined_union in Hwd. move/andP: Hwd => [Hwde Hwdr].
    rewrite (consistent_map_eval_ebexp Hco Hwde) (consistent_map_eval_rbexp Hco Hwdr).
    tauto.
  Qed.

  Lemma consistent_map_atyp E m a s :
    consistent_map E m s ->
    are_defined (vars_atom a) E ->
    atyp (subst_atom m a) E = atyp a E.
  Proof.
    move=> Hco. case: a => [ v |] //=. rewrite are_defined_singleton => Hdef.
    case Hv: (SSAVM.find v m).
    - rewrite (proj1 (proj2 (proj2 (Hco _ _ Hv Hdef)))). reflexivity.
    - reflexivity.
  Qed.

  Lemma consistent_map_eval_atom E m s a :
    consistent_map E m (OK s) ->
    are_defined (vars_atom a) E ->
    eval_atom (subst_atom m a) s = eval_atom a s.
  Proof.
    move=> Hco. case: a => [ v |] //=. rewrite are_defined_singleton => Hdef.
    case Hv: (SSAVM.find v m).
    - rewrite (proj2 (proj2 (proj2 (Hco _ _ Hv Hdef)))). reflexivity.
    - reflexivity.
  Qed.

  Lemma consistent_map_instr_succ_typenv E m s i :
    consistent_map E m s ->
    well_formed_instr E i ->
    SSATE.Equal (instr_succ_typenv (subst_instr m i) E)
                (instr_succ_typenv i E).
  Proof.
    move=> Hco.
    (case: i => //=); intros;
      by repeat match goal with
                | |- SSATE.Equal _ _ => move=> x
                | H : is_true (well_formed_instr _ _) |- _ =>
                    move: (well_formed_instr_defined_rvs H) => /= {}H
                | H : is_true (are_defined (SSAVS.union _ _) _) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    rewrite are_defined_union in H;
                    move/andP: H => [H1 H2]
                | |- context [SSAVM.find ?x (SSATE.add ?t _ _)] =>
                    let Hxt := fresh in
                    dcase (x == t); case; intro Hxt;
                    [ (move/eqP: Hxt => ?); subst; rewrite !(SSATE.Lemmas.find_add_eq (eqxx _))
                    | (move/negP: Hxt => Hxt); rewrite !(SSATE.Lemmas.find_add_neq Hxt) ]
                | Hco : consistent_map ?E ?m ?s,
                    Hdef : is_true (are_defined (vars_atom ?a) ?E)
                  |- context [atyp (subst_atom ?m ?a) ?E] =>
                    rewrite (consistent_map_atyp Hco Hdef)
                | |- ?e = ?e => reflexivity
                end.
  Qed.

  Lemma consistent_map_eval_instr E m i s1 s2 :
    consistent_map E m s1 ->
    well_formed_instr E i ->
    eval_instr E (subst_instr m i) s1 s2 <-> eval_instr E i s1 s2.
  Proof.
    move=> Hco Hwf. split => Hevi.
    - (case: i Hevi Hwf Hco => //=); inversion_clear 1; intros;
      repeat match goal with
             | |- eval_instr _ _ (ERR SSAStore.t) (ERR SSAStore.t) =>
                 exact: Eerr
             | H : is_true (well_formed_instr _ _) |- _ =>
                 move: (well_formed_instr_defined_rvs Hwf) => /= {}Hwf
             | H : is_true (are_defined (SSAVS.union _ _) _) |- _ =>
                 let H1 := fresh in
                 let H2 := fresh in
                 rewrite are_defined_union in H;
                 move/andP: H => [H1 H2]
             | Hco : consistent_map ?E ?m (OK ?s),
                 Hdef : is_true (are_defined (vars_atom ?a) ?E),
                   H : context [eval_atom (subst_atom ?m ?a) ?s] |- _ =>
                 rewrite (consistent_map_eval_atom Hco Hdef) in H
             | Hco : consistent_map ?E ?m (OK ?s),
                 Hdef : is_true (are_defined (vars_bexp ?a) ?E),
                 H : context [eval_bexp (subst_bexp ?m ?a) ?E ?s] |- _ =>
                 rewrite (consistent_map_eval_bexp Hco Hdef) in H
             | Hco : consistent_map ?E ?m (OK ?s),
                 Hdef : is_true (are_defined (vars_atom ?a) ?E),
                   H : context [atyp (subst_atom ?m ?a) ?E] |- _ =>
                 rewrite (consistent_map_atyp Hco Hdef) in H
             end; eval_instr_intro; assumption.
    - (case: i Hevi Hwf Hco => //=); inversion_clear 1; intros;
      repeat match goal with
             | |- eval_instr _ _ (ERR SSAStore.t) (ERR SSAStore.t) =>
                 exact: Eerr
             | H : is_true (well_formed_instr _ _) |- _ =>
                 move: (well_formed_instr_defined_rvs Hwf) => /= {}Hwf
             | H : is_true (are_defined (SSAVS.union _ _) _) |- _ =>
                 let H1 := fresh in
                 let H2 := fresh in
                 rewrite are_defined_union in H;
                 move/andP: H => [H1 H2]
             end;
      try match goal with
          | Hco : consistent_map ?E ?m (OK ?s),
              Hdef : is_true (are_defined (vars_atom ?a) ?E),
                H : context [atyp ?a ?E] |- _ =>
              rewrite -(consistent_map_atyp Hco Hdef) in H
          end; eval_instr_intro;
      by repeat match goal with
                | Hco : consistent_map ?E ?m (OK ?s),
                    Hdef : is_true (are_defined (vars_atom ?a) ?E)
                  |- context [eval_atom (subst_atom ?m ?a) ?s] =>
                    rewrite (consistent_map_eval_atom Hco Hdef)
                | Hco : consistent_map ?E ?m (OK ?s),
                    Hdef : is_true (are_defined (vars_bexp ?a) ?E)
                  |- context [eval_bexp (subst_bexp ?m ?a) ?E ?s] =>
                    rewrite (consistent_map_eval_bexp Hco Hdef)
                | H : ?e |- ?e => assumption
                end.
  Qed.

  Lemma consistent_map_succ E m i s t :
    consistent_map E m s ->
    well_formed_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    ssa_vars_unchanged_instr (TEKS.key_set m) i ->
    eval_instr E i s t ->
    consistent_map (instr_succ_typenv i E) (subst_map_instr m i) t.
  Proof.
    move=> Hco Hwf HunEi Hunmi Hev x a Hx Hdefx.
    case Hunx: (ssa_vars_unchanged_instr (SSAVS.singleton x) i).
    - rewrite (subst_map_instr_unchanged_find _ Hunx) in Hx.
      have HdefxE: is_defined x E.
      { rewrite is_defined_mem_vars_env in Hdefx. rewrite vars_env_instr_succ_typenv in Hdefx.
        rewrite ssa_unchanged_instr_disjoint_lvs in Hunx. rewrite VSLemmas.mem_union in Hdefx.
        rewrite VSLemmas.disjoint_singleton_l in Hunx. move/negPf: Hunx => Hunx.
        rewrite Hunx orbF in Hdefx. rewrite is_defined_mem_vars_env. exact: Hdefx. }
      move: (Hco _ _ Hx HdefxE) => [Hdefa [Hsma [Htyx Hevx]]].
      have Huna: ssa_vars_unchanged_instr (vars_atom a) i.
      { apply: (ssa_unchanged_instr_subset HunEi). apply/defsubP. assumption. }
      repeat split.
      + apply: are_defined_instr_succ_typenv. assumption.
      + rewrite well_typed_atom_unchanged_instr_succ_typenv; first assumption.
        apply: (ssa_unchanged_instr_subset HunEi). move/defsubP: Hdefa. by apply.
      + rewrite (vtyp_unchanged_instr_succ_typenv _ Hunx).
        rewrite (atyp_unchanged_instr_succ_typenv _ Huna). assumption.
      + move: Hev Hco Hevx. case: t => [ t |] //=. case: s => [ s |] //=.
        * move=> Hev Hco Hevx.
          rewrite -(acc_unchanged_instr (ssa_unchanged_instr_singleton1 Hunx) Hev).
          rewrite -(ssa_unchanged_instr_eval_atom Huna Hev). assumption.
        * move=> Hev. by inversion Hev.
    - have Hxm: SSAVM.find x m = None.
      { apply: SSAVM.Lemmas.not_mem_find_none. apply/negP=> Hmemxm. apply/negPf: Hunx.
        rewrite ssa_unchanged_instr_singleton ssa_var_unchanged_instr_not_mem.
        apply/negP=> Hmemxi. rewrite ssa_unchanged_instr_disjoint_lvs in Hunmi.
        move: (TEKS.mem_key_set1 Hmemxm) => {}Hmemxm.
        move: (VSLemmas.mem_disjoint1 Hunmi Hmemxm). rewrite Hmemxi. discriminate. }
      (case: i Hwf HunEi Hunmi Hev Hx Hdefx Hunx => //=); intros;
      try match goal with
          | H1 : ?e = None, H2 : ?e = Some _ |- _ =>
              rewrite H1 in H2; discriminate
          end.
      rewrite ssa_unchanged_instr_disjoint_lvs /= in Hunx.
      rewrite VSLemmas.disjoint_singleton_l in Hunx. move/negPn: Hunx.
      move/VSLemmas.mem_singleton1 => /eqP ?; subst.
      rewrite (SSATE.vtyp_add_eq (eqxx _)).
      case: a0 Hx Hwf HunEi Hunmi Hev Hdefx => [ u | ty bs ] /=  Hx Hwf HunEi Hunmi Hev Hdefx.
      + case Hu: (SSAVM.find u m) Hx => Hx.
        * rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
          move: (well_formed_instr_defined_rvs Hwf) => /=.
          rewrite are_defined_singleton => Hdefu.
          move: (Hco _ _ Hu Hdefu) => [Hdefa [Hsma [Htyu Hevu]]].
          have Ht0a: ~~ SSAVS.mem t0 (vars_atom a).
          { rewrite ssa_unchanged_instr_disjoint_lvs /= in HunEi.
            rewrite VSLemmas.disjoint_singleton_r in HunEi. apply/negP=> Hmemt0.
            apply/idP: HunEi. move/defsubP: Hdefa => Hsub.
            exact: (VSLemmas.mem_subset Hmemt0 Hsub). }
          repeat split.
          -- apply: are_defined_addr. assumption.
          -- rewrite well_typed_atom_notin_add; first assumption. exact: Ht0a.
          -- rewrite (atyp_add_not_mem _ _ Ht0a). assumption.
          -- move: Hev Hco Hevu. case: t => [ t |] //=. inversion_clear 1.
             move: H. move=> /= Hev Hco Hevx.
             rewrite (SSAStore.acc_Upd_eq (eqxx _) Hev). rewrite Hevx.
             symmetry. apply: (Upd_disjoint_eval_atom Hev).
             rewrite VSLemmas.disjoint_singleton_l. assumption.
        * rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
          simpl. move: (well_formed_instr_defined_rvs Hwf) => /= Hwd.
          rewrite ssa_unchanged_instr_disjoint_lvs /= in HunEi.
          have Hne: u != t0.
          { move/defsubP: Hwd => Hsub. move: (VSLemmas.disjoint_subset_l HunEi Hsub).
            rewrite VSLemmas.disjoint_singleton_l. move/VSLemmas.not_mem_singleton1.
            move/negP => Hne. assumption. }
          repeat split.
          -- apply: are_defined_addr. assumption.
          -- rewrite well_typed_atom_notin_add; first exact: (well_formed_instr_well_typed Hwf).
             simpl. apply/VSLemmas.not_mem_singleton2. apply/negP. rewrite eq_sym. exact: Hne.
          -- rewrite (SSATE.vtyp_add_neq Hne). reflexivity.
          -- move: Hev Hco. case: t => [ t |] //=. move => Hev. inversion_clear Hev.
             move: H. move=> /= Hev Hco. rewrite (SSAStore.acc_Upd_neq Hne Hev).
             rewrite (SSAStore.acc_Upd_eq (eqxx _) Hev). reflexivity.
      + clear Hdefx. rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
        simpl. repeat split.
        * move: (well_formed_instr_well_typed Hwf) => /=. rewrite /well_typed_atom /=.
          move/andP=> [Hsa Hsbs]. rewrite Hsbs andbT. exact: Hsa.
        * case: t Hev => [ t |] //=. inversion_clear 1. move: H => /= Hev.
          rewrite (SSAStore.acc_Upd_eq (eqxx _) Hev). reflexivity.
  Qed.

  Lemma consistent_map_chain_eval E m p s1 s2 :
    well_formed_ssa_program E p ->
    consistent_map_chain E m s1 p ->
    eval_program E (subst_program m p) s1 s2 <-> eval_program E p s1 s2.
  Proof.
    elim: p E m s1 s2 => [| i p IH] E m s1 s2 //=. move=> Hwf [Hco Hcop].
    move: (well_formed_ssa_hd Hwf) => Hwfi.
    move: (well_formed_ssa_tl Hwf) => Hwfp.
    split => Hevp.
    - rewrite subst_program_cons in Hevp. inversion_clear Hevp.
      move: H H0 => Hevi Hevp. move/(consistent_map_eval_instr _ Hco Hwfi): Hevi => Hevi.
      apply: (Econs Hevi). apply/(IH _ _ _ _ Hwfp (Hcop _ Hevi)).
      rewrite (consistent_map_instr_succ_typenv Hco Hwfi) in Hevp.
      exact: Hevp.
    - inversion_clear Hevp. move: H H0 => Hevi Hevp. rewrite subst_program_cons.
      move: (Hcop _ Hevi) => {}Hcop. move/(consistent_map_eval_instr _ Hco Hwfi): Hevi => Hevi.
      apply: (Econs Hevi). rewrite (consistent_map_instr_succ_typenv Hco Hwfi).
      apply/(IH _ _ _ _ (well_formed_ssa_tl Hwf) Hcop). exact: Hevp.
  Qed.

  Lemma subst_map_program_rec_consistent_map_chain E m s p :
    well_formed_ssa_program E p ->
    ssa_vars_unchanged_program (TEKS.key_set m) p ->
    consistent_map E m s ->
    consistent_map_chain E (subst_map_program_rec m p) s p.
  Proof.
    elim: p E m s => [| i p IH] E m s Hwf Hunmp Hco //=. split.
    - move=> x a Hx Hdefx. move: (well_formed_ssa_unchanged_env Hwf) => Hun.
      move: (Hdefx). rewrite -are_defined_singleton. move/defsubP => Hsub.
      move: (ssa_unchanged_program_subset Hun Hsub) => Hunx.
      rewrite (subst_map_program_rec_unchanged_find _ (ssa_unchanged_program_tl Hunx)) in Hx.
      rewrite (subst_map_instr_unchanged_find _ (ssa_unchanged_program_hd Hunx)) in Hx.
      exact: (Hco _ _ Hx Hdefx).
    - move=> t Hevi. apply: (IH _ _ _ (well_formed_ssa_tl Hwf)).
      + apply: (ssa_unchanged_program_subset _ (subst_map_instr_keys_subset _ _)).
        rewrite ssa_unchanged_program_union. rewrite (ssa_unchanged_program_tl Hunmp) /=.
        apply: (ssa_unchanged_program_subset _ (lvs_instr_subset _)).
        exact: (well_formed_ssa_vars_unchanged_hd Hwf).
      + exact: (consistent_map_succ
                  Hco (well_formed_ssa_hd Hwf)
                  (well_formed_ssa_unchanged_env_hd Hwf) (ssa_unchanged_program_hd Hunmp) Hevi).
  Qed.

  Lemma subst_map_program_consistent_map_chain E s p :
    well_formed_ssa_program E p ->
    consistent_map_chain E (subst_map_program p) s p.
  Proof.
    move=> Hwf. by apply: (subst_map_program_rec_consistent_map_chain Hwf) => //=.
  Qed.


  Lemma consistent_map_size_of_subst_rexp E m s e :
    consistent_map E m s ->
    well_formed_rexp E e ->
    size_of_rexp (subst_rexp m e) E = size_of_rexp e E.
  Proof.
    move=> Hco. elim: e => //=. move=> v. rewrite /well_formed_rexp /=.
    rewrite are_defined_singleton => /andP [Hdv Hsv].
    dcase (SSAVM.find v m); case.
    - move=> a. case: a => /=.
      + move=> u Hv. move: (Hco _ _ Hv Hdv) => [_ [_ [H _]]].
        rewrite 2!SSATE.vtyp_vsize. rewrite H. reflexivity.
      + move=> ty bs Hv. move: (Hco _ _ Hv Hdv) => [_ [_ [H _]]].
        rewrite SSATE.vtyp_vsize H. reflexivity.
    - move=> Hv. rewrite /size_of_rexp /=. reflexivity.
  Qed.

  Lemma consistent_map_disjoint_well_formed_rexp E m s e :
    consistent_map E m s ->
    VSLemmas.disjoint (vars_rexp e) (TEKS.key_set m) ->
    well_formed_rexp E (subst_rexp m e) = well_formed_rexp E e.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> v Hdisj. rewrite VSLemmas.disjoint_singleton_l in Hdisj.
      rewrite (TEKS.not_mem_key_set_find Hdisj). reflexivity.
    - move=> w op e IH Hdisj. rewrite /runary.
      rewrite !well_formed_rexp_runopb. rewrite (IH Hdisj).
      case Hwf: (well_formed_rexp E e) => //=.
      rewrite (consistent_map_size_of_subst_rexp Hco Hwf). reflexivity.
    - move=> w op e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l.
      move/andP=> [Hdisj1 Hdisj2]. rewrite /rbinary.
      rewrite !well_formed_rexp_rbinopb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=.
      case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (consistent_map_size_of_subst_rexp Hco Hwf1)
              (consistent_map_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> w e IH n Hdisj. rewrite /ruext. rewrite 2!well_formed_rexp_ruextb /=.
      rewrite (IH Hdisj). case Hwf: (well_formed_rexp E e) => //=.
      rewrite (consistent_map_size_of_subst_rexp Hco Hwf). reflexivity.
    - move=> w e IH n Hdisj. rewrite /rsext. rewrite 2!well_formed_rexp_rsextb /=.
      rewrite (IH Hdisj). case Hwf: (well_formed_rexp E e) => //=.
      rewrite (consistent_map_size_of_subst_rexp Hco Hwf). reflexivity.
  Qed.

  Lemma consistent_map_disjoint_well_formed_rbexp E m s e :
    consistent_map E m s ->
    VSLemmas.disjoint (vars_rbexp e) (TEKS.key_set m) ->
    well_formed_rbexp E (subst_rbexp m e) = well_formed_rbexp E e.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> w e1 e2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_reqb.
      rewrite (consistent_map_disjoint_well_formed_rexp Hco Hdisj1)
              (consistent_map_disjoint_well_formed_rexp Hco Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=. case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (consistent_map_size_of_subst_rexp Hco Hwf1)
              (consistent_map_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> w op e1 e2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_rcmpb.
      rewrite (consistent_map_disjoint_well_formed_rexp Hco Hdisj1)
              (consistent_map_disjoint_well_formed_rexp Hco Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=. case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (consistent_map_size_of_subst_rexp Hco Hwf1)
              (consistent_map_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_randb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_rorb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
  Qed.

  Lemma consistent_map_disjoint_well_formed_bexp E m s e :
    consistent_map E m s ->
    VSLemmas.disjoint (vars_bexp e) (TEKS.key_set m) ->
    well_formed_bexp E (subst_bexp m e) = well_formed_bexp E e.
  Proof.
    move=> Hco. case: e => [e r]. rewrite /vars_bexp /=.
    rewrite VSLemmas.disjoint_union_l => /andP [Hdisje Hdisjr].
    rewrite /subst_bexp 2!well_formed_bexp_split /=.
    rewrite (disjoint_well_formed_ebexp _ Hdisje)
            (consistent_map_disjoint_well_formed_rbexp Hco Hdisjr).
    reflexivity.
  Qed.


  (* A chain of consistent types *)

  Definition weak_consistent_type (m : SSAVM.t atom) (E : SSATE.env) : Prop :=
    forall x a, SSAVM.find x m = Some a ->
                is_defined x E ->
                are_defined (vars_atom a) E
                /\ well_typed_atom E a
                /\ SSATE.vtyp x E = atyp a E.

  Fixpoint weak_consistent_type_chain E m p :=
    match p with
    | [::] => weak_consistent_type m E
    | i::p => weak_consistent_type m E
              /\ weak_consistent_type_chain (instr_succ_typenv i E) m p
    end.


  Lemma consistent_map_weak_type E m s :
    consistent_map E m s -> weak_consistent_type m E.
  Proof. move=> Hco x a Hx Hdx. move: (Hco _ _ Hx Hdx). tauto. Qed.

  Lemma consistent_value_weak_type_map E m s :
    consistent_value m s -> weak_consistent_type m E ->
    consistent_map E m (OK s).
  Proof. move=> Hev Hty x a Hx Hdx. move: (Hev _ _ Hx) (Hty _ _ Hx Hdx). tauto. Qed.

  Lemma consistent_type_weak m E :
    consistent_type m E -> weak_consistent_type m E.
  Proof. move=> Hco x a Hx Hdx. move: (Hco _ _ Hx). tauto. Qed.

  Lemma consistent_value_type_map E m s :
    consistent_value m s -> consistent_type m E ->
    consistent_map E m (OK s).
  Proof.
    move=> Hev Hty.
    exact: (consistent_value_weak_type_map Hev (consistent_type_weak Hty)).
  Qed.

  Lemma weak_consistent_type_chain_consistent E m p :
    weak_consistent_type_chain E m p -> weak_consistent_type m E.
  Proof. case: p => [| i p] => //=. tauto. Qed.


  Global Instance add_proper_weak_consistent_type_map :
    Proper (SSAVM.Equal ==> eq ==> iff) weak_consistent_type.
  Proof.
    move=> m1 m2 Heq s1 s2 ?; subst. split => Hco x a Hx Hdx.
    - rewrite -Heq in Hx. exact: (Hco _ _ Hx Hdx).
    - rewrite Heq in Hx. exact: (Hco _ _ Hx Hdx).
  Qed.

  Global Instance add_proper_weak_consistent_type_env :
    Proper (eq ==> SSATE.Equal ==> iff) weak_consistent_type.
  Proof.
    move=> m1 m2 ? E1 E2 Heq; subst. split => Hco x a Hx Hdx.
    - move: (Hco _ _ Hx). rewrite Heq. tauto.
    - move: (Hco _ _ Hx). rewrite -Heq. tauto.
  Qed.

  Global Instance add_proper_weak_consistent_type_chain_env :
    Proper (SSATE.Equal ==> eq ==> eq ==> iff) weak_consistent_type_chain.
  Proof.
    move=> E1 E2 Heq m1 m2 ? p1 p2 ?; subst.
    elim: p2 E1 E2 m2 Heq => [| i p IH] E1 E2 m Heq //=.
    - rewrite Heq. tauto.
    - move: (add_proper_instr_succ_typenv (Logic.eq_refl i) Heq) => Heq'.
      split; move => [Hco Hsucc].
      + split; first by rewrite -Heq. apply/(IH _ _ m Heq'). exact: Hsucc.
      + split; first by rewrite Heq. apply/(IH _ _ m Heq'). exact: Hsucc.
  Qed.

  Global Instance add_proper_weak_consistent_type_chain_map :
    Proper (eq ==> SSAVM.Equal ==> eq ==> iff) weak_consistent_type_chain.
  Proof.
    move=> E1 E2 ? m1 m2 Heq p1 p2 ?; subst.
    elim: p2 E2 m1 m2 Heq => [| i p IH] E m1 m2 Heq //=.
    - rewrite Heq. tauto.
    - split; move => [Hco Hsucc].
      + rewrite Heq in Hco. split; first assumption. apply/(IH _ _ _ Heq). exact: Hsucc.
      + rewrite -Heq in Hco. split; first assumption. apply/(IH _ _ _ Heq). exact: Hsucc.
  Qed.


  Lemma disjoint_weak_consistent_type E m :
    VSLemmas.disjoint (TEKS.key_set m) (vars_env E) ->
    weak_consistent_type m E.
  Proof.
    move=> Hdisj x a Hx Hdx. move: (SSAVM.Lemmas.find_some_mem Hx) => Hmem.
    move: (TEKS.mem_key_set1 Hmem) => {}Hmem. move: (VSLemmas.mem_disjoint1 Hdisj Hmem).
    move/memdefP: Hdx. rewrite mem_vars_env. move=> ->. discriminate.
  Qed.

  Lemma weak_consistent_type_empty E : weak_consistent_type (SSAVM.empty _) E.
  Proof.
    move=> x a Hx. rewrite SSAVM.Lemmas.empty_o in Hx. discriminate.
  Qed.

  Lemma weak_consistent_type_atyp E m a :
    weak_consistent_type m E ->
    are_defined (vars_atom a) E ->
    atyp (subst_atom m a) E = atyp a E.
  Proof.
    move=> Hco. case: a => //=. move=> v. rewrite are_defined_singleton => Hdv.
    case Hv: (SSAVM.find v m) => //=. move: (proj2 (proj2 (Hco _ _ Hv Hdv))).
    symmetry. assumption.
  Qed.

  Lemma weak_consistent_type_asize E m a :
    weak_consistent_type m E ->
    are_defined (vars_atom a) E ->
    asize (subst_atom m a) E = asize a E.
  Proof.
    move=> Hco Hdef. rewrite /asize. rewrite (weak_consistent_type_atyp Hco Hdef). reflexivity.
  Qed.

  Lemma weak_consistent_type_size_of_subst_rexp E m e :
    weak_consistent_type m E ->
    well_formed_rexp E e ->
    size_of_rexp (subst_rexp m e) E = size_of_rexp e E.
  Proof.
    move=> Hco. elim: e => //=. move=> v. rewrite /well_formed_rexp /=.
    rewrite are_defined_singleton => /andP [Hdv Hsv].
    dcase (SSAVM.find v m); case.
    - move=> a. case: a => /=.
      + move=> u Hv. move: (Hco _ _ Hv Hdv) => [_ [_ H]].
        rewrite 2!SSATE.vtyp_vsize. rewrite H. reflexivity.
      + move=> ty bs Hv. move: (Hco _ _ Hv Hdv) => [_ [_ H]].
        rewrite SSATE.vtyp_vsize H. reflexivity.
    - move=> Hv. rewrite /size_of_rexp /=. reflexivity.
  Qed.

  Lemma weak_consistent_type_disjoint_well_formed_rexp E m e :
    weak_consistent_type m E ->
    VSLemmas.disjoint (vars_rexp e) (TEKS.key_set m) ->
    well_formed_rexp E (subst_rexp m e) = well_formed_rexp E e.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> v Hdisj. rewrite VSLemmas.disjoint_singleton_l in Hdisj.
      rewrite (TEKS.not_mem_key_set_find Hdisj). reflexivity.
    - move=> w op e IH Hdisj. rewrite /runary.
      rewrite !well_formed_rexp_runopb. rewrite (IH Hdisj).
      case Hwf: (well_formed_rexp E e) => //=.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf). reflexivity.
    - move=> w op e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l.
      move/andP=> [Hdisj1 Hdisj2]. rewrite /rbinary.
      rewrite !well_formed_rexp_rbinopb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=.
      case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf1)
              (weak_consistent_type_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> w e IH n Hdisj. rewrite /ruext. rewrite 2!well_formed_rexp_ruextb /=.
      rewrite (IH Hdisj). case Hwf: (well_formed_rexp E e) => //=.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf). reflexivity.
    - move=> w e IH n Hdisj. rewrite /rsext. rewrite 2!well_formed_rexp_rsextb /=.
      rewrite (IH Hdisj). case Hwf: (well_formed_rexp E e) => //=.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf). reflexivity.
  Qed.

  Lemma weak_consistent_type_disjoint_well_formed_rbexp E m e :
    weak_consistent_type m E ->
    VSLemmas.disjoint (vars_rbexp e) (TEKS.key_set m) ->
    well_formed_rbexp E (subst_rbexp m e) = well_formed_rbexp E e.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> w e1 e2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_reqb.
      rewrite (weak_consistent_type_disjoint_well_formed_rexp Hco Hdisj1)
              (weak_consistent_type_disjoint_well_formed_rexp Hco Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=. case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf1)
              (weak_consistent_type_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> w op e1 e2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_rcmpb.
      rewrite (weak_consistent_type_disjoint_well_formed_rexp Hco Hdisj1)
              (weak_consistent_type_disjoint_well_formed_rexp Hco Hdisj2).
      case Hwf1: (well_formed_rexp E e1) => //=. case Hwf2: (well_formed_rexp E e2) => //=.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf1)
              (weak_consistent_type_size_of_subst_rexp Hco Hwf2). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_randb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite VSLemmas.disjoint_union_l => /andP [Hdisj1 Hdisj2].
      rewrite 2!well_formed_rbexp_rorb. rewrite (IH1 Hdisj1) (IH2 Hdisj2).
      reflexivity.
  Qed.

  Lemma weak_consistent_type_disjoint_well_formed_bexp E m e :
    weak_consistent_type m E ->
    VSLemmas.disjoint (vars_bexp e) (TEKS.key_set m) ->
    well_formed_bexp E (subst_bexp m e) = well_formed_bexp E e.
  Proof.
    move=> Hco. case: e => [e r]. rewrite /vars_bexp /=.
    rewrite VSLemmas.disjoint_union_l => /andP [Hdisje Hdisjr].
    rewrite /subst_bexp 2!well_formed_bexp_split /=.
    rewrite (disjoint_well_formed_ebexp _ Hdisje)
            (weak_consistent_type_disjoint_well_formed_rbexp Hco Hdisjr).
    reflexivity.
  Qed.


  Lemma weak_consistent_type_instr_succ_typenv E m i :
    weak_consistent_type m E ->
    well_formed_instr E i ->
    SSATE.Equal (instr_succ_typenv (subst_instr m i) E)
                (instr_succ_typenv i E).
  Proof.
    move=> Hco.
    (case: i => //=); intros;
      by repeat match goal with
                | |- SSATE.Equal _ _ => move=> x
                | H : is_true (well_formed_instr _ _) |- _ =>
                    move: (well_formed_instr_defined_rvs H) => /= {}H
                | H : is_true (are_defined (SSAVS.union _ _) _) |- _ =>
                    let H1 := fresh in
                    let H2 := fresh in
                    rewrite are_defined_union in H;
                    move/andP: H => [H1 H2]
                | |- context [SSAVM.find ?x (SSATE.add ?t _ _)] =>
                    let Hxt := fresh in
                    dcase (x == t); case; intro Hxt;
                    [ (move/eqP: Hxt => ?); subst; rewrite !(SSATE.Lemmas.find_add_eq (eqxx _))
                    | (move/negP: Hxt => Hxt); rewrite !(SSATE.Lemmas.find_add_neq Hxt) ]
                | Hco : weak_consistent_type ?m ?E,
                    Hdef : is_true (are_defined (vars_atom ?a) ?E)
                  |- context [atyp (subst_atom ?m ?a) ?E] =>
                    rewrite (weak_consistent_type_atyp Hco Hdef)
                | |- ?e = ?e => reflexivity
             end.
  Qed.

  Lemma weak_consistent_type_succ E m i :
    weak_consistent_type m E ->
    well_formed_instr E i ->
    ssa_vars_unchanged_instr (vars_env E) i ->
    ssa_vars_unchanged_instr (TEKS.key_set m) i ->
    weak_consistent_type (subst_map_instr m i) (instr_succ_typenv i E).
  Proof.
    move=> Hco Hwf HunEi Hunmi x a Hx Hdefx.
    case Hunx: (ssa_vars_unchanged_instr (SSAVS.singleton x) i).
    - rewrite (subst_map_instr_unchanged_find _ Hunx) in Hx.
      have HdefxE: is_defined x E.
      { rewrite is_defined_mem_vars_env in Hdefx. rewrite vars_env_instr_succ_typenv in Hdefx.
        rewrite ssa_unchanged_instr_disjoint_lvs in Hunx. rewrite VSLemmas.mem_union in Hdefx.
        rewrite VSLemmas.disjoint_singleton_l in Hunx. move/negPf: Hunx => Hunx.
        rewrite Hunx orbF in Hdefx. rewrite is_defined_mem_vars_env. exact: Hdefx. }
      move: (Hco _ _ Hx HdefxE) => [Hdefa [Hsma Htyx]].
      have Huna: ssa_vars_unchanged_instr (vars_atom a) i.
      { apply: (ssa_unchanged_instr_subset HunEi). apply/defsubP. assumption. }
      repeat split.
      + apply: are_defined_instr_succ_typenv. assumption.
      + rewrite well_typed_atom_unchanged_instr_succ_typenv; first assumption.
        apply: (ssa_unchanged_instr_subset HunEi). move/defsubP: Hdefa. by apply.
      + rewrite (vtyp_unchanged_instr_succ_typenv _ Hunx).
        rewrite (atyp_unchanged_instr_succ_typenv _ Huna). assumption.
    - have Hxm: SSAVM.find x m = None.
      { apply: SSAVM.Lemmas.not_mem_find_none. apply/negP=> Hmemxm. apply/negPf: Hunx.
        rewrite ssa_unchanged_instr_singleton ssa_var_unchanged_instr_not_mem.
        apply/negP=> Hmemxi. rewrite ssa_unchanged_instr_disjoint_lvs in Hunmi.
        move: (TEKS.mem_key_set1 Hmemxm) => {}Hmemxm.
        move: (VSLemmas.mem_disjoint1 Hunmi Hmemxm). rewrite Hmemxi. discriminate. }
      (case: i Hwf HunEi Hunmi Hx Hdefx Hunx => //=); intros;
      try match goal with
          | H1 : ?e = None, H2 : ?e = Some _ |- _ =>
              rewrite H1 in H2; discriminate
          end.
      rewrite ssa_unchanged_instr_disjoint_lvs /= in Hunx.
      rewrite VSLemmas.disjoint_singleton_l in Hunx. move/negPn: Hunx.
      move/VSLemmas.mem_singleton1 => /eqP ?; subst.
      rewrite (SSATE.vtyp_add_eq (eqxx _)).
      case: a0 Hx Hwf HunEi Hunmi Hdefx => [ u | ty bs ] /=  Hx Hwf HunEi Hunmi Hdefx.
      + case Hu: (SSAVM.find u m) Hx => Hx.
        * rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
          move: (well_formed_instr_defined_rvs Hwf) => /=.
          rewrite are_defined_singleton => Hdefu.
          move: (Hco _ _ Hu Hdefu) => [Hdefa [Hsma Htyu]].
          have Hta: ~~ SSAVS.mem t (vars_atom a).
          { rewrite ssa_unchanged_instr_disjoint_lvs /= in HunEi.
            rewrite VSLemmas.disjoint_singleton_r in HunEi. apply/negP=> Hmemt.
            apply/idP: HunEi. move/defsubP: Hdefa => Hsub.
            exact: (VSLemmas.mem_subset Hmemt Hsub). }
          repeat split.
          -- apply: are_defined_addr. assumption.
          -- rewrite well_typed_atom_notin_add; first assumption.
             exact: Hta.
          -- rewrite (atyp_add_not_mem _ _ Hta). assumption.
        * rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
          simpl. move: (well_formed_instr_defined_rvs Hwf) => /= Hwd.
          rewrite ssa_unchanged_instr_disjoint_lvs /= in HunEi.
          have Hne: u != t.
          { move/defsubP: Hwd => Hsub. move: (VSLemmas.disjoint_subset_l HunEi Hsub).
            rewrite VSLemmas.disjoint_singleton_l. move/VSLemmas.not_mem_singleton1.
            move/negP => Hne. assumption. }
          repeat split.
          -- apply: are_defined_addr. assumption.
          -- rewrite well_typed_atom_notin_add; first exact: (well_formed_instr_well_typed Hwf).
             simpl. apply/VSLemmas.not_mem_singleton2. apply/negP. rewrite eq_sym. exact: Hne.
          -- rewrite (SSATE.vtyp_add_neq Hne). reflexivity.
      + clear Hdefx. rewrite (SSAVM.Lemmas.find_add_eq (eqxx _)) in Hx. case: Hx => ?; subst.
        simpl. repeat split.
        move: (well_formed_instr_well_typed Hwf) => /=. rewrite /well_typed_atom /=.
        move/andP=> [Hsa Hsbs]. rewrite Hsbs andbT. exact: Hsa.
  Qed.

  Lemma subst_map_program_rec_weak_consistent_type_chain E m p :
    well_formed_ssa_program E p ->
    ssa_vars_unchanged_program (TEKS.key_set m) p ->
    weak_consistent_type m E ->
    weak_consistent_type_chain E (subst_map_program_rec m p) p.
  Proof.
    elim: p E m => [| i p IH] E m Hwf Hunmp Hco //=. split.
    - move=> x a Hx Hdefx. move: (well_formed_ssa_unchanged_env Hwf) => Hun.
      move: (Hdefx). rewrite -are_defined_singleton. move/defsubP => Hsub.
      move: (ssa_unchanged_program_subset Hun Hsub) => Hunx.
      rewrite (subst_map_program_rec_unchanged_find _ (ssa_unchanged_program_tl Hunx)) in Hx.
      rewrite (subst_map_instr_unchanged_find _ (ssa_unchanged_program_hd Hunx)) in Hx.
      exact: (Hco _ _ Hx Hdefx).
    - apply: (IH _ _ (well_formed_ssa_tl Hwf)).
      + apply: (ssa_unchanged_program_subset _ (subst_map_instr_keys_subset _ _)).
        rewrite ssa_unchanged_program_union. rewrite (ssa_unchanged_program_tl Hunmp) /=.
        apply: (ssa_unchanged_program_subset _ (lvs_instr_subset _)).
        exact: (well_formed_ssa_vars_unchanged_hd Hwf).
      + exact: (weak_consistent_type_succ
                  Hco (well_formed_ssa_hd Hwf)
                  (well_formed_ssa_unchanged_env_hd Hwf) (ssa_unchanged_program_hd Hunmp)).
  Qed.

  Lemma subst_map_program_weak_consistent_type_chain E p :
    well_formed_ssa_program E p ->
    weak_consistent_type_chain E (subst_map_program p) p.
  Proof.
    move=> Hwf. by apply: (subst_map_program_rec_weak_consistent_type_chain Hwf) => //=.
  Qed.


  (* Initial *)

  Lemma subst_map_program_consistent_map_init E s p :
    well_formed_ssa_program E p ->
    consistent_map E (subst_map_program p) s.
  Proof.
    move=> Hwf. apply: disjoint_consistent_map.
    exact: subst_map_program_keys_disjoint.
  Qed.

  Lemma subst_map_program_weak_consistent_type_init E p :
    well_formed_ssa_program E p ->
    weak_consistent_type (subst_map_program p) E.
  Proof.
    move=> Hwf. apply: disjoint_weak_consistent_type.
    exact: subst_map_program_keys_disjoint.
  Qed.


  (* Evaluation of substituted programs *)

  Lemma subst_map_program_eval E p s1 s2 :
    well_formed_ssa_program E p ->
    eval_program E (subst_program (subst_map_program p) p) s1 s2 <->
      eval_program E p s1 s2.
  Proof.
    move=> Hwf. apply: (consistent_map_chain_eval _ Hwf).
    exact: subst_map_program_consistent_map_chain.
  Qed.


  (* Soundness and completeness *)

  Lemma rewrite_mov_sound s :
    well_formed_ssa_spec s ->
    valid_spec (rewrite_mov s) -> valid_spec s.
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /well_formed_spec => /= H.
    caseb H. move=> Hwff Hwfp Hwfg HunEp Hssap.
    rewrite /valid_spec /valid_spec_ok /valid_spec_err /rewrite_mov /subst_map_spec /=.
    move=> [Hok Herr].
    have Hwfssap: well_formed_ssa_program E p.
    { rewrite /well_formed_ssa_program. by rewrite Hwfp HunEp Hssap. }
    split.
    - move=> s1 s2 Hco Hevf Hevp.
      have Hevf': eval_bexp (subst_bexp (subst_map_program p) f) E s1.
      { rewrite disjoint_subst_bexp; first exact: Hevf.
        apply: (SSAVS.Lemmas.disjoint_subset_l _ (subst_map_program_keys_subset p)).
        apply: (SSAVS.Lemmas.disjoint_subset_r _ (well_formed_bexp_vars_subset Hwff)).
        rewrite SSAVS.Lemmas.disjoint_sym.
        rewrite ssa_unchanged_program_disjoint_lvs in HunEp.
        exact: HunEp. }
      have Hevp': eval_program E (subst_program (subst_map_program p) p) (OK s1) (OK s2).
      { apply/(subst_map_program_eval _ _ Hwfssap). exact: Hevp. }
      move: (Hok s1 s2 Hco Hevf' Hevp'). rewrite (subst_map_program_succ_typenv Hwfssap).
      move/(subst_bexp_eval_unchanged
              _
              (subst_map_program_consistent_value Hwfssap Hevp)
              (subst_map_program_consistent_type Hwfssap)). by apply.
    - move=> s Hco Hevf Hevp.
      have Hevf': eval_bexp (subst_bexp (subst_map_program p) f) E s.
      { rewrite disjoint_subst_bexp; first exact: Hevf.
        apply: (SSAVS.Lemmas.disjoint_subset_l _ (subst_map_program_keys_subset p)).
        apply: (SSAVS.Lemmas.disjoint_subset_r _ (well_formed_bexp_vars_subset Hwff)).
        rewrite SSAVS.Lemmas.disjoint_sym.
        rewrite ssa_unchanged_program_disjoint_lvs in HunEp.
        exact: HunEp. }
      apply: (Herr _ Hco Hevf'). apply/(subst_map_program_eval _ _ Hwfssap).
      exact: Hevp.
  Qed.

  Lemma rewrite_mov_complete s :
    well_formed_ssa_spec s ->
    valid_spec s -> valid_spec (rewrite_mov s).
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /well_formed_spec => /= H.
    caseb H. move=> Hwff Hwfp Hwfg HunEp Hssap.
    rewrite /valid_spec /valid_spec_ok /valid_spec_err /rewrite_mov /subst_map_spec /=.
    move=> [Hok Herr].
    have Hwfssap: well_formed_ssa_program E p.
    { rewrite /well_formed_ssa_program. by rewrite Hwfp HunEp Hssap. }
    split.
    - move=> s1 s2 Hco Hevf Hevp.
      have Hevf': eval_bexp f E s1.
      { rewrite disjoint_subst_bexp in Hevf; first exact: Hevf.
        apply: (SSAVS.Lemmas.disjoint_subset_l _ (subst_map_program_keys_subset p)).
        apply: (SSAVS.Lemmas.disjoint_subset_r _ (well_formed_bexp_vars_subset Hwff)).
        rewrite SSAVS.Lemmas.disjoint_sym.
        rewrite ssa_unchanged_program_disjoint_lvs in HunEp.
        exact: HunEp. }
      have Hevp': eval_program E p (OK s1) (OK s2).
      { move/(subst_map_program_eval _ _ Hwfssap) : Hevp. by apply. }
      move: (Hok s1 s2 Hco Hevf' Hevp'). rewrite (subst_map_program_succ_typenv Hwfssap).
      move/(subst_bexp_eval_unchanged
              _
              (subst_map_program_consistent_value Hwfssap Hevp')
              (subst_map_program_consistent_type Hwfssap)). by apply.
    - move=> s Hco Hevf Hevp.
      have Hevf': eval_bexp f E s.
      { rewrite disjoint_subst_bexp in Hevf; first exact: Hevf.
        apply: (SSAVS.Lemmas.disjoint_subset_l _ (subst_map_program_keys_subset p)).
        apply: (SSAVS.Lemmas.disjoint_subset_r _ (well_formed_bexp_vars_subset Hwff)).
        rewrite SSAVS.Lemmas.disjoint_sym.
        rewrite ssa_unchanged_program_disjoint_lvs in HunEp.
        exact: HunEp. }
      apply: (Herr _ Hco Hevf'). move/(subst_map_program_eval _ _ Hwfssap) : Hevp.
      by apply.
  Qed.


  (* well-formedness *)

  Lemma weak_consistent_type_are_defined_atom E m a :
    weak_consistent_type m E ->
    are_defined (vars_atom a) E ->
    are_defined (vars_atom (subst_atom m a)) E.
  Proof.
    case: a => [ v | ty bs ] //= Hco Hdv. rewrite are_defined_singleton in Hdv.
    case Hv: (SSAVM.find v m).
    - move: (Hco _ _ Hv Hdv). tauto.
    - simpl. rewrite are_defined_singleton. assumption.
  Qed.

  Lemma weak_consistent_type_well_typed_atom E m a :
    weak_consistent_type m E ->
    are_defined (vars_atom a) E ->
    well_typed_atom E a ->
    well_typed_atom E (subst_atom m a).
  Proof.
    case: a => [ v | ty bs ] //= Hco Hdv Hwt. rewrite are_defined_singleton in Hdv.
    rewrite /well_typed_atom /= in Hwt *. case Hv: (SSAVM.find v m).
    - move: (Hco _ _ Hv Hdv) => [Hda [Hwta Htyv]]. exact: Hwta.
    - simpl. exact: Hwt.
  Qed.

  Lemma well_typed_eexp_of_atom E a :
    well_typed_atom E a ->
    well_typed_eexp E (eexp_of_atom a).
  Proof. by case: a => [ v | ty bs ] //=. Qed.

  Lemma well_typed_rexp_of_atom E a :
    well_typed_atom E a ->
    well_typed_rexp E (rexp_of_atom a).
  Proof.
    case: a => [ v | ty bs ] //=.
    - rewrite /well_typed_atom /=. rewrite andbT /well_sized_atom /=.
      case: (is_unsigned (SSATE.vtyp v E)) => //=.
      move=> H. apply: (ltn_trans _ H). done.
    - rewrite /well_typed_atom /= /well_sized_atom. move/andP=> /= [H ->]. rewrite andbT.
      case: (is_unsigned ty) H => //=.
      move=> H. apply: (ltn_trans _ H). done.
  Qed.

  Lemma subst_eexp_are_defined E m e :
    weak_consistent_type m E ->
    are_defined (vars_eexp e) E ->
    are_defined (vars_eexp (subst_eexp m e)) E.
  Proof.
    move=> Hco. elim: e => //=.
    - move=> v. rewrite are_defined_singleton /= => Hdv.
      case Hv: (SSAVM.find v m).
      + move: (Hco _ _ Hv Hdv) => [Hda [Hwta Htyv]]. rewrite vars_eexp_of_atom.
        exact: Hda.
      + simpl. rewrite are_defined_singleton. exact: Hdv.
    - move=> op e1 IH1 e2 IH2. rewrite 2!are_defined_union.
      move/andP=> [Hdef1 Hdef2]. rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
  Qed.

  Lemma subst_eexp_well_typed E m e :
    weak_consistent_type m E ->
    are_defined (vars_eexp e) E ->
    well_typed_eexp E e ->
    well_typed_eexp E (subst_eexp m e).
  Proof.
    move=> Hco. elim: e => //=.
    - move=> v Hdv _. rewrite are_defined_singleton in Hdv.
      case Hv: (SSAVM.find v m).
      + move: (Hco _ _ Hv Hdv) => [Hda [Hwta Htyv]]. exact: (well_typed_eexp_of_atom Hwta).
      + done.
    - move=> op e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      move/andP=> [Hwt1 Hwt2]. rewrite (IH1 Hdef1 Hwt1) (IH2 Hdef2 Hwt2). reflexivity.
  Qed.

  Lemma subst_eexp_well_formed E m e :
    weak_consistent_type m E ->
    well_formed_eexp E e ->
    well_formed_eexp E (subst_eexp m e).
  Proof.
    move=> Hco. rewrite /well_formed_eexp. move/andP => [Hdef Hwt].
    rewrite (subst_eexp_are_defined Hco Hdef) (subst_eexp_well_typed Hco Hdef Hwt).
    reflexivity.
  Qed.

  Lemma subst_rexp_are_defined E m e :
    weak_consistent_type m E ->
    are_defined (vars_rexp e) E ->
    are_defined (vars_rexp (subst_rexp m e)) E.
  Proof.
    move => Hco. elim: e => //=.
    - move=> v. rewrite are_defined_singleton /= => Hdv.
      case Hv: (SSAVM.find v m).
      + move: (Hco _ _ Hv Hdv) => [Hda [Hwta Htyv]]. rewrite vars_rexp_of_atom.
        exact: Hda.
      + simpl. rewrite are_defined_singleton. exact: Hdv.
    - move=> w op e1 IH1 e2 IH2. rewrite 2!are_defined_union. move/andP => [Hdef1 Hdef2].
      rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
  Qed.

  Lemma subst_rexp_well_typed E m e :
    weak_consistent_type m E ->
    are_defined (vars_rexp e) E ->
    well_typed_rexp E e ->
    well_typed_rexp E (subst_rexp m e).
  Proof.
    move => Hco. elim: e => //=.
    - move=> v. rewrite are_defined_singleton. move => Hdv Hsv. case Hv: (SSAVM.find v m).
      + move: (Hco _ _ Hv Hdv) => [Hda [Hwta Htyv]]. exact: (well_typed_rexp_of_atom Hwta).
      + simpl. exact: Hsv.
    - move=> w op e IH Hdef H. caseb H. move=> Hw Hwt Hse.
      rewrite Hw (IH Hdef Hwt) (weak_consistent_type_size_of_subst_rexp Hco) /=; first assumption.
      rewrite /well_formed_rexp. by rewrite Hdef Hwt.
    - move=> w op e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      move=> H. caseb H. move=> Hw Hwt1 Hs1 Hwt2 Hs2.
      have Hwf1: well_formed_rexp E e1 by rewrite /well_formed_rexp Hdef1 Hwt1.
      have Hwf2: well_formed_rexp E e2 by rewrite /well_formed_rexp Hdef2 Hwt2.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf1)
              (weak_consistent_type_size_of_subst_rexp Hco Hwf2).
      rewrite (IH1 Hdef1 Hwt1) (IH2 Hdef2 Hwt2) Hw Hs1 Hs2. reflexivity.
    - move=> w e IH n Hdef. move=> H; caseb H. move=> Hw Hwt Hs.
      have Hwf: well_formed_rexp E e by rewrite /well_formed_rexp Hdef Hwt.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf).
      rewrite (IH Hdef Hwt) Hw Hs. reflexivity.
    - move=> w e IH n Hdef. move=> H; caseb H. move=> Hw Hwt Hs.
      have Hwf: well_formed_rexp E e by rewrite /well_formed_rexp Hdef Hwt.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf).
      rewrite (IH Hdef Hwt) Hw Hs. reflexivity.
  Qed.

  Lemma subst_rexp_well_formed E m e :
    weak_consistent_type m E ->
    well_formed_rexp E e ->
    well_formed_rexp E (subst_rexp m e).
  Proof.
    move=> Hco. rewrite /well_formed_rexp. move/andP => [Hdef Hwt].
    rewrite (subst_rexp_are_defined Hco Hdef) (subst_rexp_well_typed Hco Hdef Hwt).
    reflexivity.
  Qed.

  Lemma subst_eexps_are_defined E m es :
    weak_consistent_type m E ->
    are_defined (vars_eexps es) E ->
    are_defined (vars_eexps (subst_eexps m es)) E.
  Proof.
    move=> Hco. elim: es => [| e es IH] //=.
    rewrite subst_eexps_cons /= 2!are_defined_union => /andP [He Hes].
    rewrite (subst_eexp_are_defined Hco He) (IH Hes). reflexivity.
  Qed.

  Lemma subst_eexps_well_typed E m es :
    weak_consistent_type m E ->
    are_defined (vars_eexps es) E ->
    well_typed_eexps E es ->
    well_typed_eexps E (subst_eexps m es).
  Proof.
    move=> Hco. elim: es => [| e es IH] //=.
    rewrite subst_eexps_cons /= are_defined_union => /andP [He Hes].
    move/andP => [Hwfe Hwfes]. rewrite (subst_eexp_well_typed Hco He Hwfe) (IH Hes Hwfes).
    reflexivity.
  Qed.

  Lemma subst_eexps_well_formed E m es :
    weak_consistent_type m E ->
    well_formed_eexps E es ->
    well_formed_eexps E (subst_eexps m es).
  Proof.
    move=> Hco. elim: es => [| e es IH] //=. move/andP => [Hwfe Hwfes].
    rewrite subst_eexps_cons /=. rewrite (subst_eexp_well_formed Hco Hwfe) (IH Hwfes).
    reflexivity.
  Qed.

  Lemma subst_ebexp_are_defined E m e :
    weak_consistent_type m E ->
    are_defined (vars_ebexp e) E ->
    are_defined (vars_ebexp (subst_ebexp m e)) E.
  Proof.
    move => Hco. elim: e => //=.
    - move=> e1 e2. rewrite 2!are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (subst_eexp_are_defined Hco Hdef1) (subst_eexp_are_defined Hco Hdef2).
      reflexivity.
    - move=> e1 e2 ms. rewrite !are_defined_union => H; caseb H.
      move=> Hdef1 Hdef2 Hdefms.
      rewrite (subst_eexp_are_defined Hco Hdef1) (subst_eexp_are_defined Hco Hdef2)
              (subst_eexps_are_defined Hco Hdefms). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite 2!are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
  Qed.

  Lemma subst_ebexp_well_typed E m e :
    weak_consistent_type m E ->
    are_defined (vars_ebexp e) E ->
    well_typed_ebexp E e ->
    well_typed_ebexp E (subst_ebexp m e).
  Proof.
    move => Hco. elim: e => //=.
    - move=> e1 e2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      move/andP => [Hwt1 Hwt2]. rewrite (subst_eexp_well_typed Hco Hdef1 Hwt1)
                                        (subst_eexp_well_typed Hco Hdef2 Hwt2).
      reflexivity.
    - move=> e1 e2 ms. rewrite !are_defined_union => H; caseb H.
      move=> Hdef1 Hdef2 Hdefms. move=> H; caseb H. move=> Hwt1 Hwt2 Hwtms.
      rewrite (subst_eexp_well_typed Hco Hdef1 Hwt1) (subst_eexp_well_typed Hco Hdef2 Hwt2)
              (subst_eexps_well_typed Hco Hdefms Hwtms). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2].
      move/andP => [Hwt1 Hwt2]. rewrite (IH1 Hdef1 Hwt1) (IH2 Hdef2 Hwt2). reflexivity.
  Qed.

  Lemma subst_ebexp_well_formed E m e :
    weak_consistent_type m E ->
    well_formed_ebexp E e ->
    well_formed_ebexp E (subst_ebexp m e).
  Proof.
    move=> Hco. rewrite /well_formed_ebexp. move/andP => [Hdef Hwt].
    rewrite (subst_ebexp_are_defined Hco Hdef) (subst_ebexp_well_typed Hco Hdef Hwt).
    reflexivity.
  Qed.

  Lemma subst_rbexp_are_defined E m e :
    weak_consistent_type m E ->
    are_defined (vars_rbexp e) E ->
    are_defined (vars_rbexp (subst_rbexp m e)) E.
  Proof.
    move => Hco. elim: e => //=.
    - move=> w e1 e2. rewrite 2!are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (subst_rexp_are_defined Hco Hdef1) (subst_rexp_are_defined Hco Hdef2).
      reflexivity.
    - move=> w op e1 e2. rewrite 2!are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (subst_rexp_are_defined Hco Hdef1) (subst_rexp_are_defined Hco Hdef2).
      reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite 2!are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite 2!are_defined_union => /andP [Hdef1 Hdef2].
      rewrite (IH1 Hdef1) (IH2 Hdef2). reflexivity.
  Qed.

  Lemma subst_rbexp_well_typed E m e :
    weak_consistent_type m E ->
    are_defined (vars_rbexp e) E ->
    well_typed_rbexp E e ->
    well_typed_rbexp E (subst_rbexp m e).
  Proof.
    move => Hco. elim: e => //=.
    - move=> w e1 e2. rewrite are_defined_union => H1 H2; caseb H2; caseb H1.
      move=> Hdef1 Hdef2 Hw Hwt1 Hs1 Hwt2 Hs2.
      rewrite (subst_rexp_well_typed Hco Hdef1 Hwt1) (subst_rexp_well_typed Hco Hdef2 Hwt2).
      have Hwf1: well_formed_rexp E e1 by rewrite /well_formed_rexp Hdef1 Hwt1.
      have Hwf2: well_formed_rexp E e2 by rewrite /well_formed_rexp Hdef2 Hwt2.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf1)
              (weak_consistent_type_size_of_subst_rexp Hco Hwf2).
      rewrite Hw Hs1 Hs2. reflexivity.
    - move=> w op e1 e2. rewrite are_defined_union => H1 H2; caseb H2; caseb H1.
      move=> Hdef1 Hdef2 Hw Hwt1 Hs1 Hwt2 Hs2.
      rewrite (subst_rexp_well_typed Hco Hdef1 Hwt1) (subst_rexp_well_typed Hco Hdef2 Hwt2).
      have Hwf1: well_formed_rexp E e1 by rewrite /well_formed_rexp Hdef1 Hwt1.
      have Hwf2: well_formed_rexp E e2 by rewrite /well_formed_rexp Hdef2 Hwt2.
      rewrite (weak_consistent_type_size_of_subst_rexp Hco Hwf1)
              (weak_consistent_type_size_of_subst_rexp Hco Hwf2).
      rewrite Hw Hs1 Hs2. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2] /andP [Hwt1 Hwt2].
      rewrite (IH1 Hdef1 Hwt1) (IH2 Hdef2 Hwt2). reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite are_defined_union => /andP [Hdef1 Hdef2] /andP [Hwt1 Hwt2].
      rewrite (IH1 Hdef1 Hwt1) (IH2 Hdef2 Hwt2). reflexivity.
  Qed.

  Lemma subst_rbexp_well_formed E m e :
    weak_consistent_type m E ->
    well_formed_rbexp E e ->
    well_formed_rbexp E (subst_rbexp m e).
  Proof.
    move=> Hco. rewrite /well_formed_rbexp. move/andP => [Hdef Hwt].
    rewrite (subst_rbexp_are_defined Hco Hdef) (subst_rbexp_well_typed Hco Hdef Hwt).
    reflexivity.
  Qed.

  Lemma subst_bexp_are_defined E m e :
    weak_consistent_type m E ->
    are_defined (vars_bexp e) E ->
    are_defined (vars_bexp (subst_bexp m e)) E.
  Proof.
    move=> Hco. case: e => [e r]. rewrite /vars_bexp /subst_bexp /=.
    rewrite 2!are_defined_union => /andP [Hdefe Hdefr].
    rewrite (subst_ebexp_are_defined Hco Hdefe) (subst_rbexp_are_defined Hco Hdefr).
    reflexivity.
  Qed.

  Lemma subst_bexp_well_typed E m e :
    weak_consistent_type m E ->
    are_defined (vars_bexp e) E ->
    well_typed_bexp E e ->
    well_typed_bexp E (subst_bexp m e).
  Proof.
    move=> Hco. case: e => [e r]. rewrite /subst_bexp /vars_bexp /well_typed_bexp /=.
    rewrite are_defined_union => /andP [Hdefe Hdefr] /andP [Hwte Hwtr].
    rewrite (subst_ebexp_well_typed Hco Hdefe Hwte)
            (subst_rbexp_well_typed Hco Hdefr Hwtr). reflexivity.
  Qed.

  Lemma subst_bexp_well_formed E m e :
    weak_consistent_type m E ->
    well_formed_bexp E e ->
    well_formed_bexp E (subst_bexp m e).
  Proof.
    move=> Hco. case: e => [e r]. rewrite /subst_bexp /= 2!well_formed_bexp_split /=.
    move/andP => [Hwfe Hwfr]. rewrite (subst_ebexp_well_formed Hco Hwfe)
                                      (subst_rbexp_well_formed Hco Hwfr). reflexivity.
  Qed.

  Lemma subst_instr_well_formed E m i :
    weak_consistent_type m E ->
    well_formed_instr E i ->
    well_formed_instr E (subst_instr m i).
  Proof.
    move=> Hco.
    (case: i => //=); (rewrite /well_formed_instr /=); intros;
      by repeat match goal with
                | |- is_true true => reflexivity
                | H : is_true ?e |- context [?e] => rewrite H /=
                | H : is_true (_ && _) |- _ =>
                    caseb H; intros
                | Hco : weak_consistent_type ?m ?E,
                    Hda : is_true (are_defined (vars_atom ?a) ?E)
                  |- context [are_defined (vars_atom (subst_atom ?m ?a)) ?E] =>
                    rewrite (weak_consistent_type_are_defined_atom Hco Hda) /=
                | Hco : weak_consistent_type ?m ?E,
                    Hda : is_true (are_defined (vars_atom ?a) ?E),
                      Hwt : is_true (well_typed_atom ?E ?a)
                  |- context [well_typed_atom ?E (subst_atom ?m ?a)] =>
                    rewrite (weak_consistent_type_well_typed_atom Hco Hda Hwt) /=
                | Hco : weak_consistent_type ?m ?E,
                    Hda : is_true (are_defined (vars_atom ?a) ?E)
                  |- context [atyp (subst_atom ?m ?a) ?E] =>
                    rewrite (weak_consistent_type_atyp Hco Hda) /=
                | Hco : weak_consistent_type ?m ?E,
                    Hda : is_true (are_defined (vars_atom ?a) ?E)
                  |- context [asize (subst_atom ?m ?a) ?E] =>
                    rewrite (weak_consistent_type_asize Hco Hda) /=
                | Hco : weak_consistent_type ?m ?E,
                    Hdef : is_true (are_defined (vars_bexp ?b) ?E)
                  |- context [are_defined (vars_bexp (subst_bexp ?m ?b)) ?E] =>
                    rewrite (subst_bexp_are_defined Hco Hdef) /=
                | Hco : weak_consistent_type ?m ?E,
                    Hdef : is_true (are_defined (vars_bexp ?b) ?E),
                      Hwt : is_true (well_typed_bexp ?E ?b)
                  |- context [well_typed_bexp E (subst_bexp ?m ?b)] =>
                    rewrite (subst_bexp_well_typed Hco Hdef Hwt) /=
                end.
  Qed.

  Lemma subst_program_well_formed E m p :
    weak_consistent_type_chain E m p ->
    well_formed_program E p ->
    well_formed_program E (subst_program m p).
  Proof.
    elim: p E m => [| i p IH] E m //=. move=> [Hco Hsucc] /andP [Hwfi Hwfp].
    rewrite subst_program_cons /=. rewrite (subst_instr_well_formed Hco Hwfi) /=.
    rewrite (weak_consistent_type_instr_succ_typenv Hco Hwfi).
    exact: (IH _ _ Hsucc Hwfp).
  Qed.

  Lemma lvs_subst_instr m i :
    SSAVS.Equal (lvs_instr (subst_instr m i)) (lvs_instr i).
  Proof. by case: i => //=. Qed.

  Lemma lvs_subst_program m p :
    SSAVS.Equal (lvs_program (subst_program m p)) (lvs_program p).
  Proof.
    elim: p => [| i p IH] //=. rewrite subst_program_cons /=.
    rewrite lvs_subst_instr IH. reflexivity.
  Qed.

  Lemma subst_program_single_assignment E m p :
    well_formed_ssa_program E p ->
    weak_consistent_type_chain E m p ->
    ssa_single_assignment (subst_program m p).
  Proof.
    elim: p m E => [| i p IH] m E //=. move=> Hwf [Hcoi Hcop].
    rewrite subst_program_cons /=. rewrite (IH _ _ (well_formed_ssa_tl Hwf) Hcop) andbT.
    rewrite lvs_subst_instr. rewrite ssa_unchanged_program_disjoint_lvs.
    rewrite lvs_subst_program. rewrite -ssa_unchanged_program_disjoint_lvs.
    apply: (ssa_unchanged_program_subset _ (lvs_instr_subset _)).
    exact: (well_formed_ssa_vars_unchanged_hd Hwf).
  Qed.

  Lemma rewrite_mov_well_formed_ssa s :
    well_formed_ssa_spec s ->
    well_formed_ssa_spec (rewrite_mov s).
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /=.
    rewrite /well_formed_spec /rewrite_mov /subst_map_spec /=.
    move=> Hwf. caseb Hwf. move=> Hwff Hwfp Hwfg HunEp Hssap.
    have Hwfssap: well_formed_ssa_program E p.
    { rewrite /well_formed_ssa_program. by rewrite Hwfp HunEp Hssap. }
    rewrite (subst_map_program_succ_typenv Hwfssap).
    move: (subst_map_program_weak_consistent_type_init Hwfssap) => Hcowty.
    move: (subst_map_program_consistent_type Hwfssap) => Hcoty.
    move: (subst_map_program_weak_consistent_type_chain Hwfssap) => Hcowcty.
    have Hdisjfm: VSLemmas.disjoint (vars_bexp f) (TEKS.key_set (subst_map_program p)).
    { apply: (VSLemmas.disjoint_subset_r _ (subst_map_program_keys_subset p)).
      rewrite -ssa_unchanged_program_disjoint_lvs. apply: (ssa_unchanged_program_subset HunEp).
      exact: (well_formed_bexp_vars_subset Hwff). }
    (* f *)
    rewrite (weak_consistent_type_disjoint_well_formed_bexp Hcowty Hdisjfm) Hwff /=.
    (* p *)
    rewrite (subst_program_well_formed Hcowcty Hwfp) /=.
    (* g *)
    rewrite (subst_bexp_well_formed (consistent_type_weak Hcoty) Hwfg) /=.
    (* env unchanged *)
    rewrite ssa_unchanged_program_disjoint_lvs. rewrite lvs_subst_program.
    rewrite -ssa_unchanged_program_disjoint_lvs. rewrite HunEp /=.
    (* single assignment *)
    exact: (subst_program_single_assignment Hwfssap Hcowcty).
  Qed.

End RewriteMov.


(** ** Some properties about [cut_spec], [remove_asserts], and [extract_asserts] *)

Section Extra.

  Import SSA.

  (* well_formed_ssa_spec - cut_spec *)

  Ltac cut_spec_well_formed_ssa_tac :=
    match goal with
    | Hunvi : is_true (ssa_vars_unchanged_program (vars_program ?visited) (?i :: ?p)),
        Hi : is_true (well_formed_instr (program_succ_typenv ?visited ?E) ?i),
          Hun : is_true (ssa_vars_unchanged_program (vars_env (program_succ_typenv ?visited ?E)) (?i :: ?p)),
            Huni : is_true (ssa_vars_unchanged_program (lvs_instr ?i) ?p)
      |- is_true (ssa_vars_unchanged_program (vars_program (rcons ?visited ?i)) ?p) =>
        rewrite vars_program_rcons;
        rewrite ssa_unchanged_program_union;
        rewrite (ssa_unchanged_program_tl Hunvi);
        rewrite vars_instr_split;
        rewrite ssa_unchanged_program_union;
        rewrite Huni (well_formed_instr_rvs_unchanged_program Hi (ssa_unchanged_program_tl Hun));
        reflexivity
    | Hunvi : is_true (ssa_vars_unchanged_program (vars_program ?visited) (Inop :: ?p))
      |- is_true (ssa_vars_unchanged_program (vars_program (rcons ?visited Inop)) ?p) =>
        rewrite vars_program_rcons /=; rewrite SSAVS.Lemmas.union_emptyr;
        exact: (ssa_unchanged_program_tl Hunvi)
    | Hwfvi : is_true (well_formed_ssa_program ?E ?visited),
        Hi : is_true (well_formed_instr (program_succ_typenv ?visited ?E) ?i),
          Hun : is_true (ssa_vars_unchanged_program (vars_env (program_succ_typenv ?visited ?E)) (?i :: ?p)),
            Hunvi : is_true (ssa_vars_unchanged_program (vars_program ?visited) (?i :: ?p))
      |- is_true (well_formed_ssa_program ?E (rcons ?visited ?i)) =>
        (rewrite well_formed_ssa_rcons Hwfvi Hi /=);
        rewrite ssa_unchanged_instr_union;
        rewrite vars_env_program_succ_typenv in Hun;
        (rewrite (proj1 (ssa_unchanged_instr_union1 (ssa_unchanged_program_hd Hun))) /=);
        rewrite (ssa_unchanged_program_hd Hunvi); reflexivity
    | Hp : is_true (well_formed_program (instr_succ_typenv ?i (program_succ_typenv ?visited ?E)) ?p)
      |- is_true (well_formed_program (program_succ_typenv (rcons ?visited ?i) ?E) ?p) =>
        rewrite program_succ_typenv_rcons; exact: Hp
    | Hun : is_true (ssa_vars_unchanged_program (vars_env (program_succ_typenv ?visited ?E)) (?i :: ?p)),
        Huni : is_true (ssa_vars_unchanged_program (lvs_instr ?i) ?p)
      |- is_true (ssa_vars_unchanged_program (vars_env (program_succ_typenv (rcons ?visited ?i) ?E)) ?p) =>
        rewrite vars_env_program_succ_typenv ssa_unchanged_program_union;
        rewrite vars_env_program_succ_typenv in Hun;
        rewrite (ssa_unchanged_program_tl (proj1 (ssa_unchanged_program_union1 Hun)));
        rewrite lvs_program_rcons ssa_unchanged_program_union;
        rewrite (ssa_unchanged_program_tl (proj2 (ssa_unchanged_program_union1 Hun)));
        rewrite Huni; reflexivity
    | Hinc : In ?c (cut_spec_rec (?i :: rev ?visited) ?E ?f ?p ?g)
      |- In ?c (cut_spec_rec (rev (rcons ?visited ?i)) ?E ?f ?p ?g) =>
        rewrite rev_rcons; exact: Hinc
    | Hinc : In ?c (cut_spec_rec (?i :: rev ?visited) ?E ?f ?p ?g)
      |- In ?c (cut_spec_rec (rev (rcons ?visited ?i)) ?E ?f ?p ?g) =>
        rewrite rev_rcons; exact: Hinc
    end.

  Lemma cut_spec_well_formed_ssa s :
    well_formed_ssa_spec s ->
    all well_formed_ssa_spec (cut_spec s).
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /well_formed_spec /=.
    move=> H; caseb H. move=> Hf Hp Hg Hun Hssa. apply/all_forall. rewrite /cut_spec /=.
    move: Hf Hp Hg Hun Hssa.
    move: (well_formed_ssa_empty E).
    have: ssa_vars_unchanged_program (vars_program [::]) p by done.
    have {3 4 5}->: E = program_succ_typenv [::] E by reflexivity.
    have {6}->: [::] = rev [::] by reflexivity.
    move: [::].
    elim: p E f g =>
          [| i p IH] /= E f g visited Hunvi Hwfvi Hf Hp Hg Hun Hssa c Hinc.
    - case: Hinc => //= Hinc. subst; simpl. rewrite Hf /=.
      rewrite revK. rewrite (well_formed_ssa_well_formed Hwfvi) /=.
      rewrite Hg /=. rewrite (well_formed_ssa_unchanged Hwfvi) /=.
      exact: (well_formed_ssa_single_assignment Hwfvi).
    - move/andP: Hp => [Hi Hp]. move/andP: Hssa => [Huni Hssa].
      rewrite -program_succ_typenv_rcons in Hg.
      case: i Hinc Hunvi Hi Hp Hg Hun Huni; intros;
      match goal with
      | Hi : is_true (well_formed_instr _ (Icut _)) |- _ => idtac
      | |- _ => apply: (IH _ _ _ _ _ _ Hf _ Hg _ Hssa);
                try cut_spec_well_formed_ssa_tac
      end.
      (* Icut *)
      case: Hinc.
      + move=> ?; subst; simpl. rewrite Hf /=. rewrite revK (well_formed_ssa_well_formed Hwfvi) /=.
        rewrite /well_formed_instr /= in Hi. rewrite /well_formed_bexp Hi /=.
        rewrite (well_formed_ssa_unchanged Hwfvi) /=. exact: (well_formed_ssa_single_assignment Hwfvi).
      + rewrite -/(In _ _) revK => Hinc.
        apply: (IH _ _ _ [::] _ (well_formed_ssa_empty _) _ _ _ _ _ _ Hinc) => //=.
        rewrite program_succ_typenv_rcons /= in Hg. exact: Hg.
  Qed.

  Lemma cut_spec_well_formed_ssa_in s c :
    well_formed_ssa_spec s ->
    In c (cut_spec s) ->
    well_formed_ssa_spec c.
  Proof.
    move=> Hwf Hin. move/all_forall: (cut_spec_well_formed_ssa Hwf).
    apply; assumption.
  Qed.

  (* well_formed_ssa_spec - remove_asserts *)

  Lemma remove_asserts_program_unchanged vs p :
    ssa_vars_unchanged_program vs (remove_asserts_program p) =
      ssa_vars_unchanged_program vs p.
  Proof.
    elim: p => [| i p IH] //=. rewrite ssa_unchanged_program_cons. case_if.
    - rewrite ssa_unchanged_program_cons IH. reflexivity.
    - rewrite IH. case: i H => //=. move=> e _.
      rewrite ssa_unchanged_instr_assert /=. reflexivity.
  Qed.

  Lemma remove_asserts_program_single_assignment p :
    ssa_single_assignment p ->
    ssa_single_assignment (remove_asserts_program p).
  Proof.
    elim: p => [| i p IH] //=. move/andP=> [Hi Hp]. case_if.
    - simpl. rewrite remove_asserts_program_unchanged Hi (IH Hp). reflexivity.
    - exact: (IH Hp).
  Qed.

  Lemma remove_asserts_program_single_assignment_eq E p :
    well_formed_program E p ->
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment (remove_asserts_program p) = ssa_single_assignment p.
  Proof.
    move=> Hwf Hun. case Hssa: (ssa_single_assignment p).
    - exact: (remove_asserts_program_single_assignment Hssa).
    - apply/negP => H. apply/negPf: Hssa. move: Hwf Hun H.
      elim: p E => [| i p IH] //= E. move/andP=> [Hi Hp].
      rewrite ssa_unchanged_program_cons. move/andP=> [Huni Hunp].
      case_if.
    - rewrite ssa_single_assignment_cons in H0. move/andP: H0 => [Hunip Hssap].
      have HuniEp: ssa_vars_unchanged_program (vars_env (instr_succ_typenv i E)) p.
      { rewrite vars_env_instr_succ_typenv.
        rewrite ssa_unchanged_program_union. rewrite Hunp /=.
        rewrite -remove_asserts_program_unchanged Hunip /=. reflexivity. }
      rewrite -remove_asserts_program_unchanged Hunip /=.
      exact: (IH _ Hp HuniEp Hssap).
    - have Hlv: SSAVS.Equal (lvs_instr i) (SSAVS.empty) by case: i Hi Hp Huni H.
      rewrite Hlv /=. apply: (IH _ Hp _ H0).
      rewrite vars_env_instr_succ_typenv Hlv SSAVS.Lemmas.union_emptyr.
      exact: Hunp.
  Qed.

  Lemma remove_asserts_well_formed_ssa s :
    well_formed_ssa_spec s ->
    well_formed_ssa_spec (remove_asserts s).
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /=.
    move=> H; caseb H. move=> Hwf Hun Hssa.
    rewrite (remove_asserts_well_formed Hwf) /=.
    rewrite remove_asserts_program_unchanged Hun /=.
    exact: (remove_asserts_program_single_assignment Hssa).
  Qed.

  (* well_formed_ssa_spec - extract_asserts *)

  Lemma extract_asserts_unchanged s :
    ssa_vars_unchanged_program (vars_env (sinputs s)) (sprog s) ->
    all (fun a => ssa_vars_unchanged_program (vars_env (sinputs a)) (sprog a)) (extract_asserts s).
  Proof.
    rewrite /extract_asserts. case: s => E f p g /=. clear g. move=> Hun.
    apply/all_forall. move: (ssa_unchanged_program_empty (vars_env E)) Hun.
    have {2}->: [::] = rev [::] by reflexivity.
    move: [::].
    elim: p E f => [| i p IH] //= E f visited Hunvi Hunp a Hina.
    rewrite ssa_unchanged_program_cons in Hunp. move/andP: Hunp => [HunEi HunEp].
    case: i Hina HunEi => //=; intros;
    match goal with
    | H : is_true (ssa_vars_unchanged_instr _ (Iassert _)) |- _ => idtac
    | |- _ => repeat match goal with
                     | Hina : In _ (extract_asserts_rec (_ :: rev _) _ _ _) |- _ =>
                         rewrite -rev_rcons in Hina
                     | Hunvi : is_true (ssa_vars_unchanged_program (vars_env ?E) ?visited),
                         HunEi : is_true (ssa_vars_unchanged_instr (vars_env ?E) ?i),
                           HunEp : is_true (ssa_vars_unchanged_program (vars_env ?E) ?p),
                             Hina : In ?a (extract_asserts_rec (rev (rcons ?visited ?i)) ?E ?f ?p)
                       |- is_true (ssa_vars_unchanged_program (vars_env (sinputs ?a)) (sprog ?a)) =>
                         apply: (IH _ _ _ _ HunEp _ Hina);
                         rewrite ssa_unchanged_program_rcons Hunvi HunEi; reflexivity
                     end
    end.
    (* Iassert *)
    case: Hina => Hina.
    - subst; simpl. rewrite revK. exact: Hunvi.
    - exact: (IH _ _ _ Hunvi HunEp _ Hina).
  Qed.

  Lemma extract_asserts_unchanged_in s a :
    ssa_vars_unchanged_program (vars_env (sinputs s)) (sprog s) ->
    In a (extract_asserts s) ->
    ssa_vars_unchanged_program (vars_env (sinputs a)) (sprog a).
  Proof.
    move=> Hun Hin. move/all_forall: (extract_asserts_unchanged Hun).
    apply; assumption.
  Qed.

  Lemma extract_asserts_single_assignment s :
    ssa_single_assignment (sprog s) ->
    all (fun s => ssa_single_assignment (sprog s)) (extract_asserts s).
  Proof.
    rewrite /extract_asserts. case: s => E f p g /=. clear g.
    have: ssa_vars_unchanged_program (lvs_program [::]) p by done.
    have: ssa_single_assignment [::] by done.
    have {3}->: [::] = rev [::] by reflexivity.
    move: [::].
    elim: p E f => [| i p IH] //= E f visited Hssavi Hunvi Hssap.
    move/andP: Hssap => [Hunip Hssap].
    (case: i Hunvi Hunip => //); intros;
    match goal with
    | H : is_true (ssa_vars_unchanged_program (lvs_instr (Iassert _)) _) |- _ => idtac
    | |- _ => rewrite -rev_rcons;
              apply: (IH _ _ _ _ _ Hssap);
                by repeat
                     match goal with
                     | Hssavi : is_true (ssa_single_assignment ?visited),
                         Hunvi : is_true (ssa_vars_unchanged_program (lvs_program ?visited) (?i :: ?p))
                       |- is_true (ssa_single_assignment (rcons ?visited ?i)) =>
                         rewrite ssa_single_assignment_rcons
                                 Hssavi (ssa_unchanged_program_hd Hunvi); reflexivity
                     | Hunvi : is_true (ssa_vars_unchanged_program (lvs_program ?visited) (?i :: ?p)),
                         Hunip : is_true (ssa_vars_unchanged_program (lvs_instr ?i) ?p)
                       |- is_true (ssa_vars_unchanged_program (lvs_program (rcons ?visited ?i)) ?p) =>
                         rewrite lvs_program_rcons
                                 ssa_unchanged_program_union
                                 (ssa_unchanged_program_tl Hunvi) Hunip; reflexivity
                     end
    end.
    (* Iassert *)
    apply/all_forall => a. case=> Hina.
    - subst; simpl. rewrite revK. exact: Hssavi.
    - rewrite -/(In _ _) in Hina.
      move: (IH E f _ Hssavi (ssa_unchanged_program_tl Hunvi) Hssap).
      move/all_forall. apply. assumption.
  Qed.

  Lemma extract_asserts_single_assignment_in s a :
    ssa_single_assignment (sprog s) ->
    In a (extract_asserts s) ->
    ssa_single_assignment (sprog a).
  Proof.
    move=> Hssa Hin. move/all_forall: (extract_asserts_single_assignment Hssa).
    apply; assumption.
  Qed.

  Lemma extract_asserts_well_formed_ssa s :
    well_formed_ssa_spec s ->
    all well_formed_ssa_spec (extract_asserts s).
  Proof.
    rewrite /well_formed_ssa_spec. move=> /andP [/andP [Hwf Hun] Hssa].
    apply/all_forall => a Hin. rewrite (extract_asserts_well_formed_in Hin Hwf) /=.
    rewrite (extract_asserts_unchanged_in Hun Hin) /=.
    exact: (extract_asserts_single_assignment_in Hssa Hin).
  Qed.

  Lemma extract_asserts_well_formed_ssa_in s a :
    well_formed_ssa_spec s ->
    In a (extract_asserts s) ->
    well_formed_ssa_spec a.
  Proof.
    move=> Hwf Hin. move/all_forall: (extract_asserts_well_formed_ssa Hwf).
    apply. assumption.
  Qed.


  (* MA.agree - extract_asserts *)

  Lemma extract_asserts_agree_in s a :
    well_formed_ssa_spec s ->
    In a (extract_asserts s) ->
    MA.agree (vars_spec a)
             (program_succ_typenv (sprog a) (sinputs a))
             (program_succ_typenv (sprog s) (sinputs s)).
  Proof.
    rewrite /extract_asserts. case: s => E f p g /=. rewrite /well_formed_ssa_spec /well_formed_spec /=.
    move=> H. caseb H. move=> Hf Hp _ Hun Hssa. clear g.
    move: Hf Hp Hun Hssa.
    rewrite -{1 2 3 5}(cat0s p).
    have {4}->: [::] = rev [::] by reflexivity.
    move: [::].
    elim: p a E f => [| i p IH] a E f visited Hwff Hwfp Hun Hssa //=.
    (case: i Hwfp Hun Hssa => //=);
    try by (intros; rewrite -cat_rcons in Hwfp Hun Hssa *; apply: (IH _ _ _ _ Hwff Hwfp Hun Hssa);
            rewrite rev_rcons; exact: H).
    (* Iassert *)
    move=> e Hwf Hun Hssa Hin. case: Hin => Hin.
    - subst. rewrite /vars_spec /=. rewrite revK. rewrite program_succ_typenv_cat /=.
      apply: agree_program_succ_typenv_r1. rewrite -ssa_unchanged_program_disjoint_lvs.
      rewrite ssa_unchanged_program_union. move: (well_formed_bexp_vars_subset Hwff) => Hsubf.
      move: (ssa_unchanged_program_tl (proj2 (ssa_unchanged_program_cat1 Hun))) => HunEp.
      rewrite (ssa_unchanged_program_subset HunEp Hsubf) /=.
      rewrite ssa_unchanged_program_union. rewrite ssa_single_assignment_cat /= in Hssa.
      move/andP: Hssa => [/andP [Hssav Hssap] Hunv].
      move: (ssa_unchanged_program_tl Hunv) => Hunlvp.
      move: (well_formed_program_vars_subset (well_formed_program_cat1 Hwf)) => Hsubv.
      move: (ssa_unchanged_program_union2 HunEp Hunlvp) => HunElvp.
      rewrite (ssa_unchanged_program_subset HunElvp Hsubv) /=.
      move: (well_formed_program_cons1 (well_formed_program_cat2 Hwf)).
      rewrite well_formed_instr_assert => Hwfe.
      move: (well_formed_bexp_vars_subset Hwfe) => Hsube.
      rewrite vars_env_program_succ_typenv in Hsube.
      exact: (ssa_unchanged_program_subset HunElvp Hsube).
    - rewrite program_succ_typenv_cat /=. rewrite -program_succ_typenv_cat.
      apply: (IH _ _ _ _ Hwff _ _ _ Hin).
      + rewrite !well_formed_program_cat /= in Hwf *.
        move/andP: Hwf => [Hwfv /andP [_ Hwfp]]. by rewrite Hwfv Hwfp.
      + rewrite ssa_unchanged_program_cat.
        rewrite (proj1 (ssa_unchanged_program_cat1 Hun)) /=.
        exact: (ssa_unchanged_program_tl (proj2 (ssa_unchanged_program_cat1 Hun))).
      + move: (ssa_single_assignment_cat1 Hssa) => [Hssav [Hssaip Hunlv]].
        rewrite ssa_single_assignment_cat. rewrite Hssav /=.
        rewrite (proj2 (ssa_single_assignment_cons1 Hssaip)) /=.
        exact: (ssa_unchanged_program_tl Hunlv).
  Qed.

  (* MA.agree - cut_spec *)

  Lemma cut_spec_agree_in s c :
    well_formed_ssa_spec s ->
    In c (cut_spec s) ->
    MA.agree (vars_spec c)
             (program_succ_typenv (sprog c) (sinputs c))
             (program_succ_typenv (sprog s) (sinputs s)).
  Proof.
    case: s => E f p g. rewrite /well_formed_ssa_spec /well_formed_spec /=.
    move=> H; caseb H. move=> Hf Hp Hg Hun Hssa. rewrite /cut_spec /=.
    move: Hf Hp Hg Hun Hssa.
    move: (well_formed_ssa_empty E).
    have: ssa_vars_unchanged_program (vars_program [::]) p by done.
    have {3 4 5 7}->: E = program_succ_typenv [::] E by reflexivity.
    have {6}->: [::] = rev [::] by reflexivity.
    move: [::].
    elim: p E f g c =>
          [| i p IH] /= E f g c visited Hunvi Hwfvi Hf Hp Hg Hun Hssa Hinc.
    - case: Hinc => //=. move=> ?; subst; simpl. rewrite revK /vars_spec /=.
      exact: MA.agree_refl.
    - move/andP: Hp => [Hwfi Hwfp]. move/andP: Hssa => [Huni Hssap].
      case: i Hinc Hunvi Hg Hun Hwfi Hwfp Huni; intros;
      rewrite -program_succ_typenv_rcons in Hun Hg *;
        match goal with
        | Hi : is_true (well_formed_instr _ (Icut _)) |- _ => idtac
        | |- _ => apply: (IH _ _ _ _ _ _ _ Hf _ Hg _ Hssap);
                  try (cut_spec_well_formed_ssa_tac)
        end.
      (* Icut *)
      case: Hinc => Hinc.
      + subst; rewrite /vars_spec /=. rewrite revK program_succ_typenv_rcons /=.
        apply: agree_program_succ_typenv_r1. rewrite -ssa_unchanged_program_disjoint_lvs.
        (* env unchanged *)
        move: (ssa_unchanged_program_tl Hun). rewrite vars_env_program_succ_typenv.
        rewrite ssa_unchanged_program_union. move/andP=> [HunEp _].
        (* precondition unchanged *)
        move: (well_formed_bexp_vars_subset Hf) => Hsub.
        move: (ssa_unchanged_program_subset HunEp Hsub) => Hunfp.
        (* visited unchanged *)
        move: (ssa_unchanged_program_tl Hunvi) => Hunvp.
        (* cut condition unchanged *)
        rewrite /well_formed_instr /= in Hwfi. move/andP: Hwfi => [Hdefb _].
        rewrite are_defined_subset_env in Hdefb.
        rewrite vars_env_program_succ_typenv in Hdefb.
        move: (ssa_unchanged_program_subset Hunvp (lvs_program_subset _)) => Hunlvs.
        move: (ssa_unchanged_program_union2 HunEp Hunlvs) => {Hunlvs} HunElvs.
        move: (ssa_unchanged_program_subset HunElvs Hdefb) => {HunElvs Hdefb} Hunbp.
        (* *)
        rewrite ssa_unchanged_program_union Hunfp /=.
        rewrite ssa_unchanged_program_union Hunvp /=.
        exact: Hunbp.
      + rewrite -/(In c (cut_spec_rec [::] (program_succ_typenv (rev (rev visited)) E) b p g)) in Hinc.
        rewrite program_succ_typenv_rcons /= in Hg *. rewrite revK in Hinc.
        apply: (IH (program_succ_typenv visited E) b g c [::]) => //=.
        exact: well_formed_ssa_empty.
  Qed.

  Lemma cut_spec_agree s :
    well_formed_ssa_spec s ->
    Forall (fun c => MA.agree (vars_spec c)
                              (program_succ_typenv (sprog c) (sinputs c))
                              (program_succ_typenv (sprog s) (sinputs s))) (cut_spec s).
  Proof.
    move=> Hwf. apply/Forall_forall. move=> c Hinc.
    exact: (cut_spec_agree_in Hwf Hinc).
  Qed.

End Extra.


(** Properties of the conversion from SSA to SSALite *)

Section SSA2SSALite.

  Import SSALite.
  Import SSA.

  (* Programs containing neither cut nor assert statements *)

  Definition program_is_lite (p : SSA.program) : bool :=
    program_has_no_cut p && program_has_no_assert p.

  Lemma program_is_lite_cons i p :
    program_is_lite (i::p) = ~~ is_cut i && ~~ is_assert i && program_is_lite p.
  Proof.
    rewrite /program_is_lite /program_has_no_cut /program_has_no_assert /=.
    by btauto.
  Qed.

  Lemma program_is_lite_rcons p i :
    program_is_lite (rcons p i) = program_is_lite p && ~~ is_cut i && ~~ is_assert i.
  Proof.
    rewrite /program_is_lite /program_has_no_cut /program_has_no_assert /=.
    rewrite !has_rcons. by btauto.
  Qed.

  Lemma program_is_lite_cat p1 p2 :
    program_is_lite (p1 ++ p2) = program_is_lite p1 && program_is_lite p2.
  Proof.
    rewrite /program_is_lite /program_has_no_cut /program_has_no_assert /=.
    rewrite !has_cat. by btauto.
  Qed.

  Lemma program_is_lite_eval_instr_ok_exists E i s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    eval_instr E i (OK s1) s2 ->
    exists s3, s2 = OK s3.
  Proof.
    by (case: i => //=); intros; eval_instr_elim;
    match goal with
    | |- exists s : SSAStore.t, OK ?t = OK s => exists t; reflexivity
    end.
  Qed.

  Lemma program_is_lite_eval_program_ok_exists E p s1 s2 :
    program_is_lite p ->
    eval_program E p (OK s1) s2 ->
    exists s3, s2 = OK s3.
  Proof.
    elim: p E s1 s2 => [| i p IH] E s1 s2 //=.
    - move=> _. inversion_clear 1. case: s2 H0 => //=.
      move=> s _. exists s. reflexivity.
    - rewrite program_is_lite_cons. move/andP => [Hi Hp] Hevip.
      inversion_clear Hevip. move: (program_is_lite_eval_instr_ok_exists Hi H) => [s3 ?]; subst.
      move: (IH _ _ _ Hp H0) => [s4 ?]; subst. exists s4; reflexivity.
  Qed.

  Lemma program_is_lite_eval_program_cons_ok E i p s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    program_is_lite p ->
    eval_program E (i::p) (OK s1) (OK s2) ->
    exists s3, eval_instr E i (OK s1) (OK s3) /\
                 eval_program (instr_succ_typenv i E) p (OK s3) (OK s2).
  Proof.
    move=> Hi Hp Hevip. inversion_clear Hevip.
    move: (program_is_lite_eval_instr_ok_exists Hi H) => [s3 ?]; subst.
    exists s3; tauto.
  Qed.

  Lemma program_is_lite_split p :
    program_is_lite p = (SSA.program_has_no_cut p) && (program_has_no_assert p).
  Proof. reflexivity. Qed.


  (* Lite specifications *)

  Definition spec_is_lite (s : spec) : bool := program_is_lite (sprog s).

  Lemma spec_is_lite_split s :
    spec_is_lite s = (spec_has_no_cut s) && (spec_has_no_assert s).
  Proof. reflexivity. Qed.

  Lemma all_spec_is_lite_split ss :
    all spec_is_lite ss = (all spec_has_no_cut ss) && (all spec_has_no_assert ss).
  Proof.
    elim: ss => [| s ss IH] //=. rewrite IH. rewrite spec_is_lite_split.
    by btauto.
  Qed.

  Lemma cut_remove_asserts_is_lite s :
    all spec_is_lite (tmap remove_asserts (cut_spec s)).
  Proof.
    apply/all_forall. rewrite tmap_map=> t Hin.
    move: (in_map_exists Hin) => [c [Hc ?]]; subst.
    rewrite /spec_is_lite. rewrite program_is_lite_split.
    rewrite remove_asserts_program_preserve_no_cut.
    rewrite remove_asserts_program_has_no_assert andbT.
    move: (cut_spec_has_no_cut s). move/all_forall.
    by apply.
  Qed.

  Lemma cut_remove_asserts_is_lite_in s c :
    In c (cut_spec s) ->
    spec_is_lite (remove_asserts c).
  Proof.
    move=> Hin. move/all_forall: (cut_remove_asserts_is_lite s).
    apply. rewrite tmap_map. apply: in_map. assumption.
  Qed.

  Lemma cut_extract_asserts_ls_lite s :
    all spec_is_lite (tflatten (tmap extract_asserts (cut_spec s))).
  Proof.
    rewrite all_tflatten tmap_map. apply/all_forall. move=> nac Hin.
    move: (in_map_exists Hin) => [c [Hc ?]]; subst.
    rewrite all_spec_is_lite_split.
    move: (cut_spec_has_no_cut s) => /all_forall => Hnoc.
    rewrite (extract_asserts_preserve_no_cut (Hnoc _ Hc)) /=.
    exact: extract_asserts_has_no_assert.
  Qed.

  Lemma cut_extract_asserts_ls_lite_in s c a :
    In c (cut_spec s) ->
    In a (extract_asserts c) ->
    spec_is_lite a.
  Proof.
    move=> Hc Ha. move/all_forall: (cut_extract_asserts_ls_lite s).
    apply. exact: (in_tflatten_tmap Hc Ha).
  Qed.


  (* Conversion from SSA to SSALite *)

  Lemma ssa2lite_program_cons i p :
    ssa2lite_program (i::p) = ssa2lite_instr i::ssa2lite_program p.
  Proof.
    rewrite /ssa2lite_program tmap_map /= -tmap_map. reflexivity.
  Qed.

  Lemma ssa2lite_program_rcons p i :
    ssa2lite_program (rcons p i) = rcons (ssa2lite_program p) (ssa2lite_instr i).
  Proof.
    rewrite /ssa2lite_program tmap_map map_rcons -tmap_map. reflexivity.
  Qed.

  Lemma ssa2lite_program_cat p1 p2 :
    ssa2lite_program (p1 ++ p2) = ssa2lite_program p1 ++ ssa2lite_program p2.
  Proof.
    rewrite /ssa2lite_program tmap_map map_cat -!tmap_map. reflexivity.
  Qed.

  Lemma ssa2lite_instr_lvs i :
    SSAVS.Equal (SSALite.lvs_instr (ssa2lite_instr i)) (lvs_instr i).
  Proof. by case: i => //=. Qed.

  Lemma ssa2lite_instr_vars_subset i :
    SSAVS.subset (SSALite.vars_instr (ssa2lite_instr i)) (vars_instr i).
  Proof. case: i => //=; intros; exact: VSLemmas.subset_refl. Qed.

  Lemma ssa2lite_program_vars_subset p :
    SSAVS.subset (SSALite.vars_program (ssa2lite_program p)) (vars_program p).
  Proof.
    elim: p => [| i p IH] //=. rewrite ssa2lite_program_cons /=.
    exact: (VSLemmas.union_subsets (ssa2lite_instr_vars_subset i) IH).
  Qed.

  Lemma ssa2lite_spec_vars_subset s :
    SSAVS.subset (SSALite.vars_spec (ssa2lite_spec s)) (vars_spec s).
  Proof.
    rewrite /ssa2lite_spec /SSALite.vars_spec /vars_spec. case: s => E f p g /=.
    apply: (VSLemmas.union_subsets (VSLemmas.subset_refl _)).
    apply: (VSLemmas.union_subsets _ (VSLemmas.subset_refl _)).
    exact: (ssa2lite_program_vars_subset p).
  Qed.

  Lemma ssa2lite_instr_vars_equal E i :
    well_formed_instr E i ->
    SSAVS.Equal (SSAVS.union (vars_env E) (SSALite.vars_instr (ssa2lite_instr i)))
                (SSAVS.union (vars_env E) (vars_instr i)).
  Proof.
    case: i => //=.
    all: move=> e Hwf.
    all: rewrite SSAVS.Lemmas.union_emptyr.
    all: move: (well_formed_instr_subset_rvs Hwf) => /= Hsub.
    all: rewrite VSLemmas.P.union_sym.
    all: rewrite (VSLemmas.union_subset_equal Hsub).
    all: reflexivity.
  Qed.

  Lemma ssa2lite_program_vars_equal E p :
    well_formed_program E p ->
    SSAVS.Equal (SSAVS.union (vars_env E) (SSALite.vars_program (ssa2lite_program p)))
                (SSAVS.union (vars_env E) (vars_program p)).
  Proof.
    elim: p E => [| i p IH] E //=. move/andP=> [Hwfi Hwfp].
    rewrite ssa2lite_program_cons /=.
    move: (IH _ Hwfp). rewrite vars_env_instr_succ_typenv.
    have ->:
         SSAVS.Equal
         (SSAVS.union (vars_env E) (SSAVS.union (vars_instr i) (vars_program p)))
         (SSAVS.union (vars_instr i) (SSAVS.union (SSAVS.union (vars_env E) (lvs_instr i)) (vars_program p))).
    { rewrite vars_instr_split. by VSLemmas.dp_Equal. }
    move=> <-.
    have ->:
         SSAVS.Equal
         (SSAVS.union (vars_instr i)
                      (SSAVS.union (SSAVS.union (vars_env E) (lvs_instr i)) (SSALite.vars_program (ssa2lite_program p))))
         (SSAVS.union (SSAVS.union (vars_env E) (vars_instr i)) (SSALite.vars_program (ssa2lite_program p))).
    { rewrite vars_instr_split. by VSLemmas.dp_Equal. }
    rewrite -VSLemmas.P.union_assoc. rewrite (ssa2lite_instr_vars_equal Hwfi).
    reflexivity.
  Qed.

  Lemma ssa2lite_spec_vars_equal s :
    well_formed_spec s ->
    SSAVS.Equal (SSAVS.union (vars_env (SSALite.sinputs (ssa2lite_spec s))) (SSALite.vars_spec (ssa2lite_spec s)))
                (SSAVS.union (vars_env (sinputs s)) (vars_spec s)).
  Proof.
    case: s => E f p g /=. rewrite /well_formed_spec /ssa2lite_spec /SSALite.vars_spec /vars_spec /=.
    move=> /andP [/andP [_ Hwfp] _].
    have ->:
         SSAVS.Equal
         (SSAVS.union (vars_env E)
                      (SSAVS.union (SSALite.vars_bexp f)
                                   (SSAVS.union (SSALite.vars_program (ssa2lite_program p)) (SSALite.vars_bexp g))))
         (SSAVS.union (SSALite.vars_bexp f)
                      (SSAVS.union (SSALite.vars_bexp g)
                                   (SSAVS.union (vars_env E) (SSALite.vars_program (ssa2lite_program p)))))
      by VSLemmas.dp_Equal.
    rewrite (ssa2lite_program_vars_equal Hwfp).
    have ->:
         SSAVS.Equal
         (SSAVS.union (vars_env E) (SSAVS.union (vars_bexp f) (SSAVS.union (vars_program p) (vars_bexp g))))
         (SSAVS.union (vars_bexp f) (SSAVS.union (vars_bexp g) (SSAVS.union (vars_env E) (vars_program p))))
      by VSLemmas.dp_Equal.
    reflexivity.
  Qed.


  (* Typing environments *)

  Lemma ssa2lite_instr_succ_typenv E i :
    SSALite.instr_succ_typenv (ssa2lite_instr i) E = instr_succ_typenv i E.
  Proof. by case: i. Qed.

  Lemma ssa2lite_program_succ_typenv E p :
    SSALite.program_succ_typenv (ssa2lite_program p) E = program_succ_typenv p E.
  Proof.
    elim: p E => [| i p IH] E //=. rewrite ssa2lite_program_cons /=.
    rewrite ssa2lite_instr_succ_typenv. exact: IH.
  Qed.

  Lemma ssa2lite_spec_succ_typenv s :
    SSALite.program_succ_typenv (SSALite.sprog (ssa2lite_spec s)) (SSALite.sinputs (ssa2lite_spec s))
    = SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s).
  Proof. case: s => E f p g. exact: ssa2lite_program_succ_typenv. Qed.


  (* Evaluation *)

  Lemma ssa2lite_instr_sound E i s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    SSALite.eval_instr E (ssa2lite_instr i) s1 s2 ->
    eval_instr E i (OK s1) (OK s2).
  Proof.
    (case: i => //=); intros; SSALite.eval_instr_elim;
    repeat match goal with
           | H : context [SSALite.atyp] |- _ =>
               change SSALite.atyp with atyp in H
           | H : context [SSALite.eval_atom] |- _ =>
               change SSALite.eval_atom with eval_atom in H
           end; try (eval_instr_intro; assumption).
    apply: (EInondet _ H1). assumption.
  Qed.

  Lemma ssa2lite_instr_complete E i s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    eval_instr E i (OK s1) (OK s2) ->
    SSALite.eval_instr E (ssa2lite_instr i) s1 s2.
  Proof.
    (case: i => //=); intros; eval_instr_elim;
    repeat match goal with
           | H : context [atyp] |- _ =>
               change atyp with SSALite.atyp in H
           | H : context [eval_atom] |- _ =>
               change eval_atom with SSALite.eval_atom in H
           end; try (SSALite.eval_instr_intro; assumption).
    apply: (SSALite.EInondet _ H1). assumption.
  Qed.

  Lemma ssa2lite_instr_eval E i s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    SSALite.eval_instr E (ssa2lite_instr i) s1 s2 <->
      eval_instr E i (OK s1) (OK s2).
  Proof.
    by intuition auto using ssa2lite_instr_sound, ssa2lite_instr_complete.
  Qed.

  Lemma ssa2lite_program_sound E p s1 s2 :
    program_is_lite p ->
    SSALite.eval_program E (ssa2lite_program p) s1 s2 ->
    eval_program E p (OK s1) (OK s2).
  Proof.
    elim: p E s1 s2 => [| i p IH] E s1 s2 //=.
    - move=> _. inversion_clear 1. apply: Enil. simpl; assumption.
    - rewrite program_is_lite_cons ssa2lite_program_cons. move/andP=> /= [Hi Hp] Hevip.
      inversion_clear Hevip. apply: (Econs (ssa2lite_instr_sound Hi H)).
      rewrite ssa2lite_instr_succ_typenv in H0. exact: (IH _ _ _ Hp H0).
  Qed.

  Lemma ssa2lite_program_complete E p s1 s2 :
    program_is_lite p ->
    eval_program E p (OK s1) (OK s2) ->
    SSALite.eval_program E (ssa2lite_program p) s1 s2.
  Proof.
    elim: p E s1 s2 => [| i p IH] E s1 s2 //=.
    - move=> _. inversion_clear 1. apply: SSALite.Enil. simpl; assumption.
    - rewrite program_is_lite_cons ssa2lite_program_cons. move/andP=> /= [Hi Hp] Hevip.
      move: (program_is_lite_eval_program_cons_ok Hi Hp Hevip) => [s3 [Hevi Hevp]].
      apply: (SSALite.Econs (ssa2lite_instr_complete Hi Hevi)).
      rewrite ssa2lite_instr_succ_typenv. exact: (IH _ _ _ Hp Hevp).
  Qed.

  Lemma ssa2lite_spec_sound s :
    spec_is_lite s ->
    SSALite.valid_spec (ssa2lite_spec s) ->
    SSA.valid_spec s.
  Proof.
    case: s => E f p g /=.
    rewrite /SSALite.valid_spec /valid_spec /valid_spec_ok /valid_spec_err
            /ssa2lite_spec /=.
    move=> Hnca Hv. rewrite ssa2lite_program_succ_typenv in Hv. split.
    - move=> s1 s2 Hco Hevf Hevp. apply: (Hv _ _ Hco Hevf).
      exact: (ssa2lite_program_complete Hnca Hevp).
    - move=> s Hco Hevf Hevp. move: (program_is_lite_eval_program_ok_exists Hnca Hevp) => [t H].
      discriminate.
  Qed.

  Lemma ssa2lite_spec_complete s :
    spec_is_lite s ->
    SSA.valid_spec s ->
    SSALite.valid_spec (ssa2lite_spec s).
  Proof.
    case: s => E f p g /=. rewrite /SSALite.valid_spec /valid_spec /valid_spec_ok /valid_spec_err
                                   /ssa2lite_spec /=.
    move=> Hnca [Hvok Hverr]. rewrite ssa2lite_program_succ_typenv.
    move=> s1 s2 Hco Hevf Hevp. apply: (Hvok _ _ Hco Hevf).
    exact: (ssa2lite_program_sound Hnca Hevp).
  Qed.


  (* Well-formedness *)

  Lemma ssa2lite_instr_well_formed E i :
    ~~ is_cut i && ~~ is_assert i ->
    SSALite.well_formed_instr E (ssa2lite_instr i) = SSA.well_formed_instr E i.
  Proof. by case: i => //=. Qed.

  Lemma ssa2lite_program_well_formed E p :
    program_is_lite p ->
    SSALite.well_formed_program E (ssa2lite_program p) = SSA.well_formed_program E p.
  Proof.
    elim: p E => [| i p IH] E //=. rewrite program_is_lite_cons => /andP [Hncai Hncap].
    rewrite ssa2lite_program_cons /=. rewrite (ssa2lite_instr_well_formed _ Hncai).
    rewrite (IH _ Hncap). rewrite ssa2lite_instr_succ_typenv. reflexivity.
  Qed.

  Lemma ssa2lite_instr_unchanged vs i :
    SSALite.ssa_vars_unchanged_instr vs (ssa2lite_instr i) =
      SSA.ssa_vars_unchanged_instr vs i.
  Proof. by case: i => //=. Qed.

  Lemma ssa2lite_program_unchanged vs p :
    SSALite.ssa_vars_unchanged_program vs (ssa2lite_program p) =
      SSA.ssa_vars_unchanged_program vs p.
  Proof.
    elim: p => [| i p IH] //=.
    rewrite ssa2lite_program_cons.
    rewrite SSA.ssa_unchanged_program_cons SSALite.ssa_unchanged_program_cons.
    rewrite ssa2lite_instr_unchanged IH. reflexivity.
  Qed.

  Lemma ssa2lite_program_single_assignment p :
    SSALite.ssa_single_assignment (ssa2lite_program p) = SSA.ssa_single_assignment p.
  Proof.
    elim: p => [| i p IH] //=. rewrite ssa2lite_program_cons /=.
    rewrite ssa2lite_instr_lvs ssa2lite_program_unchanged IH. reflexivity.
  Qed.

  Lemma ssa2lite_program_well_formed_ssa E p :
    program_is_lite p ->
    SSALite.well_formed_ssa_program E (ssa2lite_program p) =
      SSA.well_formed_ssa_program E p.
  Proof.
    elim: p E => [| i p IH] E //=.
    rewrite program_is_lite_cons; move/andP => [Hncai Hncap].
    rewrite ssa2lite_program_cons /SSA.well_formed_ssa_program / SSALite.well_formed_ssa_program /=.
    rewrite (ssa2lite_instr_well_formed _ Hncai).
    rewrite ssa2lite_instr_succ_typenv (ssa2lite_program_well_formed _ Hncap).
    rewrite SSA.ssa_unchanged_program_cons SSALite.ssa_unchanged_program_cons
            ssa2lite_instr_unchanged ssa2lite_program_unchanged.
    rewrite ssa2lite_instr_lvs ssa2lite_program_unchanged.
    rewrite ssa2lite_program_single_assignment. reflexivity.
  Qed.

  Lemma ssa2lite_spec_well_formed s :
    spec_is_lite s ->
    SSALite.well_formed_spec (ssa2lite_spec s) = SSA.well_formed_spec s.
  Proof.
    case: s => E f p g. rewrite /spec_is_lite /SSA.well_formed_spec /SSALite.well_formed_spec /=.
    move=> Hpl. rewrite ssa2lite_program_succ_typenv.
    replace (SSALite.well_formed_bexp E f) with (SSA.well_formed_bexp E f) by reflexivity.
    replace (SSALite.well_formed_bexp (program_succ_typenv p E) g) with
      (SSA.well_formed_bexp (program_succ_typenv p E) g) by reflexivity.
    rewrite (ssa2lite_program_well_formed _ Hpl) /=.
    reflexivity.
  Qed.

  Lemma ssa2lite_spec_well_formed_ssa s :
    spec_is_lite s ->
    SSALite.well_formed_ssa_spec (ssa2lite_spec s) = SSA.well_formed_ssa_spec s.
  Proof.
    case: s => E f p g. rewrite /SSA.well_formed_ssa_spec /SSALite.well_formed_ssa_spec /=.
    move=> Hsl. rewrite (ssa2lite_spec_well_formed Hsl).
    rewrite ssa2lite_program_unchanged. rewrite ssa2lite_program_single_assignment.
    reflexivity.
  Qed.

End SSA2SSALite.
