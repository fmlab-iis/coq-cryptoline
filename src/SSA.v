From Coq Require Import List ZArith FSets OrderedType.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State BBCommon.
From ssrlib Require Import Var SsrOrder FMaps ZAriths Tactics Lists FSets.
From Cryptoline Require Import DSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Module SSA := MakeDSL SSAVarOrder SSAVS SSAVM SSATE SSAStore.

Module M2 := Map2 VS SSAVS.

Section MakeSSA.

  Open Scope N_scope.

  (* A map from a variable to its current index *)
  Definition vmap : Type := VM.t N.

  Definition empty_vmap : vmap := VM.empty N.

  Definition initial_index : N := 0.

  Definition first_assigned_index : N := 1.

  (* Find the current index of a variable *)
  Definition get_index (v : var) (m : vmap) : N :=
    match VM.find v m with
    | None => initial_index
    | Some i => i
    end.

  (* Increment the current index of a variable *)
  Definition upd_index (v : var) (m : vmap) : vmap :=
    match VM.find v m with
    | None => VM.add v first_assigned_index m
    | Some i => VM.add v (i + 1) m
    end.

  Definition ssa_var (m : vmap) (v : var) : ssavar := (v, get_index v m).

  Definition svar (x : ssavar) := fst x.
  Definition sidx (x : ssavar) := snd x.
  Hint Unfold svar sidx.

  Lemma ssa_var_preserve m : M2.preserve (ssa_var m).
  Proof.
    move=> x y H.
    rewrite (eqP H).
    exact: eqxx.
  Qed.

  Lemma ssa_var_injective m : M2.injective (ssa_var m).
  Proof.
    move=> x y /eqP H.
    case: H => H _.
    rewrite H; exact: eqxx.
  Qed.

  Definition ssa_var_well m :=
    M2.mkWellMap2 (ssa_var_preserve m) (ssa_var_injective (m:=m)).

  Definition ssa_vars (m : vmap) (vs : VS.t) : SSAVS.t :=
    M2.map2 (ssa_var m) vs.

  Definition ssa_atomic (m : vmap) (a : DSL.atomic) : SSA.atomic :=
    match a with
    | DSL.Avar v => SSA.Avar (ssa_var m v)
    | DSL.Aconst ty n => SSA.Aconst ty n
    end.

  Fixpoint ssa_eexp (m : vmap) (e : DSL.eexp) : SSA.eexp :=
    match e with
    | Evar v => SSA.evar (ssa_var m v)
    | Econst c => SSA.econst c
    | Eunop op e => SSA.eunary op (ssa_eexp m e)
    | Ebinop op e1 e2 => SSA.ebinary op (ssa_eexp m e1) (ssa_eexp m e2)
    end.

  Fixpoint ssa_rexp (m : vmap) (e : DSL.rexp) :=
    match e with
    | Rvar v => SSA.rvar (ssa_var m v)
    | Rconst w n => SSA.rconst w n
    | Runop w op e => SSA.runary w op (ssa_rexp m e)
    | Rbinop w op e1 e2 => SSA.rbinary w op (ssa_rexp m e1) (ssa_rexp m e2)
    | Ruext w e i => SSA.ruext w (ssa_rexp m e) i
    | Rsext w e i => SSA.rsext w (ssa_rexp m e) i
    end.

  Fixpoint ssa_ebexp (m : vmap) (e : DSL.ebexp) :=
    match e with
    | Etrue => SSA.etrue
    | Eeq e1 e2 => SSA.eeq (ssa_eexp m e1) (ssa_eexp m e2)
    | Eeqmod e1 e2 p => SSA.eeqmod (ssa_eexp m e1) (ssa_eexp m e2) (ssa_eexp m p)
    | Eand e1 e2 => SSA.eand (ssa_ebexp m e1) (ssa_ebexp m e2)
    end.

  Fixpoint ssa_rbexp (m : vmap) (e : DSL.rbexp) :=
    match e with
    | Rtrue => SSA.rtrue
    | Req w e1 e2 => SSA.req w (ssa_rexp m e1) (ssa_rexp m e2)
    | Rcmp w op e1 e2 => SSA.rcmp w op (ssa_rexp m e1) (ssa_rexp m e2)
    | Rneg e => SSA.rneg (ssa_rbexp m e)
    | Rand e1 e2 => SSA.rand (ssa_rbexp m e1) (ssa_rbexp m e2)
    | Ror e1 e2 => SSA.ror (ssa_rbexp m e1) (ssa_rbexp m e2)
    end.

  Definition ssa_bexp (m : vmap) (e : DSL.bexp) :=
    (ssa_ebexp m (DSL.eqn_bexp e) , ssa_rbexp m (DSL.rng_bexp e)).

  Definition ssa_instr (m : vmap) (i : DSL.instr) : vmap * SSA.instr :=
    match i with
    | DSL.Imov v a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, SSA.Imov (ssa_var m v) a)
    | DSL.Ishl v a p =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, SSA.Ishl (ssa_var m v) a p)
    | DSL.Icshl vh vl a1 a2 p =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let ml := upd_index vl m in
      let mh := upd_index vh ml in
      (mh, SSA.Icshl (ssa_var mh vh) (ssa_var ml vl) a1 a2 p)
    | DSL.Inondet v ty =>
      let m := upd_index v m in
      (m, SSA.Inondet (ssa_var m v) ty)
    | DSL.Icmov v c a1 a2 =>
      let c := ssa_atomic m c in
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Icmov (ssa_var m v) c a1 a2)
    | DSL.Inop => (m, SSA.Inop)
    | DSL.Inot v ty a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, SSA.Inot (ssa_var m v) ty a)
    | DSL.Iadd v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Iadd (ssa_var m v) a1 a2)
    | DSL.Iadds c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, SSA.Iadds (ssa_var mc c) (ssa_var mv v) a1 a2)
    | DSL.Iadc v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let m := upd_index v m in
      (m, SSA.Iadc (ssa_var m v) a1 a2 y)
    | DSL.Iadcs c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, SSA.Iadcs (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | DSL.Isub v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Isub (ssa_var m v) a1 a2)
    | DSL.Isubc c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, SSA.Isubc (ssa_var mc c) (ssa_var mv v) a1 a2)
    | DSL.Isubb c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, SSA.Isubb (ssa_var mc c) (ssa_var mv v) a1 a2)
    | DSL.Isbc v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let m := upd_index v m in
      (m, SSA.Isbc (ssa_var m v) a1 a2 y)
    | DSL.Isbcs c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, SSA.Isbcs (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | DSL.Isbb v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let m := upd_index v m in
      (m, SSA.Isbb (ssa_var m v) a1 a2 y)
    | DSL.Isbbs c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, SSA.Isbbs (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | DSL.Imul v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Imul (ssa_var m v) a1 a2)
    | DSL.Imull vh vl a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let ml := upd_index vl m in
      let mh := upd_index vh ml in
      (mh, SSA.Imull (ssa_var mh vh) (ssa_var ml vl) a1 a2)
    | DSL.Imulj v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Imulj (ssa_var m v) a1 a2)
    | DSL.Isplit vh vl a n =>
      let a := ssa_atomic m a in
      let ml := upd_index vl m in
      let mh := upd_index vh ml in
      (mh, SSA.Isplit (ssa_var mh vh) (ssa_var ml vl) a n)
    | DSL.Iand v ty a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Iand (ssa_var m v) ty a1 a2)
    | DSL.Ior v ty a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Ior (ssa_var m v) ty a1 a2)
    | DSL.Ixor v ty a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Ixor (ssa_var m v) ty a1 a2)
    | DSL.Icast v ty a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, SSA.Icast (ssa_var m v) ty a)
    | DSL.Ivpc v ty a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, SSA.Ivpc (ssa_var m v) ty a)
    | DSL.Ijoin v ah al =>
      let ah := ssa_atomic m ah in
      let al := ssa_atomic m al in
      let m := upd_index v m in
      (m, SSA.Ijoin (ssa_var m v) ah al)
    | DSL.Iassume e => (m, SSA.Iassume (ssa_bexp m e))
    end.

  Fixpoint ssa_program (m : vmap) (p : DSL.program) : vmap * SSA.program :=
    match p with
    | [::] => (m, [::])
    | hd::tl =>
      let (m, hd) := ssa_instr m hd in
      let (m, tl) := ssa_program m tl in
      (m, hd::tl)
    end.

  (* map only keys *)

  Definition add_to_ste m k v (e: SSATE.env) := SSATE.add (ssa_var m k) v e.

  Definition ssa_typenv (m: vmap) (te: TE.env) : SSATE.env :=
    TE.fold (add_to_ste m) te (SSATE.empty typ).

  Definition ssa_spec (s : DSL.spec) : SSA.spec :=
    let m := empty_vmap in
    let si := ssa_typenv m (DSL.sinputs s) in
    let f := ssa_bexp m (DSL.spre s) in
    let (m, p) := ssa_program m (DSL.sprog s) in
    let g := ssa_bexp m (DSL.spost s) in
    {| SSA.sinputs := si;
       SSA.spre := f;
       SSA.sprog := p;
       SSA.spost := g;
    |}.

  Lemma ssa_program_empty : forall m, ssa_program m [::] = (m, [::]).
  Proof.
    reflexivity.
  Qed.

  Lemma ssa_program_cons :
    forall m1 m2 hd tl p,
      ssa_program m1 (hd::tl) = (m2, p) ->
      exists m3 h t,
        ssa_instr m1 hd = (m3, h) /\ ssa_program m3 tl = (m2, t) /\ p = h::t.
  Proof.
    move=> m1 m2 hd tl p /=.
    set tmp := ssa_instr m1 hd.
    have: (tmp = ssa_instr m1 hd) by reflexivity.
    destruct tmp as [m3 h].
    set tmp := ssa_program m3 tl.
    have: (tmp = ssa_program m3 tl) by reflexivity.
    destruct tmp as [m4 t].
    move=> Htl Hhd [] Hm Hp.
    exists m3; exists h; exists t; split; [idtac | split].
    - reflexivity.
    - rewrite -Htl Hm.
      reflexivity.
    - symmetry; exact: Hp.
  Qed.

  Lemma ssa_spec_unfold s :
    exists m,
      SSA.sinputs (ssa_spec s) = ssa_typenv empty_vmap (DSL.sinputs s) /\
      SSA.spre (ssa_spec s) = ssa_bexp empty_vmap (DSL.spre s) /\
      (m, SSA.sprog (ssa_spec s)) = ssa_program empty_vmap (DSL.sprog s) /\
      SSA.spost (ssa_spec s) = ssa_bexp m (DSL.spost s).
  Proof.
    destruct s as [si f p g sep srp] => /=.
    rewrite /ssa_spec /=.
    set tmp := ssa_program empty_vmap p.
    destruct tmp as [m sp] => /=.
    exists m; repeat split; reflexivity.
  Qed.

  Lemma get_index_empty v :
    get_index v empty_vmap = 0.
  Proof.
    done.
  Qed.

  Lemma get_index_add_eq x y i s :
    x == y ->
    get_index x (VM.add y i s) = i.
  Proof.
    move=> Heq.
    rewrite (eqP Heq) /get_index (VM.Lemmas.add_eq_o _ _ (eqxx y)).
    reflexivity.
  Qed.

  Lemma get_index_add_neq x y i s :
    x != y ->
    get_index x (VM.add y i s) = get_index x s.
  Proof.
    move=> /negP Hne.
    rewrite eq_sym in Hne.
    rewrite /get_index (VM.Lemmas.add_neq_o _ _ Hne).
    reflexivity.
  Qed.

  Lemma get_upd_index_gt0 :
    forall (m : vmap) (v : var),
      0 <? get_index v (upd_index v m).
  Proof.
    move=> m v; rewrite /upd_index.
    case: (VM.find v m) => /=.
    - move=> a.
      rewrite (get_index_add_eq _ _ (eqxx v)).
      exact: Nltn0Sn.
    - rewrite (get_index_add_eq _ _ (eqxx v)).
      done.
  Qed.

  Lemma get_upd_index_lt :
    forall (m : vmap) (v : var),
      get_index v m <? get_index v (upd_index v m).
  Proof.
    move=> m v; rewrite /upd_index /get_index.
    case: (VM.find v m) => /=.
    - move=> a.
      rewrite (VM.Lemmas.add_eq_o _ _ (eqxx v)).
      exact: NltnSn.
    - rewrite (VM.Lemmas.add_eq_o _ _ (eqxx v)).
      done.
  Qed.

  Lemma get_upd_index_leF :
    forall (m : vmap) (v : var),
      get_index v (upd_index v m) <=? get_index v m -> False.
  Proof.
    move=> m v Hle.
    move: (get_upd_index_lt m v) => Hlt.
    move: (Nleq_ltn_trans Hle Hlt).
    rewrite Nltnn.
    done.
  Qed.

  Lemma get_upd_index_eq :
    forall (m : vmap) (v : var),
      get_index v (upd_index v m) = get_index v m + 1.
  Proof.
    move=> m v.
    rewrite /upd_index.
    case H: (VM.find v m).
    - rewrite /get_index.
      rewrite (VM.Lemmas.add_eq_o m _ (eqxx v)).
      rewrite H.
      reflexivity.
    - rewrite /get_index.
      rewrite (VM.Lemmas.add_eq_o m _ (eqxx v)).
      rewrite H.
      reflexivity.
  Qed.

  Lemma get_upd_index_neq :
    forall (m : vmap) (x v : var),
      x != v ->
      get_index x (upd_index v m) = get_index x m.
  Proof.
    move=> m x v => /negP Hne.
    rewrite eq_sym in Hne.
    rewrite /upd_index /get_index.
    case: (VM.find v m).
    - move=> a.
      rewrite (VM.Lemmas.add_neq_o _ _ Hne).
      reflexivity.
    - rewrite (VM.Lemmas.add_neq_o _ _ Hne).
      reflexivity.
  Qed.

  Lemma get_upd_index_le :
    forall (m : vmap) (x v : var),
      get_index x m <=? get_index x (upd_index v m).
  Proof.
    move=> m x v.
    case Hxv: (x == v).
    - move: (get_upd_index_lt m v) => Hlt.
      rewrite (eqP Hxv).
      exact: (NltnW Hlt).
    - move/idP/negP: Hxv => Hxv.
      rewrite (get_upd_index_neq _ Hxv).
      exact: Nleqnn.
  Qed.

  Lemma ssa_instr_index_le :
    forall m1 m2 v i si,
      ssa_instr m1 i = (m2, si) ->
      get_index v m1 <=? get_index v m2.
  Proof.
    move=> m1 m2 v i si.
    elim: i m1 m2 v si; intros;
      (let rec tac :=
           match goal with
           | H: ssa_instr _ _ = (_, _) |- _ =>
             case: H => <- Hsi; tac
           | |- is_true (get_index ?v ?m1 <=? get_index ?v (upd_index ?t ?m1)) =>
             exact: get_upd_index_le
           | |- is_true (get_index ?v ?m1 <=? get_index ?v (upd_index ?vl (upd_index ?vh m1))) =>
             move: (get_upd_index_le m1 v vh) => Hle1; move: (get_upd_index_le (upd_index vh m1) v vl) => Hle2; exact: (Nleq_trans Hle1 Hle2)
           | |- is_true (get_index ?v ?m <=? get_index ?v ?m) => exact: Nleqnn
           | |- _ => idtac
           end in
       tac).
  Qed.

  Lemma ssa_program_index_le :
    forall m1 m2 v p sp,
      ssa_program m1 p = (m2, sp) ->
      get_index v m1 <=? get_index v m2.
  Proof.
    move=> m1 m2 v p sp.
    elim: p m1 m2 v sp.
    - move=> m1 m2 v sp Hsp.
      rewrite ssa_program_empty in Hsp.
      case: Hsp => Hm1 Hsp.
      rewrite Hm1; exact: Nleqnn.
    - move=> hd tl IH m1 m2 v sp Hsp.
      move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
      move: (ssa_instr_index_le v Hshd) => Hle1.
      move: (IH _ _ v _ Hstl) => Hle2.
      exact: (Nleq_trans Hle1 Hle2).
  Qed.

  Lemma ssa_var_upd_eq v m :
    ssa_var (upd_index v m) v = (v, get_index v (upd_index v m)).
  Proof.
    reflexivity.
  Qed.

  Lemma ssa_var_upd_neq x v m :
    x != v ->
    ssa_var (upd_index v m) x = ssa_var m x.
  Proof.
    move=> Hxv.
    rewrite /ssa_var.
    rewrite (get_upd_index_neq _ Hxv).
    reflexivity.
  Qed.

  Lemma ssa_vars_mem_elements m v vs :
    SSAVS.mem v (ssa_vars m vs) = (v \in (SSAVS.elements (ssa_vars m vs))).
  Proof.
    move: (SSAVS.Lemmas.F.elements_iff (ssa_vars m vs) v) => [HinA Hin].
    case Hv: (v \in SSAVS.elements (ssa_vars m vs)).
    - move/InAP: Hv => Hv.
      apply/SSAVS.Lemmas.memP.
      apply: Hin.
      assumption.
    - move/negP: Hv => Hv.
      apply/negP => /SSAVS.Lemmas.memP Hmem.
      apply: Hv.
      apply/InAP.
      apply: HinA.
      assumption.
  Qed.

  Lemma ssa_vars_Empty m vs :
    VS.Empty vs ->
    SSAVS.Empty (ssa_vars m vs).
  Proof.
    exact: M2.map2_Empty1.
  Qed.

  Lemma ssa_vars_mem1 m v vs :
    SSAVS.mem (ssa_var m v) (ssa_vars m vs) = VS.mem v vs.
  Proof.
    exact: (M2.map2_mem1 (ssa_var_well m)).
  Qed.

  Lemma ssa_vars_mem2 m v vs :
    SSAVS.mem v (ssa_vars m vs) ->
    exists x, v = ssa_var m x /\ VS.mem x vs.
  Proof.
    move=> Hmem; move: (M2.map2_mem2 Hmem) => [y [/eqP Hy Hmemy]].
    rewrite Hy.
      by exists y.
  Qed.

  Lemma ssa_vars_mem3 m v i vs :
    VS.mem v vs ->
    i = get_index v m ->
    SSAVS.mem (v, i) (ssa_vars m vs).
  Proof.
    move=> Hmem Hidx.
    rewrite Hidx.
    rewrite ssa_vars_mem1.
    assumption.
  Qed.

  Lemma ssa_vars_mem_2vmap m1 m2 v vs :
    SSAVS.mem (ssa_var m1 v) (ssa_vars m2 vs) = VS.mem v vs && (get_index v m1 == get_index v m2).
  Proof.
    case Hmem: (VS.mem v vs) => /=.
    - case Hidx: (get_index v m1 == get_index v m2) => /=.
      + rewrite /ssa_var (eqP Hidx) ssa_vars_mem1.
        assumption.
      + apply/negP => H.
        move/negP: Hidx; apply.
        move: (ssa_vars_mem2 H) => [y [[Hvy /eqP Hidx] Hy]].
        rewrite {2}Hvy; assumption.
    - apply/negP => H.
      move/negP: Hmem; apply.
      move: (ssa_vars_mem2 H) => [y [[Hvy _] Hy]].
      rewrite Hvy; assumption.
  Qed.

  Lemma ssa_vars_add m v vs :
    SSAVS.Equal (ssa_vars m (VS.add v vs))
                (SSAVS.add (ssa_var m v) (ssa_vars m vs)).
  Proof.
    rewrite /ssa_vars (M2.map2_add (ssa_var_well m)).
    reflexivity.
  Qed.

  Lemma ssa_vars_upd_mem1 m x v vs :
    SSAVS.mem x (ssa_vars (upd_index v m) vs) ->
    x == ssa_var (upd_index v m) v \/
    svar x != v /\ SSAVS.mem x (ssa_vars m vs).
  Proof.
    move=> Hmem.
    move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
    rewrite Hxy.
    case Hyv: (y == v).
    - left; rewrite (eqP Hyv); exact: eqxx.
    - right; split.
      + rewrite /=. by move/idP/negP :Hyv.
      + move/idP/negP: Hyv => Hyv.
        rewrite (ssa_var_upd_neq _ Hyv) ssa_vars_mem1.
        assumption.
  Qed.

  Lemma ssa_vars_upd_mem2 m x v vs :
    x == ssa_var (upd_index v m) v ->
    VS.mem v vs ->
    SSAVS.mem x (ssa_vars (upd_index v m) vs).
  Proof.
    move=> /eqP Heq Hmem.
    rewrite Heq ssa_vars_mem1.
    assumption.
  Qed.

  Lemma ssa_vars_upd_mem3 m x v vs :
    svar x != v ->
    SSAVS.mem x (ssa_vars m vs) ->
    SSAVS.mem x (ssa_vars (upd_index v m) vs).
  Proof.
    destruct x as [x i] => /=.
    move=> Hneq Hmem.
    move: (ssa_vars_mem2 Hmem) => [y [Hxy Hmemy]].
    rewrite Hxy.
    rewrite ssa_vars_mem_2vmap.
    apply/andP; split.
    - assumption.
    - case: Hxy => [Hxy Hidx].
      rewrite Hxy in Hneq.
      rewrite (get_upd_index_neq _ Hneq).
      exact: eqxx.
  Qed.

  Lemma ssa_vars_singleton m v :
    SSAVS.Equal (ssa_vars m (VS.singleton v))
                (SSAVS.singleton (ssa_var m v)).
  Proof.
    rewrite /ssa_vars (M2.map2_singleton (ssa_var_well m)).
    reflexivity.
  Qed.

  Lemma ssa_vars_union m vs1 vs2 :
    SSAVS.Equal (ssa_vars m (VS.union vs1 vs2))
                (SSAVS.union (ssa_vars m vs1) (ssa_vars m vs2)).
  Proof.
    rewrite /ssa_vars (M2.map2_union (ssa_var_well m)).
    reflexivity.
  Qed.

  Lemma ssa_vars_atomic_comm  m (e : DSL.atomic) :
    SSAVS.Equal (ssa_vars m (DSL.vars_atomic e))
                (SSA.vars_atomic (ssa_atomic m e)).
  Proof.
    case: e.
    - move=> v.
      exact: ssa_vars_singleton.
    - reflexivity.
  Qed.

  Lemma ssa_vars_eexp_comm m (e : DSL.eexp) :
    SSAVS.Equal (ssa_vars m (DSL.vars_eexp e))
                (SSA.vars_eexp (ssa_eexp m e)).
  Proof.
    elim: e => /=.
    - exact: ssa_vars_singleton.
    - reflexivity.
    - move=> op e IH.
      assumption.
    - move=> op e1 IH1 e2 IH2.
      rewrite -IH1 -IH2 ssa_vars_union.
      reflexivity.
  Qed.

  Lemma ssa_vars_rexp_comm m (e : DSL.rexp) :
    SSAVS.Equal (ssa_vars m (DSL.vars_rexp e))
                (SSA.vars_rexp (ssa_rexp m e)).
  Proof.
    elim: e => /=.
    - exact: ssa_vars_singleton.
    - reflexivity.
    - done.
    - move=> w op e1 IH1 e2 IH2.
      rewrite -IH1 -IH2 ssa_vars_union.
      reflexivity.
    - move=> w e IH _.
      assumption.
    - move=> w e IH _.
      assumption.
  Qed.

  Lemma ssa_vars_eexp_union m (e1 e2 : DSL.eexp) :
    SSAVS.Equal (ssa_vars m (VS.union (DSL.vars_eexp e1) (DSL.vars_eexp e2)))
                (SSAVS.union (SSA.vars_eexp (ssa_eexp m e1))
                             (SSA.vars_eexp (ssa_eexp m e2))).
  Proof.
    rewrite ssa_vars_union -2!ssa_vars_eexp_comm.
    reflexivity.
  Qed.

  Lemma ssa_vars_rexp_union m (e1 e2 : DSL.rexp) :
    SSAVS.Equal (ssa_vars m (VS.union (DSL.vars_rexp e1) (DSL.vars_rexp e2)))
                (SSAVS.union (SSA.vars_rexp (ssa_rexp m e1))
                             (SSA.vars_rexp (ssa_rexp m e2))).
  Proof.
    rewrite ssa_vars_union -2!ssa_vars_rexp_comm.
    reflexivity.
  Qed.

  Lemma ssa_vars_subset m s1 s2 :
    SSAVS.subset (ssa_vars m s1) (ssa_vars m s2) = VS.subset s1 s2.
  Proof.
    case Hsub: (VS.subset s1 s2).
    - apply: SSAVS.subset_1 => x /SSAVS.Lemmas.memP Hmem.
      apply/SSAVS.Lemmas.memP.
      move: (ssa_vars_mem2 Hmem) => [y [Hxy Hmemy]].
      rewrite Hxy ssa_vars_mem1.
      exact: (VS.Lemmas.mem_subset Hmemy Hsub).
    - apply/negP => H.
      move/negP: Hsub; apply.
    - apply: VS.subset_1 => x /VS.Lemmas.memP Hmem.
      apply/VS.Lemmas.memP.
      rewrite -2!(ssa_vars_mem1 m) in Hmem *.
      exact: (SSAVS.Lemmas.mem_subset Hmem H).
  Qed.

  Lemma ssa_vars_ebexp_comm m e :
    SSAVS.Equal (ssa_vars m (DSL.vars_ebexp e))
                (SSA.vars_ebexp (ssa_ebexp m e)).
  Proof.
    elim: e => /=.
    - reflexivity.
    - move=> e1 e2. rewrite ssa_vars_eexp_union; reflexivity.
    - move=> e1 e2 e3. rewrite ssa_vars_union ssa_vars_eexp_union
                               ssa_vars_eexp_comm. reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 ssa_vars_union; reflexivity.
  Qed.

  Lemma ssa_vars_rbexp_comm m e :
    SSAVS.Equal (ssa_vars m (DSL.vars_rbexp e))
                (SSA.vars_rbexp (ssa_rbexp m e)).
  Proof.
    elim: e => /=.
    - reflexivity.
    - move=> w e1 e2. rewrite ssa_vars_rexp_union. reflexivity.
    - move=> w op e1 e2. rewrite ssa_vars_rexp_union; reflexivity.
    - done.
    - move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 ssa_vars_union; reflexivity.
    - move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 ssa_vars_union; reflexivity.
  Qed.

  Lemma ssa_vars_bexp_comm m e :
    SSAVS.Equal (ssa_vars m (DSL.vars_bexp e))
                (SSA.vars_bexp (ssa_bexp m e)).
  Proof.
    rewrite /ssa_bexp /DSL.vars_bexp /SSA.vars_bexp /=.
    rewrite ssa_vars_union ssa_vars_ebexp_comm ssa_vars_rbexp_comm.
    reflexivity.
  Qed.

  Lemma ssa_vars_ebexp_union m e1 e2 :
    SSAVS.Equal (ssa_vars m (VS.union (DSL.vars_ebexp e1) (DSL.vars_ebexp e2)))
                (SSAVS.union (SSA.vars_ebexp (ssa_ebexp m e1))
                             (SSA.vars_ebexp (ssa_ebexp m e2))).
  Proof.
    rewrite ssa_vars_union -2!ssa_vars_ebexp_comm.
    reflexivity.
  Qed.

  Lemma ssa_vars_rbexp_union m e1 e2 :
    SSAVS.Equal (ssa_vars m (VS.union (DSL.vars_rbexp e1) (DSL.vars_rbexp e2)))
                (SSAVS.union (SSA.vars_rbexp (ssa_rbexp m e1))
                             (SSA.vars_rbexp (ssa_rbexp m e2))).
  Proof.
    rewrite ssa_vars_union -2!ssa_vars_rbexp_comm.
    reflexivity.
  Qed.

  Lemma ssa_vars_bexp_union m e1 e2 :
    SSAVS.Equal (ssa_vars m (VS.union (DSL.vars_bexp e1) (DSL.vars_bexp e2)))
                (SSAVS.union (SSA.vars_bexp (ssa_bexp m e1))
                             (SSA.vars_bexp (ssa_bexp m e2))).
  Proof.
    rewrite ssa_vars_union -2!ssa_vars_bexp_comm.
    reflexivity.
  Qed.

  Lemma ssa_vars_atomic_subset m e vs :
    SSAVS.subset (SSA.vars_atomic (ssa_atomic m e)) (ssa_vars m vs) =
    VS.subset (DSL.vars_atomic e) vs.
  Proof.
    case: e => /=.
    - move=> v.
      rewrite VS.Lemmas.subset_singleton SSAVS.Lemmas.subset_singleton
              ssa_vars_mem1.
      reflexivity.
    - move=> _ _.
      rewrite VS.Lemmas.subset_empty SSAVS.Lemmas.subset_empty.
      reflexivity.
  Qed.

  Lemma ssa_vars_eexp_subset m (e : DSL.eexp) vs :
    SSAVS.subset (SSA.vars_eexp (ssa_eexp m e)) (ssa_vars m vs) =
    VS.subset (DSL.vars_eexp e) vs.
  Proof.
    case Hsub: (VS.subset (DSL.vars_eexp e) vs).
    - apply: SSAVS.subset_1 => x.
      rewrite -ssa_vars_eexp_comm => /SSAVS.Lemmas.memP Hx.
      move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
      apply/SSAVS.Lemmas.memP.
      rewrite Hv ssa_vars_mem1.
      exact: (VS.Lemmas.mem_subset Hmemv Hsub).
    - move/negP : Hsub => H.
      apply/negP => Hsub; apply: H.
      apply/VS.subset_1 => x /VS.Lemmas.memP Hx.
      move: Hx.
      rewrite -(ssa_vars_mem1 m) ssa_vars_eexp_comm => Hx.
      apply/VS.Lemmas.memP.
      move: (SSAVS.Lemmas.mem_subset Hx Hsub) => Hmem.
      rewrite ssa_vars_mem1 in Hmem.
      assumption.
  Qed.

  Lemma ssa_vars_rexp_subset m (e : DSL.rexp) vs :
    SSAVS.subset (SSA.vars_rexp (ssa_rexp m e)) (ssa_vars m vs) =
    VS.subset (DSL.vars_rexp e) vs.
  Proof.
    case Hsub: (VS.subset (DSL.vars_rexp e) vs).
    - apply: SSAVS.subset_1 => x.
      rewrite -ssa_vars_rexp_comm => /SSAVS.Lemmas.memP Hx.
      move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
      apply/SSAVS.Lemmas.memP.
      rewrite Hv ssa_vars_mem1.
      exact: (VS.Lemmas.mem_subset Hmemv Hsub).
    - move/negP : Hsub => H.
      apply/negP => Hsub; apply: H.
      apply/VS.subset_1 => x /VS.Lemmas.memP Hx.
      move: Hx.
      rewrite -(ssa_vars_mem1 m) ssa_vars_rexp_comm => Hx.
      apply/VS.Lemmas.memP.
      move: (SSAVS.Lemmas.mem_subset Hx Hsub) => Hmem.
      rewrite ssa_vars_mem1 in Hmem.
      assumption.
  Qed.

  Lemma ssa_vars_ebexp_subset m e vs :
    SSAVS.subset (SSA.vars_ebexp (ssa_ebexp m e)) (ssa_vars m vs) =
    VS.subset (DSL.vars_ebexp e) vs.
  Proof.
    case Hsub: (VS.subset (DSL.vars_ebexp e) vs).
    - apply: SSAVS.subset_1 => x.
      rewrite -ssa_vars_ebexp_comm => /SSAVS.Lemmas.memP Hx.
      move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
      apply/SSAVS.Lemmas.memP.
      rewrite Hv ssa_vars_mem1.
      exact: (VS.Lemmas.mem_subset Hmemv Hsub).
    - move/negP : Hsub => H.
      apply/negP => Hsub; apply: H.
      apply/VS.subset_1 => x /VS.Lemmas.memP Hx.
      move: Hx.
      rewrite -(ssa_vars_mem1 m) ssa_vars_ebexp_comm => Hx.
      apply/VS.Lemmas.memP.
      move: (SSAVS.Lemmas.mem_subset Hx Hsub) => Hmem.
      rewrite ssa_vars_mem1 in Hmem.
      assumption.
  Qed.

  Lemma ssa_vars_rbexp_subset m e vs :
    SSAVS.subset (SSA.vars_rbexp (ssa_rbexp m e)) (ssa_vars m vs) =
    VS.subset (DSL.vars_rbexp e) vs.
  Proof.
    case Hsub: (VS.subset (DSL.vars_rbexp e) vs).
    - apply: SSAVS.subset_1 => x.
      rewrite -ssa_vars_rbexp_comm => /SSAVS.Lemmas.memP Hx.
      move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
      apply/SSAVS.Lemmas.memP.
      rewrite Hv ssa_vars_mem1.
      exact: (VS.Lemmas.mem_subset Hmemv Hsub).
    - move/negP : Hsub => H.
      apply/negP => Hsub; apply: H.
      apply/VS.subset_1 => x /VS.Lemmas.memP Hx.
      move: Hx.
      rewrite -(ssa_vars_mem1 m) ssa_vars_rbexp_comm => Hx.
      apply/VS.Lemmas.memP.
      move: (SSAVS.Lemmas.mem_subset Hx Hsub) => Hmem.
      rewrite ssa_vars_mem1 in Hmem.
      assumption.
  Qed.

  Lemma ssa_vars_bexp_subset m e vs :
    SSAVS.subset (SSA.vars_bexp (ssa_bexp m e)) (ssa_vars m vs) =
    VS.subset (DSL.vars_bexp e) vs.
  Proof.
    case Hsub: (VS.subset (DSL.vars_bexp e) vs).
    - apply: SSAVS.subset_1 => x.
      rewrite -ssa_vars_bexp_comm => /SSAVS.Lemmas.memP Hx.
      move: (ssa_vars_mem2 Hx) => [v [Hv Hmemv]].
      apply/SSAVS.Lemmas.memP.
      rewrite Hv ssa_vars_mem1.
      exact: (VS.Lemmas.mem_subset Hmemv Hsub).
    - move/negP : Hsub => H.
      apply/negP => Hsub; apply: H.
      apply/VS.subset_1 => x /VS.Lemmas.memP Hx.
      move: Hx.
      rewrite -(ssa_vars_mem1 m) ssa_vars_bexp_comm => Hx.
      apply/VS.Lemmas.memP.
      move: (SSAVS.Lemmas.mem_subset Hx Hsub) => Hmem.
      rewrite ssa_vars_mem1 in Hmem.
      assumption.
  Qed.

  (** State equivalence *)

  Definition state_equiv (m : vmap) (s :Store.t) (ss : SSAStore.t) : Prop :=
    forall x, Store.acc x s = SSAStore.acc (x, get_index x m) ss.

  (** Convert a DSL state to an SSA state. *)

  Definition ssa_state (m : vmap) (s : Store.t) : SSAStore.t :=
    fun v =>
      if (sidx v) == get_index (svar v) m
      then Store.acc (svar v) s
      else Store.acc (svar v) Store.empty.

  Lemma acc_ssa_state_eq m s v i:
    i == get_index v m ->
    SSAStore.acc (v, i) (ssa_state m s) = Store.acc v s.
  Proof.
    move=> Heq.
    rewrite /ssa_state /SSAStore.acc /SSAStore.S.acc /=.
    rewrite (eqP Heq) eqxx.
    reflexivity.
  Qed.

  Lemma ssa_state_equiv m s:
    state_equiv m s (ssa_state m s).
  Proof.
    move=> x.
    rewrite (acc_ssa_state_eq _ (eqxx (get_index x m))).
    reflexivity.
  Qed.

  (* Type Environment Equivalence *)

  Lemma pair_neq1 :
    forall (T : eqType) (a b c d : T),
      a != c -> (a, b) != (c, d).
  Proof.
    move=> T a b c d Hne.
    apply/eqP => H.
    case: H => Hac Hbd.
    apply/idP: Hne.
    rewrite Hac; exact: eqxx.
  Qed.

  Lemma pair_neq2 :
    forall (T : eqType) (a b c d : T),
      b != d -> (a, b) != (c, d).
  Proof.
    move=> T a b c d Hne.
    apply/eqP => H.
    case: H => Hac Hbd.
    apply/idP: Hne.
    rewrite Hbd; exact: eqxx.
  Qed.

  Definition typenv_equiv (m : vmap) (te : TE.env) (ste : SSATE.env) : Prop :=
    forall x, TE.vtyp x te = SSATE.vtyp (x, get_index x m) ste.


  Lemma ssa_typenv_equiv_add (m: vmap) (te: TE.env) (ste: SSATE.env) x typ:
    typenv_equiv m te ste ->
    typenv_equiv m (TE.add x typ te) (SSATE.add (ssa_var m x) typ ste).
  Proof.
    move=> H.
    intros y.
    case Heq: (y==x).
    - move/idP: Heq => Heq.
      rewrite (TE.vtyp_add_eq Heq).
      rewrite -/(ssa_var m y).
      have Hseq: (ssa_var m y) == (ssa_var m x) by rewrite (eqP Heq).
      rewrite (SSATE.vtyp_add_eq Hseq).
      reflexivity.
    - move/idP/negP: Heq => Hneq.
      rewrite (TE.vtyp_add_neq Hneq).
      rewrite -/(ssa_var m y).
      have Hsneq: (ssa_var m y) != (ssa_var m x).
      {
        rewrite /ssa_var.
        exact: (pair_neq1 _ _ Hneq).
      }
      rewrite (SSATE.vtyp_add_neq Hsneq).
      exact: H.
  Qed.

  Lemma typenv_equiv_empty (m: vmap):
    typenv_equiv m (TE.empty typ) (SSATE.empty typ).
  Proof.
    intros x.
    have Hnmem: (~~ TE.mem x (TE.empty typ)) by rewrite TE.Lemmas.empty_a.
    have Hsnmem: (~~ SSATE.mem (ssa_var m x) (SSATE.empty typ)) by rewrite SSATE.Lemmas.empty_a.
    rewrite (TE.not_mem_vtyp Hnmem).
    rewrite (SSATE.not_mem_vtyp Hsnmem).
    reflexivity.
  Qed.

  Lemma ssa_typenv_equiv_empty (m: vmap) (te: TE.env):
    TE.Empty te ->
    typenv_equiv m te (ssa_typenv m te).
  Proof.
    move=> Hempty.
    move: m.
    (* intros x. *)
    rewrite /ssa_typenv /=.
    move=> m.
    have Heq: (TE.fold (add_to_ste m) te (SSATE.empty typ)) = (SSATE.empty typ).
    {

      apply (DSL.TEKS.MLemmas.OP.P.fold_Empty _ (add_to_ste m) (SSATE.empty typ) Hempty).
    }
    rewrite Heq.
    intros x.
    move: (DSL.TEKS.MLemmas.Empty_mem x Hempty) => Hnm.
    rewrite (TE.not_mem_vtyp Hnm).
    have Hsnmem: (~~ SSATE.mem (ssa_var m x) (SSATE.empty typ)) by rewrite SSATE.Lemmas.empty_a.
    rewrite (SSATE.not_mem_vtyp Hsnmem).
    reflexivity.
  Qed.

  Instance add_to_set_proper m:
    Proper (TE.SE.eq ==> eq ==> SSATE.Equal ==> SSATE.Equal) (add_to_ste m).
  Proof.
    move=> x y Hxy a b -> s1 s2 Heq.
    rewrite /add_to_ste.
    rewrite Heq.
    rewrite (eqP Hxy).
    reflexivity.
  Qed.

  Lemma add_to_set_transpose_neqkey m:
    DSL.TEKS.MLemmas.OP.P.transpose_neqkey SSATE.Equal (add_to_ste m).
  Proof.
    move=> x y a b s Hxy.
    rewrite /add_to_ste.
    rewrite /SSATE.Equal.
    move=> z.
    have Hnxy: (ssa_var m x) != (ssa_var m y).
    {
      rewrite pair_neq1.
      done.
        by move/idP: Hxy.
    }
    case H1: (z == ssa_var m x); case H2: (z == ssa_var m y).
    - move/idP/eqP: H1 => H1. move/idP/eqP: H2 => H2.
      rewrite -H1 -H2 in Hnxy.
      move/eqP: Hnxy => Hnxy.
        by destruct Hnxy.
    - move/idP: H1 => H1. move/negP: H2 => H2.
      rewrite (SSA.TEKS.MLemmas.find_add_eq H1).
      rewrite (SSA.TEKS.MLemmas.find_add_neq H2).
      rewrite (SSA.TEKS.MLemmas.find_add_eq H1).
      reflexivity.
    - move/idP: H2 => H2. move/negP: H1 => H1.
      rewrite (SSA.TEKS.MLemmas.find_add_eq H2).
      rewrite (SSA.TEKS.MLemmas.find_add_neq H1).
      rewrite (SSA.TEKS.MLemmas.find_add_eq H2).
      reflexivity.
    - move/negP: H1 => H1. move/negP: H2 => H2.
      rewrite (SSA.TEKS.MLemmas.find_add_neq H1).
      rewrite (SSA.TEKS.MLemmas.find_add_neq H2).
      rewrite (SSA.TEKS.MLemmas.find_add_neq H2).
      rewrite (SSA.TEKS.MLemmas.find_add_neq H1).
      reflexivity.
  Qed.

  Lemma ssa_typenv_equiv (m: vmap) (te: TE.t typ):
    typenv_equiv m te (ssa_typenv m te).
  Proof.
    move: te.
    apply DSL.TEKS.MLemmas.OP.P.map_induction.
    intros te.
    - exact: ssa_typenv_equiv_empty.
    - intros te te' IH x e HnIn HAdd y.
      rewrite /ssa_typenv.
      move: (DSL.TEKS.MLemmas.Add_mem_add x HAdd) => Hmem.
      move: (DSL.TEKS.MLemmas.Add_in HAdd) => Hin.
      rewrite /TE.vtyp.
      replace (TE.vtyp y te') with
          (
            match VM.find y te' with
            | None => TE.deftyp
            | Some ty => ty
            end

          ) by reflexivity.
      rewrite -/(ssa_var m y).
      replace (SSATE.vtyp (ssa_var m y) (TE.fold (add_to_ste m) te' (SSATE.empty typ))) with
          (
            match SSAVM.find (ssa_var m y) (TE.fold (add_to_ste m) te' (SSATE.empty typ)) with
            | None => SSATE.deftyp
            | Some ty => ty
            end

          ) by reflexivity.
      move: (DSL.TEKS.MLemmas.OP.P.fold_Add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper m)
               (add_to_set_transpose_neqkey m)
               (SSATE.empty typ)
               HnIn HAdd) => Heq.
      rewrite -/(ssa_var m y).
      rewrite /SSATE.Equal in Heq.
      rewrite (Heq (ssa_var m y)).
      case Hyx: (y == x).
      + rewrite (eqP Hyx).
        rewrite HAdd.
        rewrite (DSL.TEKS.MLemmas.find_add_eq).
        rewrite /add_to_ste.
        rewrite SSA.TEKS.MLemmas.find_add_eq.
        reflexivity.
        reflexivity.
        reflexivity.
      + rewrite HAdd.
        move/negP: Hyx => Hyx.
        rewrite (DSL.TEKS.MLemmas.find_add_neq Hyx).
        rewrite /add_to_ste.
        rewrite SSA.TEKS.MLemmas.find_add_neq.
        exact: IH.
        move/idP: Hyx => Hyx.
        rewrite /SSATE.SE.eq.
        rewrite /ssa_var.
        apply /negP.
        exact: (pair_neq1 _ _ Hyx).
  Qed.

  Corollary ssa_typenv_preserve m TE v:
    TE.vtyp v TE= SSATE.vtyp (ssa_var m v) (ssa_typenv m TE) .
    exact: ssa_typenv_equiv.
  Qed.

  Lemma ssa_typenv_mem_empty (m: vmap) (te: TE.env) x:
    TE.Empty te ->
    TE.mem x te  = SSATE.mem (ssa_var m x) (ssa_typenv m te).
  Proof.
    move=> Hempty.
    move: m.
    rewrite /ssa_typenv /=.
    move=> m.
    have Heq: (TE.fold (add_to_ste m) te (SSATE.empty typ)) = (SSATE.empty typ).
    {

      apply (DSL.TEKS.MLemmas.OP.P.fold_Empty _ (add_to_ste m) (SSATE.empty typ) Hempty).
    }
    rewrite Heq.
    move: (DSL.TEKS.MLemmas.Empty_mem x Hempty) => Hnm.
    have Hsnmem: (~~ SSATE.mem (ssa_var m x) (SSATE.empty typ)) by rewrite SSATE.Lemmas.empty_a.
    move/negPf: Hnm => ->.
    move/negPf: Hsnmem => ->.
    reflexivity.
  Qed.

  Lemma ssa_typenv_mem m x te:
    TE.mem x te = SSATE.mem (ssa_var m x) (ssa_typenv m te).
  Proof.
    move: te.
    apply DSL.TEKS.MLemmas.OP.P.map_induction.
    - intros te.
      exact: ssa_typenv_mem_empty.
    - intros te te' IH y e HnIn HAdd.
      rewrite /ssa_typenv.
      move: (DSL.TEKS.MLemmas.Add_mem_add x HAdd) => Hmem.
      move: (DSL.TEKS.MLemmas.Add_in HAdd) => Hin.
      move: (DSL.TEKS.MLemmas.OP.P.fold_Add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper m)
               (add_to_set_transpose_neqkey m)
               (SSATE.empty typ)
               HnIn HAdd) => Heq.
      rewrite /SSATE.Equal in Heq.
      case Hyx: (x == y).
    - rewrite Hmem.
      rewrite (DSL.TELemmas.mem_add_eq Hyx).
      move: (Heq (ssa_var m x)) => Heq2.
      move: (SSA.TELemmas.find_eq_mem_eq Heq2) => Heq3.
      rewrite Heq3.
      rewrite SSA.TEKS.MLemmas.mem_add_eq.
      reflexivity.
        by rewrite (eqP Hyx).
    - rewrite Hmem.
      move/negP: Hyx => Hyx.
      rewrite (DSL.TELemmas.mem_add_neq Hyx).
      move: (Heq (ssa_var m x)) => Heq2.
      move: (SSA.TELemmas.find_eq_mem_eq Heq2) => Heq3.
      rewrite Heq3.
      rewrite SSA.TEKS.MLemmas.mem_add_neq.
      exact: IH.
      move/idP: Hyx => Hyx.
      rewrite /SSATE.SE.eq.
      rewrite /ssa_var.
      apply /negP.
      exact: (pair_neq1 _ _ Hyx).
  Qed.

  Lemma ssa_typenv_exist_aux x m te:
    ~ SSATE.mem x (ssa_typenv m te) \/ exists v, ssa_var m v = x.
  Proof.
    move: te.
    apply DSL.TEKS.MLemmas.OP.P.map_induction_bis.
    - move=> te te' Heq.
      move: (DSL.TEKS.MLemmas.F.Equal_sym Heq) => {Heq} Heq.
      move=> H.
      case: H => H.
      + left.
        rewrite /ssa_typenv in H |- *.
          by rewrite (DSL.TEKS.MLemmas.fold_Equal
                        (SSA.TEKS.MLemmas.F.Equal_ST typ)
                        (SSATE.empty typ)
                        (add_to_set_proper m)
                        Heq).
      + by right.
    - by left.
    - move=> y yty te.
      rewrite /ssa_typenv.
      move=> Hnin H.
      case: H => H.
      + rewrite (DSL.TEKS.MLemmas.OP.P.fold_add
                   (SSA.TEKS.MLemmas.F.Equal_ST typ)
                   (add_to_set_proper m)
                   (add_to_set_transpose_neqkey m)
                   yty (SSATE.empty typ)
                   Hnin).
        rewrite -[add_to_ste m y yty]/(SSATE.add (ssa_var m y) yty).
        case Heq: (x == ssa_var m y).
        * right.
          exists y.
            by rewrite (eqP Heq).
        * left.
          move/negP: Heq => Hneq.
          rewrite eq_sym in Hneq.
          rewrite (SSATE.Lemmas.add_neq_b _ _ Hneq).
          exact: H.
      + by right.
  Qed.

  Lemma ssa_typenv_exist x m te:
    SSATE.mem x (ssa_typenv m te) ->
    exists v, ssa_var m v = x.
  Proof.
    move: (ssa_typenv_exist_aux x m te) => H.
    move=> H2.
    elim: H => H.
    - by rewrite H2 in H.
    - exact: H.
  Qed.

  Lemma ssa_vars_env_comm m te :
    SSAVS.Equal (SSA.vars_env (ssa_typenv m te))
                (ssa_vars m (DSL.vars_env te)).
  Proof.
    move=> x.
    split.
    - move=> Hin.
      move/SSA.VSLemmas.memP: Hin => Hmem.
      apply/SSA.VSLemmas.memP.
      rewrite SSA.mem_vars_env in Hmem.
      move: (ssa_typenv_exist Hmem) => [v] Hsv.
      rewrite -Hsv.
      rewrite ssa_vars_mem1.
      rewrite -Hsv in Hmem.
      rewrite -ssa_typenv_mem in Hmem.
      rewrite DSL.mem_vars_env.
      exact: Hmem.
    - move=> Hin.
      move/SSA.VSLemmas.memP: Hin => Hmem.
      apply/SSA.VSLemmas.memP.
      rewrite SSA.mem_vars_env.
      move: (ssa_vars_mem2 Hmem) => [v [Hsv Hmem2]].
      rewrite Hsv.
      rewrite -ssa_typenv_mem.
      rewrite DSL.mem_vars_env in Hmem2.
      exact: Hmem2.
  Qed.

  Lemma ssa_typenv_add_empty (m: vmap) (te: TE.env) x ty:
    TE.Empty te ->
    SSATE.Equal (ssa_typenv (upd_index x m) (TE.add x ty te))
                (SSATE.add (ssa_var (upd_index x m) x) ty (ssa_typenv m te)).
  Proof.
    move=> Hempty.
    move: m.
    rewrite /ssa_typenv /=.
    move=> m.
    have Heq: (TE.fold (add_to_ste m) te (SSATE.empty typ)) = (SSATE.empty typ).
    {
      apply (DSL.TEKS.MLemmas.OP.P.fold_Empty _ (add_to_ste m) (SSATE.empty typ) Hempty).
    }
    rewrite Heq.
    move: (DSL.TEKS.MLemmas.Empty_mem x Hempty) => Hnm.
    have Hsnmem: (~~ SSATE.mem (ssa_var m x) (SSATE.empty typ)) by rewrite SSATE.Lemmas.empty_a.
    move/DSL.TELemmas.memP: Hnm => HnIn.
    move: (DSL.TEKS.MLemmas.OP.P.fold_add
             (SSA.TEKS.MLemmas.F.Equal_ST typ)
             (add_to_set_proper (upd_index x m))
             (add_to_set_transpose_neqkey (upd_index x m))
             ty (SSATE.empty typ)
             HnIn) => Heq2.
    rewrite -> Heq2.
    have Heq3: (TE.fold (add_to_ste (upd_index x m)) te (SSATE.empty typ)) = (SSATE.empty typ).
    {
      apply (DSL.TEKS.MLemmas.OP.P.fold_Empty _ (add_to_ste (upd_index x m)) (SSATE.empty typ) Hempty).
    }
    rewrite Heq3.
    reflexivity.
  Qed.

  Lemma SSATE_add_not_in_sub1 m te x y yty:
    x != y ->
    SSATE.Equal (add_to_ste (upd_index x m) y yty te)
                (add_to_ste m y yty te).
  Proof.
    move=> Hneq.
    rewrite /add_to_ste.
    rewrite eq_sym in Hneq.
    rewrite (ssa_var_upd_neq m Hneq).
    reflexivity.
  Qed.

  Lemma SSATE_add_not_in_sub2 m x te:
    TE.In x te \/
    SSATE.Equal (TE.fold (add_to_ste (upd_index x m)) te (SSATE.empty typ))
                (TE.fold (add_to_ste m) te (SSATE.empty typ)).
  Proof.
    move: te.
    apply DSL.TEKS.MLemmas.OP.P.map_induction_bis.
    - move=> t te' Heq.
      move: (DSL.TEKS.MLemmas.F.Equal_sym Heq) => {Heq} Heq.
      move=> H.
      case: H => H.
      + left.
        eapply DSL.TELemmas.In_m.
        exact: eqxx.
        exact: Heq.
        exact: H.
      + right.
        rewrite (DSL.TEKS.MLemmas.fold_Equal
                   (SSA.TEKS.MLemmas.F.Equal_ST typ)
                   (SSATE.empty typ)
                   (add_to_set_proper (upd_index x m))
                   Heq).
        rewrite (DSL.TEKS.MLemmas.fold_Equal
                   (SSA.TEKS.MLemmas.F.Equal_ST typ)
                   (SSATE.empty typ)
                   (add_to_set_proper m)
                   Heq).
        exact: H.
    - right.
      done.
    - move=> y yty te'.
      move=> HnIny IH.
      elim: IH => H.
      + left.
        rewrite DSL.TELemmas.add_in_iff.
        right. done.
      + case Hxy: (x == y).
        * left.
          apply /DSL.TEKS.MLemmas.memP.
          exact: (DSL.TEKS.MLemmas.mem_add_eq Hxy).
        * right.
          rewrite (DSL.TEKS.MLemmas.OP.P.fold_add
                     (SSA.TEKS.MLemmas.F.Equal_ST typ)
                     (add_to_set_proper (upd_index x m))
                     (add_to_set_transpose_neqkey (upd_index x m))
                     yty (SSATE.empty typ)
                     HnIny).
          rewrite (DSL.TEKS.MLemmas.OP.P.fold_add
                     (SSA.TEKS.MLemmas.F.Equal_ST typ)
                     (add_to_set_proper m)
                     (add_to_set_transpose_neqkey m)
                     yty (SSATE.empty typ)
                     HnIny).
          rewrite H.
          move/negP/idP: Hxy => Hxy.
          rewrite (SSATE_add_not_in_sub1 m _ yty Hxy).
          reflexivity.
  Qed.

  Lemma SSATE_add_not_in m x te:
    ~ TE.In x te ->
    SSATE.Equal (TE.fold (add_to_ste (upd_index x m)) te (SSATE.empty typ))
                (TE.fold (add_to_ste m) te (SSATE.empty typ)).

  Proof.
    move=> HnIn.
    move: (SSATE_add_not_in_sub2 m x te) => Hsub.
    elim: Hsub => H.
    - move /DSL.TEKS.MLemmas.memP: HnIn => HnIn.
      move /DSL.TEKS.MLemmas.memP: H => H.
      rewrite H in HnIn.
      discriminate.
    - exact: H.
  Qed.

  Lemma ssa_typenv_add_submap_sub1 m x xty yty te:
    ~ TE.In x te ->
    SSA.TELemmas.submap
      (add_to_ste (upd_index x m) x xty (TE.fold (add_to_ste m) te (SSATE.empty typ)))
      (add_to_ste (upd_index x m) x xty
                  (add_to_ste m x yty (TE.fold (add_to_ste m) te (SSATE.empty typ)))).
  Proof.
    move=> HnIn.
    move=> z zty.
    rewrite /add_to_ste.
    rewrite ssa_var_upd_eq.
    rewrite get_upd_index_eq.
    case Heq: ((x, get_index x m + 1) == z).
    - rewrite (SSA.TELemmas.add_eq_o _ _ Heq).
      move=> H.
      rewrite (SSA.TELemmas.add_eq_o _ _ Heq).
      exact: H.
    - move/negP: Heq => Hneq.
      rewrite (SSA.TELemmas.add_neq_o _ _ Hneq).
      move=> H.
      rewrite (SSA.TELemmas.add_neq_o _ _ Hneq).
      rewrite /ssa_var.
      move: (ssa_typenv_mem m x te) => Hmem.
      rewrite -[(TE.fold (fun (k : var) (v : typ) => [eta SSATE.add (ssa_var m k) v]) te
                         (SSATE.empty typ))]/(ssa_typenv m te) in H.
      move/DSL.TEKS.MLemmas.memP: HnIn => HnIn.
      rewrite Hmem in HnIn.
      case Heq: ((x, get_index x m) == z).
      + rewrite (SSA.TELemmas.add_eq_o _ _ Heq).
        move/eqP: Heq => Heq.
        rewrite -[(x, get_index x m)]/(ssa_var m x) in Heq.
        rewrite -Heq in H.
        rewrite (SSA.TELemmas.not_mem_find_none HnIn) in H.
        discriminate.
      + move/negP: Heq => Hneq2.
        rewrite (SSA.TELemmas.add_neq_o _ _ Hneq2).
        exact: H.
  Qed.

  Lemma TE_add_neq_swap (te: TE.env) x xty y yty:
    x != y ->
    TE.Equal (TE.add x xty (TE.add y yty te))
             (TE.add y yty (TE.add x xty te)).
  Proof.
    move=> Hneq.
    move=> z.
    case Heq: (x == z).
    - rewrite (DSL.TELemmas.add_eq_o _ _ Heq).
      have Hneqyz: (y != z) by rewrite -(eqP Heq) eq_sym.
      move/negP: Hneqyz => Hneqyz.
      rewrite (DSL.TELemmas.add_neq_o _ _ Hneqyz).
      rewrite (DSL.TELemmas.add_eq_o _ _ Heq).
      reflexivity.
    - move/negP: Heq => Hneqxz.
      rewrite (DSL.TELemmas.add_neq_o _ _ Hneqxz).
      case Heqyz: (y == z).
      + rewrite (DSL.TELemmas.add_eq_o _ _ Heqyz).
        rewrite (DSL.TELemmas.add_eq_o _ _ Heqyz).
        reflexivity.
      + move/negP: Heqyz => Hneqyz.
        rewrite (DSL.TELemmas.add_neq_o _ _ Hneqyz).
        rewrite (DSL.TELemmas.add_neq_o _ _ Hneqyz).
        rewrite (DSL.TELemmas.add_neq_o _ _ Hneqxz).
        reflexivity.
  Qed.

  Lemma add_to_ste_neq_swap m (ste: SSATE.env) x xty y yty:
    x != y ->
    SSATE.Equal
      (add_to_ste (upd_index x m) x xty
                  (add_to_ste m y yty ste))
      (add_to_ste (upd_index x m) y yty
                  (add_to_ste (upd_index x m) x xty ste)).
  Proof.
    move=> Hneq.
    rewrite /add_to_ste.
    move=> z.
    case Heq: ((ssa_var (upd_index x m) x) == z).
    - rewrite (SSA.TELemmas.add_eq_o _ _ Heq).
      have Hneqyz: ((ssa_var (upd_index x m) y) != z).
      {
        rewrite -(eqP Heq).
        rewrite eq_sym in Hneq.
        exact: (pair_neq1 _ _ Hneq).
      }
      move/negP: Hneqyz => Hneqyz.
      rewrite (SSA.TELemmas.add_neq_o _ _ Hneqyz).
      rewrite (SSA.TELemmas.add_eq_o _ _ Heq).
      reflexivity.
    - move/negP: Heq => Hneqxz.
      rewrite (SSA.TELemmas.add_neq_o _ _ Hneqxz).
      case Heqyz: ((ssa_var m y) == z).
      + rewrite (SSA.TELemmas.add_eq_o _ _ Heqyz).
        rewrite eq_sym in Hneq.
        rewrite (ssa_var_upd_neq _ Hneq).
        rewrite (SSA.TELemmas.add_eq_o _ _ Heqyz).
        reflexivity.
      + move/negP: Heqyz => Hneqyz.
        rewrite (SSA.TELemmas.add_neq_o _ _ Hneqyz).
        rewrite eq_sym in Hneq.
        rewrite (ssa_var_upd_neq _ Hneq).
        rewrite (SSA.TELemmas.add_neq_o _ _ Hneqyz).
        rewrite (SSA.TELemmas.add_neq_o _ _ Hneqxz).
        reflexivity.
  Qed.

  Lemma ssa_typenv_add_submap m te x ty:
    SSA.TELemmas.submap (ssa_typenv (upd_index x m) (TE.add x ty te))
                        (SSATE.add (ssa_var (upd_index x m) x) ty (ssa_typenv m te)).
  Proof.
    move: te.
    apply DSL.TEKS.MLemmas.OP.P.map_induction.
    - move=> te Hempty.
      move=> y yty.
      rewrite (ssa_typenv_add_empty m x ty Hempty).
      done.
    - move=> te te' IH y yty HnIn HAdd.
      move=> z zty.
      rewrite /ssa_typenv.
      move: (DSL.TEKS.MLemmas.OP.P.fold_add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper m)
               (add_to_set_transpose_neqkey m)
               yty (SSATE.empty typ)
               HnIn) => Heq_add_m.
      move: (DSL.TEKS.MLemmas.OP.P.fold_add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper (upd_index x m))
               (add_to_set_transpose_neqkey (upd_index x m))
               yty (SSATE.empty typ)
               HnIn) => Heq_add_m'.
      move: (DSL.TEKS.MLemmas.OP.P.fold_Add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper m)
               (add_to_set_transpose_neqkey m)
               (SSATE.empty typ)
               HnIn HAdd) => Heq_Add_m.
      move: (DSL.TEKS.MLemmas.OP.P.fold_Add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper (upd_index x m))
               (add_to_set_transpose_neqkey (upd_index x m))
               (SSATE.empty typ)
               HnIn HAdd) => Heq_Add_m'.
      case Hyx: (x == y).
    - move: HnIn => HnInx.
      rewrite -(eqP Hyx) in HnInx.
      move: (DSL.TEKS.MLemmas.OP.P.fold_add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper (upd_index x m))
               (add_to_set_transpose_neqkey (upd_index x m))
               ty (SSATE.empty typ)
               HnInx) => Heq5 .
      have Hte': (TE.Equal te' (TE.add y yty te)) by exact: HAdd.
      have Hte'2: (TE.Equal (TE.add x ty te') (TE.add x ty te)).
      {
        rewrite Hte'.
        rewrite -(eqP Hyx).
        move=> a.
        case Hax: (a == x).
        + by rewrite !(DSL.TELemmas.find_add_eq Hax).
        + move/negP: Hax => Hax.
          rewrite !(DSL.TELemmas.find_add_neq Hax).
          reflexivity.
      }
      rewrite (DSL.TEKS.MLemmas.fold_Equal
                 (SSA.TEKS.MLemmas.F.Equal_ST typ)
                 (SSATE.empty typ)
                 (add_to_set_proper (upd_index x m))
                 Hte'2).
      rewrite (DSL.TEKS.MLemmas.fold_Equal
                 (SSA.TEKS.MLemmas.F.Equal_ST typ)
                 (SSATE.empty typ)
                 (add_to_set_proper m)
                 Hte').
      rewrite Heq5.
      rewrite Heq_add_m.
      rewrite -(eqP Hyx).
      rewrite -[SSATE.add (ssa_var (upd_index x m) x) ty]/(add_to_ste (upd_index x m) x ty).
      rewrite (SSATE_add_not_in _ HnInx).
      exact: (ssa_typenv_add_submap_sub1 yty HnInx).
    - rewrite Heq_Add_m.
      have Hte': (TE.Equal te' (TE.add y yty te)) by exact: HAdd.
      have Hte'2: (TE.Equal (TE.add x ty te') (TE.add x ty (TE.add y yty te))) by rewrite Hte'.
      rewrite (DSL.TEKS.MLemmas.fold_Equal
                 (SSA.TEKS.MLemmas.F.Equal_ST typ)
                 (SSATE.empty typ)
                 (add_to_set_proper (upd_index x m))
                 Hte'2).
      move/negP/idP: Hyx => Hyx.
      move: (TE_add_neq_swap te ty yty Hyx) => Hswap.
      rewrite (DSL.TEKS.MLemmas.fold_Equal
                 (SSA.TEKS.MLemmas.F.Equal_ST typ)
                 (SSATE.empty typ)
                 (add_to_set_proper (upd_index x m))
                 Hswap).
      move: (HnIn) => HnIn2.
      move/negP: Hyx => Hyx.
      rewrite <- (DSL.TELemmas.add_neq_in_iff te ty Hyx) in HnIn2.
      move: (DSL.TEKS.MLemmas.OP.P.fold_add
               (SSA.TEKS.MLemmas.F.Equal_ST typ)
               (add_to_set_proper (upd_index x m))
               (add_to_set_transpose_neqkey (upd_index x m))
               yty (SSATE.empty typ)
               HnIn2) => Heq'.
      rewrite Heq'.
      rewrite /ssa_typenv in IH.
      rewrite -[SSATE.add (ssa_var (upd_index x m) x) ty]/(add_to_ste (upd_index x m) x ty).
      move/negP: Hyx => Hyx.
      move: z zty.
      apply: (@SSA.TELemmas.submap_trans _ (add_to_ste (upd_index x m) y yty
                                                       ((SSATE.add (ssa_var (upd_index x m) x) ty (TE.fold (add_to_ste m) te (SSATE.empty typ)))))).
      + move=> z zty.
        rewrite /add_to_ste.
        case Htmp: ((ssa_var (upd_index x m) y) == z).
        * rewrite 2!(SSA.TELemmas.add_eq_o _ _ Htmp).
          done.
        * move/negP: Htmp => Htmp.
          rewrite 2!(SSA.TELemmas.add_neq_o _ _ Htmp).
          exact: IH.
      + move=> z zty.
        rewrite (add_to_ste_neq_swap m _ ty yty Hyx).
        done.
  Qed.

  Lemma ssa_typenv_add2_submap m te x xty y yty:
    SSA.TELemmas.submap (ssa_typenv (upd_index y (upd_index x m)) (TE.add y yty (TE.add x xty te)))
                        (SSATE.add (ssa_var (upd_index y (upd_index x m)) y) yty
                                   (SSATE.add (ssa_var (upd_index x m) x) xty (ssa_typenv m te))).
  Proof.
    move: (@ssa_typenv_add_submap (upd_index x m) (TE.add x xty te) y yty) => Hsub.
    eapply SSA.TELemmas.submap_trans.
    - exact: Hsub.
    - apply SSA.submap_add.
      exact: ssa_typenv_add_submap.
  Qed.

  Lemma ssa_atomic_atyp m a te:
    DSL.atyp a te =
    SSA.atyp (ssa_atomic m a) (ssa_typenv m te).
  Proof.
    elim: a m te; intros; rewrite /=.
    - exact: ssa_typenv_preserve.
    - reflexivity.
  Qed.

  Lemma ssa_atomic_asize m a E :
    DSL.asize a E = SSA.asize (ssa_atomic m a) (ssa_typenv m E).
  Proof.
    rewrite /DSL.asize /SSA.asize. rewrite -ssa_atomic_atyp. reflexivity.
  Qed.

  Lemma ssa_instr_succ_typenv_submap m1 m2 i si te:
    ssa_instr m1 i = (m2, si) ->
    SSA.TELemmas.submap (ssa_typenv m2 (DSL.instr_succ_typenv i te))
                        (SSA.instr_succ_typenv si (ssa_typenv m1 te)).
  Proof.
    elim: i m1 m2 si te => /=; rewrite /=; intros;
                             (let rec tac :=
                                  match goal with
                                  | H : (_, _) = (_, _) |- _ => case: H => <- <- /=; tac
                                  | H : is_true (_ && _) |- _ =>
                                    let H1 := fresh in
                                    let H2 := fresh in
                                    move/andP: H => [H1 H2]; tac
                                  | |- is_true (_ && _) => apply/andP; split; tac
                                  | |- context [SSA.atyp (ssa_atomic ?m ?a) (ssa_typenv ?m ?te)]
                                    => rewrite -ssa_atomic_atyp; tac
                                  | |- SSA.TELemmas.submap (ssa_typenv (upd_index ?x ?m) (TE.add ?x ?ty ?te))
                                                           ( SSATE.add (ssa_var (upd_index ?x ?m) ?x) ?ty (ssa_typenv ?m ?te) )
                                    => exact: ssa_typenv_add_submap
                                  | |- SSA.TELemmas.submap (ssa_typenv (upd_index ?y (upd_index ?x ?m)) (TE.add ?y ?yty (TE.add ?x ?xty ?te)))
                                                           ((SSATE.add (ssa_var (upd_index ?y (upd_index ?x ?m)) ?y) ?yty )
                                                              (SSATE.add (ssa_var (upd_index ?x ?m) ?x) ?xty (ssa_typenv ?m ?te)))
                                    => exact: ssa_typenv_add2_submap
                                  | |- SSA.TELemmas.submap ?ste ?ste =>
                                    exact: SSA.TELemmas.submap_refl
                                  | |- is_true(true) => done
                                  | |- ?e => progress (auto)
                                  | |- ?e => idtac
                                  end in tac).
  Qed.

  Lemma ssa_typenv_size te v m:
    TE.vsize v te = SSATE.vsize (ssa_var m v) (ssa_typenv m te).
  Proof.
    move: (ssa_typenv_preserve m te v) => H.
      by rewrite (TE.vtyp_vsize H).
  Qed.

  Lemma ssa_eval_eunop :
    forall (op : eunop) (v : Z),
      SSA.eval_eunop op v = DSL.eval_eunop op v.
  Proof.
      by case.
  Qed.

  Lemma ssa_eval_runop :
    forall (op : runop)  (v : bits),
      SSA.eval_runop op v = DSL.eval_runop op v.
  Proof.
      by case.
  Qed.

  Lemma ssa_eval_ebinop :
    forall (op : ebinop) (v1 v2 : Z),
      SSA.eval_ebinop op v1 v2 = DSL.eval_ebinop op v1 v2.
  Proof.
      by case.
  Qed.

  Lemma ssa_eval_rbinop :
    forall (op : rbinop) (v1 v2 : bits),
      SSA.eval_rbinop op v1 v2 = DSL.eval_rbinop op v1 v2.
  Proof.
      by case.
  Qed.

  Lemma ssa_eval_rcmpop :
    forall (op : rcmpop)  (v1 v2 : bits),
      SSA.eval_rcmpop op v1 v2 = DSL.eval_rcmpop op v1 v2.
  Proof.
      by case.
  Qed.

  Lemma ssa_acc2z m E SE s ss v :
    state_equiv m s ss ->
    typenv_equiv m E SE ->
    SSA.acc2z SE (ssa_var m v) ss = DSL.acc2z E v s.
  Proof.
    move=> Hs Ht. rewrite /DSL.acc2z /DSL.bv2z. rewrite (Hs v).
    rewrite (Ht v). reflexivity.
  Qed.

  Lemma ssa_eval_atomic m s ss a :
    state_equiv m s ss ->
    SSA.eval_atomic (ssa_atomic m a) ss = DSL.eval_atomic a s.
  Proof.
    move=> Heq; elim: a => /=.
    - move=> v.
      rewrite (Heq v).
      reflexivity.
    - reflexivity.
  Qed.

  Lemma ssa_eval_eexp m s ss te ste (e : DSL.eexp) :
    state_equiv m s ss ->
    typenv_equiv m te ste ->
    SSA.eval_eexp (ssa_eexp m e) ste ss = DSL.eval_eexp e te s.
  Proof.
    move=> Hseq Hteq; elim: e => /=.
    - move=> v. exact: (ssa_acc2z v Hseq Hteq).
    - reflexivity.
    - move=> op e IH. rewrite IH. reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
  Qed.

  Lemma ssa_eval_rexp m s ss (e : DSL.rexp) :
    state_equiv m s ss ->
    SSA.eval_rexp (ssa_rexp m e) ss = DSL.eval_rexp e s.
  Proof.
    move=> Heq; elim: e => /=.
    - move=> v. exact: (Logic.eq_sym (Heq v)).
    - reflexivity.
    - move=> w op e1 IH. by rewrite ssa_eval_runop IH.
    - move=> w op e1 IH1 e2 IH2. rewrite ssa_eval_rbinop IH1 IH2. reflexivity.
    - move=> w e IH p. rewrite IH. reflexivity.
    - move=> w e IH p. rewrite IH. reflexivity.
  Qed.

  Lemma ssa_eval_ebexp m s ss te ste e :
    state_equiv m s ss ->
    typenv_equiv m te ste ->
    SSA.eval_ebexp (ssa_ebexp m e) ste ss <-> DSL.eval_ebexp e te s.
  Proof.
    move=> Hseq Hteq; elim: e => /=.
    - done.
    - move=> e1 e2. rewrite 2!(ssa_eval_eexp _ Hseq Hteq). done.
    - move=> e1 e2 p. rewrite 3!(ssa_eval_eexp _ Hseq Hteq). done.
    - move=> e1 [IH11 IH12] e2 [IH21 IH22]. tauto.
  Qed.

  Lemma ssa_eval_ebexp1 m s ss te ste e :
    state_equiv m s ss ->
    typenv_equiv m te ste ->
    SSA.eval_ebexp (ssa_ebexp m e) ste ss -> DSL.eval_ebexp e te s.
  Proof.
    move=> Hseq Hteq He.
    move: (ssa_eval_ebexp e Hseq Hteq) => [H1 H2].
    exact: (H1 He).
  Qed.

  Lemma ssa_eval_ebexp2 m s ss te ste e :
    state_equiv m s ss ->
    typenv_equiv m te ste ->
    DSL.eval_ebexp e te s -> SSA.eval_ebexp (ssa_ebexp m e) ste ss.
  Proof.
    move=> Hseq Hteq He.
    move: (ssa_eval_ebexp e Hseq Hteq) => [H1 H2].
    exact: (H2 He).
  Qed.

  Lemma ssa_eval_rbexp m s ss e :
    state_equiv m s ss ->
    SSA.eval_rbexp (ssa_rbexp m e) ss <-> DSL.eval_rbexp e s.
  Proof.
    move=> Heq; elim: e => /=.
    - done.
    - move=> w e1 e2. rewrite 2!(ssa_eval_rexp _ Heq). done.
    - move=> w op e1 e2. rewrite 2!(ssa_eval_rexp _ Heq) ssa_eval_rcmpop. done.
    - move=> e1 [IH11 IH12]. tauto.
    - move=> e1 [IH11 IH12] e2 [IH21 IH22]. tauto.
    - move=> e1 [IH11 IH12] e2 [IH21 IH22]. tauto.
  Qed.

  Lemma ssa_eval_rbexp1 m s ss e :
    state_equiv m s ss ->
    SSA.eval_rbexp (ssa_rbexp m e) ss -> DSL.eval_rbexp e s.
  Proof.
    move=> Heq He.
    move: (ssa_eval_rbexp e Heq) => [H1 H2].
    exact: (H1 He).
  Qed.

  Lemma ssa_eval_rbexp2 m s ss e :
    state_equiv m s ss ->
    DSL.eval_rbexp e s -> SSA.eval_rbexp (ssa_rbexp m e) ss.
  Proof.
    move=> Heq He.
    move: (ssa_eval_rbexp e Heq) => [H1 H2].
    exact: (H2 He).
  Qed.

  Lemma ssa_eval_bexp m s ss te ste e :
    state_equiv m s ss ->
    typenv_equiv m te ste ->
    SSA.eval_bexp (ssa_bexp m e) ste ss <-> DSL.eval_bexp e te s.
  Proof.
    move=> Hseq Hteq. split; move=> [H1 H2].
    - exact: (conj (ssa_eval_ebexp1 Hseq Hteq H1) (ssa_eval_rbexp1 Hseq H2)).
    - exact: (conj (ssa_eval_ebexp2 Hseq Hteq H1) (ssa_eval_rbexp2 Hseq H2)).
  Qed.

  Lemma ssa_eval_bexp1 m s ss te ste e :
    state_equiv m s ss ->
    typenv_equiv m te ste ->
    SSA.eval_bexp (ssa_bexp m e) ste ss -> DSL.eval_bexp e te s.
  Proof.
    move=> Hseq Hteq He.
    move: (ssa_eval_bexp e Hseq Hteq) => [H1 H2].
    exact: (H1 He).
  Qed.

  Lemma ssa_eval_bexp2 m s ss te ste e :
    state_equiv m s ss ->
    typenv_equiv m te ste ->
    DSL.eval_bexp e te s -> SSA.eval_bexp (ssa_bexp m e) ste ss.
  Proof.
    move=> Hseq Hteq He.
    move: (ssa_eval_bexp e Hseq Hteq) => [H1 H2].
    exact: (H2 He).
  Qed.

  Lemma state_equiv_upd m s ss x v :
    state_equiv m s ss ->
    state_equiv (upd_index x m)
                (Store.upd x v s)
                (SSAStore.upd (ssa_var (upd_index x m) x) v ss).
  Proof.
    move=> Heq y.
    case Hyx: (y == x) => /=.
    - rewrite (Store.acc_upd_eq Hyx).
      rewrite (eqP Hyx) (SSAStore.acc_upd_eq (eqxx (ssa_var _ x))).
      reflexivity.
    - move/idP/negP: Hyx => Hyx.
      rewrite (Store.acc_upd_neq Hyx).
      rewrite (SSAStore.acc_upd_neq (pair_neq1 _ _ Hyx)).
      rewrite (get_upd_index_neq _ Hyx).
      exact: Heq.
  Qed.

  Lemma state_equiv_Upd m s1 s2 ss1 ss2 x v :
    state_equiv m s1 ss1 ->
    Store.Upd x v s1 s2 ->
    SSAStore.Upd (ssa_var (upd_index x m) x) v ss1 ss2 ->
    state_equiv (upd_index x m) s2 ss2.
  Proof.
    move=> Heq Hupd Hsupd y.
    case Hyx: (y == x) => /=.
    - rewrite (Store.acc_Upd_eq Hyx Hupd).
      rewrite (eqP Hyx) (SSAStore.acc_Upd_eq (eqxx (ssa_var _ x)) Hsupd).
      reflexivity.
    - move/idP/negP: Hyx => Hyx.
      rewrite (Store.acc_Upd_neq Hyx Hupd).
      rewrite (SSAStore.acc_Upd_neq (pair_neq1 _ _ Hyx) Hsupd).
      rewrite (get_upd_index_neq _ Hyx).
      exact: Heq.
  Qed.

  Lemma state_equiv_upd2 m s ss x vx y vy :
    state_equiv m s ss ->
    state_equiv (upd_index y (upd_index x m))
                (Store.upd2 x vx y vy s)
                (SSAStore.upd2
                   (ssa_var (upd_index x m) x) vx
                   (ssa_var (upd_index y (upd_index x m)) y) vy
                   ss).
  Proof.
    move=> Heq z.
    case Hzy: (z == y) => /=.
    - rewrite (Store.acc_upd_eq Hzy).
      rewrite (eqP Hzy) (SSAStore.acc_upd_eq (eqxx (ssa_var _ y))).
      reflexivity.
    - move/idP/negP: Hzy => Hzy.
      rewrite (Store.acc_upd_neq Hzy).
      rewrite (SSAStore.acc_upd_neq (pair_neq1 _ _ Hzy)).
      rewrite (get_upd_index_neq _ Hzy).
      exact: state_equiv_upd.
  Qed.

  Lemma state_equiv_Upd2 m s1 s2 ss1 ss2 x vx y vy :
    state_equiv m s1 ss1 ->
    Store.Upd2 x vx y vy s1 s2 ->
    SSAStore.Upd2 (ssa_var (upd_index x m) x) vx
                  (ssa_var (upd_index y (upd_index x m)) y) vy
                  ss1 ss2 ->
    state_equiv (upd_index y (upd_index x m)) s2 ss2.
  Proof.
    move=> Heq Hupd Hsupd z.
    case Hzy: (z == y) => /=.
    - rewrite (Store.acc_Upd_eq Hzy Hupd).
      rewrite (eqP Hzy) (SSAStore.acc_Upd_eq (eqxx (ssa_var _ y)) Hsupd).
      reflexivity.
    - move/idP/negP: Hzy => Hzy.
      rewrite (Store.acc_Upd_neq Hzy Hupd).
      rewrite (SSAStore.acc_Upd_neq (pair_neq1 _ _ Hzy) Hsupd).
      rewrite (get_upd_index_neq _ Hzy).
      exact: state_equiv_Upd.
  Qed.

  Lemma typenv_equiv_add m te ste x typ :
    typenv_equiv m te ste ->
    typenv_equiv (upd_index x m)
                 (TE.add x typ te)
                 (SSATE.add (ssa_var (upd_index x m) x) typ ste).
  Proof.
    move=> Heq y.
    case Hyx: (y == x) => /=.
    - rewrite (TE.vtyp_add_eq Hyx).
      rewrite (eqP Hyx) (SSATE.vtyp_add_eq (eqxx (ssa_var _ x))).
      reflexivity.
    - move/idP/negP: Hyx => Hyx.
      rewrite (TE.vtyp_add_neq Hyx).
      rewrite (SSATE.vtyp_add_neq (pair_neq1 _ _ Hyx)).
      rewrite (get_upd_index_neq _ Hyx).
      exact: Heq.
  Qed.

  Lemma typenv_equiv_add2 m te ste x xtyp y ytyp:
    typenv_equiv m te ste ->
    typenv_equiv (upd_index y (upd_index x m))
                 (TE.add y ytyp (TE.add x xtyp te))
                 (SSATE.add (ssa_var (upd_index y (upd_index x m)) y) ytyp
                            (SSATE.add (ssa_var (upd_index x m) x) xtyp ste)).
  Proof.
    move=> Heq z.
    case Hzy: (z == y) => /=.
    - rewrite (TE.vtyp_add_eq Hzy).
      rewrite (eqP Hzy) (SSATE.vtyp_add_eq (eqxx (ssa_var _ y))).
      reflexivity.
    - move/idP/negP: Hzy => Hzy.
      rewrite (TE.vtyp_add_neq Hzy).
      rewrite (SSATE.vtyp_add_neq (pair_neq1 _ _ Hzy)).
      rewrite (get_upd_index_neq _ Hzy).
      exact: typenv_equiv_add.
  Qed.

  Hint Resolve typenv_equiv_add typenv_equiv_add2.

  Lemma ssa_atyp m a te ste:
    typenv_equiv m te ste ->
    SSA.atyp (ssa_atomic m a) ste = DSL.atyp a te.
  Proof.
    elim: a m te ste => /=; intros.
    - by rewrite H.
    - done.
  Qed.

  Ltac ssa_eval_instr_succ_tac :=
    match goal with
    | H: ssa_instr _ _ = (?p1, ?p2) |- _ =>
      case: H => <- <-
    | |- _ /\ _ => split
    | |- exists ss2 , _ => eexists
    | H: ?e |- ?e => exact: H
    | |- context [SSA.instr_succ_typenv _ _] => rewrite /=
    | Heq: state_equiv ?m ?s ?ss |- context [SSA.eval_atomic (ssa_atomic ?m ?a) ?ss]
      => rewrite (ssa_eval_atomic a Heq)
    | Heq: typenv_equiv ?m1 ?te1 ?ste1 |- context[SSA.atyp (ssa_atomic ?m1 ?a) ?ste1]
      => rewrite (ssa_atyp a Heq)
    | |- SSA.eval_instr _ _ _ _ => econstructor
    | |- SSAStore.Upd ?x ?v ?s ?s => exact: SSAStore.Upd_upd
    | |- SSAStore.Upd ?x ?v ?s1 ?s2 => exact: SSAStore.Upd_upd
    | |- SSAStore.Upd2 ?x1 ?v1 ?x2 ?v2 ?s1 ?s2 => exact: SSAStore.Upd2_upd2
    | H: DSL.instr_succ_typenv _ ?te1 = ?te2 |- context [?te2]
      => rewrite /= in H; erewrite <- H; clear H
    | |- state_equiv _ _ (SSAStore.upd ?x ?v ?s) => eapply state_equiv_Upd
    | |- state_equiv _ _ (SSAStore.upd2 ?x1 ?v1 ?x2 ?v2 ?s) => eapply state_equiv_Upd2
    | H : state_equiv ?m _ _ |- state_equiv ?m _ _ => exact: H
    | H: typenv_equiv ?m1 ?te1 ?ste1
      |- typenv_equiv (upd_index ?t ?m1) (TE.add ?t ?typ ?te1) ?ste2
      => eapply typenv_equiv_add
    | H: typenv_equiv ?m1 ?te1 ?ste1
      |- typenv_equiv (upd_index ?t2 (upd_index ?t ?m1)) (TE.add ?t2 ?typ2 (TE.add ?t ?typ ?te1)) ?ste2
      => eapply typenv_equiv_add2
    | H: DSL.eval_instr _ _ _ _ |- _ => inversion H; subst; clear H
    | |- ?e => progress (eauto)
    | |- ?e => fail "not match" e
    end.

  Lemma ssa_eval_instr_succ m1 m2 s1 s2 te1 te2 ste1 ss1 i si:
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    typenv_equiv m1 te1 ste1 ->
    DSL.eval_instr te1 i s1 s2 ->
    DSL.instr_succ_typenv i te1 = te2 ->
    exists ss2 ste2,
      SSA.eval_instr ste1 si ss1 ss2 /\
      SSA.instr_succ_typenv si ste1 = ste2 /\
      state_equiv m2 s2 ss2 /\
      typenv_equiv m2 te2 ste2.
  Proof.
    elim: i m1 m2 s1 s2 te1 te2 ste1 ss1 si; intros.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      inversion_clear H2.
      exists (SSAStore.upd (ssa_var (upd_index t m1) t) n ss1).
      repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      inversion_clear H2.
      + (* cmovT *)
        repeat ssa_eval_instr_succ_tac.
      + (* cmovF *)
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        apply SSA.EIcmovF; repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      rewrite /= in H3.
      inversion H2; subst;clear H2.
      + ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        eapply SSA.EImullU.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
      + ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        eapply SSA.EImullS.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      rewrite /= in H3.
      inversion H2; subst;clear H2.
      + ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        eapply SSA.EImuljU.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
      + ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        eapply SSA.EImuljS.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      rewrite /= in H3.
      inversion H2; subst;clear H2.
      + ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        eapply SSA.EIsplitU.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
      + ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        ssa_eval_instr_succ_tac.
        eapply SSA.EIsplitS.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
        repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      inversion H2; subst; clear H2.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      rewrite ssa_var_upd_eq.
      (* rewrite (ssa_atyp a H1). *)
      (* exact: SSAStore.Upd_upd. *)
      (* rewrite /=. *)
      repeat ssa_eval_instr_succ_tac.
      rewrite /=.
      repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      inversion H2; subst; clear H2.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      rewrite ssa_var_upd_eq.
      rewrite /=.
      repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
    - ssa_eval_instr_succ_tac.
      inversion H2; subst; clear H2.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      ssa_eval_instr_succ_tac.
      erewrite (ssa_eval_bexp).
      all: repeat ssa_eval_instr_succ_tac.
  Qed.

  Lemma ssa_eval_program_succ m1 m2 s1 s2 te1 te2 p sp ss1 ste1:
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    typenv_equiv m1 te1 ste1 ->
    DSL.eval_program te1 p s1 s2 ->
    DSL.program_succ_typenv p te1 = te2 ->
    exists ss2 ste2,
      SSA.eval_program ste1 sp ss1 ss2 /\
      SSA.program_succ_typenv sp ste1 = ste2 /\
      state_equiv m2 s2 ss2 /\
      typenv_equiv m2 te2 ste2.
  Proof.
    elim: p m1 m2 s1 s2 te1 te2 sp ss1 ste1.
    - move=> m1 m2 s1 s2 te1 te2 sp ss1 ste1 /=.
      case=> <- <-.
      move=> Hse Hte Hep Hteq.
      rewrite /DSL.eval_program in Hep.
      rewrite /= in Hep.
      inversion Hep; subst.
      exists ss1, ste1. split_andb_goal.
      + constructor.
      + constructor.
      + assumption.
      + assumption.
    - move=> hd tl IH m1 m2 s1 s2 te1 te2 [| shd stl] ss1 ste1.
      + move=> Hsp. rewrite /= in Hsp. move: Hsp.
        case Hsi_hd: (ssa_instr m1 hd) => [sm1 shd].
        case Hsp_tl: (ssa_program sm1 tl) => [sm2 stl].
        inversion 1.
      + move=> Hsp Hseq Hteq Hep Hpst.
        inversion Hsp.
        move: H0.
        case Hsi_hd: (ssa_instr m1 hd) => [sm1 sshd].
        case Hsp_tl: (ssa_program sm1 tl) => [sm2 sstl].
        move=> Hpair.
        case: Hpair => <- <- <-.
        move: Hpst.
        inversion Hep; subst.
        move=> Hpst.
        rewrite /= in Hpst.
        remember (DSL.instr_succ_typenv hd te1) as te3.
        symmetry in Heqte3.
        move: (ssa_eval_instr_succ Hsi_hd Hseq Hteq H1 Heqte3) => Htmp.
        destruct Htmp as [ss3 [ste3 Hwit]].
        inversion Hwit as [Hseval [Hsstyp [Hseq2 Hteq2]]].
        move: (IH _ _ _ _ _ _ _ _ _ Hsp_tl Hseq2 Hteq2 H4 Hpst) => HIH.
        destruct HIH as [ss2 [ste2 Hswit]].
        inversion Hswit as [Hsep [Hstyp [Hseq3 Hteq3]]].
        exists ss2, ste2.
        split_andb_goal.
        eapply SSA.Econs.
        * exact: Hseval.
        * rewrite Hsstyp.
        * exact: Hsep.
        * rewrite /=.
            by rewrite Hsstyp.
        * exact: Hseq3.
        * exact: Hteq3.
  Qed.

  Ltac dessa_eval_instr_succ_tac :=
    match goal with
    | H: ssa_instr ?m ?i = (?p1, ?p2) |- _ =>
      case: H => <- Hsi; subst
    | |- _ /\ _ => split
    | |- exists s2 , _ => eexists
    | H: ?e |- ?e => exact: H
    | |- context [DSL.instr_succ_typenv _ _] => rewrite /=
    | Heq: state_equiv ?m ?s ?ss |- context [DSL.eval_atomic ?a ?s]
      => rewrite -(ssa_eval_atomic a Heq)
    | Heq: typenv_equiv ?m1 ?te1 ?ste1 |- context[DSL.atyp ?a ?te1]
      => rewrite -(ssa_atyp a Heq)
    | |- DSL.eval_instr _ _ _ _ => econstructor
    | |- Store.Upd ?x ?v ?s ?s => exact: Store.Upd_upd
    | |- Store.Upd ?x ?v ?s1 ?s2 => exact: Store.Upd_upd
    | |- Store.Upd2 ?x1 ?v1 ?x2 ?v2 ?s1 ?s2 => exact: Store.Upd2_upd2
    | H: SSA.instr_succ_typenv _ ?ste1 = ?ste2 |- context [?ste2]
      => (rewrite /= in H); erewrite <- H; clear H
    | |- state_equiv _ (Store.upd ?x ?v ?s) _ => eapply state_equiv_Upd
    | |- state_equiv _ (Store.upd2 ?x1 ?v1 ?x2 ?v2 ?s) _ => eapply state_equiv_Upd2
    | H : state_equiv ?m _ _ |- state_equiv ?m _ _ => exact: H
    | H: typenv_equiv ?m1 ?te1 ?ste1
      |- typenv_equiv (upd_index ?t ?m1) (TE.add ?t ?typ ?te1) ?ste2
      => eapply typenv_equiv_add
    | H: typenv_equiv ?m1 ?te1 ?ste1
      |- typenv_equiv (upd_index ?t2 (upd_index ?t ?m1)) (TE.add ?t2 ?typ2 (TE.add ?t ?typ ?te1)) ?ste2
      => eapply typenv_equiv_add2
    | H: SSA.eval_instr _ _ _ _ |- _ => inversion H; subst; clear H
    | |- ?e => progress (eauto)
    | |- ?e => fail "not match" e
    end.

  Lemma dessa_eval_instr_succ m1 m2 s1 ss1 ss2 te1 ste1 ste2 i si:
    ssa_instr m1 i = (m2, si) ->
    state_equiv m1 s1 ss1 ->
    typenv_equiv m1 te1 ste1 ->
    SSA.eval_instr ste1 si ss1 ss2 ->
    SSA.instr_succ_typenv si ste1 = ste2 ->
    exists s2 te2,
      DSL.eval_instr te1 i s1 s2 /\
      DSL.instr_succ_typenv i te1 = te2 /\
      state_equiv m2 s2 ss2 /\
      typenv_equiv m2 te2 ste2.
  Proof.
    elim: i m1 m2 s1 te1 ste1 ste2 ss1 ss2 si; intros.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - dessa_eval_instr_succ_tac.
      inversion_clear H2.
      exists (Store.upd t n s1).
      repeat dessa_eval_instr_succ_tac.
    - dessa_eval_instr_succ_tac.
      inversion_clear H2.
      + (* cmovT *)
        repeat dessa_eval_instr_succ_tac.
      + (* cmovF *)
        dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        apply DSL.EIcmovF; repeat dessa_eval_instr_succ_tac.
        repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - dessa_eval_instr_succ_tac.
      inversion H2; subst;clear H2.
      + repeat dessa_eval_instr_succ_tac.
      + dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        eapply DSL.EImullS.
        repeat dessa_eval_instr_succ_tac.
        repeat dessa_eval_instr_succ_tac.
        repeat dessa_eval_instr_succ_tac.
    - dessa_eval_instr_succ_tac.
      inversion H2; subst;clear H2.
      + repeat dessa_eval_instr_succ_tac.
      + dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        eapply DSL.EImuljS.
        repeat dessa_eval_instr_succ_tac.
        repeat dessa_eval_instr_succ_tac.
        repeat dessa_eval_instr_succ_tac.
    - dessa_eval_instr_succ_tac.
      (* rewrite /= in H3. *)
      inversion H2; subst;clear H2.
      + repeat dessa_eval_instr_succ_tac.
      + dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        dessa_eval_instr_succ_tac.
        eapply DSL.EIsplitS.
        repeat dessa_eval_instr_succ_tac.
        repeat dessa_eval_instr_succ_tac.
        repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - repeat dessa_eval_instr_succ_tac.
    - dessa_eval_instr_succ_tac.
      inversion H2; subst; clear H2.
      dessa_eval_instr_succ_tac.
      dessa_eval_instr_succ_tac.
      dessa_eval_instr_succ_tac.
      dessa_eval_instr_succ_tac.
      erewrite <- (ssa_eval_bexp).
      all: repeat dessa_eval_instr_succ_tac.
  Qed.

  Lemma dessa_eval_program_succ m1 m2 s1 ss1 ss2 te1 ste1 ste2 p sp:
    ssa_program m1 p = (m2, sp) ->
    state_equiv m1 s1 ss1 ->
    typenv_equiv m1 te1 ste1 ->
    SSA.eval_program ste1 sp ss1 ss2 ->
    SSA.program_succ_typenv sp ste1 = ste2 ->
    exists s2 te2,
      DSL.eval_program te1 p s1 s2 /\
      DSL.program_succ_typenv p te1 = te2 /\
      state_equiv m2 s2 ss2 /\
      typenv_equiv m2 te2 ste2.
  Proof.
    elim: p m1 m2 s1 te1 sp ss1 ss2 ste1 ste2.
    - move=> m1 m2 s1 te1 sp ss1 ss2 ste1 ste2 /=.
      case=> <- <-.
      move=> Hse Hte Hep Hteq.
      rewrite /SSA.eval_program in Hep.
      rewrite /= in Hep.
      inversion Hep; subst.
      exists s1, te1. split_andb_goal.
      + constructor.
      + constructor.
      + assumption.
      + assumption.
    - move=> hd tl IH m1 m2 s1 te1 [| shd stl] ss1 ss2 ste1 ste2.
      + move=> Hsp. rewrite /= in Hsp. move: Hsp.
        case Hsi_hd: (ssa_instr m1 hd) => [sm1 shd].
        case Hsp_tl: (ssa_program sm1 tl) => [sm2 stl].
        inversion 1.
      + move=> Hsp Hseq Hteq Hep Hpst.
        inversion Hsp.
        move: H0.
        case Hsi_hd: (ssa_instr m1 hd) => [sm1 sshd].
        case Hsp_tl: (ssa_program sm1 tl) => [sm2 sstl].
        move=> Hpair.
        case: Hpair => Htmp1 Htmp2 Htmp3.
        move: Hpst.
        inversion Hep; subst.
        move=> Hpst.
        rewrite /= in Hpst.
        remember (SSA.instr_succ_typenv shd ste1) as ste3.
        symmetry in Heqste3.
        move: (dessa_eval_instr_succ Hsi_hd Hseq Hteq H1 Heqste3) => Htmp.
        destruct Htmp as [s3 [te3 Hwit]].
        inversion Hwit as [Hseval [Hsstyp [Hseq2 Hteq2]]].
        move: (IH _ _ _ _ _ _ _ _ _ Hsp_tl Hseq2 Hteq2 H4 Hpst) => HIH.
        destruct HIH as [s2 [te2 Hswit]].
        inversion Hswit as [Hsep [Hstyp [Hseq3 Hteq3]]].
        exists s2, te2.
        split_andb_goal.
        eapply DSL.Econs.
        * exact: Hseval.
        * rewrite Hsstyp.
        * exact: Hsep.
        * rewrite /=.
            by rewrite Hsstyp.
        * exact: Hseq3.
        * exact: Hteq3.
  Qed.

  (** Convert an SSA state to a DSL state. *)

  Definition dessa_state (m : vmap) (s : SSAStore.t) : Store.t :=
    fun v => SSAStore.acc (v, get_index v m) s.

  Lemma acc_dessa_state :
    forall (m : vmap) (s : SSAStore.t) (v : var),
      Store.acc v (dessa_state m s) = SSAStore.acc (v, get_index v m) s.
  Proof.
    reflexivity.
  Qed.

  Lemma ssa_dessaK :
    forall (m : vmap) (s : Store.t) (x : var),
      Store.acc x (dessa_state m (ssa_state m s)) = Store.acc x s.
  Proof.
    move=> m s x.
    rewrite acc_dessa_state.
    rewrite (acc_ssa_state_eq _ (eqxx (get_index x m))).
    reflexivity.
  Qed.

  Corollary dessa_state_equiv :
    forall m s, state_equiv m (dessa_state m s) s.
  Proof.
    move=> m s x.
    exact: acc_dessa_state.
  Qed.

  Lemma ssa_store_conform m s te:
    Store.conform s te ->
    SSAStore.conform (ssa_state m s) (ssa_typenv m te).
  Proof.
    rewrite /Store.conform /SSAStore.conform /= => Hconform.
    move=> x Hmem.
    move: (ssa_typenv_exist Hmem) => [v].
    move=> Hssa.
    rewrite -Hssa in Hmem |- *.
    rewrite -ssa_typenv_mem in Hmem.
    rewrite -ssa_typenv_size.
    rewrite (Hconform _ Hmem).
    move: (ssa_state_equiv m s) => Hstate_equiv.
    rewrite (Hstate_equiv v).
    reflexivity.
  Qed.

  Corollary ssa_store_conform_empty s te:
    Store.conform s te ->
    SSAStore.conform (ssa_state empty_vmap s) (ssa_typenv empty_vmap te).
  Proof.
    exact: ssa_store_conform.
  Qed.

  Lemma dessa_store_conform m ss te:
    SSAStore.conform ss (ssa_typenv m te) ->
    Store.conform (dessa_state m ss) te.
  Proof.
    rewrite /Store.conform /SSAStore.conform /= => Hconform.
    move=> x Hmem.
    rewrite (ssa_typenv_mem m) in Hmem.
    rewrite (ssa_typenv_size _ _ m).
    rewrite (Hconform _ Hmem).
    move: (dessa_state_equiv m ss) => Hstate_equiv.
    rewrite -(Hstate_equiv x).
    reflexivity.
  Qed.

  Corollary dessa_store_conform_empty ss te:
    SSAStore.conform ss (ssa_typenv empty_vmap te) ->
    Store.conform (dessa_state empty_vmap ss) te.
  Proof.
    exact: dessa_store_conform.
  Qed.

  (** Soundness and completeness *)

  Theorem ssa_spec_sound (s : DSL.spec) :
    SSA.valid_spec (ssa_spec s) -> DSL.valid_spec s.
  Proof.
    destruct s as [input pre pg post].
    rewrite /ssa_spec /=.
    remember (ssa_typenv empty_vmap input) as sinput.
    remember (ssa_bexp empty_vmap pre) as spre.
    remember (ssa_program empty_vmap pg) as tmp.
    destruct tmp as [m ssa_p].
    remember (ssa_p) as sprog.
    remember (ssa_bexp m post) as spost.
    rewrite /SSA.valid_spec /DSL.valid_spec /=.
    rewrite Heqsinput Heqspre Heqspost.
    move=> Hsvalid.
    move=> s1 s2 Hconform Heval_bexp Heval_prog.
    move: (ssa_state_equiv empty_vmap s1) => Heq_state.
    move: (ssa_typenv_equiv empty_vmap input) => Heq_typenv.
    move: (ssa_store_conform_empty Hconform) => Hsconform.
    symmetry in Heqtmp.
    remember (DSL.program_succ_typenv pg input) as tsucc.
    symmetry in Heqtsucc.
    move: (ssa_eval_program_succ Heqtmp Heq_state Heq_typenv Heval_prog Heqtsucc) => [ss2 [ste2 [Hsep [H]]]].
    move: (Hsvalid (ssa_state empty_vmap s1) ss2) => {Hsvalid} Hsvalid.
    move: (Hsvalid Hsconform) => {Hsvalid} Hsvalid.
    move: (ssa_eval_bexp2 Heq_state Heq_typenv Heval_bexp) => Hsf.
    move: (Hsvalid Hsf) => {Hsvalid} Hsvalid.
    move: (Hsvalid Hsep) => {Hsvalid} Hsvalid.
    move=> [Heq_state2 Heq_typenv2].
    rewrite H in Hsvalid.
    exact: (ssa_eval_bexp1 Heq_state2 Heq_typenv2 Hsvalid).
  Qed.

  Theorem ssa_spec_complete (s : DSL.spec) :
    DSL.valid_spec s -> SSA.valid_spec (ssa_spec s).
  Proof.
    destruct s as [input pre pg post].
    rewrite /ssa_spec /=.
    remember (ssa_typenv empty_vmap input) as sinput.
    remember (ssa_bexp empty_vmap pre) as spre.
    remember (ssa_program empty_vmap pg) as tmp.
    destruct tmp as [m ssa_p].
    remember (ssa_p) as sprog.
    remember (ssa_bexp m post) as spost.
    rewrite /SSA.valid_spec /DSL.valid_spec /=.
    rewrite Heqsinput Heqspre Heqspost.
    move=> Hvalid.
    move=> ss1 ss2 Hsconform Hseval_bexp Hseval_prog.
    move: (dessa_state_equiv empty_vmap ss1) => Heq_state.
    move: (ssa_typenv_equiv empty_vmap input) => Heq_typenv.
    move: (dessa_store_conform_empty Hsconform) => Hconform.
    symmetry in Heqtmp.
    remember (SSA.program_succ_typenv sprog sinput) as tsucc.
    symmetry in Heqtsucc.
    rewrite Heqsinput in Heqtsucc.
    move: (dessa_eval_program_succ Heqtmp Heq_state Heq_typenv Hseval_prog Heqtsucc)
    => [s2 [ste2 [Hep [Hpst [Heq_state2 Heq_typenv2]]]]].
    move: (Hvalid (dessa_state empty_vmap ss1) s2) => {Hvalid} Hvalid.
    move: (Hvalid Hconform) => {Hvalid} Hvalid.
    move: (ssa_eval_bexp1 Heq_state Heq_typenv Hseval_bexp) => Hsf.
    move: (Hvalid Hsf) => {Hvalid} Hvalid.
    move: (Hvalid Hep) => {Hvalid} Hvalid.
    rewrite Hpst in Hvalid.
    rewrite Heqtsucc.
    exact: (ssa_eval_bexp2 Heq_state2 Heq_typenv2 Hvalid).
  Qed.

  (** Well-formed SSA *)

  Definition ssa_var_unchanged_instr v i : bool :=
    ~~ (SSAVS.mem v (SSA.lvs_instr i)).

  Definition ssa_unchanged_instr_var i v : bool :=
    ssa_var_unchanged_instr v i .

  Definition ssa_vars_unchanged_instr vs i : bool :=
    SSAVS.for_all (ssa_unchanged_instr_var i) vs .

  Definition ssa_var_unchanged_program v p : bool :=
    all (ssa_var_unchanged_instr v) p.

  Definition ssa_unchanged_program_var p v : bool :=
    all (ssa_var_unchanged_instr v) p .

  Definition ssa_vars_unchanged_program vs p : bool :=
    SSAVS.for_all (ssa_unchanged_program_var p) vs .

  Fixpoint ssa_single_assignment (p : SSA.program) : bool :=
    match p with
    | [::] => true
    | hd::tl =>
      (ssa_vars_unchanged_program (SSA.lvs_instr hd) tl) &&
                                                         (ssa_single_assignment tl)
    end.

  Definition well_formed_ssa_program (te: SSATE.env) (p : SSA.program) : bool :=
    (SSA.well_formed_program te p)
      && ssa_vars_unchanged_program (SSA.vars_env te) p
      && ssa_single_assignment p.

  Definition well_formed_ssa_spec (s : SSA.spec) : bool :=
    (SSA.well_formed_spec s)
      && ssa_vars_unchanged_program (SSA.vars_env (SSA.sinputs s)) (SSA.sprog s)
      && ssa_single_assignment (SSA.sprog s).

  Ltac neq_store_upd_acc :=
    match goal with
    | Hupd : SSAStore.Upd _ _ ?s1 ?s2
      |- SSAStore.acc _ ?s1 = SSAStore.acc _ ?s2 =>
      rewrite (SSAStore.acc_Upd_neq _ Hupd) //
    | H : SSAStore.Upd2 _ _ _ _ ?s1 ?s2
      |- SSAStore.acc _ ?s1 = SSAStore.acc _ ?s2 =>
      rewrite (SSAStore.acc_Upd2_neq _ _ H) //
    end .

  Ltac acc_unchanged_instr_upd :=
    match goal with
    | Hun : is_true (ssa_var_unchanged_instr ?x ?i),
            Heval : SSA.eval_instr _ (?i) ?s1 ?s2
      |- SSAStore.acc ?x ?s1 = SSAStore.acc ?x ?s2 =>
      rewrite /ssa_var_unchanged_instr /SSA.lvs_instr in Hun;
      move : (SSA.VSLemmas.not_mem_singleton1 Hun) => {Hun};
      rewrite /SSAVS.SE.eq => /negP Hneq;
      inversion_clear Heval;
      neq_store_upd_acc
    | Hun : is_true (ssa_var_unchanged_instr ?x ?i),
            Heval : SSA.eval_instr _ (?i) ?s1 ?s2
      |- SSAStore.acc ?x ?s1 = SSAStore.acc ?x ?s2 =>
      let Hun1 := fresh in
      let Hneqw := fresh in
      let Hneqv := fresh in
      rewrite /ssa_var_unchanged_instr /SSA.lvs_instr in Hun;
      move : (SSA.VSLemmas.not_mem_add1 Hun) => {Hun} [Hneqv Hun1];
      move : (SSA.VSLemmas.not_mem_singleton1 Hun1) Hneqv => {Hun1};
      rewrite /SSAVS.SE.eq => /negP Hneqw /negP Hneqv;
      inversion_clear Heval;
      neq_store_upd_acc
    | Hun : is_true (ssa_var_unchanged_instr ?x ?i),
            Heval : SSA.eval_instr _ (?i) ?s1 ?s2
      |- SSAStore.acc ?x ?s1 = SSAStore.acc ?x ?s2 =>
      rewrite /ssa_var_unchanged_instr /SSA.lvs_instr in Hun;
      inversion_clear Heval;
      trivial
    end .


  Lemma acc_unchanged_instr te v i s1 s2 :
    ssa_var_unchanged_instr v i ->
    SSA.eval_instr te i s1 s2 ->
    SSAStore.acc v s1 = SSAStore.acc v s2.
  Proof. elim: i; intros; by acc_unchanged_instr_upd. Qed.

  Lemma acc_unchanged_program te v p s1 s2 :
    ssa_unchanged_program_var p v ->
    SSA.eval_program te p s1 s2 ->
    SSAStore.acc v s1 = SSAStore.acc v s2.
  Proof .
    elim: p te s1 s2 => /= .
    - move=> te s1 s2 _ Hep.
      inversion_clear Hep.
      reflexivity.
    - move=> hd tl IH te s1 s2 /andP [Huchd Huctl] Hep.
      inversion_clear Hep .
      rewrite (acc_unchanged_instr Huchd H).
      apply (IH _ _ _ Huctl H0) .
  Qed.

  Lemma ssa_var_unchanged_program_cons1 v hd tl :
    ssa_unchanged_program_var (hd::tl) v ->
    ssa_var_unchanged_instr v hd /\ ssa_unchanged_program_var tl v .
  Proof.
    move => /andP H // .
  Qed .

  Lemma ssa_var_unchanged_program_cons2 v hd tl :
    ssa_var_unchanged_instr v hd ->
    ssa_unchanged_program_var tl v ->
    ssa_unchanged_program_var (hd::tl) v .
  Proof .
    move=> Hhd Htl.
    rewrite /ssa_unchanged_program_var /= -/(ssa_unchanged_program_var tl v) Hhd Htl // .
  Qed .

  Lemma ssa_var_unchanged_program_cons v hd tl :
    ssa_unchanged_program_var (hd::tl) v =
    (ssa_var_unchanged_instr v hd) && (ssa_unchanged_program_var tl v).
  Proof.
    case H: (ssa_var_unchanged_instr v hd && ssa_var_unchanged_program v tl).
    - move/andP: H=> [H1 H2]. exact: (ssa_var_unchanged_program_cons2 H1 H2).
    - apply/negP => Hcons. move/negP: H; apply. apply/andP.
      exact: (ssa_var_unchanged_program_cons1 Hcons).
  Qed.

  Lemma ssa_var_unchanged_program_cat1 v p1 p2 :
    ssa_unchanged_program_var (p1 ++ p2) v ->
    ssa_unchanged_program_var p1 v /\ ssa_unchanged_program_var p2 v .
  Proof.
    elim: p1 p2.
    - move=> /= p2; done .
    - move=> hd tl IH p2 /andP [Hhd Htlp2] .
      move: (IH _ Htlp2) => {IH Htlp2} [Htl Hp2] .
      rewrite /= Hhd Htl Hp2 // .
  Qed .

  Lemma ssa_var_unchanged_program_cat2 v p1 p2 :
    ssa_unchanged_program_var p1 v ->
    ssa_unchanged_program_var p2 v ->
    ssa_unchanged_program_var (p1 ++ p2) v .
  Proof.
    elim: p1 p2.
    - move=> /= p2 _ Hp2 // .
    - move=> hd tl IH p2 [Hhdtl Hp2].
      move: (ssa_var_unchanged_program_cons1 Hhdtl) => {Hhdtl} [Hhd Htl].
      apply/andP; split; first done .
      exact: (IH _ Htl Hp2) .
  Qed .

  Lemma acc_unchanged_program_cons te v hd tl s1 s2 s3 :
    ssa_unchanged_program_var (hd::tl) v ->
    SSA.eval_instr te hd s1 s2 ->
    SSA.eval_program te tl s2 s3 ->
    SSAStore.acc v s2 = SSAStore.acc v s1 /\
    SSAStore.acc v s3 = SSAStore.acc v s1 .
  Proof .
    move=> /andP [Hunhd Huntl] Hehd Hetl .
    move: (acc_unchanged_instr Hunhd Hehd) (acc_unchanged_program Huntl Hetl) =>
    H21 H32 .
    rewrite -H32 -H21 .
    split; reflexivity .
  Qed .

  Lemma acc_unchanged_program_cat te v p1 p2 s1 s2 s3 :
    ssa_unchanged_program_var (p1 ++ p2) v ->
    SSA.eval_program te p1 s1 s2 ->
    SSA.eval_program te p2 s2 s3 ->
    SSAStore.acc v s2 = SSAStore.acc v s1 /\
    SSAStore.acc v s3 = SSAStore.acc v s1 .
  Proof .
    move=> Hun12 Hep1 Hep2.
    move: (ssa_var_unchanged_program_cat1 Hun12) => {Hun12} [Hun1 Hun2] .
    rewrite -(acc_unchanged_program Hun2 Hep2) -(acc_unchanged_program Hun1 Hep1) .
    split; reflexivity .
  Qed.

  Lemma ssa_unchanged_instr_var_compat i :
    SetoidList.compat_bool SSAVS.E.eq (ssa_unchanged_instr_var i).
  Proof.
    move=> x y Heq; rewrite (eqP Heq) // .
  Qed .

  Lemma ssa_unchanged_program_var_compat p :
    SetoidList.compat_bool SSAVS.E.eq (ssa_unchanged_program_var p) .
  Proof .
    move=> x y Heq; rewrite (eqP Heq) // .
  Qed .

  Lemma ssa_unchanged_instr_mem v vs i :
    ssa_vars_unchanged_instr vs i ->
    SSAVS.mem v vs ->
    ssa_var_unchanged_instr v i .
  Proof.
    move=> Hun Hmem.
    apply: (SSAVS.for_all_2 (ssa_unchanged_instr_var_compat i) Hun).
    apply/SSA.VSLemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_program_mem v vs p :
    ssa_vars_unchanged_program vs p ->
    SSAVS.mem v vs ->
    ssa_unchanged_program_var p v.
  Proof.
    move=> Hun Hmem.
    apply: (SSAVS.for_all_2 (ssa_unchanged_program_var_compat p) Hun).
    apply/SSA.VSLemmas.memP; assumption.
  Qed.

  Lemma ssa_var_unchanged_instr_not_mem v i :
    ssa_var_unchanged_instr v i = ~~ SSAVS.mem v (SSA.lvs_instr i).
  Proof.
    case Hmem: (SSAVS.mem v (SSA.lvs_instr i)) => /=.
    - apply/negPn. exact: Hmem.
    - move/negP/idP: Hmem. by apply.
  Qed.

  Lemma ssa_var_unchanged_program_not_mem v p :
    ssa_unchanged_program_var p v = ~~ SSAVS.mem v (SSA.lvs_program p) .
  Proof .
    case Hmem: (SSAVS.mem v (SSA.lvs_program p)) => /= .
    - elim: p Hmem => /=.
      + done.
      + move=> hd tl IH Hmem. case: (SSA.VSLemmas.mem_union1 Hmem) =>
                              {Hmem} Hmem.
        * rewrite /ssa_var_unchanged_instr Hmem. done.
        * rewrite (IH Hmem). by case: (ssa_var_unchanged_instr v hd).
    - move/negP/idP: Hmem => Hmem. elim: p Hmem => /=.
      + done.
      + move=> hd tl IH Hmem. move: (SSA.VSLemmas.not_mem_union1 Hmem) =>
                              {Hmem} [Hmem1 Hmem2]. move: (IH Hmem2) => Hun.
        rewrite ssa_var_unchanged_instr_not_mem Hmem1 Hun. done.
  Qed.

  Lemma ssa_unchanged_instr_global vs i :
    (forall v, SSAVS.mem v vs -> ssa_var_unchanged_instr v i) ->
    ssa_vars_unchanged_instr vs i.
  Proof.
    move=> H.
    apply: (SSAVS.for_all_1 (ssa_unchanged_instr_var_compat i)).
    move=> v Hin.
    apply: H; apply/SSA.VSLemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_program_global vs p :
    (forall v, SSAVS.mem v vs -> ssa_unchanged_program_var p v) ->
    ssa_vars_unchanged_program vs p.
  Proof.
    move=> H.
    apply: (SSAVS.for_all_1 (ssa_unchanged_program_var_compat p)).
    move=> v Hin.
    apply: H; apply/SSA.VSLemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_instr_local vs i :
    ssa_vars_unchanged_instr vs i ->
    (forall v, SSAVS.mem v vs -> ssa_var_unchanged_instr v i).
  Proof.
    move=> H v Hmem.
    apply: (SSAVS.for_all_2 (ssa_unchanged_instr_var_compat i) H).
    apply/SSA.VSLemmas.memP; assumption.
  Qed.

  Lemma ssa_unchanged_program_local vs p :
    ssa_vars_unchanged_program vs p ->
    (forall v, SSAVS.mem v vs -> ssa_unchanged_program_var p v).
  Proof.
    move=> H v Hmem.
    exact: (ssa_unchanged_program_mem H Hmem).
  Qed.

  Lemma ssa_unchanged_program_cons1 vs hd tl :
    ssa_vars_unchanged_program vs (hd::tl) ->
    ssa_vars_unchanged_instr vs hd /\ ssa_vars_unchanged_program vs tl.
  Proof.
    move=> H. move: (ssa_unchanged_program_local H) => {H} H. split.
    - apply: ssa_unchanged_instr_global => v Hmem.
      move: (H v Hmem) => {H} H.
      exact: (proj1 (ssa_var_unchanged_program_cons1 H)).
    - apply: ssa_unchanged_program_global => v Hmem.
      move: (H v Hmem) => {H} H.
      exact: (proj2 (ssa_var_unchanged_program_cons1 H)).
  Qed.

  Lemma ssa_unchanged_program_cons2 vs hd tl :
    ssa_vars_unchanged_instr vs hd ->
    ssa_vars_unchanged_program vs tl ->
    ssa_vars_unchanged_program vs (hd::tl).
  Proof.
    move=> [Hhd Htl]. apply: ssa_unchanged_program_global => v Hmem.
    apply/andP; split.
    - exact: (ssa_unchanged_instr_local Hhd Hmem).
    - exact: (ssa_unchanged_program_local Htl Hmem).
  Qed.

  Lemma ssa_unchanged_program_cons vs hd tl :
    ssa_vars_unchanged_program vs (hd::tl) =
    (ssa_vars_unchanged_instr vs hd) && (ssa_vars_unchanged_program vs tl).
  Proof.
    case H: (ssa_vars_unchanged_instr vs hd && ssa_vars_unchanged_program vs tl).
    - move/andP: H=> [H1 H2]. exact: (ssa_unchanged_program_cons2 H1 H2).
    - apply/negP => Hcons. move/negP: H; apply. apply/andP.
      exact: (ssa_unchanged_program_cons1 Hcons).
  Qed.

  Lemma ssa_unchanged_program_cat1 vs p1 p2 :
    ssa_vars_unchanged_program vs (p1 ++ p2) ->
    ssa_vars_unchanged_program vs p1 /\ ssa_vars_unchanged_program vs p2.
  Proof.
    move=> H; split; apply: ssa_unchanged_program_global => v Hmem.
    - exact: (proj1 (ssa_var_unchanged_program_cat1
                       (ssa_unchanged_program_local H Hmem))).
    - exact: (proj2 (ssa_var_unchanged_program_cat1
                       (ssa_unchanged_program_local H Hmem))).
  Qed.

  Lemma ssa_unchanged_program_cat2 vs p1 p2 :
    ssa_vars_unchanged_program vs p1 ->
    ssa_vars_unchanged_program vs p2 ->
    ssa_vars_unchanged_program vs (p1 ++ p2).
  Proof.
    move=> Hp1 Hp2. apply: ssa_unchanged_program_global => v Hmem.
    apply: ssa_var_unchanged_program_cat2.
    - exact: (ssa_unchanged_program_local Hp1 Hmem).
    - exact: (ssa_unchanged_program_local Hp2 Hmem).
  Qed.

  Lemma ssa_unchanged_program_cat vs p1 p2 :
    ssa_vars_unchanged_program vs (p1 ++ p2) =
    (ssa_vars_unchanged_program vs p1) && (ssa_vars_unchanged_program vs p2).
  Proof.
    case H: ((ssa_vars_unchanged_program vs p1) && (ssa_vars_unchanged_program vs p2)).
    - move/andP: H=> [H1 H2]. by apply: ssa_unchanged_program_cat2.
    - apply/negP=> Hcat. move/idP/negP: H.
      by move: (ssa_unchanged_program_cat1 Hcat) => [-> ->].
  Qed.

  Lemma ssa_unchanged_program_hd vs hd tl :
    ssa_vars_unchanged_program vs (hd::tl) ->
    ssa_vars_unchanged_instr vs hd.
  Proof.
    move=> Hun; move: (ssa_unchanged_program_cons1 Hun) => [Hhd Htl]; assumption.
  Qed.

  Lemma ssa_unchanged_program_tl vs hd tl :
    ssa_vars_unchanged_program vs (hd::tl) ->
    ssa_vars_unchanged_program vs tl.
  Proof.
    move=> Hun; move: (ssa_unchanged_program_cons1 Hun) => [Hhd Htl]; assumption.
  Qed.

  Lemma ssa_unchanged_instr_singleton1 v i :
    ssa_vars_unchanged_instr (SSAVS.singleton v) i ->
    ssa_var_unchanged_instr v i.
  Proof.
    move=> Hun.
    apply: (ssa_unchanged_instr_mem Hun).
    apply: SSA.VSLemmas.mem_singleton2.
    exact: eqxx.
  Qed.

  Lemma ssa_unchanged_program_singleton1 v p :
    ssa_vars_unchanged_program (SSAVS.singleton v) p ->
    ssa_unchanged_program_var p v.
  Proof.
    move=> Hun.
    apply: (ssa_unchanged_program_mem Hun).
    apply: SSA.VSLemmas.mem_singleton2.
    exact: eqxx.
  Qed.

  Lemma ssa_unchanged_instr_singleton2 v i :
    ssa_var_unchanged_instr v i ->
    ssa_vars_unchanged_instr (SSAVS.singleton v) i.
  Proof.
    move=> Hun.
    apply: ssa_unchanged_instr_global => x Hmem.
    move: (SSA.VSLemmas.mem_singleton1 Hmem) => Heq.
    rewrite (eqP Heq); assumption.
  Qed.

  Lemma ssa_unchanged_program_singleton2 v p :
    ssa_unchanged_program_var p v ->
    ssa_vars_unchanged_program (SSAVS.singleton v) p.
  Proof.
    move=> Hun.
    apply: ssa_unchanged_program_global => x Hmem.
    move: (SSA.VSLemmas.mem_singleton1 Hmem) => Heq.
    rewrite (eqP Heq); assumption.
  Qed.

  Lemma ssa_unchanged_instr_union1 s1 s2 i :
    ssa_vars_unchanged_instr (SSAVS.union s1 s2) i ->
    ssa_vars_unchanged_instr s1 i /\ ssa_vars_unchanged_instr s2 i.
  Proof.
    move=> Hun.
    move: (ssa_unchanged_instr_local Hun) => {Hun} Hun.
    split; apply: ssa_unchanged_instr_global => v Hmem.
    - apply: Hun.
      exact: SSA.VSLemmas.mem_union2.
    - apply: Hun.
      exact: SSA.VSLemmas.mem_union3.
  Qed.

  Lemma ssa_unchanged_program_union1 s1 s2 p :
    ssa_vars_unchanged_program (SSAVS.union s1 s2) p ->
    ssa_vars_unchanged_program s1 p /\ ssa_vars_unchanged_program s2 p.
  Proof.
    move=> Hun.
    move: (ssa_unchanged_program_local Hun) => {Hun} Hun.
    split; apply: ssa_unchanged_program_global => v Hmem.
    - apply: Hun.
      exact: SSA.VSLemmas.mem_union2.
    - apply: Hun.
      exact: SSA.VSLemmas.mem_union3.
  Qed.

  Lemma ssa_unchanged_instr_union2 s1 s2 i :
    ssa_vars_unchanged_instr s1 i -> ssa_vars_unchanged_instr s2 i ->
    ssa_vars_unchanged_instr (SSAVS.union s1 s2) i.
  Proof.
    move=> Hun1 Hun2.
    apply: ssa_unchanged_instr_global => x Hmem.
    move: (SSA.VSLemmas.mem_union1 Hmem); case => {Hmem} Hmem.
    - exact: (ssa_unchanged_instr_mem Hun1 Hmem).
    - exact: (ssa_unchanged_instr_mem Hun2 Hmem).
  Qed.

  Lemma ssa_unchanged_program_union2 s1 s2 p :
    ssa_vars_unchanged_program s1 p -> ssa_vars_unchanged_program s2 p ->
    ssa_vars_unchanged_program (SSAVS.union s1 s2) p.
  Proof.
    move=> Hun1 Hun2.
    apply: ssa_unchanged_program_global => x Hmem.
    move: (SSA.VSLemmas.mem_union1 Hmem); case => {Hmem} Hmem.
    - exact: (ssa_unchanged_program_mem Hun1 Hmem).
    - exact: (ssa_unchanged_program_mem Hun2 Hmem).
  Qed.

  Lemma ssa_unchanged_instr_union s1 s2 i :
    ssa_vars_unchanged_instr (SSAVS.union s1 s2) i =
    (ssa_vars_unchanged_instr s1 i && ssa_vars_unchanged_instr s2 i).
  Proof.
    case H: (ssa_vars_unchanged_instr s1 i && ssa_vars_unchanged_instr s2 i).
    - move/andP: H=> [H1 H2]. exact: (ssa_unchanged_instr_union2 H1 H2).
    - apply/negP=> Hun. move/negP: H; apply. apply/andP.
      exact: (ssa_unchanged_instr_union1 Hun).
  Qed.

  Lemma ssa_unchanged_program_union s1 s2 p :
    ssa_vars_unchanged_program (SSAVS.union s1 s2) p =
    (ssa_vars_unchanged_program s1 p && ssa_vars_unchanged_program s2 p).
  Proof.
    case H: (ssa_vars_unchanged_program s1 p && ssa_vars_unchanged_program s2 p).
    - move/andP: H=> [H1 H2]. exact: (ssa_unchanged_program_union2 H1 H2).
    - apply/negP=> Hun. move/negP: H; apply. apply/andP.
      exact: (ssa_unchanged_program_union1 Hun).
  Qed.

  Lemma ssa_unchanged_instr_subset vs1 vs2 i :
    ssa_vars_unchanged_instr vs2 i ->
    SSAVS.subset vs1 vs2 ->
    ssa_vars_unchanged_instr vs1 i.
  Proof.
    move=> Hun Hsub.
    move: (ssa_unchanged_instr_local Hun) => {Hun} Hun.
    apply: ssa_unchanged_instr_global.
    move=> v Hmem; apply: Hun.
    exact: (SSA.VSLemmas.mem_subset Hmem Hsub).
  Qed.

  Lemma ssa_unchanged_program_subset vs1 vs2 p :
    ssa_vars_unchanged_program vs2 p ->
    SSAVS.subset vs1 vs2 ->
    ssa_vars_unchanged_program vs1 p.
  Proof.
    move=> Hun Hsub.
    move: (ssa_unchanged_program_local Hun) => {Hun} Hun.
    apply: ssa_unchanged_program_global.
    move=> v Hmem; apply: Hun.
    exact: (SSA.VSLemmas.mem_subset Hmem Hsub).
  Qed.

  Lemma ssa_unchanged_instr_add1 v s p :
    ssa_vars_unchanged_instr (SSAVS.add v s) p ->
    ssa_var_unchanged_instr v p /\ ssa_vars_unchanged_instr s p.
  Proof.
    move=> H; split.
    - apply: (ssa_unchanged_instr_mem H).
      apply: SSA.VSLemmas.mem_add2.
      exact: SSAVS.E.eq_refl.
    - apply: (ssa_unchanged_instr_subset H).
      exact: (SSA.VSLemmas.subset_add _ (SSA.VSLemmas.subset_refl s)).
  Qed.

  Lemma ssa_unchanged_instr_add2 v s p :
    ssa_var_unchanged_instr v p /\ ssa_vars_unchanged_instr s p ->
    ssa_vars_unchanged_instr (SSAVS.add v s) p.
  Proof.
    move=> [H1 H2].
    apply: ssa_unchanged_instr_global => x Hmem.
    case: (SSA.VSLemmas.mem_add1 Hmem) => {Hmem}.
    - move=> Heq. by rewrite (eqP Heq).
    - move=> Hmem. exact: (ssa_unchanged_instr_mem H2 Hmem).
  Qed.

  Lemma ssa_unchanged_program_add1 v s p :
    ssa_vars_unchanged_program (SSAVS.add v s) p ->
    ssa_unchanged_program_var p v /\ ssa_vars_unchanged_program s p.
  Proof.
    move=> H; split.
    - apply: (ssa_unchanged_program_mem H).
      apply: SSA.VSLemmas.mem_add2.
      exact: SSAVS.E.eq_refl.
    - apply: (ssa_unchanged_program_subset H).
      exact: (SSA.VSLemmas.subset_add _ (SSA.VSLemmas.subset_refl s)).
  Qed.

  Lemma ssa_unchanged_program_add2 v s p :
    ssa_unchanged_program_var p v /\ ssa_vars_unchanged_program s p ->
    ssa_vars_unchanged_program (SSAVS.add v s) p.
  Proof.
    move=> [H1 H2].
    apply: ssa_unchanged_program_global => x Hmem.
    case: (SSA.VSLemmas.mem_add1 Hmem) => {Hmem}.
    - move=> Heq.
        by rewrite (eqP Heq).
    - move=> Hmem.
      exact: (ssa_unchanged_program_mem H2 Hmem).
  Qed.

  Lemma ssa_unchanged_program_empty vs :
    ssa_vars_unchanged_program vs [::].
  Proof.
    apply: ssa_unchanged_program_global => v Hv.
    done.
  Qed.

  Lemma ssa_unchanged_instr_disjoint_lvs vs i :
    ssa_vars_unchanged_instr vs i =
    SSA.VSLemmas.disjoint vs (SSA.lvs_instr i) .
  Proof.
    case Hdisj: (SSA.VSLemmas.disjoint vs (SSA.lvs_instr i)) .
    - apply: ssa_unchanged_instr_global => v Hmem .
      exact: (SSA.VSLemmas.mem_disjoint1 Hdisj Hmem) .
    - apply/negP => Hunch. move/negP: Hdisj; apply .
      move: (ssa_unchanged_instr_local Hunch) => {Hunch} Hunch .
      exact: (SSA.VSLemmas.mem_disjoint3 Hunch) .
  Qed .

  Lemma ssa_unchanged_program_disjoint_lvs vs p :
    ssa_vars_unchanged_program vs p =
    SSA.VSLemmas.disjoint vs (SSA.lvs_program p) .
  Proof.
    case Hdisj: (SSA.VSLemmas.disjoint vs (SSA.lvs_program p)) .
    - elim: p vs Hdisj => /=.
      + move=> vs _. exact: ssa_unchanged_program_empty.
      + move=> hd tl IH vs Hdisj. rewrite SSA.VSLemmas.disjoint_union in Hdisj.
        move/andP: Hdisj => [Hdisjhd Hdisjtl]. apply: ssa_unchanged_program_cons2.
        * rewrite ssa_unchanged_instr_disjoint_lvs. exact: Hdisjhd.
        * exact: (IH _ Hdisjtl).
    - apply/negP => Hunch. move/negP: Hdisj; apply.
      move: (ssa_unchanged_program_local Hunch) => {Hunch} Hunch.
      apply: SSA.VSLemmas.mem_disjoint3. move=> x Hmem.
      move: (Hunch x Hmem). rewrite ssa_var_unchanged_program_not_mem. done.
  Qed.

  Lemma ssa_unchanged_program_replace vs1 vs2 p :
    SSAVS.Equal vs1 vs2 ->
    ssa_vars_unchanged_program vs1 p ->
    ssa_vars_unchanged_program vs2 p.
  Proof.
    move=> Heq Hunch. apply: (ssa_unchanged_program_subset Hunch).
    rewrite Heq. exact: SSAVS.Lemmas.subset_refl.
  Qed.


  Lemma ssa_var_unchanged_eqn_instr v i :
    ssa_var_unchanged_instr v (SSA.eqn_instr i) = ssa_var_unchanged_instr v i.
  Proof. case: i => //=. by case. Qed.

  Lemma ssa_var_unchanged_rng_instr v i :
    ssa_var_unchanged_instr v (SSA.rng_instr i) = ssa_var_unchanged_instr v i.
  Proof. case: i => //=. by case. Qed.

  Lemma ssa_unchanged_eqn_instr_var i v :
    ssa_unchanged_instr_var (SSA.eqn_instr i) v = ssa_unchanged_instr_var i v.
  Proof. case: i => //=. by case. Qed.

  Lemma ssa_unchanged_rng_instr_var i v :
    ssa_unchanged_instr_var (SSA.rng_instr i) v = ssa_unchanged_instr_var i v.
  Proof. case: i => //=. by case. Qed.

  Lemma ssa_vars_unchanged_eqn_instr vs i :
    ssa_vars_unchanged_instr vs (SSA.eqn_instr i) = ssa_vars_unchanged_instr vs i.
  Proof. case: i => //=. by case. Qed.

  Lemma ssa_vars_unchanged_rng_instr vs i :
    ssa_vars_unchanged_instr vs (SSA.rng_instr i) = ssa_vars_unchanged_instr vs i.
  Proof. case: i => //=. by case. Qed.

  Lemma ssa_var_unchanged_eqn_program v p :
    ssa_var_unchanged_program v (SSA.eqn_program p) = ssa_var_unchanged_program v p.
  Proof. elim: p => [| i p IH] //=. by rewrite ssa_var_unchanged_eqn_instr IH. Qed.

  Lemma ssa_var_unchanged_rng_program v p :
    ssa_var_unchanged_program v (SSA.rng_program p) = ssa_var_unchanged_program v p.
  Proof. elim: p => [| i p IH] //=. by rewrite ssa_var_unchanged_rng_instr IH. Qed.

  Lemma ssa_unchanged_eqn_program_var p v :
    ssa_unchanged_program_var (SSA.eqn_program p) v = ssa_unchanged_program_var p v.
  Proof. elim: p => [| i p IH] //=. by rewrite ssa_var_unchanged_eqn_instr IH. Qed.

  Lemma ssa_unchanged_rng_program_var p v :
    ssa_unchanged_program_var (SSA.rng_program p) v = ssa_unchanged_program_var p v.
  Proof. elim: p => [| i p IH] //=. by rewrite ssa_var_unchanged_rng_instr IH. Qed.

  Lemma ssa_vars_unchanged_eqn_program vs p :
    ssa_vars_unchanged_program vs (SSA.eqn_program p) =
    ssa_vars_unchanged_program vs p.
  Proof.
    elim: p => [| i p IH] //=.
      by rewrite !ssa_unchanged_program_cons ssa_vars_unchanged_eqn_instr IH.
  Qed.

  Lemma ssa_vars_unchanged_rng_program vs p :
    ssa_vars_unchanged_program vs (SSA.rng_program p) =
    ssa_vars_unchanged_program vs p.
  Proof.
    elim: p => [| i p IH] //=.
      by rewrite !ssa_unchanged_program_cons ssa_vars_unchanged_rng_instr IH.
  Qed.


  Lemma ssa_unchanged_instr_eval_singleton v te s1 s2 i :
    ssa_vars_unchanged_instr (SSAVS.singleton v) i ->
    SSA.eval_instr te i s1 s2 ->
    SSAStore.acc v s1 = SSAStore.acc v s2.
  Proof.
    move=> Hun Hei.
    move: (ssa_unchanged_instr_singleton1 Hun) => {Hun} Hun.
    exact: (acc_unchanged_instr Hun Hei).
  Qed.

  Lemma ssa_unchanged_instr_acc2z v te s1 s2 i :
    ssa_vars_unchanged_instr (SSAVS.singleton v) i ->
    SSA.eval_instr te i s1 s2 ->
    SSA.acc2z te v s1 = SSA.acc2z te v s2.
  Proof.
    move=> Hun Hei. rewrite /SSA.acc2z.
    rewrite (ssa_unchanged_instr_eval_singleton Hun Hei). reflexivity.
  Qed.

  Lemma ssa_unchanged_instr_eval_atomic a te s1 s2 i :
    ssa_vars_unchanged_instr (SSA.vars_atomic a) i ->
    SSA.eval_instr te i s1 s2 ->
    SSA.eval_atomic a s1 = SSA.eval_atomic a s2.
  Proof.
    case: a => /=.
    - move=> v. exact: ssa_unchanged_instr_eval_singleton.
    - reflexivity.
  Qed.

  Lemma ssa_unchanged_instr_eval_eexp e te s1 s2 i :
    ssa_vars_unchanged_instr (SSA.vars_eexp e) i ->
    SSA.eval_instr te i s1 s2 ->
    SSA.eval_eexp e te s1 = SSA.eval_eexp e te s2.
  Proof.
    elim: e => /=.
    - move=> a Hun Hei. exact: (ssa_unchanged_instr_acc2z Hun Hei).
    - reflexivity.
    - move=> op e IH Hun Hei. rewrite (IH Hun Hei); reflexivity.
    - move=> op e1 IH1 e2 IH2 Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei); reflexivity.
  Qed.

  Lemma ssa_unchanged_instr_eval_rexp e te s1 s2 i :
    ssa_vars_unchanged_instr (SSA.vars_rexp e) i ->
    SSA.eval_instr te i s1 s2 ->
    SSA.eval_rexp e s1 = SSA.eval_rexp e s2.
  Proof.
    elim: e => /=.
    - move=> a. exact: ssa_unchanged_instr_eval_singleton.
    - reflexivity.
    - move=> _ op e0 IH0 Hun Hei .
      rewrite (IH0 Hun Hei) // .
    - move=> _ op e1 IH1 e2 IH2 Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei); reflexivity.
    - move=> _ e IH n Hun Hei. rewrite (IH Hun Hei); reflexivity.
    - move=> _ e IH n Hun Hei. rewrite (IH Hun Hei) // .
  Qed.

  Lemma ssa_unchanged_program_eval_singleton v te s1 s2 p :
    ssa_vars_unchanged_program (SSAVS.singleton v) p ->
    SSA.eval_program te p s1 s2 ->
    SSAStore.acc v s1 = SSAStore.acc v s2.
  Proof.
    move=> Hun Hep.
    move: (ssa_unchanged_program_singleton1 Hun) => {Hun} Hun.
    exact: (acc_unchanged_program Hun Hep).
  Qed.

  Lemma ssa_unchanged_program_acc2z v te s1 s2 p :
    ssa_vars_unchanged_program (SSAVS.singleton v) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.acc2z te v s1 = SSA.acc2z te v s2.
  Proof.
    move=> Hun Hep. rewrite /SSA.acc2z.
    rewrite (ssa_unchanged_program_eval_singleton Hun Hep). reflexivity.
  Qed.

  Lemma ssa_unchanged_program_eval_atomic a te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_atomic a) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_atomic a s1 = SSA.eval_atomic a s2.
  Proof.
    case: a => /=.
    - move=> v. exact: ssa_unchanged_program_eval_singleton.
    - reflexivity.
  Qed.

  Lemma ssa_unchanged_program_eval_eexp e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_eexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_eexp e te s1 = SSA.eval_eexp e te s2.
  Proof.
    elim: e => /=.
    - move=> a Hun Hep. exact: (ssa_unchanged_program_acc2z Hun Hep).
    - reflexivity.
    - move=> op e IH Hun Hep. rewrite (IH Hun Hep); reflexivity.
    - move=> op e1 IH1 e2 IH2 Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep); reflexivity.
  Qed.

  Lemma ssa_unchanged_program_eval_rexp e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_rexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_rexp e s1 = SSA.eval_rexp e s2.
  Proof.
    elim: e => /=.
    - move=> a Hun Hep.
      exact: (ssa_unchanged_program_eval_singleton Hun Hep).
    - reflexivity.
    - move=> _ e v IH Hun Hep.
      rewrite (IH Hun Hep) // .
    - move=> _ op e1 IH1 e2 IH2 Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep); reflexivity.
    - move=> _ e IH n Hun Hep.
      rewrite (IH Hun Hep); reflexivity.
    - move=> _ e IH n Hun Hep.
      rewrite (IH Hun Hep); reflexivity.
  Qed.

  Lemma ssa_unchanged_instr_eval_ebexp e te s1 s2 i :
    ssa_vars_unchanged_instr (SSA.vars_ebexp e) i ->
    SSA.eval_instr te i s1 s2 ->
    SSA.eval_ebexp e te s1 <-> SSA.eval_ebexp e te s2.
  Proof.
    elim: e => /=.
    - done.
    - move=> e1 e2 Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (ssa_unchanged_instr_eval_eexp Hun1 Hei)
              (ssa_unchanged_instr_eval_eexp Hun2 Hei).
      done.
    - move=> e1 e2 p Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      move: (ssa_unchanged_instr_union1 Hun2) => {Hun2} [Hun2 Hunp].
      rewrite (ssa_unchanged_instr_eval_eexp Hun1 Hei)
              (ssa_unchanged_instr_eval_eexp Hun2 Hei)
              (ssa_unchanged_instr_eval_eexp Hunp Hei).
      done.
    - move=> e1 IH1 e2 IH2 Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei).
      done.
  Qed.

  Lemma ssa_unchanged_instr_eval_rbexp e te s1 s2 i :
    ssa_vars_unchanged_instr (SSA.vars_rbexp e) i ->
    SSA.eval_instr te i s1 s2 ->
    SSA.eval_rbexp e s1 <-> SSA.eval_rbexp e s2.
  Proof.
    elim: e => /=.
    - done.
    - move=> _ e1 e2 Hun Hei .
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2] .
      rewrite (ssa_unchanged_instr_eval_rexp Hun1 Hei)
              (ssa_unchanged_instr_eval_rexp Hun2 Hei) // .
    - move=> _ op e1 e2 Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (ssa_unchanged_instr_eval_rexp Hun1 Hei)
              (ssa_unchanged_instr_eval_rexp Hun2 Hei) // .
    - move=> e IH Hun Hei .
      rewrite (IH Hun Hei) // .
    - move=> e1 IH1 e2 IH2 Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei) // .
    - move=> e1 IH1 e2 IH2 Hun Hei.
      move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hei) (IH2 Hun2 Hei) //.
  Qed.

  Lemma ssa_unchanged_instr_eval_bexp e te s1 s2 i :
    ssa_vars_unchanged_instr (SSA.vars_bexp e) i ->
    SSA.eval_instr te i s1 s2 ->
    SSA.eval_bexp e te s1 <-> SSA.eval_bexp e te s2.
  Proof.
    move=> Hun Hei. move: (ssa_unchanged_instr_union1 Hun) => {Hun} [Hun1 Hun2].
    split; move => [H1 H2].
    - exact: (conj (proj1 (ssa_unchanged_instr_eval_ebexp Hun1 Hei) H1)
                   (proj1 (ssa_unchanged_instr_eval_rbexp Hun2 Hei) H2)).
    - exact: (conj (proj2 (ssa_unchanged_instr_eval_ebexp Hun1 Hei) H1)
                   (proj2 (ssa_unchanged_instr_eval_rbexp Hun2 Hei) H2)).
  Qed.

  Lemma ssa_unchanged_program_eval_ebexp e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_ebexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_ebexp e te s1 <-> SSA.eval_ebexp e te s2.
  Proof.
    elim: e => /=.
    - done.
    - move=> e1 e2 Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (ssa_unchanged_program_eval_eexp Hun1 Hep)
              (ssa_unchanged_program_eval_eexp Hun2 Hep).
      done.
    - move=> e1 e2 n Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      move: (ssa_unchanged_program_union1 Hun2) => {Hun2} [Hun2 Hunp].
      rewrite (ssa_unchanged_program_eval_eexp Hun1 Hep)
              (ssa_unchanged_program_eval_eexp Hun2 Hep)
              (ssa_unchanged_program_eval_eexp Hunp Hep).
      done.
    - move=> e1 IH1 e2 IH2 Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep).
      done.
  Qed.

  Lemma ssa_unchanged_program_eval_ebexp1 te e s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_ebexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_ebexp e te s1 -> SSA.eval_ebexp e te s2.
  Proof.
    move=> Hun Hep He.
    exact: (proj1 (ssa_unchanged_program_eval_ebexp Hun Hep) He).
  Qed.

  Lemma ssa_unchanged_program_eval_ebexp2 e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_ebexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_ebexp e te s2 -> SSA.eval_ebexp e te s1.
  Proof.
    move=> Hun Hep He.
    exact: (proj2 (ssa_unchanged_program_eval_ebexp Hun Hep) He).
  Qed.

  Lemma ssa_unchanged_program_eval_rbexp e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_rbexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_rbexp e s1 <-> SSA.eval_rbexp e s2.
  Proof.
    elim: e => /=.
    - done.
    - move => _ e1 e2 Hun Hep .
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (ssa_unchanged_program_eval_rexp Hun1 Hep)
              (ssa_unchanged_program_eval_rexp Hun2 Hep) // .
    - move=> _ op e1 e2 Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (ssa_unchanged_program_eval_rexp Hun1 Hep)
              (ssa_unchanged_program_eval_rexp Hun2 Hep) // .
    - move=> e IH Hun Hep.
      rewrite (IH Hun Hep) // .
    - move=> e1 IH1 e2 IH2 Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep) // .
    - move=> e1 IH1 e2 IH2 Hun Hep.
      move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
      rewrite (IH1 Hun1 Hep) (IH2 Hun2 Hep) //.
  Qed.

  Lemma ssa_unchanged_program_eval_rbexp1 e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_rbexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_rbexp e s1 -> SSA.eval_rbexp e s2.
  Proof.
    move=> Hun Hep He.
    exact: (proj1 (ssa_unchanged_program_eval_rbexp Hun Hep) He).
  Qed.

  Lemma ssa_unchanged_program_eval_rbexp2 e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_rbexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_rbexp e s2 -> SSA.eval_rbexp e s1.
  Proof.
    move=> Hun Hep He.
    exact: (proj2 (ssa_unchanged_program_eval_rbexp Hun Hep) He).
  Qed.

  Lemma ssa_unchanged_program_eval_bexp e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_bexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_bexp e te s1 <-> SSA.eval_bexp e te s2.
  Proof.
    move=> Hun Hep. move: (ssa_unchanged_program_union1 Hun) => {Hun} [Hun1 Hun2].
    split; move=> [H1 H2].
    - exact: (conj (proj1 (ssa_unchanged_program_eval_ebexp Hun1 Hep) H1)
                   (proj1 (ssa_unchanged_program_eval_rbexp Hun2 Hep) H2)).
    - exact: (conj (proj2 (ssa_unchanged_program_eval_ebexp Hun1 Hep) H1)
                   (proj2 (ssa_unchanged_program_eval_rbexp Hun2 Hep) H2)).
  Qed.

  Lemma ssa_unchanged_program_eval_bexp1 e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_bexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_bexp e te s1 -> SSA.eval_bexp e te s2.
  Proof.
    move=> Hunch Hp He.
    move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
    exact: (H1 He).
  Qed.

  Lemma ssa_unchanged_program_eval_bexp2 e te s1 s2 p :
    ssa_vars_unchanged_program (SSA.vars_bexp e) p ->
    SSA.eval_program te p s1 s2 ->
    SSA.eval_bexp e te s2 -> SSA.eval_bexp e te s1.
  Proof.
    move=> Hunch Hp He.
    move: (ssa_unchanged_program_eval_bexp Hunch Hp) => [H1 H2].
    exact: (H2 He).
  Qed.

  Lemma ssa_single_assignment_cons1 i p :
    ssa_single_assignment (i::p) ->
    (ssa_vars_unchanged_program (SSA.lvs_instr i) p) /\
    (ssa_single_assignment p).
  Proof.
    move=> H; apply/andP; exact: H.
  Qed.

  Lemma ssa_single_assignment_cons2 i p :
    (ssa_vars_unchanged_program (SSA.lvs_instr i) p) ->
    (ssa_single_assignment p) ->
    ssa_single_assignment (i::p).
  Proof.
    move=> Hi Hp; by rewrite /ssa_single_assignment -/ssa_single_assignment Hi Hp.
  Qed.

  Lemma ssa_single_assignment_cons i p :
    ssa_single_assignment (i::p) =
    (ssa_vars_unchanged_program (SSA.lvs_instr i) p) && (ssa_single_assignment p).
  Proof.
    case H: ((ssa_vars_unchanged_program (SSA.lvs_instr i) p) &&
             (ssa_single_assignment p)).
    - move/andP: H=> [H1 H2]. exact: ssa_single_assignment_cons2.
    - apply/negP=> Hcons. move/idP/negP: H. rewrite negb_andb. case/orP=> H.
      + move/negP: H; apply. exact: (proj1 (ssa_single_assignment_cons1 Hcons)).
      + move/negP: H; apply. exact: (proj2 (ssa_single_assignment_cons1 Hcons)).
  Qed.

  Lemma ssa_single_assignment_cat1 p1 p2 :
    ssa_single_assignment (p1 ++ p2) ->
    ssa_single_assignment p1 /\ ssa_single_assignment p2 /\
    (ssa_vars_unchanged_program (SSA.lvs_program p1) p2).
  Proof.
    elim: p1 => /=.
    - move=> Hp2; repeat split. exact: Hp2.
    - move=> i p1 IH /andP [Hun12 Hssa12].
      move: (IH Hssa12) => [Hssa1 [Hssa2 Hun2]] => {Hssa12 IH}. repeat split.
      + by rewrite (proj1 (ssa_unchanged_program_cat1 Hun12)) Hssa1.
      + exact: Hssa2.
      + apply: ssa_unchanged_program_union2.
        * exact: (proj2 (ssa_unchanged_program_cat1 Hun12)).
        * exact: Hun2.
  Qed.

  Lemma ssa_single_assignment_cat2 p1 p2 :
    ssa_single_assignment p1 -> ssa_single_assignment p2 ->
    (ssa_vars_unchanged_program (SSA.lvs_program p1) p2) ->
    ssa_single_assignment (p1 ++ p2).
  Proof.
    elim: p1 => /=.
    - move=> _ Hssa2 _. exact: Hssa2.
    - move=> i p1 IH /andP [Hun1 Hssa1] Hssa2 Hun12.
      apply/andP; split.
      + apply: ssa_unchanged_program_cat2.
        * exact: Hun1.
        * apply: (ssa_unchanged_program_subset Hun12).
          apply: SSA.VSLemmas.subset_union1. exact: SSA.VSLemmas.subset_refl.
      + apply: (IH Hssa1 Hssa2). apply: (ssa_unchanged_program_subset Hun12).
        apply: SSA.VSLemmas.subset_union2. exact: SSA.VSLemmas.subset_refl.
  Qed.

  Lemma ssa_single_assignment_cat p1 p2 :
    ssa_single_assignment (p1 ++ p2) =
    (ssa_single_assignment p1 && ssa_single_assignment p2 &&
     (ssa_vars_unchanged_program (SSA.lvs_program p1) p2)).
  Proof.
    case H: (ssa_single_assignment p1 && ssa_single_assignment p2 &&
             ssa_vars_unchanged_program (SSA.lvs_program p1) p2).
    - move/andP: H=> [/andP [H1 H2] H3]. by apply: ssa_single_assignment_cat2.
    - apply/negP=> Hcat. move/idP/negP: H.
      by move: (ssa_single_assignment_cat1 Hcat) => [-> [-> ->]].
  Qed.

  Lemma ssa_single_assignment_rng_program p :
    ssa_single_assignment p -> ssa_single_assignment (SSA.rng_program p).
  Proof.
    elim: p => [| i p IH] Hssa //=. rewrite ssa_single_assignment_cons in Hssa.
    move/andP: Hssa => [Hun Hssa]. rewrite (IH Hssa) andbT.
    rewrite -ssa_vars_unchanged_rng_program in Hun.
    apply : (ssa_unchanged_program_subset Hun).
    exact: SSA.rng_lvs_instr_subset.
  Qed.


  Lemma ssa_unchanged_instr_succ_typenv_submap E i :
    ssa_vars_unchanged_instr (SSA.vars_env E) i ->
    SSA.TELemmas.submap E (SSA.instr_succ_typenv i E).
  Proof.
    (case: i => //=; intros);
      repeat
        (match goal with
         | H : is_true (ssa_vars_unchanged_instr _ _) |- _ =>
           rewrite ssa_unchanged_instr_disjoint_lvs /= in H
         | H : is_true (SSA.VSLemmas.disjoint _ (SSAVS.singleton _)) |- _ =>
           rewrite SSA.VSLemmas.disjoint_singleton in H
         | H : is_true (SSA.VSLemmas.disjoint _ (SSAVS.add _ _)) |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           rewrite SSA.VSLemmas.disjoint_add in H; move/andP: H => [H1 H2]
         | H : context c [SSAVS.mem _ (SSA.vars_env _)] |- _ =>
           rewrite -SSA.vars_env_mem in H
         | H : is_true (~~ SSATE.mem _ _) |- _ =>
           let H1 := fresh in
           move: (SSA.TELemmas.not_mem_find_none H) => {H} H1
         | H : SSATE.find ?v ?E = None |-
           SSA.TELemmas.submap ?E (SSATE.add ?v _ _) =>
           apply: (SSA.TELemmas.submap_none_add _ _ H)
         | |- SSA.TELemmas.submap ?E ?E =>
           exact: SSA.TELemmas.submap_refl
         end
        ).
  Qed.

  Lemma ssa_unchanged_program_succ_typenv_submap E p :
    ssa_vars_unchanged_program (SSA.vars_env E) p ->
    ssa_single_assignment p ->
    SSA.TELemmas.submap E (SSA.program_succ_typenv p E).
  Proof.
    elim: p E => [| i p IH] E Hunch Hssa /=.
    - exact: SSA.TELemmas.submap_refl.
    - rewrite ssa_unchanged_program_cons in Hunch. move/andP: Hunch => [Hi Hp].
      move: (ssa_single_assignment_cons1 Hssa) => [Hssa_i Hssa_p].
      apply: (@SSA.TELemmas.submap_trans _ (SSA.instr_succ_typenv i E)).
      + apply: ssa_unchanged_instr_succ_typenv_submap. exact: Hi.
      + apply: (IH _ _ Hssa_p). move: (SSA.vars_env_instr_succ_typenv i E) => Heq.
        move: (SSAVS.Lemmas.P.equal_sym Heq) => {Heq} Heq.
        apply: (ssa_unchanged_program_replace Heq).
        rewrite ssa_unchanged_program_union Hp Hssa_i. done.
  Qed.


  Lemma well_formed_ssa_empty E : well_formed_ssa_program E [::].
  Proof.
    apply/andP; split=> //=. exact: ssa_unchanged_program_empty.
  Qed.

  Lemma well_formed_ssa_vars_unchanged_hd te hd tl :
    well_formed_ssa_program te (hd::tl) ->
    ssa_vars_unchanged_program (SSA.vars_instr hd) tl.
  Proof.
    move => /andP [/andP [Hwf Huc] Hssa].
    apply: (@ssa_unchanged_program_replace
              (SSAVS.union (SSA.lvs_instr hd) (SSA.rvs_instr hd))).
    - rewrite -SSA.vars_instr_split.
      reflexivity.
    - apply: ssa_unchanged_program_union2.
      + move/andP: Hssa => [Hssa1 Hssa2].
        exact: Hssa1.
      + apply: (@ssa_unchanged_program_subset _ (SSA.vars_env te)).
        * exact: (ssa_unchanged_program_tl Huc).
          apply SSA.well_formed_instr_subset_rvs.
          exact: (SSA.well_formed_program_cons1 Hwf).
  Qed.

  Lemma well_formed_ssa_well_formed E p :
    well_formed_ssa_program E p -> SSA.well_formed_program E p.
  Proof.
    move/andP=> [/andP [H1 H2] H3]. assumption.
  Qed.

  Lemma well_formed_ssa_unchanged E p :
    well_formed_ssa_program E p -> ssa_vars_unchanged_program (SSA.vars_env E) p.
  Proof.
    move/andP=> [/andP [H1 H2] H3]. assumption.
  Qed.

  Lemma well_formed_ssa_single_assignment E p :
    well_formed_ssa_program E p -> ssa_single_assignment p.
  Proof.
    move/andP=> [/andP [H1 H2] H3]. assumption.
  Qed.

  Lemma well_formed_ssa_hd E hd tl :
    well_formed_ssa_program E (hd::tl) -> SSA.well_formed_instr E hd.
  Proof.
    move/andP=> [/andP [H _] _]. rewrite SSA.well_formed_program_cons in H.
    by move/andP: H => [-> _].
  Qed.

  Lemma well_formed_ssa_tl te hd tl :
    well_formed_ssa_program te (hd::tl) ->
    well_formed_ssa_program (SSA.instr_succ_typenv hd te) tl.
  Proof.
    move=> Hwfssa.
    move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
    apply/andP; split; first (apply/andP; split).
    - exact: (SSA.well_formed_program_cons2 Hwf).
    - rewrite /ssa_vars_unchanged_program.
      apply (SSAVS.for_all_1 (ssa_unchanged_program_var_compat tl)).
      move=> x.
      rewrite SSA.vars_env_instr_succ_typenv.
      move=> Hin.
      move: (ssa_unchanged_program_tl Huc) => H1.
      move/andP: Hssa => [H2 _].
      move: (ssa_unchanged_program_union2 H1 H2) => H3.
      move: (SSAVS.for_all_2 (ssa_unchanged_program_var_compat tl) H3) => H4.
      exact: (H4 _ Hin).
    - move/andP: Hssa => [_ H].
      exact: H.
  Qed.

  Lemma well_formed_instr_rvs_unchanged_instr te i i' :
    SSA.well_formed_instr te i -> ssa_vars_unchanged_instr (SSA.vars_env te) i' ->
    ssa_vars_unchanged_instr (SSA.rvs_instr i) i'.
  Proof.
    move=> Hwell Hun. apply: (ssa_unchanged_instr_subset Hun).
    exact: SSA.well_formed_instr_subset_rvs.
  Qed.

  Lemma well_formed_instr_rvs_unchanged_program te i p :
    SSA.well_formed_instr te i -> ssa_vars_unchanged_program (SSA.vars_env te) p ->
    ssa_vars_unchanged_program (SSA.rvs_instr i) p.
  Proof.
    move=> Hwell Hun. apply: (ssa_unchanged_program_subset Hun).
    exact: SSA.well_formed_instr_subset_rvs.
  Qed.

  Corollary well_formed_ssa_spec_program s :
    well_formed_ssa_spec s ->
    well_formed_ssa_program (SSA.sinputs s) (SSA.sprog s).
  Proof.
    move=> /andP [/andP [/andP [/andP [/andP Hpre Hwell] Hprog] Hvs] Hssa].
      by rewrite /well_formed_ssa_program Hwell Hvs Hssa.
  Qed.

  Corollary well_formed_ssa_spec_pre_unchanged s :
    well_formed_ssa_spec s ->
    ssa_vars_unchanged_program (SSA.vars_bexp (SSA.spre s)) (SSA.sprog s).
  Proof.
    move=> /andP [/andP [/andP [/andP [/andP [Hwd Hwt] Hp] Hg] Hun] Hssa].
    eapply ssa_unchanged_program_subset.
    - exact: Hun.
    - by rewrite -SSA.are_defined_subset_env.
  Qed.

  Corollary well_formed_ssa_spec_post_subset s :
    well_formed_ssa_spec s ->
    SSAVS.subset (SSA.vars_bexp (SSA.spost s))
                 (SSA.vars_env (SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s))).
  Proof.
    move=> /andP [/andP [/andP [/andP [ /andP [Hwd Hwt] Hp] /andP [Hwd2 Hwt2]] Hun] Hssa].
      by rewrite -SSA.are_defined_subset_env.
  Qed.

  Ltac le_ssa_var_unchanged_instr :=
    match goal with
    | H : ssa_instr _ _ = (_, _) |- _ =>
      case: H; move=> _ <-; le_ssa_var_unchanged_instr
    | |- is_true (ssa_var_unchanged_instr (?v, ?iv) ?i) =>
      rewrite /ssa_var_unchanged_instr /=; le_ssa_var_unchanged_instr
    | H : is_true (?iv <=? get_index ?v ?m)
      |- is_true (~~ SSAVS.mem (?v, ?iv) (SSAVS.singleton (ssa_var (upd_index ?x ?m) ?x))) =>
      let Hmem := fresh in
      let Heq := fresh in
      let Hv := fresh in
      let Hi := fresh in
      apply/negP => /= Hmem;
                    move: (SSA.VSLemmas.mem_singleton1 Hmem) => {Hmem} Heq;
                                                                move/eqP: Heq => [Hv Hi];
                                                                                 rewrite Hv Hi in H;
                                                                                 exact: (get_upd_index_leF H)
    | H : is_true (?iv <=? get_index ?v ?m)
      |- is_true (~~ SSAVS.mem (?v, ?iv)
                     (SSAVS.add
                        (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1)
                        (SSAVS.singleton (ssa_var (upd_index ?v2 ?m) ?v2)))) =>
      let Hmem := fresh in
      let Hv := fresh in
      let Hi := fresh in
      apply/negP => /= Hmem;
                    move: (SSA.VSLemmas.mem_add1 Hmem); case => {Hmem} Hmem;
                                                                [ move/eqP: Hmem => [Hv Hi]; rewrite Hv Hi in H;
                                                                                    apply: (@get_upd_index_leF (upd_index v2 m) v1);
                                                                                    apply: (Nleq_trans H); exact: get_upd_index_le
                                                                |
                                                                move: (SSA.VSLemmas.mem_singleton1 Hmem) => {Hmem} Hmem;
                                                                                                            move/eqP: Hmem => [Hv Hi]; rewrite Hv Hi in H;
                                                                                                                              exact: (@get_upd_index_leF m v2)
                                                                ]
    | |- _ => idtac
    end.

  Lemma ssa_instr_le_unchanged m1 m2 i si :
    forall v iv,
      iv <=? get_index v m1 ->
      ssa_instr m1 i = (m2, si) ->
      ssa_var_unchanged_instr (v, iv) si.
  Proof.
    elim: i m1 m2 si; intros; by le_ssa_var_unchanged_instr.
  Qed.

  Lemma ssa_program_le_unchanged m1 m2 p sp :
    forall v i,
      i <=? get_index v m1 ->
      ssa_program m1 p = (m2, sp) ->
      ssa_var_unchanged_program (v, i) sp.
  Proof.
    elim: p m1 m2 sp.
    - move=> m1 m2 sp v i Hi /= [Hm Hp].
        by rewrite -Hp.
    - move=> hd tl IH m1 m2 sp v i Hle Hsp.
      move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
      rewrite Hsp => {Hsp sp} /=.
      apply/andP; split.
      + exact: (ssa_instr_le_unchanged Hle Hshd).
      + move: (ssa_instr_index_le v Hshd) => Hle2.
        move: (Nleq_trans Hle Hle2) => {Hle Hle2} Hle.
        exact: (IH _ _ _ _ _ Hle Hstl).
  Qed.

  Ltac ssa_lv_hd_unchanged_tl :=
    match goal with
    | Hstl : ssa_program ?m3 ?tl = (?m2, ?stl),
             H : ssa_instr ?m1 ?hd = (?m3, ?shd)
      |- _ =>
      move: Hstl; case: H => <- <- /= Hstl; ssa_lv_hd_unchanged_tl
    | Hstl : ssa_program (upd_index ?v ?m1) ?tl = (?m2, ?stl)
      |- is_true (ssa_vars_unchanged_program
                    (SSAVS.singleton (ssa_var (upd_index ?v ?m1) ?v)) ?stl) =>
      apply: ssa_unchanged_program_singleton2;
      apply: (ssa_program_le_unchanged _ Hstl);
      exact: Nleqnn
    | Hstl : ssa_program (upd_index ?v1 (upd_index ?v2 ?m1)) ?tl = (?m2, ?stl)
      |- is_true (ssa_vars_unchanged_program
                    (SSAVS.add
                       (ssa_var (upd_index ?v1 (upd_index ?v2 ?m1)) ?v1)
                       (SSAVS.singleton
                          (ssa_var (upd_index ?v2 ?m1) ?v2))) ?stl) =>
      apply: ssa_unchanged_program_add2; split;
      [ apply: (ssa_program_le_unchanged _ Hstl);
        exact: Nleqnn
      | apply ssa_unchanged_program_singleton2;
        apply: (ssa_program_le_unchanged _ Hstl);
        exact: get_upd_index_le ]
    | |- _ => idtac
    end.

  Theorem ssa_program_single_assignment m1 m2 p sp :
    ssa_program m1 p = (m2, sp) ->
    ssa_single_assignment sp.
  Proof.
    elim: p m1 m2 sp.
    - move=> m1 m2 sp [] _ <-.
      done.
    - move=> hd tl IH m1 m2 sp Hsp.
      move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl ->]]]]].
      apply/andP; split.
      + case: hd Hshd; intros; by ssa_lv_hd_unchanged_tl.
      + exact: (IH _ _ _ Hstl).
  Qed.

  Lemma ssa_vars_are_defined_singleton m te t:
    DSL.are_defined (VS.singleton t) te <->
    SSA.are_defined (SSAVS.singleton (ssa_var m t)) (ssa_typenv m te).
  Proof.
    rewrite /DSL.are_defined /SSA.are_defined /=; split; move=> H.
    - rewrite (SSAVS.for_all_1 (SSA.are_defined_compat (ssa_typenv m te))).
      + done.
      + move: (VS.for_all_2 (DSL.are_defined_compat te) H) => {H} H.
        intros x Hin.
        move: (Hin) => Heq.
        rewrite -> SSA.VSLemmas.singleton_iff in Heq.
        rewrite - Heq.
        move: (DSL.VSLemmas.P.Dec.FSetDecideTestCases.test_In_singleton t) => Hsingle.
        move: (H t Hsingle) => Ht.
        move/idP: Ht => Ht.
        apply/idP.
        rewrite /SSA.is_defined.
        rewrite -ssa_typenv_mem.
        exact: Ht.
    - rewrite (VS.for_all_1 (DSL.are_defined_compat te)).
      + done.
      + move: (SSAVS.for_all_2 (SSA.are_defined_compat (ssa_typenv m te)) H) => {H} H.
        intros x Hin.
        move: (Hin) => Heq.
        rewrite -> DSL.VSLemmas.singleton_iff in Heq.
        rewrite - Heq.
        move: (SSA.VSLemmas.P.Dec.FSetDecideTestCases.test_In_singleton (ssa_var m t)) => Hsingle.
        move: (H _ Hsingle) => Ht.
        move/idP: Ht => Ht.
        apply/idP.
        rewrite /DSL.is_defined.
        rewrite (ssa_typenv_mem m).
        exact: Ht.
  Qed.

  Lemma ssa_vars_are_defined_atomic m a te:
    DSL.are_defined (DSL.vars_atomic a) te <->
    SSA.are_defined (SSA.vars_atomic (ssa_atomic m a)) (ssa_typenv m te).
  Proof.
    split.
    - elim: a m te; rewrite /=; intros.
      + by rewrite -> (ssa_vars_are_defined_singleton m) in H.
      + done.
    - elim: a m te; rewrite /=; intros.
      + by rewrite <- (ssa_vars_are_defined_singleton) in H.
      + done.
  Qed.

  Lemma ssa_vars_are_defined_eexp m e te:
    DSL.are_defined (DSL.vars_eexp e) te <->
    SSA.are_defined (SSA.vars_eexp (ssa_eexp m e)) (ssa_typenv m te).
  Proof.
    split; elim: e m te; intros; rewrite /= in H *.
    - by rewrite -> (ssa_vars_are_defined_singleton m) in H.
    - done.
    - apply H. by rewrite /= in H0.
    - rewrite /= DSL.are_defined_union in H1.
      move/andP: H1 => [H1_1 H1_2].
      rewrite SSA.are_defined_union. apply/andP; split.
      + exact: (H _ _ H1_1).
      + exact: (H0 _ _ H1_2).
    - by rewrite <- (ssa_vars_are_defined_singleton) in H.
    - done.
    - apply H with m. by rewrite /= in H0.
    - rewrite /= SSA.are_defined_union in H1.
      move/andP: H1 => [H1_1 H1_2].
      rewrite DSL.are_defined_union. apply/andP; split.
      + exact: (H _ _ H1_1).
      + exact: (H0 _ _ H1_2).
  Qed.

  Lemma ssa_vars_are_defined_rexp m r te:
    DSL.are_defined (DSL.vars_rexp r) te <->
    SSA.are_defined (SSA.vars_rexp (ssa_rexp m r)) (ssa_typenv m te).
  Proof.
    split; elim: r m te; intros; rewrite /= in H *.
    - by rewrite -> (ssa_vars_are_defined_singleton m) in H.
    - done.
    - apply H. by rewrite /= in H0.
    - rewrite /= DSL.are_defined_union in H1.
      move/andP: H1 => [H1_1 H1_2].
      rewrite SSA.are_defined_union. apply/andP; split.
      + exact: (H _ _ H1_1).
      + exact: (H0 _ _ H1_2).
    - apply H. by rewrite /= in H0.
    - apply H. by rewrite /= in H0.
    - by rewrite <- (ssa_vars_are_defined_singleton) in H.
    - done.
    - apply H with m. by rewrite /= in H0.
    - rewrite /= SSA.are_defined_union in H1.
      move/andP: H1 => [H1_1 H1_2].
      rewrite DSL.are_defined_union. apply/andP; split.
      + exact: (H _ _ H1_1).
      + exact: (H0 _ _ H1_2).
    - apply H with m. by rewrite /= in H0.
    - apply H with m. by rewrite /= in H0.
  Qed.

  Lemma ssa_vars_are_defined_ebexp m e te:
    DSL.are_defined (DSL.vars_ebexp e) te <->
    SSA.are_defined (SSA.vars_ebexp (ssa_ebexp m e)) (ssa_typenv m te).
  Proof.
    split; elim: e m te; intros; rewrite /= in H *.
    - done.
    - rewrite DSL.are_defined_union in H; move/andP: H => [He He0].
      rewrite SSA.are_defined_union; apply/andP; split; by apply ssa_vars_are_defined_eexp.
    - rewrite DSL.are_defined_union in H; move/andP: H => [He H].
      rewrite DSL.are_defined_union in H; move/andP: H => [He0 He1].
      rewrite SSA.are_defined_union; apply/andP; split; first by apply ssa_vars_are_defined_eexp.
      rewrite SSA.are_defined_union; apply/andP; split; by apply ssa_vars_are_defined_eexp.
    - rewrite SSA.are_defined_union; apply/andP; rewrite /= in H1;
        rewrite DSL.are_defined_union in H1; move/andP: H1 => [H1_1 H1_2]; split; by [apply H|apply H0].
    - done.
    - rewrite SSA.are_defined_union in H; move/andP: H => [He He0].
      rewrite DSL.are_defined_union; apply/andP; split; by apply (ssa_vars_are_defined_eexp m).
    - rewrite SSA.are_defined_union in H; move/andP: H => [He H].
      rewrite SSA.are_defined_union in H; move/andP: H => [He0 He1].
      rewrite DSL.are_defined_union; apply/andP; split; first by apply (ssa_vars_are_defined_eexp m).
      rewrite DSL.are_defined_union; apply/andP; split; by apply (ssa_vars_are_defined_eexp m).
    - rewrite DSL.are_defined_union; apply/andP; rewrite /= in H1;
        rewrite SSA.are_defined_union in H1; move/andP: H1 => [H1_1 H1_2]; split; by [apply (H m) |apply (H0 m)].
  Qed.

  Lemma ssa_vars_are_defined_rbexp m r te:
    DSL.are_defined (DSL.vars_rbexp r) te <->
    SSA.are_defined (SSA.vars_rbexp (ssa_rbexp m r)) (ssa_typenv m te).
  Proof.
    split; elim: r m te; intros; rewrite /= in H *.
    - done.
    - rewrite DSL.are_defined_union in H; move/andP: H => [He He0].
      rewrite SSA.are_defined_union; apply/andP; split; by apply ssa_vars_are_defined_rexp.
    - rewrite DSL.are_defined_union in H; move/andP: H => [He H].
      rewrite SSA.are_defined_union; apply/andP; split; by apply ssa_vars_are_defined_rexp.
    - apply H; rewrite /= in H0; done.
    - rewrite SSA.are_defined_union; apply/andP; rewrite /= in H1;
        rewrite DSL.are_defined_union in H1; move/andP: H1 => [H1_1 H1_2]; split; by [apply H|apply H0].
    - rewrite SSA.are_defined_union; apply/andP; rewrite /= in H1;
        rewrite DSL.are_defined_union in H1; move/andP: H1 => [H1_1 H1_2]; split; by [apply H|apply H0].
    - done.
    - rewrite SSA.are_defined_union in H; move/andP: H => [He He0].
      rewrite DSL.are_defined_union; apply/andP; split; by apply (ssa_vars_are_defined_rexp m).
    - rewrite SSA.are_defined_union in H; move/andP: H => [He H].
      rewrite DSL.are_defined_union; apply/andP; split; by apply (ssa_vars_are_defined_rexp m).
    - apply (H m); rewrite /= in H0; done.
    - rewrite DSL.are_defined_union; apply/andP; rewrite /= in H1;
        rewrite SSA.are_defined_union in H1; move/andP: H1 => [H1_1 H1_2]; split; by [apply (H m)|apply (H0 m)].
    - rewrite DSL.are_defined_union; apply/andP; rewrite /= in H1;
        rewrite SSA.are_defined_union in H1; move/andP: H1 => [H1_1 H1_2]; split; by [apply (H m)|apply (H0 m)].
  Qed.

  Lemma ssa_vars_are_defined_bexp m b te:
    DSL.are_defined (DSL.vars_bexp b) te <->
    SSA.are_defined (SSA.vars_bexp (ssa_bexp m b)) (ssa_typenv m te).
  Proof.
    elim: b m te; split; intros.
    - rewrite /DSL.vars_bexp /= in H.
      rewrite DSL.are_defined_union in H; move/andP: H => [He Hr].
      rewrite /SSA.vars_bexp /=.
      rewrite SSA.are_defined_union; apply/andP; split.
      + by apply ssa_vars_are_defined_ebexp.
      + by apply ssa_vars_are_defined_rbexp.
    - rewrite /SSA.vars_bexp /= in H.
      rewrite SSA.are_defined_union in H; move/andP: H => [He Hr].
      rewrite /DSL.vars_bexp /=.
      rewrite DSL.are_defined_union; apply/andP; split.
      + by apply (ssa_vars_are_defined_ebexp m).
      + by apply (ssa_vars_are_defined_rbexp m).
  Qed.

  Lemma ssa_instr_well_defined te m1 m2 i si :
    DSL.well_formed_instr te i ->
    ssa_instr m1 i = (m2, si) ->
    SSA.well_defined_instr (ssa_typenv m1 te) si.
  Proof.
    rewrite /DSL.well_formed_instr.
    rewrite /DSL.well_defined_instr /SSA.well_defined_instr.
    case: i => /=; intros;
                 (let rec tac :=
                      match goal with
                      | H : (_, _) = (_, _) |- _ => case: H => _ <- /=; tac
                      | H : is_true (_ && _) |- _ =>
                        let H1 := fresh in
                        let H2 := fresh in
                        move/andP: H => [H1 H2]; tac
                      | |- is_true (_ && _) => apply/andP; split; tac
                      | H : is_true (VS.subset (DSL.vars_atomic ?a) ?vs)
                        |- is_true (SSAVS.subset
                                      (SSA.vars_atomic (ssa_atomic ?m ?a))
                                      (ssa_vars ?m ?vs)) =>
                        rewrite ssa_vars_atomic_subset; assumption
                      | H : is_true (?v1 != ?v2)
                        |- is_true (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1 !=
                                            ssa_var (upd_index ?v2 ?m) ?v2) =>
                        exact: (pair_neq1 _ _ H)
                      | H : is_true (VS.mem ?v ?vs) |-
                        is_true (SSAVS.mem (ssa_var ?m ?v) (ssa_vars ?m ?vs)) =>
                        rewrite ssa_vars_mem1; exact: H
                      | H: is_true (DSL.are_defined (DSL.vars_atomic ?a) ?te)
                        |- is_true (SSA.are_defined (SSA.vars_atomic (ssa_atomic ?m ?a))
                                                    (ssa_typenv ?m ?te)) => rewrite -ssa_vars_are_defined_atomic; exact: H
                      | |- is_true(true) => done
                      | |- ?e => progress (auto)
                      | |- ?e => idtac
                      end in tac) .
      by apply ssa_vars_are_defined_bexp.
  Qed.


  Lemma ssa_well_typed_eexp m te e:
    DSL.well_typed_eexp te e <->
    SSA.well_typed_eexp (ssa_typenv m te) (ssa_eexp m e).
  Proof.
    split; elim: e m te; intros; rewrite /=.
    - done.
    - done.
    - apply H. by rewrite /= in H0.
    - rewrite /= in H1.
      move/andP: H1 => [H1_1 H1_2].
      apply/andP; split; by [apply H | apply H0].
    - done.
    - done.
    - apply (H m). by rewrite /= in H0.
    - rewrite /= in H1.
      move/andP: H1 => [H1_1 H1_2].
      apply/andP; split; by [ apply (H m) | apply (H0 m)].
  Qed.

  Lemma ssa_typenv_size_rexp m te r:
    DSL.size_of_rexp r te = SSA.size_of_rexp (ssa_rexp m r) (ssa_typenv m te).
  Proof.
    elim: r te m; intros; rewrite /=; try reflexivity.
    exact: ssa_typenv_size.
  Qed.

  Lemma ssa_well_typed_rexp m te e:
    DSL.well_typed_rexp te e <->
    SSA.well_typed_rexp (ssa_typenv m te) (ssa_rexp m e).
  Proof.
    split; elim: e m te; intros; rewrite /=.
    - done.
    - done.
    - rewrite /= in H0.
      move/andP: H0 => [H0_1 H0_2].
      apply/andP; split.
      + by apply H.
      + by rewrite -ssa_typenv_size_rexp.
    - rewrite /= in H1.
      split_andb_hyps.
      split_andb_goal.
      + by apply H.
      + by rewrite -ssa_typenv_size_rexp.
      + by apply H0.
      + by rewrite -ssa_typenv_size_rexp.
    - rewrite /= in H0.
      split_andb_hyps; split_andb_goal.
      + by apply H.
      + by rewrite -ssa_typenv_size_rexp.
    - rewrite /= in H0.
      split_andb_hyps; split_andb_goal.
      + by apply H.
      + by rewrite -ssa_typenv_size_rexp.
    - done.
    - done.
    - rewrite /= in H0.
      move/andP: H0 => [H0_1 H0_2].
      apply/andP; split.
      + by apply (H m).
      + by rewrite (ssa_typenv_size_rexp m).
    - rewrite /= in H1.
      split_andb_hyps.
      split_andb_goal.
      + by apply (H m).
      + by rewrite (ssa_typenv_size_rexp m).
      + by apply (H0 m).
      + by rewrite (ssa_typenv_size_rexp m).
    - rewrite /= in H0.
      split_andb_hyps; split_andb_goal.
      + by apply (H m).
      + by rewrite (ssa_typenv_size_rexp m).
    - rewrite /= in H0.
      split_andb_hyps; split_andb_goal.
      + by apply (H m).
      + by rewrite (ssa_typenv_size_rexp m).
  Qed.

  Lemma ssa_well_typed_ebexp m te e:
    DSL.well_typed_ebexp te e <->
    SSA.well_typed_ebexp (ssa_typenv m te) (ssa_ebexp m e).
  Proof.
    split; elim: e m te; intros; rewrite /=; rewrite /= in H; split_andb_hyps; split_andb_goal.
    - done.
    - by apply ssa_well_typed_eexp.
    - by apply ssa_well_typed_eexp.
    - by apply ssa_well_typed_eexp.
    - by apply ssa_well_typed_eexp.
    - by apply ssa_well_typed_eexp.
    - rewrite /= in H1; split_andb_hyps; by apply H.
    - rewrite /= in H1; split_andb_hyps; by apply H0.
    - done.
    - by apply (ssa_well_typed_eexp m).
    - by apply (ssa_well_typed_eexp m).
    - by apply (ssa_well_typed_eexp m).
    - by apply (ssa_well_typed_eexp m).
    - by apply (ssa_well_typed_eexp m).
    - rewrite /= in H1; split_andb_hyps; by apply (H m).
    - rewrite /= in H1; split_andb_hyps; by apply (H0 m).
  Qed.

  Lemma ssa_well_typed_rbexp m te e:
    DSL.well_typed_rbexp te e <->
    SSA.well_typed_rbexp (ssa_typenv m te) (ssa_rbexp m e).
  Proof.
    split; elim: e m te; intros; rewrite /=; rewrite /= in H; split_andb_hyps; split_andb_goal.
    - done.
    - by apply ssa_well_typed_rexp.
    - by rewrite -ssa_typenv_size_rexp.
    - by apply ssa_well_typed_rexp.
    - by rewrite -ssa_typenv_size_rexp.
    - by apply ssa_well_typed_rexp.
    - by rewrite -ssa_typenv_size_rexp.
    - by apply ssa_well_typed_rexp.
    - by rewrite -ssa_typenv_size_rexp.
    - rewrite /= in H0; split_andb_hyps; by apply H.
    - rewrite /= in H1; split_andb_hyps; by apply H.
    - rewrite /= in H1; split_andb_hyps; by apply H0.
    - rewrite /= in H1; split_andb_hyps; by apply H.
    - rewrite /= in H1; split_andb_hyps; by apply H0.
    - done.
    - by apply (ssa_well_typed_rexp m).
    - by rewrite (ssa_typenv_size_rexp m).
    - by apply (ssa_well_typed_rexp m).
    - by rewrite (ssa_typenv_size_rexp m).
    - by apply (ssa_well_typed_rexp m).
    - by rewrite (ssa_typenv_size_rexp m).
    - by apply (ssa_well_typed_rexp m).
    - by rewrite (ssa_typenv_size_rexp m).
    - rewrite /= in H0; split_andb_hyps; by apply (H m).
    - rewrite /= in H1; split_andb_hyps; by apply (H m).
    - rewrite /= in H1; split_andb_hyps; by apply (H0 m).
    - rewrite /= in H1; split_andb_hyps; by apply (H m).
    - rewrite /= in H1; split_andb_hyps; by apply (H0 m).
  Qed.

  Lemma ssa_well_typed_bexp m te b:
    DSL.well_typed_bexp te b <->
    SSA.well_typed_bexp (ssa_typenv m te) (ssa_bexp m b).
  Proof.
    elim: b m te; split; intros.
    - rewrite /DSL.well_typed_bexp /= in H.
      rewrite /SSA.well_typed_bexp /=.
      split_andb_hyps; split_andb_goal.
      + by apply ssa_well_typed_ebexp.
      + by apply ssa_well_typed_rbexp.
    - rewrite /SSA.well_typed_bexp /= in H.
      rewrite /DSL.well_typed_bexp /=.
      split_andb_hyps; split_andb_goal.
      + by apply (ssa_well_typed_ebexp m).
      + by apply (ssa_well_typed_rbexp m).
  Qed.

  Lemma ssa_size_matched_atomic m a :
    DSL.size_matched_atomic a =
    SSA.size_matched_atomic (ssa_atomic m a).
  Proof. by case: a. Qed.

  Lemma ssa_well_sized_atomic m E a :
    DSL.well_sized_atomic E a =
    SSA.well_sized_atomic (ssa_typenv m E) (ssa_atomic m a).
  Proof.
    rewrite /DSL.well_sized_atomic /SSA.well_sized_atomic.
    rewrite -ssa_atomic_asize -ssa_atomic_atyp. reflexivity.
  Qed.

  Lemma ssa_well_typed_atomic m E a :
    DSL.well_typed_atomic E a =
    SSA.well_typed_atomic (ssa_typenv m E) (ssa_atomic m a).
  Proof.
    rewrite /DSL.well_typed_atomic /SSA.well_typed_atomic.
    rewrite -ssa_size_matched_atomic -ssa_well_sized_atomic. reflexivity.
  Qed.

  Lemma ssa_instr_well_typed te m1 m2 i si :
    DSL.well_formed_instr te i ->
    ssa_instr m1 i = (m2, si) ->
    SSA.well_typed_instr (ssa_typenv m1 te) si.
  Proof.
    rewrite /DSL.well_formed_instr /DSL.well_defined_instr
            /DSL.well_typed_instr /SSA.well_typed_instr.
    (case: i => /=; intros);
      (let rec tac :=
           match goal with
           | H : (_, _) = (_, _) |- _ => case: H => _ <- /=; tac
           | H : is_true (_ && _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             move/andP: H => [H1 H2]; tac
           | |- is_true (_ && _) => apply/andP; split; tac
           | H : is_true (VS.subset (DSL.vars_atomic ?a) ?vs)
             |- is_true (SSAVS.subset
                           (SSA.vars_atomic (ssa_atomic ?m ?a))
                           (ssa_vars ?m ?vs)) =>
             rewrite ssa_vars_atomic_subset; assumption
           | H : is_true (?v1 != ?v2)
             |- is_true (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1 !=
                                 ssa_var (upd_index ?v2 ?m) ?v2) =>
             exact: (pair_neq1 _ _ H)
           | H : is_true (VS.mem ?v ?vs) |-
             is_true (SSAVS.mem (ssa_var ?m ?v) (ssa_vars ?m ?vs)) =>
             rewrite ssa_vars_mem1; exact: H
           | |- context [SSA.atyp (ssa_atomic ?m ?a) (ssa_typenv ?m ?te)]
             => rewrite -ssa_atomic_atyp; tac
           | H: is_true (DSL.are_defined (DSL.vars_atomic ?a) ?te)
             |- is_true (SSA.are_defined (SSA.vars_atomic (ssa_atomic ?m ?a))
                                         (ssa_typenv ?m ?te)) =>
             rewrite -ssa_vars_are_defined_atomic; exact: H
           | H : is_true (?v1 != ?v2)
             |- is_true (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1 !=
                                 ssa_var (upd_index ?v2 ?m) ?v2) =>
             exact: (pair_neq1 _ _ H)
           | |- is_true (SSA.well_typed_atomic _ _) =>
             rewrite -ssa_well_typed_atomic; tac
           | |- context f [SSA.asize (ssa_atomic ?m ?a) (ssa_typenv ?m ?E)%N] =>
             rewrite -(ssa_atomic_asize m a E); tac
           | |- is_true(true) => done
           | |- ?e => progress (auto)
           | |- ?e => idtac
           end in tac) .
      by apply ssa_well_typed_bexp.
  Qed.

  Lemma ssa_instr_well_formed te m1 m2 i si :
    DSL.well_formed_instr te i ->
    ssa_instr m1 i = (m2, si) ->
    SSA.well_formed_instr (ssa_typenv m1 te) si.
  Proof.
    move=> Hwf Hsi.
    rewrite /SSA.well_formed_instr.
      by rewrite (ssa_instr_well_defined Hwf Hsi) (ssa_instr_well_typed Hwf Hsi).
  Qed.

  Lemma ssa_program_well_formed1 te m1 m2 p sp :
    DSL.well_formed_program te p ->
    ssa_program m1 p = (m2, sp) ->
    SSA.well_formed_program (ssa_typenv m1 te) sp.
  Proof.
    elim: p te m1 m2 sp.
    - move=> te m1 m2 sp.
      rewrite /=.
      move=> _.
      case=> _ <-.
      done.
    - move=> hd tl IH te m1 m2 sp.
      rewrite /=.
      move=> /andP [Hwf_hd Hwf_tl].
      case H_hd: (ssa_instr m1 hd) => [sm_hd sp_hd].
      case H_tl: (ssa_program sm_hd tl) => [sm_tl sp_tl].
      case=> Hsm <-.
      rewrite /=.
      apply/andP; split.
      + exact: (ssa_instr_well_formed Hwf_hd H_hd).
      + move: (IH _ _ _ _ Hwf_tl H_tl) => HIH.
        move: (@ssa_instr_succ_typenv_submap _ _ _ _ te H_hd) => Hsub.
        exact: (SSA.well_formed_program_submap HIH Hsub).
  Qed.

  Lemma ssa_typenv_mem_index m te v i:
    SSAVS.mem (v, i) (SSA.vars_env (ssa_typenv m te)) ->
    i = get_index v m.
  Proof.
    rewrite ssa_vars_env_comm.
    move=> Hmem.
    move: (ssa_vars_mem2 Hmem) => {Hmem} Hmem.
    destruct Hmem.
    inversion H.
    rewrite /ssa_var /= in H0.
      by case: H0 => -> ->.
  Qed.

  Lemma ssa_typenv_mem_le v i m te:
    SSAVS.mem (v, i) (SSA.vars_env (ssa_typenv m te)) ->
    i <=? get_index v m.
  Proof.
    move=> Hmem.
    move: (ssa_typenv_mem_index Hmem) => Hidx.
      by rewrite Hidx Nleqnn.
  Qed.

  Theorem ssa_program_well_formed te m1 m2 p sp :
    DSL.well_formed_program te p ->
    ssa_program m1 p = (m2, sp) ->
    well_formed_ssa_program (ssa_typenv m1 te) sp.
  Proof.
    move=> Hwf Hsp.
    rewrite /well_formed_ssa_program.
    apply/andP. split.
    apply/andP. split.
    - exact: (ssa_program_well_formed1 Hwf Hsp).
    - apply: ssa_unchanged_program_global => v Hmem.
      destruct v as [v i].
      apply: (ssa_program_le_unchanged _ Hsp).
      exact: (ssa_typenv_mem_le Hmem).
    - exact: (ssa_program_single_assignment Hsp).
  Qed.

  Lemma ssa_singleton_var_index m t v i :
    SSAVS.mem (v, i) (SSAVS.singleton (ssa_var m t)) ->
    get_index v m = i.
  Proof.
    move=> Hmem.
    move: (SSA.VSLemmas.mem_singleton1 Hmem) => /eqP [] <- <-.
    reflexivity.
  Qed.

  Lemma ssa_atomic_var_index m a v i :
    SSAVS.mem (v, i) (SSA.vars_atomic (ssa_atomic m a)) ->
    get_index v m = i.
  Proof.
    case: a => /=.
    - move=> x. exact: ssa_singleton_var_index.
    - move=> _ _ H.
      rewrite SSA.VSLemmas.mem_empty in H.
      discriminate.
  Qed.

  Lemma ssa_eexp_var_index m (e : DSL.eexp) v i :
    SSAVS.mem (v, i) (SSA.vars_eexp (ssa_eexp m e)) ->
    get_index v m = i.
  Proof.
    elim: e m v i => /=.
    - move=> a m x i Hmem. exact: (ssa_singleton_var_index Hmem).
    - move=> c m v i H. rewrite SSA.VSLemmas.mem_empty in H. discriminate.
    - move=> op e IH m v i Hmem. exact: IH.
    - move=> op e1 IH1 e2 IH2 m v i Hmem.
      case: (SSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
      + exact: IH1.
      + exact: IH2.
  Qed.

  Lemma ssa_rexp_var_index m (e : DSL.rexp) v i :
    SSAVS.mem (v, i) (SSA.vars_rexp (ssa_rexp m e)) ->
    get_index v m = i.
  Proof.
    elim: e m v i => /=.
    - move=> a m x i Hmem. exact: (ssa_singleton_var_index Hmem).
    - move=> w c m v i H. rewrite SSA.VSLemmas.mem_empty in H. discriminate.
    - move=> w1 op e1 IH1 m v i Hmem. exact: IH1.
    - move=> w op e1 IH1 e2 IH2 m v i Hmem.
      case: (SSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
      + exact: IH1.
      + exact: IH2.
    - move=> w e IH p m v i Hmem. exact: IH.
    - move=> w e IH p m v i Hmem. exact: IH.
  Qed.

  Lemma ssa_ebexp_var_index m e v i :
    SSAVS.mem (v, i) (SSA.vars_ebexp (ssa_ebexp m e)) ->
    get_index v m = i.
  Proof.
    elim: e m v i => /=.
    - move=> m v i Hmem.
      discriminate.
    - move=> e1 e2 m v i Hmem.
      rewrite SSA.VSLemmas.union_b in Hmem.
      move/orP: Hmem; case=> Hmem;
                               apply: (ssa_eexp_var_index Hmem); reflexivity.
    - move=> e1 e2 p m v i Hmem.
      rewrite !SSA.VSLemmas.union_b in Hmem.
      repeat (move/orP: Hmem; case=> Hmem);
        exact: (ssa_eexp_var_index Hmem).
    - move=> e1 IH1 e2 IH2 m v i Hmem.
      rewrite SSA.VSLemmas.union_b in Hmem.
      move/orP: Hmem; case=> Hmem.
      + exact: IH1.
      + exact: IH2.
  Qed.

  Lemma ssa_rbexp_var_index m e v i :
    SSAVS.mem (v, i) (SSA.vars_rbexp (ssa_rbexp m e)) ->
    get_index v m = i.
  Proof.
    elim: e m v i => /=.
    - move=> m v i Hmem.
      discriminate.
    - move=> w e1 e2 m v i Hmem.
      rewrite SSA.VSLemmas.union_b in Hmem.
      move/orP: Hmem; case=> Hmem;
                               apply: (ssa_rexp_var_index Hmem); reflexivity.
    - move=> w op e1 e2 m v i Hmem.
      rewrite SSA.VSLemmas.union_b in Hmem.
      move/orP: Hmem; case=> Hmem;
                               apply: (ssa_rexp_var_index Hmem); reflexivity.
    - move=> e IH m v i Hmem.
      exact: IH.
    - move=> e1 IH1 e2 IH2 m v i Hmem.
      rewrite SSA.VSLemmas.union_b in Hmem.
      move/orP: Hmem; case=> Hmem.
      + exact: IH1.
      + exact: IH2.
    - move=> e1 IH1 e2 IH2 m v i Hmem.
      rewrite SSA.VSLemmas.union_b in Hmem.
      move/orP: Hmem; case=> Hmem.
      + exact: IH1.
      + exact: IH2.
  Qed.

  Lemma ssa_bexp_var_index m e v i :
    SSAVS.mem (v, i) (SSA.vars_bexp (ssa_bexp m e)) ->
    get_index v m = i.
  Proof.
    move=> Hmem. case: (SSA.VSLemmas.mem_union1 Hmem) => {Hmem} Hmem.
    - exact: (ssa_ebexp_var_index Hmem).
    - exact: (ssa_rbexp_var_index Hmem).
  Qed.

  Lemma ssa_spec_in_pre_unchanged s v :
    SSAVS.mem v (SSA.vars_bexp (SSA.spre (ssa_spec s))) ->
    ssa_var_unchanged_program v (SSA.sprog (ssa_spec s)).
  Proof.
    move: (ssa_spec_unfold s) => [m [Hinputs [Hpre [Hprog Hpost]]]].
    move=> Hmem.
    rewrite Hpre in Hmem.
    destruct v as [v i].
    move: (ssa_bexp_var_index Hmem) => Hidx.
    apply: (ssa_program_le_unchanged (m1:=empty_vmap)).
    - rewrite Hidx.
      exact: Nleqnn.
    - symmetry; exact: Hprog.
  Qed.

  Lemma ssa_spec_unchanged_pre s :
    ssa_vars_unchanged_program (SSA.vars_bexp (SSA.spre (ssa_spec s))) (SSA.sprog (ssa_spec s)).
  Proof.
    move: (ssa_spec_unfold s) => [m [Hinput [Hpre [Hprog Hpost]]]].
    destruct s as [f p g]; rewrite /= in Hpre Hprog Hpost *.
    apply: ssa_unchanged_program_global => v Hmem.
    exact: ssa_spec_in_pre_unchanged.
  Qed.

  Lemma ssa_spec_well_formed_sub1 s:
    DSL.well_formed_bexp (DSL.sinputs s) (DSL.spre s) ->
    SSA.well_formed_bexp (SSA.sinputs (ssa_spec s)) (SSA.spre (ssa_spec s)).
  Proof.
    move: (ssa_spec_unfold s) => [m [Hinput [Hpre [Hprog Hpost]]]].
    rewrite Hinput Hpre.
    move=> /andP [Hdwd Hdwt].
    apply/andP; split.
    - move/ssa_vars_are_defined_bexp: Hdwd => Hdwd.
      exact: Hdwd.
    - move/ssa_well_typed_bexp: Hdwt => Hdwt.
      exact: Hdwt.
  Qed.

  Lemma ssa_program_well_defined m1 m2 p sp e te:
    DSL.well_formed_program te p ->
    DSL.well_formed_bexp (DSL.program_succ_typenv p te) e ->
    ssa_program m1 p = (m2, sp) ->
    SSA.are_defined (SSA.vars_bexp (ssa_bexp m2 e))
                    (SSA.program_succ_typenv sp (ssa_typenv m1 te)).
  Proof.
    elim: p m1 m2 sp e te.
    - rewrite /=.
      move=> m1 m2 sp e te _ /andP [Hwd Hwt] [<- <-].
      rewrite /=.
      move/ssa_vars_are_defined_bexp: Hwd => Hwd.
      exact: Hwd.
    - move=> hd tl IH m1 m2 sp e te.
      rewrite /=.
      case Hsi_hd: (ssa_instr m1 hd) => [sm1 shd].
      case Hsp_tl: (ssa_program sm1 tl) => [sm2 stl].
      move=> /andP [Hwf_hd Hwf_tl] Hwf_bexp [<- <-].
      rewrite /=.
      move: (IH _ _ _ _ _ Hwf_tl Hwf_bexp Hsp_tl).
      apply SSA.are_defined_submap.
      apply SSA.submap_program_succ_typenv.
      move: (ssa_program_well_formed Hwf_tl Hsp_tl) => /andP [/andP [Hwell Hvs] Hsingle].
      exact: Hwell.
      exact: ssa_instr_succ_typenv_submap.
  Qed.

  Lemma ssa_program_well_typed m1 m2 p sp te e:
    DSL.well_formed_program te p ->
    DSL.well_formed_bexp (DSL.program_succ_typenv p te) e ->
    ssa_program m1 p = (m2, sp) ->
    SSA.well_typed_bexp
      (SSA.program_succ_typenv sp (ssa_typenv m1 te))
      (ssa_bexp m2 e).
  Proof.
    elim: p m1 m2 sp e te.
    - rewrite /=.
      move=> m1 m2 sp e te _ /andP [Hwd Hwt] [<- <-].
      rewrite /=.
      move/ssa_well_typed_bexp: Hwt => Hwt.
      exact: Hwt.
    - move=> hd tl IH m1 m2 sp e te.
      rewrite /=.
      case Hsi_hd: (ssa_instr m1 hd) => [sm1 shd].
      case Hsp_tl: (ssa_program sm1 tl) => [sm2 stl].
      move=> /andP [Hwf_hd Hwf_tl] Hwf_bexp [<- <-].
      rewrite /=.
      move: (IH _ _ _ _ _ Hwf_tl Hwf_bexp Hsp_tl).
      apply SSA.well_typed_bexp_submap.
      apply SSA.submap_program_succ_typenv.
      move: (ssa_program_well_formed Hwf_tl Hsp_tl) => /andP [/andP [Hwell Hvs] Hsingle].
      exact: Hwell.
      exact: ssa_instr_succ_typenv_submap.
      exact: (ssa_program_well_defined Hwf_tl Hwf_bexp Hsp_tl).
  Qed.

  Lemma ssa_spec_well_formed_sub2 s m' sp:
    DSL.well_formed_program (DSL.sinputs s) (DSL.sprog s) ->
    DSL.well_formed_bexp (DSL.program_succ_typenv (DSL.sprog s) (DSL.sinputs s)) (DSL.spost s) ->
    ssa_program empty_vmap (DSL.sprog s) = (m', sp) ->
    SSA.well_formed_bexp (SSA.program_succ_typenv (SSA.sprog (ssa_spec s))
                                                  (SSA.sinputs (ssa_spec s)))
                         (SSA.spost (ssa_spec s)).
  Proof.
    move=> Hwellprog.
    move: (ssa_spec_unfold s) => [m [Hinput [Hpre [Hprog Hpost]]]].
    move: (ssa_program_well_formed Hwellprog (Logic.eq_sym Hprog)) => /andP [/andP [Hwell Hvs] Hsingle].
    rewrite -Hprog.
    move=> Hwf.
    move=> Hsp.
    rewrite Hinput Hpost.
    apply/andP; split.
    - exact: (ssa_program_well_defined Hwellprog Hwf (Logic.eq_sym Hprog)).
    - exact: (ssa_program_well_typed Hwellprog Hwf (Logic.eq_sym Hprog)).
  Qed.

  Theorem ssa_spec_well_formed s :
    DSL.well_formed_spec s ->
    well_formed_ssa_spec (ssa_spec s).
  Proof.
    move=> /andP [/andP [Hsubpre Hwellprog] Hsubpost].
    move: (ssa_spec_unfold s) => [m [Hinput [Hpre [Hprog Hpost]]]].
    move: (ssa_program_well_formed Hwellprog (Logic.eq_sym Hprog)) => /andP [/andP [Hwell Hvs] Hsingle].
    apply/andP; split; [apply/andP; split | idtac].
    - apply/andP; split; [apply/andP; split | idtac].
      + exact: (ssa_spec_well_formed_sub1 Hsubpre).
      + rewrite Hinput. exact: Hwell.
      + exact: (ssa_spec_well_formed_sub2 Hwellprog Hsubpost (Logic.eq_sym Hprog)).
    - rewrite Hinput. assumption.
    - exact: (ssa_program_single_assignment (Logic.eq_sym Hprog)).
  Qed.

End MakeSSA.


Section SSAStoreEq.

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

  Ltac ssa_vars_unchanged_instr_to_mem :=
    match goal with
    | H : is_true (ssa_vars_unchanged_instr ?vs ?i) |- _ =>
      let Hdisj := fresh "Hdisj" in
      (have: (ssa_vars_unchanged_instr vs i) by assumption);
      (rewrite ssa_unchanged_instr_disjoint_lvs => /= Hdisj);
      repeat split_disjoint
    end.

  Ltac intro_neqs :=
    match goal with
    | H : is_true (SSATE.mem ?x ?E) |- _ =>
      move/memenvP: H => H; try intro_neqs
    | H1 : is_true (~~ SSAVS.mem ?v (vars_env ?E)),
      H2 : is_true (SSAVS.mem ?x (vars_env ?E)) |- _ =>
      let H := fresh in dcase (x == v); case;
      [move/eqP=> H; rewrite -H H2 in H1; discriminate | move/idP/negP=> H; clear H1];
      try intro_neqs
    end.

  Ltac invert_eval_instr :=
    match goal with
    | H : eval_instr _ _ _ _ |- _ => inversion_clear H
    end.

  Ltac decide_eqi :=
    match goal with
    | |- bvs_eqi ?E ?s ?s => exact: bvs_eqi_refl
    | Hmem : is_true (~~ SSAVS.mem ?v (vars_env ?E)),
      Hupd : SSAStore.Upd ?v _ ?s1 ?s2 |-
      bvs_eqi ?E ?s1 ?s2 =>
      let Hx := fresh in
      move=> x Hx; intro_neqs; rewrite (SSAStore.acc_Upd_neq _ Hupd);
             [ reflexivity | assumption ]
    | Hmemh : is_true (~~ SSAVS.mem ?vh (vars_env ?E)),
      Hmeml : is_true (~~ SSAVS.mem ?vl (vars_env ?E)),
      Hupd : SSAStore.Upd2 ?vl _ ?vh _ ?s1 ?s2 |-
      bvs_eqi ?E ?s1 ?s2 =>
      let Hx := fresh in
      move=> x Hx; intro_neqs; rewrite (SSAStore.acc_Upd2_neq _ _ Hupd);
             [ reflexivity | assumption | assumption ]
    end.

  Lemma bvs_eqi_eval_instr E i s1 s2 :
    ssa_vars_unchanged_instr (vars_env E) i -> eval_instr E i s1 s2 ->
    bvs_eqi E s1 s2.
  Proof.
    (case: i => /=);
      try (move=> *; ssa_vars_unchanged_instr_to_mem;
                  invert_eval_instr; by decide_eqi).
  Qed.

  Lemma bvs_eqi_eval_rng_instr E i s1 s2 :
    ssa_vars_unchanged_instr (vars_env E) i ->
    eval_instr E (rng_instr i) s1 s2 ->
    bvs_eqi E s1 s2.
  Proof.
    (case: i => /=);
      try (move=> *; ssa_vars_unchanged_instr_to_mem;
                  invert_eval_instr; by decide_eqi).
    case => e r /=. move=> Hun Hei. inversion_clear Hei. exact: bvs_eqi_refl.
  Qed.

  Lemma bvs_eqi_eval_program E p s1 s2 :
    ssa_vars_unchanged_program (vars_env E) p ->
    ssa_single_assignment p -> eval_program E p s1 s2 ->
    bvs_eqi E s1 s2.
  Proof.
    elim: p E s1 s2 => [| i P IH] E s1 s2 /=.
    - move=>_ _ Hev; inversion_clear Hev; exact: bvs_eqi_refl.
    - rewrite ssa_unchanged_program_cons => /andP [Hun_i Hun_p] /andP [Hssa_i Hssa_p]
                                             Hev. inversion_clear Hev.
      have Hun_succ: (ssa_vars_unchanged_program (vars_env (instr_succ_typenv i E)) P).
      { apply: (ssa_unchanged_program_replace
                  (SSAVS.Lemmas.P.equal_sym (vars_env_instr_succ_typenv i E))).
          by rewrite ssa_unchanged_program_union Hun_p Hssa_i. }
      move: (IH (instr_succ_typenv i E) t s2 Hun_succ Hssa_p H0) => Heqi_p.
      move=> x Hx. rewrite -(Heqi_p x (mem_instr_succ_typenv i Hx)).
      move: (bvs_eqi_eval_instr Hun_i H) => Heqi_i. exact: (Heqi_i x Hx).
  Qed.

End SSAStoreEq.
