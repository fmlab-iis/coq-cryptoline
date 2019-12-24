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

  (*
  Definition ssa_pws (pwss: DSL.prove_with_spec) : SSA.prove_with_spec :=
    match pwss with
    | DSL.Precondition => SSA.Precondition
    | DSL.AllCuts => SSA.AllCuts
    | DSL.AllAssumes => SSA.AllAssumes
    | DSL.AllGhosts => SSA.AllGhosts
    end.

  Definition ssa_pwss pwss := seq.map ssa_pws pwss.
   *)

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
    (* | DSL.Iaddr c v a1 a2 => *)
    (*   let a1 := ssa_atomic m a1 in *)
    (*   let a2 := ssa_atomic m a2 in *)
    (*   let mv := upd_index v m in *)
    (*   let mc := upd_index c mv in *)
    (*   (mc, DSL.Iaddr (ssa_var mc c) (ssa_var mv v) a1 a2) *)
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
    (* | DSL.Iadcr c v a1 a2 y => *)
    (*   let a1 := ssa_atomic m a1 in *)
    (*   let a2 := ssa_atomic m a2 in *)
    (*   let y := ssa_atomic m y in *)
    (*   let mv := upd_index v m in *)
    (*   let mc := upd_index c mv in *)
    (*   (mc, DSL.Iadcr (ssa_var mc c) (ssa_var mv v) a1 a2 y) *)
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
    (* | DSL.Isubr c v a1 a2 => *)
    (*   let a1 := ssa_atomic m a1 in *)
    (*   let a2 := ssa_atomic m a2 in *)
    (*   let mv := upd_index v m in *)
    (*   let mc := upd_index c mv in *)
    (*   (mc, DSL.Isubr (ssa_var mc c) (ssa_var mv v) a1 a2) *)
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
    (* | DSL.Isbcr c v a1 a2 y => *)
    (*   let a1 := ssa_atomic m a1 in *)
    (*   let a2 := ssa_atomic m a2 in *)
    (*   let y := ssa_atomic m y in *)
    (*   let mv := upd_index v m in *)
    (*   let mc := upd_index c mv in *)
    (*   (mc, DSL.Isbcr (ssa_var mc c) (ssa_var mv v) a1 a2 y) *)
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
    (* | DSL.Isbbr c v a1 a2 y => *)
    (*   let a1 := ssa_atomic m a1 in *)
    (*   let a2 := ssa_atomic m a2 in *)
    (*   let y := ssa_atomic m y in *)
    (*   let mv := upd_index v m in *)
    (*   let mc := upd_index c mv in *)
    (*   (mc, DSL.Isbbr (ssa_var mc c) (ssa_var mv v) a1 a2 y) *)
    | DSL.Imul v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, SSA.Imul (ssa_var m v) a1 a2)
    (* | DSL.Imuls c v a1 a2 => *)
    (*   let a1 := ssa_atomic m a1 in *)
    (*   let a2 := ssa_atomic m a2 in *)
    (*   let mv := upd_index v m in *)
    (*   let mc := upd_index c mv in *)
    (*   (mc, DSL.Imuls (ssa_var mc c) (ssa_var mv v) a1 a2) *)
    (* | DSL.Imulr c v a1 a2 => *)
    (*   let a1 := ssa_atomic m a1 in *)
    (*   let a2 := ssa_atomic m a2 in *)
    (*   let mv := upd_index v m in *)
    (*   let mc := upd_index c mv in *)
    (*   (mc, DSL.Imulr (ssa_var mc c) (ssa_var mv v) a1 a2) *)
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
    (*
    | DSL.Iassert e => (m, SSA.Iassert (ssa_bexp m e))
    | DSL.Iecut e pwss => (m, SSA.Iecut (ssa_ebexp m e) (ssa_pwss pwss))
    | DSL.Ircut e pwss => (m, SSA.Ircut  (ssa_rbexp m e) (ssa_pwss pwss))
     (* | DSL.Ighost vs e => (m, SSA.Ighost (ssa_vars m vs) (ssa_bexp m e)) *)
     (* | _ => (m, i) *)
     *)
    end.

  Fixpoint ssa_program (m : vmap) (p : DSL.program) : vmap * SSA.program :=
    match p with
    | [::] => (m, [::])
    | hd::tl =>
      let (m, hd) := ssa_instr m hd in
      let (m, tl) := ssa_program m tl in
      (m, hd::tl)
    end.

  (* TODO: check defintion *)
  (* map only keys *)

  Definition add_to_ste m k v (e: SSATE.env) := SSATE.add (ssa_var m k) v e.

  Definition ssa_typenv (m: vmap) (te: TE.env) : SSATE.env :=
    TE.fold (add_to_ste m) te (SSATE.empty typ).

  (* TODO: Define SSA translation *)
  Definition ssa_spec (s : DSL.spec) : SSA.spec :=
    let m := empty_vmap in
    let si := ssa_typenv m (DSL.sinputs s) in
    let f := ssa_bexp m (DSL.spre s) in
    let (m, p) := ssa_program m (DSL.sprog s) in
    let g := ssa_bexp m (DSL.spost s) in
    (*
    let sep := ssa_pwss (DSL.sepwss s) in
    let srp := ssa_pwss (DSL.srpwss s) in
     *)
    {| SSA.sinputs := si;
       SSA.spre := f;
       SSA.sprog := p;
       SSA.spost := g;
    (*
       SSA.sepwss := sep;
       SSA.srpwss := srp;
     *)
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
  (*
      SSA.sepwss (ssa_spec s) = ssa_pwss (DSL.sepwss s) /\
      SSA.srpwss (ssa_spec s) = ssa_pwss (DSL.srpwss s).
   *)
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

  Lemma ssa_typenv_vars_env m te:
    SSA.vars_env (ssa_typenv m te) = (ssa_vars m (DSL.vars_env te)).
  Proof.
  Admitted.

  Lemma ssa_vars_mem2_typ m v te :
    SSATE.mem v (ssa_typenv m te) ->
    exists x, v = ssa_var m x /\ TE.mem x te.
  Proof.
    move=> Hmem.
    move/SSA.vars_env_mem: Hmem => Hmem.
    rewrite ssa_typenv_vars_env in Hmem.
    move: (M2.map2_mem2 Hmem) => [y [/eqP Hy Hmemy]].
    rewrite Hy.
    move/DSL.vars_env_mem: Hmemy => Hmemy.
      by exists y.
  Qed.

  Lemma ssa_vars_mem3_typ m v i te :
    TE.mem v te ->
    i = get_index v m ->
    SSATE.mem (v, i) (ssa_typenv m te).
  Proof.
    move=> Hmem Hidx.
    apply /SSA.vars_env_mem.
    rewrite ssa_typenv_vars_env.
    rewrite Hidx.
    rewrite ssa_vars_mem1.
    move/DSL.vars_env_mem : Hmem => Hmem.
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

  Lemma ssa_vars_upd_index_subset1 m v vs :
    SSAVS.subset (ssa_vars (upd_index v m) vs)
                 (SSAVS.add (ssa_var (upd_index v m) v) (ssa_vars m vs)).
  Proof.
    apply: SSAVS.subset_1 => x /SSAVS.Lemmas.memP Hmem.
    apply/SSAVS.Lemmas.memP.
    move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
    rewrite Hxy.
    case Hyv: (y == v).
    - apply: SSAVS.Lemmas.mem_add2.
      rewrite (eqP Hyv).
      exact: eqxx.
    - apply: SSAVS.Lemmas.mem_add3.
      rewrite ssa_vars_mem_2vmap.
      apply/andP; split.
      + assumption.
      + move/idP/negP: Hyv => Hyv.
        rewrite (get_upd_index_neq _ Hyv).
        exact: eqxx.
  Qed.

  Lemma ssa_vars_upd_index_subset2 m vh vl vs :
    SSAVS.subset
      (ssa_vars (upd_index vh (upd_index vl m)) vs)
      (SSAVS.add
         (ssa_var (upd_index vh (upd_index vl m)) vh)
         (SSAVS.add
            (ssa_var (upd_index vl m) vl) (ssa_vars m vs))).
  Proof.
    apply: SSAVS.subset_1 => x /SSAVS.Lemmas.memP Hmem.
    apply/SSAVS.Lemmas.memP. move: (ssa_vars_mem2 Hmem) => [y [Hxy Hy]].
    rewrite Hxy. case Hyvl: (y == vh).
    - apply: SSAVS.Lemmas.mem_add2. rewrite (eqP Hyvl). exact: eqxx.
    - move/idP/negP: Hyvl => Hyvl. rewrite (ssa_var_upd_neq _ Hyvl).
      case Hyvh: (y == vl).
      + apply: SSAVS.Lemmas.mem_add3. apply: SSAVS.Lemmas.mem_add2.
        rewrite (eqP Hyvh). exact: eqxx.
      + move/idP/negP: Hyvh => Hyvh. rewrite (ssa_var_upd_neq _ Hyvh).
        apply: SSAVS.Lemmas.mem_add3. apply: SSAVS.Lemmas.mem_add3.
        rewrite ssa_vars_mem1. assumption.
  Qed.

  (* zero lval, one atomic for Inondet *)
  Lemma ssa_vars_instr_subset_1lv m1 vs v:
    let m2 := upd_index v m1 in
    SSAVS.subset
      (ssa_vars m2 (VS.union vs (VS.singleton v)))
      (SSAVS.union (ssa_vars m1 vs)
                   (SSAVS.singleton (ssa_var m2 v))).
  Proof.
  Admitted.

  (* one lval, one atomic *)
  Lemma ssa_vars_instr_subset11 m1 vs v e :
    let m2 := upd_index v m1 in
    SSAVS.subset
      (ssa_vars m2 (VS.union vs (VS.add v (DSL.vars_atomic e))))
      (SSAVS.union (ssa_vars m1 vs)
                   (SSAVS.add (ssa_var m2 v)
                              (SSA.vars_atomic (ssa_atomic m1 e)))).
  Proof.
    move=> /=.
    set m2 := upd_index v m1.
    set vse := DSL.vars_atomic e.
    set ssam1vs := ssa_vars m1 vs.
    set ssam2v := ssa_var m2 v.
    set ssam1e := ssa_atomic m1 e.
    move: (ssa_vars_upd_index_subset1 m1 v vs) => Hsub1.
    move: (ssa_vars_upd_index_subset1 m1 v vse) => Hsub2.
    have: SSAVS.mem ssam2v (SSAVS.add ssam2v ssam1vs) by
        apply: SSAVS.Lemmas.mem_add2; exact: eqxx.
    move=> Hmem.
    move: (SSAVS.Lemmas.subset_add3 Hmem Hsub1) => {Hmem Hsub1} Hsub1.
    move: (SSAVS.Lemmas.union_subsets Hsub1 Hsub2) => {Hsub1 Hsub2}.
    rewrite -{1}ssa_vars_add -{1}ssa_vars_union => Hsub.
    have: SSAVS.subset (ssa_vars m2 (VS.union vs (VS.add v vse)))
                       (ssa_vars m2 (VS.union (VS.add v vs) vse)).
    { rewrite ssa_vars_subset VS.Lemmas.OP.P.union_sym VS.Lemmas.OP.P.union_add
              VS.Lemmas.OP.P.union_sym -VS.Lemmas.OP.P.union_add.
      exact: VS.Lemmas.subset_refl. }
    move=> Hsub1.
    move: (SSAVS.Lemmas.subset_trans Hsub1 Hsub) => {Hsub1 Hsub} Hsub.
    have: SSAVS.subset
            (SSAVS.union
               (SSAVS.add ssam2v ssam1vs)
               (SSAVS.add ssam2v (ssa_vars m1 vse)))
            (SSAVS.union
               ssam1vs
               (SSAVS.add ssam2v (SSA.vars_atomic ssam1e))).
    { rewrite SSAVS.Lemmas.OP.P.union_add.
      apply: SSAVS.Lemmas.subset_add3.
      - apply: SSAVS.Lemmas.mem_union3.
        apply: SSAVS.Lemmas.mem_add2.
        exact: eqxx.
      - rewrite ssa_vars_atomic_comm.
        exact: SSAVS.Lemmas.subset_refl. }
    move=> Hsub2.
    move: (SSAVS.Lemmas.subset_trans Hsub Hsub2) => {Hsub Hsub2} Hsub.
    assumption.
  Qed.

  (* one lval, two atomics *)
  Lemma ssa_vars_instr_subset12 m1 vs v e1 e2 :
    let m2 := upd_index v m1 in
    let vse1 := DSL.vars_atomic e1 in
    let vse2 := DSL.vars_atomic e2 in
    let ssam1vs := ssa_vars m1 vs in
    let ssam2v := ssa_var m2 v in
    let vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1) in
    let vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2) in
    SSAVS.S.subset
      (ssa_vars m2 (VS.union vs (VS.add v (VS.union vse1 vse2))))
      (SSAVS.S.union
         ssam1vs
         (SSAVS.S.add ssam2v (SSAVS.S.union vsssam1e1 vsssam1e2))).
  Proof.
    move=> /=.
    set m2 := upd_index v m1.
    set vse1 := DSL.vars_atomic e1.
    set vse2 := DSL.vars_atomic e2.
    set ssam1vs := ssa_vars m1 vs.
    set ssam2v := ssa_var m2 v.
    set vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1).
    set vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2).

    have: SSAVS.S.Equal
            (ssa_vars m2 (VS.union vs (VS.add v (VS.union vse1 vse2))))
            (SSAVS.S.union (ssa_vars m2 (VS.union vs (VS.add v vse1)))
                           (ssa_vars m2 (VS.union vs (VS.add v vse2)))).
    { rewrite !ssa_vars_union !ssa_vars_add !ssa_vars_union.
      rewrite SSAVS.S.Lemmas.union2_same1 SSAVS.S.Lemmas.add2_same.
      reflexivity. }
    move=> ->.

    have: SSAVS.S.Equal
            (SSAVS.S.union
               ssam1vs
               (SSAVS.S.add ssam2v (SSAVS.S.union vsssam1e1 vsssam1e2)))
            (SSAVS.S.union
               (SSAVS.S.union ssam1vs
                              (SSAVS.S.add ssam2v vsssam1e1))
               (SSAVS.S.union ssam1vs
                              (SSAVS.S.add ssam2v vsssam1e2))).
    { rewrite SSAVS.S.Lemmas.union2_same1 SSAVS.S.Lemmas.add2_same.
      reflexivity. }
    move=> ->.

    apply: SSAVS.S.Lemmas.union_subsets; exact: ssa_vars_instr_subset11.
  Qed.

  (* one lval, two atomics plus one rval *)
  Lemma ssa_vars_instr_subset13 m1 vs v e1 e2 c :
    let m2 := upd_index v m1 in
    let vse1 := DSL.vars_atomic e1 in
    let vse2 := DSL.vars_atomic e2 in
    let ssam1vs := ssa_vars m1 vs in
    let ssam2v := ssa_var m2 v in
    let ssam1c := ssa_var m1 c in
    let vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1) in
    let vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2) in
    SSAVS.S.subset
      (ssa_vars m2 (VS.union vs (VS.add c (VS.add v (VS.union vse1 vse2)))))
      (SSAVS.S.union
         ssam1vs
         (SSAVS.S.add
            ssam1c
            (SSAVS.S.add ssam2v (SSAVS.S.union vsssam1e1 vsssam1e2)))).
  Proof.
    move=> /=.
    set m2 := upd_index v m1.
    set vse1 := DSL.vars_atomic e1.
    set vse2 := DSL.vars_atomic e2.
    set ssam1vs := ssa_vars m1 vs.
    set ssam2v := ssa_var m2 v.
    set ssam1c := ssa_var m1 c.
    set vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1).
    set vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2).
    set ssavs :=
      (SSAVS.S.union ssam1vs
                     (SSAVS.S.add ssam1c
                                  (SSAVS.S.add ssam2v (SSAVS.S.union vsssam1e1 vsssam1e2)))).
    have: SSAVS.S.mem (ssa_var m2 c) ssavs.
    { case Hcv: (c == v).
      - rewrite (eqP Hcv). apply: SSAVS.S.Lemmas.mem_union3.
        apply: SSAVS.S.Lemmas.mem_add3. apply: SSAVS.S.Lemmas.mem_add2.
        exact: eqxx.
      - move/idP/negP: Hcv => Hcv. rewrite (ssa_var_upd_neq _ Hcv).
        apply: SSAVS.S.Lemmas.mem_union3. apply: SSAVS.S.Lemmas.mem_add2.
        exact: eqxx. }
    move=> Hc.
    rewrite ssa_vars_union ssa_vars_add SSAVS.S.Lemmas.union_add2
    -ssa_vars_union.
    apply: (SSAVS.S.Lemmas.subset_add3 Hc).
    rewrite /ssavs SSAVS.S.Lemmas.union_add2.
    apply: SSAVS.S.Lemmas.subset_add2.
    exact: ssa_vars_instr_subset12.
  Qed.


  (* two lvals, one atomic *)
  Lemma ssa_vars_instr_subset21 m1 vs v1 v2 e :
    let m2 := upd_index v2 m1 in
    let m3 := upd_index v1 m2 in
    let vse := DSL.vars_atomic e in
    let ssam1vs := ssa_vars m1 vs in
    let ssam2v2 := ssa_var m2 v2 in
    let ssam3v1 := ssa_var m3 v1 in
    let vsssam1e := SSA.vars_atomic (ssa_atomic m1 e) in
    SSAVS.S.subset
      (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse))))
      (SSAVS.S.union
         ssam1vs
         (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 vsssam1e))).
  Proof.
    move=> /=.
    set m2 := upd_index v2 m1.
    set m3 := upd_index v1 m2.
    set vse := DSL.vars_atomic e.
    set ssam1vs := ssa_vars m1 vs.
    set ssam2v2 := ssa_var m2 v2.
    set ssam3v1 := ssa_var m3 v1.
    set ssam3v2 := ssa_var m3 v2.
    set ssam1e := ssa_vars m1 (DSL.vars_atomic e).
    set vsssam1e := SSA.vars_atomic (ssa_atomic m1 e).
    move: (ssa_vars_upd_index_subset2 m1 v1 v2 vs) => Hsub1.
    move: (ssa_vars_upd_index_subset2 m1 v1 v2 vse) => Hsub2.
    have: SSAVS.S.mem ssam3v1
                      (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 ssam1vs))
      by apply: SSAVS.S.Lemmas.mem_add2; exact: eqxx.
    have: SSAVS.S.mem ssam3v2
                      (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 ssam1vs)).
    { case H12: (v2 == v1).
      - (* case true *)
        apply: SSAVS.S.Lemmas.mem_add2. rewrite /ssam3v2 /ssam3v1 (eqP H12).
        exact: eqxx.
      - (* case false *)
        move/idP/negP: H12 => H12. rewrite /ssam3v2 (ssa_var_upd_neq _ H12).
        apply: SSAVS.S.Lemmas.mem_add3; apply: SSAVS.S.Lemmas.mem_add2.
        exact: eqxx. }
    move=> Hmemv2 Hmemv1.
    move: (SSAVS.S.Lemmas.subset_add3 Hmemv2 Hsub1) => {Hmemv2 Hsub1} Hsub1.
    move: (SSAVS.S.Lemmas.subset_add3 Hmemv1 Hsub1) => {Hmemv1 Hsub1} Hsub1.
    move: (SSAVS.S.Lemmas.union_subsets Hsub1 Hsub2) => {Hsub1 Hsub2}.
    rewrite -2!{1}ssa_vars_add -{1}ssa_vars_union => Hsub.
    have: SSAVS.S.subset
            (SSAVS.S.union
               (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 ssam1vs))
               (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 (ssa_vars m1 vse))))
            (SSAVS.S.union
               ssam1vs
               (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 vsssam1e))).
    { rewrite /vsssam1e -ssa_vars_atomic_comm.
      rewrite SSAVS.S.Lemmas.OP.P.union_add.
      have: SSAVS.S.mem
              ssam3v1
              (SSAVS.S.union
                 ssam1vs
                 (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 ssam1e)))
        by apply: SSAVS.S.Lemmas.mem_union3;
        apply: SSAVS.S.Lemmas.mem_add2;
        exact: eqxx.
      move=> Hmem; apply: (SSAVS.S.Lemmas.subset_add3 Hmem) => {Hmem}.
      rewrite SSAVS.S.Lemmas.OP.P.union_add.
      have: SSAVS.S.mem
              ssam2v2
              (SSAVS.S.union
                 ssam1vs
                 (SSAVS.S.add ssam3v1 (SSAVS.S.add ssam2v2 ssam1e)))
        by apply: SSAVS.S.Lemmas.mem_union3;
        apply: SSAVS.S.Lemmas.mem_add3;
        apply: SSAVS.S.Lemmas.mem_add2;
        exact: eqxx.
      move=> Hmem; apply: (SSAVS.S.Lemmas.subset_add3 Hmem) => {Hmem}.
      exact: SSAVS.S.Lemmas.subset_refl. }
    move=> Hsub1.
    move: (SSAVS.S.Lemmas.subset_trans Hsub Hsub1) => {Hsub1 Hsub} Hsub.
    have: SSAVS.S.subset
            (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse))))
            (ssa_vars m3 (VS.union (VS.add v1 (VS.add v2 vs)) vse)).
    { rewrite ssa_vars_subset VS.Lemmas.OP.P.union_sym
              4!VS.Lemmas.OP.P.union_add VS.Lemmas.OP.P.union_sym.
      exact: VS.Lemmas.subset_refl. }
    move=> Hsub2.
    move: (SSAVS.S.Lemmas.subset_trans Hsub2 Hsub) => {Hsub Hsub2} Hsub.
    assumption.
  Qed.

  (* two lvals, two atomics *)
  Lemma ssa_vars_instr_subset22 m1 vs v1 v2 e1 e2 :
    let m2 := upd_index v2 m1 in
    let m3 := upd_index v1 m2 in
    let vse1 := DSL.vars_atomic e1 in
    let vse2 := DSL.vars_atomic e2 in
    let ssam1vs := ssa_vars m1 vs in
    let ssam2v2 := ssa_var m2 v2 in
    let ssam3v1 := ssa_var m3 v1 in
    let vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1) in
    let vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2) in
    SSAVS.S.subset
      (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 (VS.union vse1 vse2)))))
      (SSAVS.S.union
         ssam1vs
         (SSAVS.S.add ssam3v1
                      (SSAVS.S.add ssam2v2
                                   (SSAVS.S.union vsssam1e1 vsssam1e2)))).
  Proof.
    move=> /=.
    set m2 := upd_index v2 m1.
    set m3 := upd_index v1 m2.
    set vse1 := (DSL.vars_atomic e1).
    set vse2 := (DSL.vars_atomic e2).
    set ssam1vs := (ssa_vars m1 vs).
    set ssam2v2 := ssa_var m2 v2.
    set ssam3v1 := ssa_var m3 v1.
    set ssam3v2 := ssa_var m3 v2.
    set ssam1e1 := ssa_vars m1 (DSL.vars_atomic e1).
    set ssam1e2 := ssa_vars m1 (DSL.vars_atomic e2).
    set vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1).
    set vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2).

    have: SSAVS.S.Equal
            (ssa_vars m3
                      (VS.union vs (VS.add v1 (VS.add v2 (VS.union vse1 vse2)))))
            (SSAVS.S.union
               (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse1))))
               (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 vse2))))).
    { rewrite !ssa_vars_union !ssa_vars_add !ssa_vars_union.
      rewrite SSAVS.S.Lemmas.union2_same1 SSAVS.S.Lemmas.add2_same
              SSAVS.S.Lemmas.add2_same. reflexivity. }
    move=> ->.

    have: SSAVS.S.Equal
            (SSAVS.S.union
               ssam1vs
               (SSAVS.S.add
                  ssam3v1
                  (SSAVS.S.add ssam2v2 (SSAVS.S.union vsssam1e1 vsssam1e2))))
            (SSAVS.S.union
               (SSAVS.S.union
                  ssam1vs
                  (SSAVS.S.add ssam3v1
                               (SSAVS.S.add ssam2v2 vsssam1e1)))
               (SSAVS.S.union
                  ssam1vs
                  (SSAVS.S.add ssam3v1
                               (SSAVS.S.add ssam2v2 vsssam1e2)))).
    { rewrite SSAVS.S.Lemmas.union2_same1 SSAVS.S.Lemmas.add2_same
              SSAVS.S.Lemmas.add2_same. reflexivity. }
    move=> ->.

    apply: SSAVS.S.Lemmas.union_subsets; exact: ssa_vars_instr_subset21.
  Qed.

  (* two lvals, two atomics plus one rval *)
  Lemma ssa_vars_instr_subset23 m1 vs v1 v2 e1 e2 a :
    let m2 := upd_index v2 m1 in
    let m3 := upd_index v1 m2 in
    let vse1 := DSL.vars_atomic e1 in
    let vse2 := DSL.vars_atomic e2 in
    let ssam1vs := ssa_vars m1 vs in
    let ssam2v2 := ssa_var m2 v2 in
    let ssam3v1 := ssa_var m3 v1 in
    let ssam1a := ssa_var m1 a in
    let vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1) in
    let vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2) in
    SSAVS.S.subset
      (ssa_vars m3 (VS.union vs (VS.add a (VS.add v1 (VS.add v2 (VS.union vse1 vse2))))))
      (SSAVS.S.union
         ssam1vs
         (SSAVS.S.add
            ssam1a
            (SSAVS.S.add
               ssam3v1
               (SSAVS.S.add ssam2v2 (SSAVS.S.union vsssam1e1 vsssam1e2))))).
  Proof.
    move=> /=.
    set m2 := upd_index v2 m1.
    set m3 := upd_index v1 m2.
    set vse1 := (DSL.vars_atomic e1).
    set vse2 := (DSL.vars_atomic e2).
    set ssam1vs := (ssa_vars m1 vs).
    set ssam2v2 := ssa_var m2 v2.
    set ssam3v1 := ssa_var m3 v1.
    set ssam3v2 := ssa_var m3 v2.
    set ssam1e1 := ssa_vars m1 (DSL.vars_atomic e1).
    set ssam1e2 := ssa_vars m1 (DSL.vars_atomic e2).
    set ssam1a := ssa_var m1 a.
    set vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1).
    set vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2).
    set ssavs :=
      (SSAVS.S.union ssam1vs
                     (SSAVS.S.add ssam1a
                                  (SSAVS.S.add ssam3v1
                                               (SSAVS.S.add ssam2v2 (SSAVS.S.union vsssam1e1 vsssam1e2))))).
    have: SSAVS.S.mem (ssa_var m3 a) ssavs.
    { case Hav1: (a == v1).
      - rewrite (eqP Hav1). apply: SSAVS.S.Lemmas.mem_union3.
        apply: SSAVS.S.Lemmas.mem_add3. apply: SSAVS.S.Lemmas.mem_add2.
        exact: eqxx.
      - move/idP/negP: Hav1 => Hav1. rewrite /m3 (ssa_var_upd_neq _ Hav1).
        case Hav2: (a == v2).
        + rewrite (eqP Hav2). apply: SSAVS.S.Lemmas.mem_union3.
          apply: SSAVS.S.Lemmas.mem_add3. apply: SSAVS.S.Lemmas.mem_add3.
          apply: SSAVS.S.Lemmas.mem_add2. exact: eqxx.
        + move/idP/negP: Hav2 => Hav2.
          rewrite /m2 (ssa_var_upd_neq _ Hav2). apply: SSAVS.S.Lemmas.mem_union3.
          apply: SSAVS.S.Lemmas.mem_add2. exact: eqxx. }
    move=> Ha.
    rewrite ssa_vars_union ssa_vars_add SSAVS.S.Lemmas.union_add2 -ssa_vars_union.
    apply: (SSAVS.S.Lemmas.subset_add3 Ha).
    apply: SSAVS.S.Lemmas.subset_trans; first by exact: ssa_vars_instr_subset22.
    have: SSAVS.S.Equal
            ssavs
            (SSAVS.S.add ssam1a
                         (SSAVS.S.union ssam1vs
                                        (SSAVS.S.add ssam3v1
                                                     (SSAVS.S.add ssam2v2 (SSAVS.S.union vsssam1e1 vsssam1e2))))).
    { rewrite -SSAVS.S.Lemmas.union_add2. reflexivity. }
    move=> ->.
    apply: SSAVS.S.Lemmas.subset_add2.
    exact: SSAVS.S.Lemmas.subset_refl.
  Qed.

  Lemma ssa_vars_instr_subset_1lv_3ra m1 vs v e1 e2 e3 :
    let m2 := upd_index v m1 in
    let vse1 := DSL.vars_atomic e1 in
    let vse2 := DSL.vars_atomic e2 in
    let vse3 := DSL.vars_atomic e3 in
    let ssam1vs := ssa_vars m1 vs in
    let ssam2v := ssa_var m2 v in
    let vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1) in
    let vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2) in
    let vsssam1e3 := SSA.vars_atomic (ssa_atomic m1 e3) in
    SSAVS.S.subset
      (ssa_vars m2 (VS.union vs (VS.add v (VS.union vse1 (VS.union vse2 vse3)))))
      (SSAVS.S.union
         ssam1vs
         (SSAVS.S.add ssam2v (SSAVS.S.union vsssam1e1 (SSAVS.S.union vsssam1e2 vsssam1e3)))).
  Proof.
  Admitted.

  (* 2 lvar 3 ratom *)
  Lemma ssa_vars_instr_subset_2lv_3ra m1 vs v1 v2 e1 e2 e3 :
    let m2 := upd_index v2 m1 in
    let m3 := upd_index v1 m2 in
    let vse1 := DSL.vars_atomic e1 in
    let vse2 := DSL.vars_atomic e2 in
    let vse3 := DSL.vars_atomic e3 in
    let ssam1vs := ssa_vars m1 vs in
    let ssam2v2 := ssa_var m2 v2 in
    let ssam3v1 := ssa_var m3 v1 in
    let vsssam1e1 := SSA.vars_atomic (ssa_atomic m1 e1) in
    let vsssam1e2 := SSA.vars_atomic (ssa_atomic m1 e2) in
    let vsssam1e3 := SSA.vars_atomic (ssa_atomic m1 e3) in
    SSAVS.S.subset
      (ssa_vars m3 (VS.union vs (VS.add v1 (VS.add v2 (VS.union vse1 (VS.union vse2 vse3))))))
      (SSAVS.S.union
         ssam1vs
         (SSAVS.S.add
            ssam3v1
            (SSAVS.S.add ssam2v2 (SSAVS.S.union vsssam1e1
                                                (SSAVS.S.union vsssam1e2 vsssam1e3))))).
  Proof.
  Admitted.

  Lemma ssa_vars_empty m:
    ssa_vars m VS.empty = SSAVS.empty.
  Proof.
      by rewrite /ssa_vars /M2.map2 M2.Lemmas1.OP.P.elements_empty.
  Qed.

  Lemma ssa_vars_instr_subset m1 m2 vs i si :
    ssa_instr m1 i = (m2, si) ->
    SSAVS.subset (ssa_vars m2 (VS.union vs (DSL.vars_instr i)))
                 (SSAVS.union (ssa_vars m1 vs) (SSA.vars_instr si)).
  Proof.
    case: i =>  /=; intros;
                 (match goal with
                  | H : (_, _) = (_, _) |- _ => case: H => <- <- /=
                  end
                 );
                 try first [
                       exact: ssa_vars_instr_subset_1lv |
                       exact: ssa_vars_instr_subset11 |
                       exact: ssa_vars_instr_subset12 |
                       exact: ssa_vars_instr_subset13 |
                       exact: ssa_vars_instr_subset21 |
                       exact: ssa_vars_instr_subset22 |
                       exact: ssa_vars_instr_subset23 |
                       exact: ssa_vars_instr_subset_1lv_3ra |
                       exact: ssa_vars_instr_subset_2lv_3ra
                     ].
    - (* Inop *)
      rewrite ssa_vars_union ssa_vars_empty.
      exact: SSAVS.Lemmas.subset_refl.
    - rewrite ssa_vars_union. rewrite ssa_vars_bexp_comm.
      exact: SSAVS.Lemmas.subset_refl.
  Qed.

  Lemma ssa_vars_post_subset vs m1 m2 p sp g :
    VS.subset (DSL.vars_bexp g) (VS.union vs (DSL.vars_program p)) ->
    ssa_program m1 p = (m2, sp) ->
    SSAVS.subset (SSA.vars_bexp (ssa_bexp m2 g)) (SSAVS.union (ssa_vars m1 vs) (SSA.vars_program sp)).
  Proof.
    elim: p vs m1 m2 sp g => /=.
    - move=> vs m1 m2 sp g Hsub [] Hm Hsp.
      rewrite -Hsp -Hm /=.
      rewrite (SSAVS.Lemmas.OP.P.empty_union_2 _ SSAVS.empty_1).
      rewrite ssa_vars_bexp_subset.
      rewrite -(VS.Lemmas.OP.P.empty_union_2 vs VS.empty_1).
      assumption.
    - move=> hd tl IH vs m1 m2 sp g Hsub Hsp.
      move: (ssa_program_cons Hsp) => {Hsp} [m3 [shd [stl [Hshd [Hstl Hsp]]]]].
      rewrite Hsp /= => {Hsp}.
      move: Hsub; rewrite -VS.Lemmas.OP.P.union_assoc => Hsub.
      move: (IH _ _ _ _ _ Hsub Hstl) => {IH Hsub Hstl} H0.
      move: (SSAVS.subset_2 H0) => {H0} H0.
      move: (ssa_vars_instr_subset vs Hshd) => {Hshd} H1.
      move: (SSAVS.subset_2 H1) => {H1} H1.
      move: (SSAVS.Lemmas.OP.P.union_subset_4 (s'':=SSA.vars_program stl) H1) => {H1} H1.
      rewrite -SSAVS.Lemmas.OP.P.union_assoc.
      move: (SSAVS.Lemmas.OP.P.subset_trans H0 H1) => {H0 H1} H2.
      apply: SSAVS.subset_1.
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

  Definition typenv_equiv (m : vmap) (te : TE.env) (ste : SSATE.env) : Prop :=
    forall x, TE.vtyp x te = SSATE.vtyp (x, get_index x m) ste.

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

  Lemma ssa_typenv_add_submap m te x ty:
    SSA.TELemmas.submap (ssa_typenv (upd_index x m) (TE.add x ty te))
    (SSATE.add (ssa_var (upd_index x m) x) ty (ssa_typenv m te)).
  Proof.
  Admitted.

  Lemma ssa_typenv_add2_submap m te x xty y yty:
    SSA.TELemmas.submap (ssa_typenv (upd_index y (upd_index x m)) (TE.add y yty (TE.add x xty te)))
    (SSATE.add (ssa_var (upd_index y (upd_index x m)) y) yty
              (SSATE.add (ssa_var (upd_index x m) x) xty (ssa_typenv m te))).
  Proof.
  Admitted.

  Lemma ssa_atomic_atyp m a te:
    DSL.atyp a te =
    SSA.atyp (ssa_atomic m a) (ssa_typenv m te).
  Proof.
    elim: a m te; intros; rewrite /=.
    - exact: ssa_typenv_preserve.
    - reflexivity.
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
    - move=> v. rewrite (Hseq v).
      rewrite Hteq.
      reflexivity.
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
    - repeat ssa_eval_instr_succ_tac.
    - repeat ssa_eval_instr_succ_tac.
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
  Admitted.

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
  Admitted.

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

  (* Definition dessa_typenv (m : vmap) (ste : SSATE.env) : TE.env := *)
  (*   fun v => SSATE.vtyp (v, get_index v m) ste. *)

  Definition dessa_typenv (m : vmap) (ste : SSATE.env) : TE.env :=
    SSATE.fold (fun k v ste =>
                  if sidx k == get_index (svar k) m then
                    TE.add (svar k) v ste
                  else ste
               ) ste (TE.empty typ).

  Lemma acc_dessa_typenv :
    forall (m : vmap) (ste : SSATE.env) (v : var),
      TE.vtyp v (dessa_typenv m ste) = SSATE.vtyp (v, get_index v m) ste.
  Proof.
  Admitted.

  Lemma ssa_dessa_typenv_K :
    forall (m : vmap) (te : TE.env) (x : var),
      TE.vtyp x (dessa_typenv m (ssa_typenv m te)) = TE.vtyp x te.
  Proof.
    move=> m s x.
    rewrite acc_dessa_typenv.
    symmetry.
    exact: ssa_typenv_preserve.
  Qed.

  (** Soundness and completeness *)

  Theorem ssa_spec_sound (s : DSL.spec) :
    SSA.valid_spec (ssa_spec s) -> DSL.valid_spec s.
  Proof.
    (* destruct s as [input pre pg post]. *)
    (* rewrite /ssa_spec /=. *)
    (* set t1 := ssa_typenv empty_vmap input. *)
    (* have Heq_typ: (t1 = ssa_typenv empty_vmap input) by reflexivity. *)
    (* set t2 := ssa_program empty_vmap pg. *)
    (* have: (t2 = ssa_program empty_vmap pg) by reflexivity. *)
    (* destruct t2 as [m ssa_p]. *)
    (* move=> Hpg Hspec s1 s2 /= Hf Hepre Hep. *)
    (* pose ss1 := ssa_state empty_vmap s1. *)
    (* move: (ssa_state_equiv empty_vmap s1) => Heq1. *)
    (* move: (ssa_typenv_equiv empty_vmap input) => Heq2. *)
    (* symmetry in Hpg. *)
    (* set tsucc := (DSL.program_succ_typenv pg input). *)
    (* have Htsucc: (tsucc = (DSL.program_succ_typenv pg input)) by reflexivity. *)
    (* move: (ssa_eval_program_succ Hpg Heq1 Heq2 Hep Htsucc) => [ss2 [ste2 [Hsep [H]]]] *)
    (* move: (ssa_eval_bexp2 Heq1 Hf) => Hsf. *)
    (* move: (Hspec ss1 ss2 Hsf Hesp) => /= Hsg. *)
    (* exact: (ssa_eval_bexp1 Heq2 Hsg). *)
  Admitted.

  Theorem ssa_spec_complete (s : DSL.spec) :
    DSL.valid_spec s -> SSA.valid_spec (ssa_spec s).
  Proof.
    (* destruct s as [f p g]. *)
    (* rewrite /ssa_spec /=. *)
    (* set t := ssa_program empty_vmap p. *)
    (* have: (t = ssa_program empty_vmap p) by reflexivity. *)
    (* destruct t as [m ssa_p]. *)
    (* move=> Hp Hspec ss1 ss2 /= Hsf Hesp. *)
    (* pose s1 := dessa_state empty_vmap ss1. *)
    (* pose Heq1 := (dessa_state_equiv empty_vmap ss1). *)
    (* move: (dessa_eval_program_succ (Logic.eq_sym Hp) Heq1 Hesp) => [s2 [Hep Heq2]]. *)
    (* move: (ssa_eval_bexp1 Heq1 Hsf) => Hf. *)
    (* move: (Hspec s1 s2 Hf Hep) => /= Hg. *)
    (* exact: (ssa_eval_bexp2 Heq2 Hg). *)
  Admitted.

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
    SSA.well_formed_program te p &&
                            ssa_vars_unchanged_program (SSA.vars_env te) p &&
                            ssa_single_assignment p.

  Definition well_formed_ssa_spec (s : SSA.spec) : bool :=
    SSA.well_formed_spec s &&
                         ssa_vars_unchanged_program (SSA.vars_env (SSA.sinputs s)) (SSA.sprog s) &&
                         ssa_single_assignment (SSA.sprog s).

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
  Proof .
    elim : i => /=; intros; acc_unchanged_instr_upd .
  Qed .

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

  Lemma ssa_var_unchanged_program_concat1 v p1 p2 :
    ssa_unchanged_program_var (p1 ++ p2) v ->
    ssa_unchanged_program_var p1 v /\ ssa_unchanged_program_var p2 v .
  Proof.
    elim: p1 p2.
    - move=> /= p2; done .
    - move=> hd tl IH p2 /andP [Hhd Htlp2] .
      move: (IH _ Htlp2) => {IH Htlp2} [Htl Hp2] .
      rewrite /= Hhd Htl Hp2 // .
  Qed .

  Lemma ssa_var_unchanged_program_concat2 v p1 p2 :
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

  Lemma acc_unchanged_program_concat te v p1 p2 s1 s2 s3 :
    ssa_unchanged_program_var (p1 ++ p2) v ->
    SSA.eval_program te p1 s1 s2 ->
    SSA.eval_program te p2 s2 s3 ->
    SSAStore.acc v s2 = SSAStore.acc v s1 /\
    SSAStore.acc v s3 = SSAStore.acc v s1 .
  Proof .
    move=> Hun12 Hep1 Hep2.
    move: (ssa_var_unchanged_program_concat1 Hun12) => {Hun12} [Hun1 Hun2] .
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

  Lemma ssa_unchanged_program_concat1 vs p1 p2 :
    ssa_vars_unchanged_program vs (p1 ++ p2) ->
    ssa_vars_unchanged_program vs p1 /\ ssa_vars_unchanged_program vs p2.
  Proof.
    move=> H; split; apply: ssa_unchanged_program_global => v Hmem.
    - exact: (proj1 (ssa_var_unchanged_program_concat1
                       (ssa_unchanged_program_local H Hmem))).
    - exact: (proj2 (ssa_var_unchanged_program_concat1
                       (ssa_unchanged_program_local H Hmem))).
  Qed.

  Lemma ssa_unchanged_program_concat2 vs p1 p2 :
    ssa_vars_unchanged_program vs p1 ->
    ssa_vars_unchanged_program vs p2 ->
    ssa_vars_unchanged_program vs (p1 ++ p2).
  Proof.
    move=> Hp1 Hp2. apply: ssa_unchanged_program_global => v Hmem.
    apply: ssa_var_unchanged_program_concat2.
    - exact: (ssa_unchanged_program_local Hp1 Hmem).
    - exact: (ssa_unchanged_program_local Hp2 Hmem).
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
    move=> Heq H.
    move: (ssa_unchanged_program_local H) => {H} H.
    apply: ssa_unchanged_program_global => v Hv.
    apply: H.
    rewrite Heq.
    assumption.
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
    - move=> a Hun Hei. rewrite (ssa_unchanged_instr_eval_singleton Hun Hei).
      reflexivity.
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
    - move=> a Hun Hep. rewrite (ssa_unchanged_program_eval_singleton Hun Hep).
      reflexivity.
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

  Lemma ssa_single_assignment_concat1 p1 p2 :
    ssa_single_assignment (p1 ++ p2) ->
    ssa_single_assignment p1 /\ ssa_single_assignment p2 /\
    (ssa_vars_unchanged_program (SSA.lvs_program p1) p2).
  Proof.
    elim: p1 => /=.
    - move=> Hp2; repeat split. exact: Hp2.
    - move=> i p1 IH /andP [Hun12 Hssa12].
      move: (IH Hssa12) => [Hssa1 [Hssa2 Hun2]] => {Hssa12 IH}. repeat split.
      + by rewrite (proj1 (ssa_unchanged_program_concat1 Hun12)) Hssa1.
      + exact: Hssa2.
      + apply: ssa_unchanged_program_union2.
        * exact: (proj2 (ssa_unchanged_program_concat1 Hun12)).
        * exact: Hun2.
  Qed.

  Lemma ssa_single_assignment_concat2 p1 p2 :
    ssa_single_assignment p1 -> ssa_single_assignment p2 ->
    (ssa_vars_unchanged_program (SSA.lvs_program p1) p2) ->
    ssa_single_assignment (p1 ++ p2).
  Proof.
    elim: p1 => /=.
    - move=> _ Hssa2 _. exact: Hssa2.
    - move=> i p1 IH /andP [Hun1 Hssa1] Hssa2 Hun12.
      apply/andP; split.
      + apply: ssa_unchanged_program_concat2.
        * exact: Hun1.
        * apply: (ssa_unchanged_program_subset Hun12).
          apply: SSA.VSLemmas.subset_union1. exact: SSA.VSLemmas.subset_refl.
      + apply: (IH Hssa1 Hssa2). apply: (ssa_unchanged_program_subset Hun12).
        apply: SSA.VSLemmas.subset_union2. exact: SSA.VSLemmas.subset_refl.
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

  Lemma well_formed_ssa_tl te hd tl :
    well_formed_ssa_program te (hd::tl) ->
    well_formed_ssa_program (SSA.instr_succ_typenv hd te) tl.
  Proof.
    move=> Hwfssa.
    move: (Hwfssa) => /andP [/andP [Hwf Huc] Hssa].
    apply/andP; split; first (apply/andP; split).
    - exact: (SSA.well_formed_program_cons2 Hwf).
    - rewrite SSA.vars_env_instr_succ_typenv.
      apply: ssa_unchanged_program_union2.
      + exact: (ssa_unchanged_program_tl Huc).
      + move/andP: Hssa => [H _].
        exact: H.
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
    exact: Hun.
    by rewrite -SSA.are_defined_subset.
  Qed.

  Corollary well_formed_ssa_spec_post_subset s :
    well_formed_ssa_spec s ->
    SSAVS.subset (SSA.vars_bexp (SSA.spost s))
                 (SSA.vars_env (SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s))).
  Proof.
    move=> /andP [/andP [/andP [/andP [ /andP [Hwd Hwt] Hp] /andP [Hwd2 Hwt2]] Hun] Hssa].
    by rewrite -SSA.are_defined_subset.
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

  Lemma ssa_vars_env_comm m te :
    SSAVS.Equal (SSA.vars_env (ssa_typenv m te))
                (ssa_vars m (DSL.vars_env te)).
  Proof.
    intro.
    split.
    - move=> Hin.
  Admitted.

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
    - rewrite /= in H1.
      move/DSL.are_defined_union/andP: H1 => [H1_1 H1_2].
      apply/SSA.are_defined_union/andP; split.
      + exact: (H _ _ H1_1).
      + exact: (H0 _ _ H1_2).
    - by rewrite <- (ssa_vars_are_defined_singleton) in H.
    - done.
    - apply H with m. by rewrite /= in H0.
    - rewrite /= in H1.
      move/SSA.are_defined_union/andP: H1 => [H1_1 H1_2].
      apply/DSL.are_defined_union/andP; split.
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
    - rewrite /= in H1.
      move/DSL.are_defined_union/andP: H1 => [H1_1 H1_2].
      apply/SSA.are_defined_union/andP; split.
      + exact: (H _ _ H1_1).
      + exact: (H0 _ _ H1_2).
    - apply H. by rewrite /= in H0.
    - apply H. by rewrite /= in H0.
    - by rewrite <- (ssa_vars_are_defined_singleton) in H.
    - done.
    - apply H with m. by rewrite /= in H0.
    - rewrite /= in H1.
      move/SSA.are_defined_union/andP: H1 => [H1_1 H1_2].
      apply/DSL.are_defined_union/andP; split.
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
    - move/DSL.are_defined_union/andP: H => [He He0].
      apply/SSA.are_defined_union/andP; split; by apply ssa_vars_are_defined_eexp.
    - move/DSL.are_defined_union/andP: H => [He H].
      move/DSL.are_defined_union/andP: H => [He0 He1].
      apply/SSA.are_defined_union/andP; split; first by apply ssa_vars_are_defined_eexp.
      apply/SSA.are_defined_union/andP; split; by apply ssa_vars_are_defined_eexp.
    - apply/SSA.are_defined_union/andP; rewrite /= in H1;
        move/DSL.are_defined_union/andP: H1 => [H1_1 H1_2]; split; by [apply H|apply H0].
    - done.
    - move/SSA.are_defined_union/andP: H => [He He0].
      apply/DSL.are_defined_union/andP; split; by apply (ssa_vars_are_defined_eexp m).
    - move/SSA.are_defined_union/andP: H => [He H].
      move/SSA.are_defined_union/andP: H => [He0 He1].
      apply/DSL.are_defined_union/andP; split; first by apply (ssa_vars_are_defined_eexp m).
      apply/DSL.are_defined_union/andP; split; by apply (ssa_vars_are_defined_eexp m).
    - apply/DSL.are_defined_union/andP; rewrite /= in H1;
        move/SSA.are_defined_union/andP: H1 => [H1_1 H1_2]; split; by [apply (H m) |apply (H0 m)].
  Qed.

  Lemma ssa_vars_are_defined_rbexp m r te:
    DSL.are_defined (DSL.vars_rbexp r) te <->
    SSA.are_defined (SSA.vars_rbexp (ssa_rbexp m r)) (ssa_typenv m te).
  Proof.
    split; elim: r m te; intros; rewrite /= in H *.
    - done.
    - move/DSL.are_defined_union/andP: H => [He He0].
      apply/SSA.are_defined_union/andP; split; by apply ssa_vars_are_defined_rexp.
    - move/DSL.are_defined_union/andP: H => [He H].
      apply/SSA.are_defined_union/andP; split; by apply ssa_vars_are_defined_rexp.
    - apply H; rewrite /= in H0; done.
    - apply/SSA.are_defined_union/andP; rewrite /= in H1;
        move/DSL.are_defined_union/andP: H1 => [H1_1 H1_2]; split; by [apply H|apply H0].
    - apply/SSA.are_defined_union/andP; rewrite /= in H1;
        move/DSL.are_defined_union/andP: H1 => [H1_1 H1_2]; split; by [apply H|apply H0].
    - done.
    - move/SSA.are_defined_union/andP: H => [He He0].
      apply/DSL.are_defined_union/andP; split; by apply (ssa_vars_are_defined_rexp m).
    - move/SSA.are_defined_union/andP: H => [He H].
      apply/DSL.are_defined_union/andP; split; by apply (ssa_vars_are_defined_rexp m).
    - apply (H m); rewrite /= in H0; done.
    - apply/DSL.are_defined_union/andP; rewrite /= in H1;
        move/SSA.are_defined_union/andP: H1 => [H1_1 H1_2]; split; by [apply (H m)|apply (H0 m)].
    - apply/DSL.are_defined_union/andP; rewrite /= in H1;
        move/SSA.are_defined_union/andP: H1 => [H1_1 H1_2]; split; by [apply (H m)|apply (H0 m)].
  Qed.

  Lemma ssa_vars_are_defined_bexp m b te:
    DSL.are_defined (DSL.vars_bexp b) te <->
    SSA.are_defined (SSA.vars_bexp (ssa_bexp m b)) (ssa_typenv m te).
  Proof.
    elim: b m te; split; intros.
    - rewrite /DSL.vars_bexp /= in H.
      move/DSL.are_defined_union/andP: H => [He Hr].
      rewrite /SSA.vars_bexp /=.
      apply/SSA.are_defined_union/andP; split.
      + by apply ssa_vars_are_defined_ebexp.
      + by apply ssa_vars_are_defined_rbexp.
    - rewrite /SSA.vars_bexp /= in H.
      move/SSA.are_defined_union/andP: H => [He Hr].
      rewrite /DSL.vars_bexp /=.
      apply/DSL.are_defined_union/andP; split.
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

  Lemma ssa_instr_well_typed te m1 m2 i si :
    DSL.well_formed_instr te i ->
    ssa_instr m1 i = (m2, si) ->
    SSA.well_typed_instr (ssa_typenv m1 te) si.
  Proof.
    rewrite /DSL.well_formed_instr /DSL.well_defined_instr /DSL.well_typed_instr /SSA.well_typed_instr.
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
                     | |- context [SSA.atyp (ssa_atomic ?m ?a) (ssa_typenv ?m ?te)]
                       => rewrite -ssa_atomic_atyp; tac
                     | H: is_true (DSL.are_defined (DSL.vars_atomic ?a) ?te)
                       |- is_true (SSA.are_defined (SSA.vars_atomic (ssa_atomic ?m ?a))
                                         (ssa_typenv ?m ?te)) => rewrite -ssa_vars_are_defined_atomic; exact: H
                     | H : is_true (?v1 != ?v2)
                       |- is_true (ssa_var (upd_index ?v1 (upd_index ?v2 ?m)) ?v1 !=
                                          ssa_var (upd_index ?v2 ?m) ?v2) =>
                       exact: (pair_neq1 _ _ H)
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



  Theorem ssa_program_well_formed1 te m1 m2 p sp :
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

  Lemma ssa_typenv_mem_le v i m te:
    SSAVS.mem (v, i) (SSA.vars_env (ssa_typenv m te)) ->
    i <=? get_index v m.
  Proof.
  Admitted.

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

  Definition well_formed_ssa_spec2 (s : SSA.spec) : bool :=
    SSA.well_formed_spec s &&
                         ssa_vars_unchanged_program (SSA.vars_env (SSA.sinputs s)) (SSA.sprog s) &&
                         ssa_single_assignment (SSA.sprog s).

  Lemma ssa_spec_well_formed_sub1 s:
    DSL.well_formed_bexp (DSL.sinputs s) (DSL.spre s) ->
    SSA.well_formed_bexp (SSA.sinputs (ssa_spec s)) (SSA.spre (ssa_spec s)).
  Proof.
  Admitted.

  Lemma ssa_spec_well_formed_sub2 s m1 m2 p sp:
    DSL.well_formed_bexp (DSL.program_succ_typenv (DSL.sprog s) (DSL.sinputs s)) (DSL.spost s) ->
    ssa_program m1 p = (m2, sp) ->
    SSA.well_formed_bexp (SSA.program_succ_typenv (SSA.sprog (ssa_spec s))
                                                  (SSA.sinputs (ssa_spec s)))
                         (SSA.spost (ssa_spec s)).
  Proof.
  Admitted.

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
        (* rewrite /SSA.well_formed_bexp. *)
        (* rewrite Hpre ssa_vars_bexp_subset. *)
        (* assumption. *)
      + rewrite Hinput. exact: Hwell.
      + exact: (ssa_spec_well_formed_sub2 Hsubpost (Logic.eq_sym Hprog)).
    - rewrite Hinput. assumption.
    - exact: (ssa_program_single_assignment (Logic.eq_sym Hprog)).
  Qed.




End MakeSSA.
