From Coq Require Import List ZArith FSets OrderedType.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From ssrlib Require Import Var SsrOrder FMaps ZAriths Tactics Lists FSets.
From Cryptoline Require Import DSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module SSA := MakeDSL SSAVarOrder SSAVS SSAVM SSATE SSAStore.

Module M2 := Map2 VS SSAVS.

Section MakeSSA.

  Local Open Scope N_scope.

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

  Definition ssa_typenv (m: vmap) (te: TE.env) : SSATE.env :=
    TE.fold (fun k v e => SSATE.add (ssa_var m k) v e) te (SSATE.empty typ).

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
  (*
    - rewrite ssa_vars_union. rewrite ssa_vars_bexp_comm.
      exact: SSAVS.Lemmas.subset_refl.
    - rewrite ssa_vars_union. rewrite ssa_vars_ebexp_comm.
      exact: SSAVS.Lemmas.subset_refl.
    - rewrite ssa_vars_union. rewrite ssa_vars_rbexp_comm.
      exact: SSAVS.Lemmas.subset_refl.
   *)
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


  Lemma ssa_typenv_preserve m TE v:
    SSATE.vtyp (ssa_var m v) (ssa_typenv m TE) = TE.vtyp v TE.
    (* correct bc. ssa_var is injective *)
    (* TODO: need some works *)
  Admitted.

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

  Lemma ssa_eval_eexp m TE s ss (e : DSL.eexp) :
    state_equiv m s ss ->
    SSA.eval_eexp (ssa_eexp m e) (ssa_typenv m TE) ss = DSL.eval_eexp e TE s.
  Proof.
    move=> Heq; elim: e => /=.
    - move=> v. rewrite (Heq v).
      rewrite ssa_typenv_preserve.
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

  Lemma ssa_eval_ebexp m TE s ss e :
    state_equiv m s ss ->
    SSA.eval_ebexp (ssa_ebexp m e) (ssa_typenv m TE) ss <-> DSL.eval_ebexp e TE s.
  Proof.
    move=> Heq; elim: e => /=.
    - done.
    - move=> e1 e2. rewrite 2!(ssa_eval_eexp _ _ Heq). done.
    - move=> e1 e2 p. rewrite 3!(ssa_eval_eexp _ _ Heq). done.
    - move=> e1 [IH11 IH12] e2 [IH21 IH22]. tauto.
  Qed.

  Lemma ssa_eval_ebexp1 m TE s ss e :
    state_equiv m s ss ->
    SSA.eval_ebexp (ssa_ebexp m e) (ssa_typenv m TE) ss -> DSL.eval_ebexp e TE s.
  Proof.
    move=> Heq He.
    move: (ssa_eval_ebexp TE e Heq) => [H1 H2].
    exact: (H1 He).
  Qed.

  Lemma ssa_eval_ebexp2 m TE s ss e :
    state_equiv m s ss ->
    DSL.eval_ebexp e TE s -> SSA.eval_ebexp (ssa_ebexp m e) (ssa_typenv m TE) ss.
  Proof.
    move=> Heq He.
    move: (ssa_eval_ebexp TE e Heq) => [H1 H2].
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

  Lemma ssa_eval_bexp m TE s ss e :
    state_equiv m s ss ->
    SSA.eval_bexp (ssa_bexp m e) (ssa_typenv m TE) ss <-> DSL.eval_bexp e TE s.
  Proof.
    move=> Heq. split; move=> [H1 H2].
    - exact: (conj (ssa_eval_ebexp1 Heq H1) (ssa_eval_rbexp1 Heq H2)).
    - exact: (conj (ssa_eval_ebexp2 Heq H1) (ssa_eval_rbexp2 Heq H2)).
  Qed.

  Lemma ssa_eval_bexp1 m TE s ss e :
    state_equiv m s ss ->
    SSA.eval_bexp (ssa_bexp m e) (ssa_typenv m TE ) ss -> DSL.eval_bexp e TE s.
  Proof.
    move=> Heq He.
    move: (ssa_eval_bexp TE e Heq) => [H1 H2].
    exact: (H1 He).
  Qed.

  Lemma ssa_eval_bexp2 m s TE ss e :
    state_equiv m s ss ->
    DSL.eval_bexp e TE s -> SSA.eval_bexp (ssa_bexp m e) (ssa_typenv m TE) ss.
  Proof.
    move=> Heq He.
    move: (ssa_eval_bexp TE e Heq) => [H1 H2].
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

  (* Ltac ssa_eval_state_equiv_tac := *)
  (*   simpl; intros; *)
  (*   let rec tac := *)
  (*       lazymatch goal with *)
  (*       | H : (_, _) = (_, _) |- _ => *)
  (*         case: H; intros; subst; simpl; tac *)
  (*       | H : state_equiv ?m ?s ?ss *)
  (*         |- context f [SSA.eval_atomic (ssa_atomic ?m ?a) ?ss] => *)
  (*         rewrite (ssa_eval_atomic a H); tac *)
  (*       | H : state_equiv ?m ?s ?ss *)
  (*         |- context f [SSAStore.acc (ssa_var ?m ?a) ?ss] => *)
  (*         rewrite -(H a); tac *)
  (*       | H : state_equiv ?m ?s ?ss |- _ => *)
  (*         try first [ exact: (state_equiv_upd _ _ H) | *)
  (*                     exact: (state_equiv_upd2 _ _ _ _ H) ] *)
  (*       end in *)
  (*   tac. *)

  (* Lemma ssa_eval_instr : *)
  (*   forall m1 m2 TE1 TE2 s1 s2 ss1 ss2 i si, *)
  (*     ssa_instr m1 i = (m2, si) -> *)
  (*     ssa_typenv m1 TE1 = TE2 -> *)
  (*     state_equiv m1 s1 ss1 -> *)
  (*     DSL.eval_instr TE1 i = s2 -> *)
  (*     SSA.eval_instr TE2 ss1 si = ss2 -> *)
  (*     state_equiv m2 s2 ss2. *)
  (* Proof. *)
  (*   move=> m1 m2 s1 s2 ss1 ss2 i. *)
  (*   case: i; by ssa_eval_state_equiv_tac. *)
  (* Qed. *)

  (*
  (* TODO: Check if all variables in a program are not indexed. *)

  Definition unindexed_var (v : var) : bool :=
    vidx v == 1.

  Definition unindexed_vars vs := VS.for_all unindexed_var vs.

  Definition unindexed_atomic  (a : atomic) : bool :=
    match a with
    | Avar v => unindexed_var v
    | Aconst ty n => true
    end.

  Fixpoint unindexed_eexp (e: eexp) :=
    match e with
    | Evar v => unindexed_var v
    | Econst c => true
    | Eunop op e => unindexed_eexp e
    | Ebinop op e1 e2 => unindexed_eexp e1 && unindexed_eexp e2
    end.

  Fixpoint unindexed_rexp (e: rexp) :=
    match e with
    | Rvar v => unindexed_var v
    | Rconst w n => true
    | Runop w op e => unindexed_rexp e
    | Rbinop w op e1 e2 => unindexed_rexp e1 && unindexed_rexp e2
    | Ruext w e i => unindexed_rexp e
    | Rsext w e i => unindexed_rexp e
    end.

  Fixpoint unindexed_ebexp (e: ebexp) :=
    match e with
    | Etrue => true
    | Eeq e1 e2 => unindexed_eexp e1 && unindexed_eexp e2
    | Eeqmod e1 e2 p => unindexed_eexp e1 && unindexed_eexp e2 && unindexed_eexp p
    | Eand e1 e2 => unindexed_ebexp e1 && unindexed_ebexp e2
    end.

  Fixpoint unindexed_rbexp (e: rbexp) :=
    match e with
    | Rtrue => true
    | Req w e1 e2 => unindexed_rexp e1 && unindexed_rexp e2
    | Rcmp w op e1 e2 => unindexed_rexp e1 && unindexed_rexp e2
    | Rneg e =>  unindexed_rbexp e
    | Rand e1 e2 => unindexed_rbexp e1 && unindexed_rbexp e2
    | Ror e1 e2 => unindexed_rbexp e1 && unindexed_rbexp e2
    end.

  Definition unindexed_bexp e := unindexed_ebexp (eqn_bexp e) && unindexed_rbexp (rng_bexp e).

  Definition unindexed_instr (i: instr) : bool :=
    match i with
    | Imov v a
    | Ishl v a _ =>
      let v := unindexed_var v in
      let a := unindexed_atomic a in
      v && a
    | Icshl vh vl a1 a2 _ =>
      let vh := unindexed_var vh in
      let vl := unindexed_var vl in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      vh && vl && a1 && a2
    | Inondet v =>
      let v := unindexed_var v in v
    | Icmov v c a1 a2 =>
      let v := unindexed_var v in
      let c := unindexed_atomic c in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      v && c && a1 && a2
    | Inop => true
    | Inot v a =>
      let v := unindexed_var v in
      let a := unindexed_atomic a in
      v && a
    | Iadd v a1 a2 =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      v && a1 && a2
    | Iadds c v a1 a2
    | Iaddr c v a1 a2 =>
      let c := unindexed_var c in
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      c && v && a1 && a2
    | Iadc v a1 a2 y =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      let y := unindexed_atomic y in
      v && a1 && a2 && y
    | Iadcs c v a1 a2 y
    | Iadcr c v a1 a2 y =>
      let c := unindexed_var c in
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      let y := unindexed_atomic y in
      c && v && a1 && a2 && y
    | Isub v a1 a2 =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      v && a1 && a2
    | Isubc c v a1 a2
    | Isubb c v a1 a2
    | Isubr c v a1 a2 =>
      let c := unindexed_var c in
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      c && v && a1 && a2
    | Isbc v a1 a2 y =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      let y := unindexed_atomic y in
      v && a1 && a2 && y
    | Isbcs c v a1 a2 y
    | Isbcr c v a1 a2 y =>
      let c := unindexed_var c in
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      let y := unindexed_atomic y in
      c && v && a1 && a2 && y
    | Isbb v a1 a2 y =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      let y := unindexed_atomic y in
      v && a1 && a2 && y
    | Isbbs c v a1 a2 y
    | Isbbr c v a1 a2 y =>
      let c := unindexed_var c in
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      let y := unindexed_atomic y in
      c && v && a1 && a2 && y
    | Imul v a1 a2 =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      v && a1 && a2
    | Imuls c v a1 a2
    | Imulr c v a1 a2 =>
      let c := unindexed_var c in
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      c && v && a1 && a2
    | Imull vh vl a1 a2 =>
      let vh := unindexed_var vh in
      let vl := unindexed_var vl in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      vh && vl && a1 && a2
    | Imulj v a1 a2 =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      v && a1 && a2
    | Isplit vh vl a n =>
      let vh := unindexed_var vh in
      let vl := unindexed_var vl in
      let a := unindexed_atomic a in
      vh && vl && a
    | Iand v a1 a2
    | Ior v a1 a2
    | Ixor v a1 a2 =>
      let v := unindexed_var v in
      let a1 := unindexed_atomic a1 in
      let a2 := unindexed_atomic a2 in
      v && a1 && a2
    | Icast v a
    | Ivpc v a =>
      let v := unindexed_var v in
      let a := unindexed_atomic a in
      v && a
    | Ijoin v ah al =>
      let v := unindexed_var v in
      let ah := unindexed_atomic ah in
      let al := unindexed_atomic al in
      v && ah && al
    | Iassert e => unindexed_bexp e
    | Iassume e => unindexed_bexp e
    | Iecut e pwss => unindexed_ebexp e
    | Ircut e pwss => unindexed_rbexp e
    | Ighost vs e => unindexed_vars vs && unindexed_bexp e
    end.

  Fixpoint unindexed_program (p : program) : bool :=
    match p with
    | [::] => true
    | hd::tl =>
      let unidx_instr := unindexed_instr hd in
      let unidx_tl := unindexed_program tl in
      unidx_instr && unidx_tl
    end.

   *)

  (** Well-formed SSA *)

  Definition ssa_var_unchanged_instr v i : bool :=
    ~~ (SSAVS.mem v (SSA.lvs_instr i)).

  Definition ssa_unchanged_instr_var i v : bool :=
    ssa_var_unchanged_instr v i .

  Definition ssa_vars_unchanged_instr vs i : bool :=
    SSAVS.for_all (ssa_unchanged_instr_var i) vs .

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

  Definition well_formed_ssa_spec (te: SSATE.env) (s : SSA.spec) : bool :=
    SSA.well_formed_spec s &&
                         ssa_vars_unchanged_program (SSA.vars_env te) (SSA.sprog s) &&
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
        * apply: SSA.well_formed_instr_subset_rvs.
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
    well_formed_ssa_spec (SSA.sinputs s) s ->
    well_formed_ssa_program (SSA.sinputs s) (SSA.sprog s).
  Proof.
    move=> /andP [/andP [/andP [/andP [/andP Hpre Hwell] Hprog] Hvs] Hssa].
    by rewrite /well_formed_ssa_program Hwell Hvs Hssa.
  Qed.

  Corollary well_formed_ssa_spec_pre_unchanged s :
    well_formed_ssa_spec (SSA.sinputs s) s ->
    ssa_vars_unchanged_program (SSA.vars_bexp (SSA.spre s)) (SSA.sprog s).
  Proof.
    move=> /andP [/andP [/andP [/andP [/andP [Hwd Hwt] Hp] Hg] Hun] Hssa].
    exact: (ssa_unchanged_program_subset Hun Hwd).
  Qed.

  Corollary well_formed_ssa_spec_post_subset s :
    well_formed_ssa_spec (SSA.sinputs s) s ->
    SSAVS.subset (SSA.vars_bexp (SSA.spost s))
                 (SSA.vars_env (SSA.program_succ_typenv (SSA.sprog s) (SSA.sinputs s))).
  Proof.
    move=> /andP [/andP [/andP [/andP [ /andP [Hwd Hwt] Hp] /andP [Hwd2 Hwt2]] Hun] Hssa].
    exact: Hwd2.
  Qed.



End MakeSSA.
