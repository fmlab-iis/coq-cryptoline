From Coq Require Import List ZArith FSets OrderedType.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From BitBlasting Require Import Typ TypEnv State.
From ssrlib Require Import Var SsrOrder FMaps ZAriths Tactics Lists FSets.
From Cryptoline Require Import DSL.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module SSA := MakeDSL SSAVarOrder SSAVS SSAVM SSATE SSAStore.

Module M2 := Map2 VS VS.

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

  Definition ssa_vars (m : vmap) (vs : VS.t) : SSAVS.t :=
    SSAVS.Lemmas.OP.P.of_list (map (ssa_var m) (VS.elements vs)).

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
  Definition ssa_instr (m : vmap) (i : instr) : vmap * instr :=
    match i with
    | Imov v a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, Imov (ssa_var m v) a)
    | Ishl v a p =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, Ishl (ssa_var m v) a p)
    | Icshl vh vl a1 a2 p =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let ml := upd_index vl m in
      let mh := upd_index vh ml in
      (mh, Icshl (ssa_var mh vh) (ssa_var ml vl) a1 a2 p)
    | Inondet v =>
      let m := upd_index v m in
      (m, Inondet (ssa_var m v))
    | Icmov v c a1 a2 =>
      let c := ssa_atomic m c in
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Icmov (ssa_var m v) c a1 a2)
    | Inop => (m, Inop)
    | Inot v a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, Inot (ssa_var m v) a)
    | Iadd v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Iadd (ssa_var m v) a1 a2)
    | Iadds c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Iadds (ssa_var mc c) (ssa_var mv v) a1 a2)
    | Iaddr c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Iaddr (ssa_var mc c) (ssa_var mv v) a1 a2)
    | Iadc v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let m := upd_index v m in
      (m, Iadc (ssa_var m v) a1 a2 y)
    | Iadcs c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Iadcs (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | Iadcr c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Iadcr (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | Isub v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Isub (ssa_var m v) a1 a2)
    | Isubc c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Isubc (ssa_var mc c) (ssa_var mv v) a1 a2)
    | Isubb c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Isubb (ssa_var mc c) (ssa_var mv v) a1 a2)
    | Isubr c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Isubr (ssa_var mc c) (ssa_var mv v) a1 a2)
    | Isbc v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let m := upd_index v m in
      (m, Isbc (ssa_var m v) a1 a2 y)
    | Isbcs c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Isbcs (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | Isbcr c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Isbcr (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | Isbb v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let m := upd_index v m in
      (m, Isbb (ssa_var m v) a1 a2 y)
    | Isbbs c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Isbbs (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | Isbbr c v a1 a2 y =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let y := ssa_atomic m y in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Isbbr (ssa_var mc c) (ssa_var mv v) a1 a2 y)
    | Imul v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Imul (ssa_var m v) a1 a2)
    | Imuls c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Imuls (ssa_var mc c) (ssa_var mv v) a1 a2)
    | Imulr c v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let mv := upd_index v m in
      let mc := upd_index c mv in
      (mc, Imulr (ssa_var mc c) (ssa_var mv v) a1 a2)
    | Imull vh vl a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let ml := upd_index vl m in
      let mh := upd_index vh ml in
      (mh, Imull (ssa_var mh vh) (ssa_var ml vl) a1 a2)
    | Imulj v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Imulj (ssa_var m v) a1 a2)
    | Isplit vh vl a n =>
      let a := ssa_atomic m a in
      let ml := upd_index vl m in
      let mh := upd_index vh ml in
      (mh, Isplit (ssa_var mh vh) (ssa_var ml vl) a n)
    | Iand v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Iand (ssa_var m v) a1 a2)
    | Ior v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Ior (ssa_var m v) a1 a2)
    | Ixor v a1 a2 =>
      let a1 := ssa_atomic m a1 in
      let a2 := ssa_atomic m a2 in
      let m := upd_index v m in
      (m, Ixor (ssa_var m v) a1 a2)
    | Icast v a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, Imov (ssa_var m v) a)
    | Ivpc v a =>
      let a := ssa_atomic m a in
      let m := upd_index v m in
      (m, Imov (ssa_var m v) a)
    | Ijoin v ah al =>
      let ah := ssa_atomic m ah in
      let al := ssa_atomic m al in
      let m := upd_index v m in
      (m, Ijoin (ssa_var m v) ah al)
    | Iassert e => (m, Iassert (ssa_bexp m e))
    | Iassume e => (m, Iassume (ssa_bexp m e))
    | Iecut e pwss => (m, Iecut ( ssa_ebexp m e ) pwss)
    | Ircut e pwss => (m, Ircut ( ssa_rbexp m e ) pwss)
    | Ighost vs e => (m, Ighost (ssa_vars m vs) (ssa_bexp m e))
                      (* | _ => (m, i) *)
    end.

  Fixpoint ssa_program (m : vmap) (p : program) : vmap * program :=
    match p with
    | [::] => (m, [::])
    | hd::tl =>
      let (m, hd) := ssa_instr m hd in
      let (m, tl) := ssa_program m tl in
      (m, hd::tl)
    end.

  (* TODO: Define SSA translation *)
  Definition ssa_spec (s : spec) : spec :=
    let m := empty_vmap in
    let f := ssa_bexp m (spre s) in
    let (m, p) := ssa_program m (sprog s) in
    let g := ssa_bexp m (spost s) in
    {| sinputs := (sinputs s);
       spre := f;
       sprog := p;
       spost := g;
       sepwss := (sepwss s);
       srpwss := (srpwss s);
    |}.


  (* TODO: Check if all variables in a program are not indexed. *)

  Definition unindexed_var (v : var) : bool :=
    vidx v == 0.

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
    exists m, spre (ssa_spec s) = ssa_bexp empty_vmap (spre s) /\
         (m, sprog (ssa_spec s)) = ssa_program empty_vmap (sprog s) /\
         spost (ssa_spec s) = ssa_bexp m (spost s).
  Proof.
    destruct s as [f p g] => /=.
    rewrite /ssa_spec /=.
    set tmp := ssa_program empty_vmap g.
    destruct tmp as [m sp] => /=.
    exists m; split; [idtac | split]; reflexivity.
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
    ssa_var (upd_index v m) v = {|vname := vname v; vidx := get_index v (upd_index v m) |}.
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
    VS.mem v (ssa_vars m vs) = (v \in (VS.elements (ssa_vars m vs))).
  Proof.
    move: (VS.Lemmas.elements_iff (ssa_vars m vs) v) => [HinA Hin].
    case Hv: (v \in VS.elements (ssa_vars m vs)).
    - move/InAP: Hv => Hv.
      apply/VS.Lemmas.memP.
      apply: Hin.
      assumption.
    - move/negP: Hv => Hv.
      apply/negP => /VS.Lemmas.memP Hmem.
      apply: Hv.
      apply/InAP.
      apply: HinA.
      assumption.
  Qed.

  Lemma ssa_vars_Empty m vs :
    VS.Empty vs ->
    VS.Empty (ssa_vars m vs).
  Proof.
    rewrite /ssa_vars.
    move=> Hempty.
    apply VS.Lemmas.OP.P.elements_Empty in Hempty.
    rewrite /M2.map2.
    rewrite Hempty.
    rewrite /=.
    exact: VS.empty_1.
  Qed.

  Lemma ssa_var_preserve m x y : x == y -> ssa_var m x == ssa_var m y.
  Proof.
    move=> H.
    rewrite (eqP H).
    exact: eqxx.
  Qed.

  Lemma ssa_var_injective m x y :
    unindexed_var x ->
    unindexed_var y ->
    ssa_var m x == ssa_var m y ->
    x == y.
  Proof.
    rewrite /unindexed_var.
    move=> Hu1 Hu2 /eqP H.
    case: H => H H2.
    have: (x =? y)%var by rewrite /var_eqn H (eqP Hu1) (eqP Hu2) !eqxx.
      by move/var_eqP -> .
  Qed.

  Lemma inA_ssa_var_map1 m x s :
    InA VS.E.eq x s ->
    InA VS.E.eq (ssa_var m x) (map (ssa_var m) s).
  Proof.
    elim: s m x => /=.
    - move=> m x H; by inversion H.
    - move=> hd tl IH m x Hin.
      inversion_clear Hin.
      + apply: InA_cons_hd.
        exact: (ssa_var_preserve m H).
      + apply: InA_cons_tl.
        exact: (IH _ _ H).
  Qed.

  Lemma inA_ssa_var_map2 m x s :
    unindexed_var x ->
    all unindexed_var s ->
    InA VS.E.eq (ssa_var m x) (map (ssa_var m) s) ->
    InA VS.E.eq x s.
  Proof.
    elim: s m x => /=.
    - move=> m x Hu _ H; by inversion H.
    - move=> hd tl IH m x Hux /andP [Huhd Hutl] Hin.
      inversion_clear Hin.
      + apply: InA_cons_hd.
        exact: (ssa_var_injective Hux Huhd H).
      + apply: InA_cons_tl.
        exact: (IH _ _ _ _ H).
  Qed.

  Lemma inA_ssa_var_map3 m x s :
    InA VS.E.eq x (map (ssa_var m) s) ->
    exists y, VS.E.eq x (ssa_var m y) /\ InA VS.E.eq y s.
  Proof.
    elim: s m x => /=.
    - move=> x m H; by inversion H.
    - move=> hd tl IH x m Hin.
      inversion_clear Hin.
      + exists hd; split.
        * assumption.
        * apply: InA_cons_hd.
          exact: VS.E.eq_refl.
      + move: (IH _ _ H) => [y [Heq HinA]].
        exists y; split.
        * assumption.
        * exact: InA_cons_tl.
  Qed.

  Definition ssa_var_map2 m s :=
    VS.Lemmas.OP.P.of_list (map (ssa_var m) (VS.elements s)).

  Lemma map2_Empty1 m s :
    VS.Empty s ->
    VS.Empty (ssa_var_map2 m s).
  Proof.
    move=> Hemp1.
    rewrite /ssa_var_map2.
    move=> x Hin.
    move: (VS.Lemmas.OP.P.elements_Empty s) => [H _].
    rewrite (H Hemp1) /= in Hin => {H}.
    move: (VS.Lemmas.empty_iff x) => [H _].
    apply: H; assumption.
  Qed.

  Lemma ssa_var_map2_Empty2 m s :
    VS.Empty (ssa_var_map2 m s) ->
    VS.Empty s.
  Proof.
    move=> Hemp1.
    rewrite /ssa_var_map2 in Hemp1.
    move=> x Hmem.
    apply: (Hemp1 (ssa_var m x)).
    apply: VS.Lemmas.in_of_list2.
    apply: inA_ssa_var_map1.
    exact: (VS.elements_1 Hmem).
  Qed.

  Lemma compat_unindexed_var: compat_bool VS.TS.SE.eq unindexed_var.
  Proof.
    rewrite /compat_bool /Proper.
    rewrite /respectful /impl.
    move=> a b H1.
    inversion H1.
      by rewrite (eqP H0).
  Qed.

  Lemma ssa_var_map2_mem1 m (x: var) xs :
    unindexed_var x ->
    unindexed_vars xs ->
    VS.mem (ssa_var m x) (ssa_vars m xs) = VS.mem x xs.
  Proof.
    move=> Hux Huxs.
    case Hmem1: (VS.mem x xs).
    - apply: VS.Lemmas.mem_of_list2.
      apply: inA_ssa_var_map1.
      move/VS.Lemmas.memP: Hmem1 => Hin1.
      exact: (VS.elements_1 Hin1).
    - apply/negP => Hmem2.
      move/negP: Hmem1; apply.
      move: (VS.Lemmas.mem_of_list1 Hmem2) => HinA.
      rewrite /unindexed_vars in Huxs.
      move: (VS.Lemmas.for_all_b xs compat_unindexed_var) => H2.
      rewrite H2 in Huxs.
      move: (inA_ssa_var_map2 Hux Huxs HinA) => {HinA} HinA.
      apply/VS.Lemmas.memP.
      exact: (VS.elements_2 HinA).
  Qed.

  Lemma ssa_var_map2_mem2 m x xs :
    VS.mem x (ssa_var_map2 m xs) ->
    exists y, VS.E.eq x (ssa_var m y) /\ VS.mem y xs.
  Proof.
    rewrite /ssa_var_map2 => Hmem.
    move: (VS.Lemmas.mem_of_list1 Hmem) => {Hmem} HinA.
    move: (inA_ssa_var_map3 HinA) => {HinA} [y [Heq HinA]].
    exists y; split.
    - assumption.
    - apply/VS.Lemmas.memP.
      exact: VS.elements_2.
  Qed.

  Lemma ssa_var_map2_singleton m x :
    unindexed_var x ->
    unindexed_vars (VS.singleton x) ->
    VS.Equal (ssa_var_map2 m (VS.singleton x)) (VS.singleton (ssa_var m x)).
  Proof.
    move=> Hux Huxs v; split => /VS.Lemmas.memP Hmem; apply: VS.Lemmas.memP.
    - move: (ssa_var_map2_mem2 Hmem) => [y [Hy Hmemy]].
      apply: VS.Lemmas.mem_singleton2. rewrite (eqP Hy).
      exact: (ssa_var_preserve m (VS.Lemmas.mem_singleton1 Hmemy)).
    - rewrite (eqP (VS.Lemmas.mem_singleton1 Hmem)) (ssa_var_map2_mem1 m Hux Huxs).
      apply: VS.Lemmas.mem_singleton2. exact: VS.E.eq_refl.
  Qed.

  Lemma ssa_vars_mem1 m v vs :
    unindexed_var v ->
    unindexed_vars vs ->
    VS.mem (ssa_var m v) (ssa_vars m vs) = VS.mem v vs.
  Proof.
    move=> Hux Huxs.
    exact: (ssa_var_map2_mem1 m Hux Huxs).
  Qed.

  Lemma ssa_vars_mem2 m v vs :
    VS.mem v (ssa_vars m vs) ->
    exists x, v = ssa_var m x /\ VS.mem x vs.
  Proof.
    move=> Hmem; move: (ssa_var_map2_mem2 Hmem) => [y [/eqP Hy Hmemy]].
    rewrite Hy.
      by exists y.
  Qed.

  Lemma ssa_vars_mem3 m v i vs :
    unindexed_var v ->
    unindexed_vars vs ->
    VS.mem v vs ->
    i = get_index v m ->
    VS.mem {| vname := vname v; vidx :=i |} (ssa_vars m vs).
  Proof.
    move=> Hux Huxs Hmem Hidx.
    rewrite Hidx.
    rewrite (ssa_vars_mem1 m Hux Huxs).
    assumption.
  Qed.
  *)

End MakeSSA.
