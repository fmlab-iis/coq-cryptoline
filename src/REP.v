
(** * Root entailment problems (REP) *)

From Coq Require Import List ZArith String Recdef.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import EqVar Types EqOrder ZAriths EqStore EqFSets EqFMaps Tactics Seqs.
From BitBlasting Require Import State.
From Cryptoline Require Import Options DSLLite SSALite.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ZSEQM := TStateEqmod SSAVarOrder ZValueType ZSSAStore SSAVS.


(** ** Syntax *)

Local Notation var := SSAVarOrder.t.

Notation zexp := SSALite.eexp.

Notation zbexp := SSALite.ebexp.

Notation vars_zexp := SSALite.vars_eexp.

Notation vars_zexps := SSALite.vars_eexps.

Notation vars_zbexp := SSALite.vars_ebexp.

(** A root entailment problem checks if the premise entails the consequence. *)

Record rep : Type := { premise : zbexp; conseq : zbexp }.

Definition rep_eqn (ps1 ps2 : rep) : bool :=
  (premise ps1 == premise ps2) && (conseq ps1 == conseq ps2).

Lemma rep_eqn_eq ps1 ps2 : rep_eqn ps1 ps2 -> ps1 = ps2.
Proof.
  case: ps1 => [pres1 post1]. case: ps2 => [pres2 post2]. rewrite /rep_eqn /=.
  move/andP=> [/eqP -> /eqP ->]. reflexivity.
Qed.

Lemma rep_eqn_refl ps : rep_eqn ps ps.
Proof. by rewrite /rep_eqn 2!eqxx. Qed.

Lemma rep_eqP (ps1 ps2 : rep) : reflect (ps1 = ps2) (rep_eqn ps1 ps2).
Proof.
  case H: (rep_eqn ps1 ps2).
  - apply: ReflectT. exact: (rep_eqn_eq H).
  - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: rep_eqn_refl.
Qed.

Definition rep_eqMixin := EqMixin rep_eqP.
#[global]
 Canonical rep_eqType := Eval hnf in EqType rep rep_eqMixin.


(** ** Semantics *)

Fixpoint eval_zexp (e : zexp) (s : ZSSAStore.t) : Z :=
  match e with
  | Evar v => ZSSAStore.acc v s
  | Econst n => n
  | Eunop op e => SSALite.eval_eunop op (eval_zexp e s)
  | Ebinop op e1 e2 => SSALite.eval_ebinop op (eval_zexp e1 s) (eval_zexp e2 s)
  | Epow e n => Z.pow (eval_zexp e s) (Z.of_N n)
  end.

Fixpoint eval_zexps (es : seq zexp) (s : ZSSAStore.t) : seq Z :=
  match es with
  | [::] => [::]
  | e::es => (eval_zexp e s)::(eval_zexps es s)
  end.

Fixpoint eval_zbexp (e : zbexp) (s : ZSSAStore.t) : Prop :=
  match e with
  | Etrue => True
  | Eeq e1 e2 => eval_zexp e1 s = eval_zexp e2 s
  | Eeqmod e1 e2 ms => zeqms (eval_zexp e1 s) (eval_zexp e2 s) (eval_zexps ms s)
  | Eand e1 e2 => eval_zbexp e1 s /\ eval_zbexp e2 s
  end.

Definition entails (f g : zbexp) : Prop :=
  forall s, eval_zbexp f s -> eval_zbexp g s.

Definition valid_rep (s : rep) : Prop :=
  entails (premise s) (conseq s).

Definition valid_reps (ss : seq rep) : Prop :=
  forall s, s \in ss -> valid_rep s.


(** ** String outputs *)

Definition string_of_zexp := SSALite.string_of_eexp.

Definition string_of_zexps := SSALite.string_of_eexps.

Definition string_of_zbexp := SSALite.string_of_ebexp.


(** ** Atomic root entailment problems (AREP) *)

Inductive azbexp : Type :=
| Seq : zexp -> zexp -> azbexp
| Seqmod : zexp -> zexp -> seq zexp -> azbexp.

Definition azbexp_eqn (e1 e2 : azbexp) : bool :=
  match e1, e2 with
  | Seq e1 e2, Seq e3 e4 => (Eeq e1 e2) == (Eeq e3 e4)
  | Seqmod e1 e2 ms1, Seqmod e3 e4 ms2 => (Eeqmod e1 e2 ms1) == (Eeqmod e3 e4 ms2)
  | _, _ => false
  end.

Definition string_of_azbexp (e : azbexp) : string :=
  match e with
  | Seq e1 e2 =>
      (string_of_zexp e1 ++ " = " ++ string_of_zexp e2)%string
  | Seqmod e1 e2 ms =>
      (string_of_zexp e1 ++ " = " ++ string_of_zexp e2
                           ++ "(mod [" ++ string_of_zexps ", " ms ++ "])")%string
  end.

Lemma azbexp_eqn_eq (e1 e2 : azbexp) : azbexp_eqn e1 e2 -> e1 = e2.
Proof.
  elim: e1 e2 => [e1 e2 | e1 e2 p1] [] //=.
  - by move=> ? ? /eqP [] -> ->.
  - by move=> ? ? ? /eqP [] -> -> ->.
Qed.

Lemma azbexp_eqn_refl (e : azbexp) : azbexp_eqn e e.
Proof. by elim: e => /=. Qed.

Lemma azbexp_eqn_sym {e1 e2 : azbexp} : azbexp_eqn e1 e2 -> azbexp_eqn e2 e1.
Proof. move=> H; rewrite (azbexp_eqn_eq H); exact: azbexp_eqn_refl. Qed.

Lemma azbexp_eqn_trans {e1 e2 e3 : azbexp} :
  azbexp_eqn e1 e2 -> azbexp_eqn e2 e3 -> azbexp_eqn e1 e3.
Proof.
  move=> H1 H2. rewrite (azbexp_eqn_eq H1) (azbexp_eqn_eq H2).
  exact: azbexp_eqn_refl.
Qed.

Lemma azbexp_eqP (e1 e2 : azbexp) : reflect (e1 = e2) (azbexp_eqn e1 e2).
Proof.
  case H: (azbexp_eqn e1 e2).
  - apply: ReflectT. exact: (azbexp_eqn_eq H).
  - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: azbexp_eqn_refl.
Qed.

Definition azbexp_eqMixin := EqMixin azbexp_eqP.
#[global]
 Canonical azbexp_eqType := Eval hnf in EqType azbexp azbexp_eqMixin.

Definition eval_azbexp (e : azbexp) (s : ZSSAStore.t) : Prop :=
  match e with
  | Seq e1 e2 => eval_zbexp (Eeq e1 e2) s
  | Seqmod e1 e2 ms => eval_zbexp (Eeqmod e1 e2 ms) s
  end.

Record arep : Type := { apremises : seq azbexp; aconseq : azbexp }.

Definition arep_eqn (ps1 ps2 : arep) : bool :=
  (apremises ps1 == apremises ps2) && (aconseq ps1 == aconseq ps2).

Lemma arep_eqn_eq ps1 ps2 : arep_eqn ps1 ps2 -> ps1 = ps2.
Proof.
  case: ps1 => [pres1 post1]. case: ps2 => [pres2 post2]. rewrite /arep_eqn /=.
  move/andP=> [/eqP -> /eqP ->]. reflexivity.
Qed.

Lemma arep_eqn_refl ps : arep_eqn ps ps.
Proof. by rewrite /arep_eqn 2!eqxx. Qed.

Lemma arep_eqP (ps1 ps2 : arep) : reflect (ps1 = ps2) (arep_eqn ps1 ps2).
Proof.
  case H: (arep_eqn ps1 ps2).
  - apply: ReflectT. exact: (arep_eqn_eq H).
  - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: arep_eqn_refl.
Qed.

Definition arep_eqMixin := EqMixin arep_eqP.
#[global]
 Canonical arep_eqType := Eval hnf in EqType arep arep_eqMixin.

Definition valid_arep (s : arep) : Prop :=
  forall st : ZSSAStore.t,
    (forall e : azbexp, e \in (apremises s) -> eval_azbexp e st) ->
    eval_azbexp (aconseq s) st.

(* Check if an atomic root entailment problem is trivial. *)
Definition is_arep_trivial (s : arep) : bool :=
  aconseq s \in apremises s.


(** ** Simplification of atomic root entailment problems *)

Section AtomicRootEntailmentSimpl.

  Import SSALite.

  Fixpoint zexp_subst (p : zexp) (r : zexp) (e : zexp) :=
    if e == p then r
    else match e with
         | Eunop op e => Eunop op (zexp_subst p r e)
         | Ebinop op e1 e2 => Ebinop op  (zexp_subst p r e1) (zexp_subst p r e2)
         | Epow e n => Epow (zexp_subst p r e) n
         | _ => e
         end.

  Definition zexps_subst (p : zexp) (r : zexp) (es : seq zexp) :=
    tmap (zexp_subst p r) es.

  Definition azbexp_subst (p : zexp) (r : zexp) (e : azbexp) :=
    match e with
    | Seq e1 e2 => Seq (zexp_subst p r e1) (zexp_subst p r e2)
    | Seqmod e1 e2 ms => Seqmod (zexp_subst p r e1) (zexp_subst p r e2)
                                (zexps_subst p r ms)
    end.

  Definition subst_azbexps (p r : zexp) (es : seq azbexp) : seq azbexp :=
    tmap (azbexp_subst p r) es.

  Fixpoint single_variables (e : zexp) :=
    match e with
    | Evar v => SSAVS.singleton v
    | Econst _ => SSAVS.empty
    | Eunop _ e => single_variables e
    | Ebinop op e1 e2 =>
        if (op == Eadd) || (op == Esub) then SSAVS.union (single_variables e1) (single_variables e2)
        else SSAVS.empty
    | Epow e _ => SSAVS.empty
    end.

  Fixpoint num_occurrence (v : var) (e : zexp) :=
    match e with
    | Evar x => if x == v then 1 else 0
    | Eunop _ e => num_occurrence v e
    | Ebinop _ e1 e2 => num_occurrence v e1 + num_occurrence v e2
    | Epow e _ => num_occurrence v e
    | _ => 0
    end.

  Fixpoint separate v (e : zexp) (pat : zexp) {struct e} :=
    match e with
    | Evar x => if x == v then Some pat
                else None
    | Eunop Eneg e => if SSAVS.mem v (vars_zexp e) then separate v e (eneg pat)
                      else None
    | Ebinop op e1 e2 =>
       let in1 := SSAVS.mem v (vars_zexp e1) in
       let in2 := SSAVS.mem v (vars_zexp e2) in
       match op, in1, in2 with
       | Eadd, true, false => separate v e1 (esub pat e2)
       | Eadd, false, true => separate v e2 (esub pat e1)
       | Esub, true, false => separate v e1 (eadd pat e2)
       | Esub, false, true => separate v e2 (esub e1 pat)
       | _, _, _ => None
       end
    | _ => None
    end.

  Definition get_rewrite_pattern (e : zexp) :=
    let candidates := SSAVS.filter (fun v => num_occurrence v e == 1) (single_variables e) in
    if SSAVS.cardinal candidates == 0 then
      None
    else
      match SSAVS.min_elt candidates with
      | None => None
      | Some v =>
          match separate v e (econst Z.zero) with
          | None => None
          | Some pat =>
              (*let pat := simplify_eexp pat in*)
              Some (v, pat)
          end
      end.

  Definition is_assignment (e : azbexp) : option (ssavar * zexp) :=
    match e with
    | Seq (Evar v) e => Some (v, e)
    | Seq e (Evar v) => Some (v, e)
    | Seq (Ebinop Eadd (Evar v) el) er => Some (v, Ebinop Esub er el)
    | Seq el (Ebinop Eadd (Evar v) er) => Some (v, Ebinop Esub el er)
    | Seq e1 e2 => get_rewrite_pattern (esub e1 e2)
    | Seqmod _ _ _ => None
    end.

  Definition size_lt {A : Type} (es1 es2 : seq A) : Prop :=
    (size es1 < size es2)%coq_nat.

  (** Simplification procedure *)

  Function simplify_arep_rec
          (visited : seq azbexp) (premises : seq azbexp) (conseq : azbexp)
          {wf (@size_lt azbexp) premises} :=
    match premises with
    | [::] => (rev visited, conseq)
    | e::es =>
      match is_assignment e with
      | None => simplify_arep_rec (e::visited) es conseq
      | Some (p, r) => simplify_arep_rec (subst_azbexps (evar p) r visited)
                                         (subst_azbexps (evar p) r es)
                                         (azbexp_subst (evar p) r conseq)
      end
    end.
  Proof.
    - move=> _ premises _ e es ? [p' r'] p r [] ? ? Ha.
      rewrite /size_lt /subst_azbexps tmap_map size_map /=. exact: Nat.lt_succ_diag_r.
    - move=> _ premises _ e es ? Ha. rewrite /size_lt /=. exact: Nat.lt_succ_diag_r.
    - exact: (well_founded_ltof (seq azbexp) size).
  Defined.

  Definition simplify_arep (s : arep) : arep :=
    let (ps, q) := simplify_arep_rec [::] (apremises s) (aconseq s) in
    {| apremises := ps; aconseq := q |}.


  (** Simplification procedure with precomputed appearing variables *)

  Definition azbexp_subst_vars_cache
             (p : ssavar) (r : zexp) vspr (ve : SSAVS.t * azbexp) :=
    let vs := ve.1 in
    let e := ve.2 in
    if SSAVS.mem p vs then (SSAVS.remove p (SSAVS.union vs vspr),
                            azbexp_subst (evar p) r e)
    else ve.

  Definition subst_azbexps_vars_cache
             (p : ssavar) (r : zexp) vspr (ves : seq (SSAVS.t * azbexp)) :=
    tmap (azbexp_subst_vars_cache p r vspr) ves.

  Function simplify_arep_vars_cache_rec
           (visited : seq (SSAVS.t * azbexp)) (premises : seq (SSAVS.t * azbexp))
           (conseq : (SSAVS.t * azbexp))
           {wf (@size_lt (SSAVS.t * azbexp)) premises} :=
    match premises with
    | [::] => (rev visited, conseq)
    | ve::ves =>
      match is_assignment ve.2 with
      | None => simplify_arep_vars_cache_rec (ve::visited) ves conseq
      | Some (p, r) =>
        simplify_arep_vars_cache_rec (subst_azbexps_vars_cache p r ve.1 visited)
                                     (subst_azbexps_vars_cache p r ve.1 ves)
                                     (azbexp_subst_vars_cache p r ve.1 conseq)
      end
    end.
  Proof.
    - move=> _ premises _ ve ves ? [p' r'] p r [] ? ? Ha.
      rewrite /size_lt /subst_azbexps_vars_cache tmap_map size_map /=.
      exact: Nat.lt_succ_diag_r.
    - move=> _ premises _ e es ? Ha. rewrite /size_lt /=. exact: Nat.lt_succ_diag_r.
    - exact: (well_founded_ltof (seq (SSAVS.t * azbexp)) size).
  Defined.

  Definition vars_azbexp (e : azbexp) : SSAVS.t :=
    match e with
    | Seq e1 e2 => SSAVS.union (vars_eexp e1) (vars_eexp e2)
    | Seqmod e1 e2 ms => SSAVS.union (SSAVS.union (vars_eexp e1) (vars_eexp e2))
                                     (vars_eexps ms)
    end.

  Definition pair_azbexp_with_vars (e : azbexp) : SSAVS.t * azbexp :=
    (vars_azbexp e, e).

  Definition simplify_arep_vars_cache (s : arep) : arep :=
    let vs_ps := tmap pair_azbexp_with_vars (apremises s) in
    let vs_q := pair_azbexp_with_vars (aconseq s) in
    let (vs_ps', vs_q') := simplify_arep_vars_cache_rec [::] vs_ps vs_q in
    {| apremises := (split vs_ps').2; aconseq := vs_q'.2 |}.

End AtomicRootEntailmentSimpl.


(** ** Conversion from REP to AREP *)

Section REP2AREP.

  Fixpoint split_zbexp (e : zbexp) : seq azbexp :=
    match e with
    | Etrue => [::]
    | Eeq e1 e2 => [::Seq e1 e2]
    | Eeqmod e1 e2 ms => [::Seqmod e1 e2 ms]
    | Eand e1 e2 => split_zbexp e1 ++ split_zbexp e2
    end.

  Definition areps_of_rep_full (s : rep) : seq arep :=
    let premises := split_zbexp (premise s) in
    let conseqs := split_zbexp (conseq s) in
    tmap (fun conseq => {| apremises := premises; aconseq := conseq |}) conseqs.

  (* Remove trivial atomic root entailment problems at the end of this conversion. *)
  Definition areps_of_rep (s : rep) : seq arep :=
    let areps := areps_of_rep_full s in
    List.filter (fun s => ~~ (is_arep_trivial s)) areps.

  Definition areps_of_rep_simplified (o : options) (s : rep) : seq arep :=
    if vars_cache_in_rewrite_assignments o then tmap simplify_arep_vars_cache (areps_of_rep s)
    else tmap simplify_arep (areps_of_rep s).

End REP2AREP.


(** ** Properties of root entailment problems *)

Section REPLemmas.

  Lemma entails_eand f g1 g2 :
    entails f (Eand g1 g2) <-> entails f g1 /\ entails f g2.
  Proof.
    split.
    - move=> H; split; move=> s Hf; move: (H s Hf) => /=; tauto.
    - move=> [H1 H2] s Hf; split; move: (H1 s Hf) (H2 s Hf); tauto.
  Qed.

  Lemma size_eval_zexps es s : size (eval_zexps es s) = size es.
  Proof. elim: es => [| e es IH] //=. by rewrite IH. Qed.

  Lemma eval_zbexp_eands_cons e es s :
    eval_zbexp (SSALite.eands (e::es)) s <-> eval_zbexp e s /\ eval_zbexp (SSALite.eands es) s.
  Proof. done. Qed.

  Lemma eval_zbexp_eands_cat es1 es2 s :
    eval_zbexp (SSALite.eands (es1 ++ es2)) s <->
    (eval_zbexp (SSALite.eands es1) s) /\ (eval_zbexp (SSALite.eands es2) s).
  Proof.
    elim: es1 es2 => [| e1 es1 IH] es2 /=.
    - by tauto.
    - split.
      + move=> [He1 H12]. move/IH: H12 => [Hes1 Hes2]. by tauto.
      + move=> [[He1 Hes1] Hes2]. split; first assumption.
        apply/IH. done.
  Qed.

  Lemma eval_zbexp_eands_split_eand e s :
    eval_zbexp (eands (split_eand e)) s <-> eval_zbexp e s.
  Proof.
    elim: e => //=.
    - move=> e1 e2; split.
      + move=> [H _]; assumption.
      + move=> H; tauto.
    - move=> e1 e2 ms; split.
      + move=> [H _]; assumption.
      + move=> H; tauto.
    - move=> e1 IH1 e2 IH2; split.
      + move/eval_zbexp_eands_cat=> [H1 H2]. move: ((proj1 IH1) H1) ((proj1 IH2) H2). tauto.
      + move=> [H1 H2]. move: ((proj2 IH1) H1) ((proj2 IH2) H2) => {}H1 {}H2.
        apply/eval_zbexp_eands_cat. tauto.
  Qed.


  Lemma valid_reps_empty : valid_reps [::].
  Proof. move=> s Hin. discriminate. Qed.

  Lemma valid_reps_hd s ss :
    valid_reps (s::ss) -> valid_rep s.
  Proof. apply. exact: mem_head. Qed.

  Lemma valid_reps_tl s ss :
    valid_reps (s::ss) -> valid_reps ss.
  Proof.
    move=> H st Hin. apply: H. rewrite in_cons Hin orbT. reflexivity.
  Qed.

  Lemma valid_reps_cons s ss :
    valid_reps (s::ss) <-> valid_rep s /\ valid_reps ss.
  Proof.
    split.
    - move=> H; split.
      + exact: (valid_reps_hd H).
      + exact: (valid_reps_tl H).
    - move=> [H1 H2] st Hin. rewrite in_cons in Hin. case/orP: Hin=> Hin.
      + move/eqP: Hin => ?; subst. assumption.
      + exact: (H2 _ Hin).
  Qed.

  Lemma valid_reps_cat ss1 ss2 :
    valid_reps (ss1 ++ ss2) <-> valid_reps ss1 /\ valid_reps ss2.
  Proof.
    elim: ss1 ss2 => [| s1 ss1 IH] ss2 /=.
    - split.
      + move=> H; split; [exact: valid_reps_empty | exact: H].
      + move=> [_ H]; exact: H.
    - split.
      + move/valid_reps_cons=> [H1 H2]. move: (IH ss2) => {IH} [IH1 IH2].
        move: (IH1 H2) => {IH1} [IH11 IH12]. split.
        * apply/valid_reps_cons. tauto.
        * assumption.
      + move=> [/valid_reps_cons [Hs1 Hss1] Hss2]. apply/valid_reps_cons.
        move: (IH ss2) => {IH} [IH1 IH2]. split; first assumption.
        apply: IH2. tauto.
  Qed.

  Lemma valid_reps_cat1 ss1 ss2 :
    valid_reps (ss1 ++ ss2) -> valid_reps ss1.
  Proof. move/valid_reps_cat=> [H1 H2]; assumption. Qed.

  Lemma valid_reps_cat2 ss1 ss2 :
    valid_reps (ss1 ++ ss2) -> valid_reps ss2.
  Proof. move/valid_reps_cat=> [H1 H2]; assumption. Qed.


  Lemma steq_eval_zexp e {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zexp e s1 = eval_zexp e s2.
  Proof.
    elim: e => //=.
    - move=> op e IH Heq. rewrite (IH Heq). reflexivity.
    - move=> op e1 IH1 e2 IH2 Heq. rewrite (IH1 Heq) (IH2 Heq). reflexivity.
    - move=> e IH n Heq. rewrite (IH Heq). reflexivity.
  Qed.

  Lemma steq_eval_zexps es {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zexps es s1 = eval_zexps es s2.
  Proof.
    elim: es => [| e es IH] //= Heq. rewrite (steq_eval_zexp e Heq).
    rewrite (IH Heq). reflexivity.
  Qed.

  Lemma steq_eval_zbexp e {s1 s2} :
    ZSSAStore.Equal s1 s2 -> eval_zbexp e s1 <-> eval_zbexp e s2.
  Proof.
    elim: e => //=.
    - move=> e1 e2 Heq. rewrite (steq_eval_zexp e1 Heq) (steq_eval_zexp e2 Heq).
      tauto.
    - move=> e1 e2 ms Heq. rewrite (steq_eval_zexp e1 Heq) (steq_eval_zexp e2 Heq)
                                   (steq_eval_zexps ms Heq). tauto.
    - move=> e1 IH1 e2 IH2 Heq. move: (IH1 Heq) (IH2 Heq) => {IH1 IH2} IH1 IH2. tauto.
  Qed.


  Lemma eval_zexp_upd {x v s e} :
    ~~ SSAVS.mem x (vars_zexp e) ->
    eval_zexp e (ZSSAStore.upd x v s) = eval_zexp e s.
  Proof.
    elim: e x v s => //=.
    - move=> y x v s Hmem. move: (SSAVS.Lemmas.not_mem_singleton1 Hmem) =>
                           {Hmem} /negP Hne. rewrite eq_sym in Hne.
      rewrite (ZSSAStore.acc_upd_neq Hne). reflexivity.
    - move=> op e IH x v s Hmem. rewrite (IH _ _ _ Hmem). reflexivity.
    - move=> op e1 IH1 e2 IH2 x v s Hmem. move: (SSAVS.Lemmas.not_mem_union1 Hmem) =>
      {Hmem} [Hmem1 Hmem2]. rewrite (IH1 _ _ _ Hmem1) (IH2 _ _ _ Hmem2). reflexivity.
    - move=> e IH n x v s Hmem. rewrite (IH _ _ _ Hmem). reflexivity.
  Qed.

  Lemma eval_zexps_upd {x v s es} :
    ~~ SSAVS.mem x (vars_zexps es) ->
    eval_zexps es (ZSSAStore.upd x v s) = eval_zexps es s.
  Proof.
    elim: es => [| e es IH] //=. rewrite SSAVS.S.Lemmas.union_b negb_or.
    move/andP=> [Hmem1 Hmem2]. rewrite (eval_zexp_upd Hmem1). rewrite (IH Hmem2).
    reflexivity.
  Qed.

  Lemma eval_zbexp_upd {x v s e} :
    ~~ SSAVS.mem x (vars_zbexp e) ->
    eval_zbexp e (ZSSAStore.upd x v s) <-> eval_zbexp e s.
  Proof.
    elim: e x v s => //=.
    - move=> e1 e2 x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      rewrite (eval_zexp_upd Hmem1) (eval_zexp_upd Hmem2). done.
    - move=> e1 e2 ms x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem2 Hmemms].
      rewrite (eval_zexp_upd Hmem1) (eval_zexp_upd Hmem2) (eval_zexps_upd Hmemms). done.
    - move=> e1 IH1 e2 IH2 x v s Hmem.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem) => {Hmem} [Hmem1 Hmem2].
      move: (IH1 x v s Hmem1) (IH2 x v s Hmem2) => {IH1 IH2} IH1 IH2. split; tauto.
  Qed.

  Lemma eval_zexp_upd2 {x1 x2 v1 v2 s e} :
    ~~ SSAVS.mem x1 (vars_zexp e) ->
    ~~ SSAVS.mem x2 (vars_zexp e) ->
    eval_zexp e (ZSSAStore.upd2 x1 v1 x2 v2 s) = eval_zexp e s.
  Proof.
    elim: e x1 v1 x2 v2 s => //=.
    - move=> y x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_singleton1 Hmem1) => {Hmem1} Hmem1.
      move: (SSAVS.Lemmas.not_mem_singleton1 Hmem2) => {Hmem2} Hmem2.
      move/negP: Hmem1 => Hne1. move/negP: Hmem2 => Hne2. rewrite eq_sym in Hne1.
      rewrite eq_sym in Hne2. rewrite (ZSSAStore.acc_upd2_neq Hne1 Hne2). reflexivity.
    - move=> op e IH x1 v1 x2 v2 s Hmem1 Hmem2. rewrite (IH _ _ _ _ _ Hmem1 Hmem2).
      reflexivity.
    - move=> op e1 IH1 e2 IH2 x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      rewrite (IH1 _ _ _ _ _ Hmem11 Hmem21) (IH2 _ _ _ _ _ Hmem12 Hmem22). reflexivity.
    - move=> e IH n x1 v1 x2 v2 s Hmem1 Hmem2. rewrite (IH _ _ _ _ _ Hmem1 Hmem2).
      reflexivity.
  Qed.

  Lemma eval_zexps_upd2 {x1 x2 v1 v2 s es} :
    ~~ SSAVS.mem x1 (vars_zexps es) ->
    ~~ SSAVS.mem x2 (vars_zexps es) ->
    eval_zexps es (ZSSAStore.upd2 x1 v1 x2 v2 s) = eval_zexps es s.
  Proof.
    elim: es => [| e es IH] //=. rewrite 2!SSAVS.S.Lemmas.union_b 2!negb_or.
    move=> /andP [Hmem1e Hmem1es] /andP [Hmem2e Hmem2es].
    rewrite (eval_zexp_upd2 Hmem1e Hmem2e) (IH Hmem1es Hmem2es). reflexivity.
  Qed.

  Lemma eval_zbexp_upd2 {x1 v1 x2 v2 s e} :
    ~~ SSAVS.mem x1 (vars_zbexp e) ->
    ~~ SSAVS.mem x2 (vars_zbexp e) ->
    eval_zbexp e (ZSSAStore.upd2 x1 v1 x2 v2 s) <-> eval_zbexp e s.
  Proof.
    elim: e x1 v1 x2 v2 s => //=.
    - move=> e1 e2 x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      rewrite (eval_zexp_upd2 Hmem11 Hmem21) (eval_zexp_upd2 Hmem12 Hmem22). done.
    - move=> e1 e2 ms x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem12) => {Hmem12} [Hmem12 Hmem1ms].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem22) => {Hmem22} [Hmem22 Hmem2ms].
      rewrite (eval_zexp_upd2 Hmem11 Hmem21) (eval_zexp_upd2 Hmem12 Hmem22)
              (eval_zexps_upd2 Hmem1ms Hmem2ms). done.
    - move=> e1 IH1 e2 IH2 x1 v1 x2 v2 s Hmem1 Hmem2.
      move: (SSAVS.Lemmas.not_mem_union1 Hmem1) => {Hmem1} [Hmem11 Hmem12].
      move: (SSAVS.Lemmas.not_mem_union1 Hmem2) => {Hmem2} [Hmem21 Hmem22].
      move: (IH1 x1 v1 x2 v2 s Hmem11 Hmem21) (IH2 x1 v1 x2 v2 s Hmem12 Hmem22) =>
      {IH1 IH2} IH1 IH2. split; tauto.
  Qed.


  (* State equivalence *)

  Definition zs_eqi (E : SSAVS.t) (s1 s2 : ZSSAStore.t) :=
    forall x, SSAVS.mem x E -> ZSSAStore.acc x s1 = ZSSAStore.acc x s2.

  Lemma zs_eqi_refl E s : zs_eqi E s s.
  Proof. move=> *; reflexivity. Qed.

  Lemma zs_eqi_sym E s1 s2 : zs_eqi E s1 s2 -> zs_eqi E s2 s1.
  Proof. move=> Heqi x Hx. exact: (Logic.eq_sym (Heqi x Hx)). Qed.

  Lemma zs_eqi_trans E s1 s2 s3 :
    zs_eqi E s1 s2 -> zs_eqi E s2 s3 -> zs_eqi E s1 s3.
  Proof.
    move=> H12 H23 x Hx. rewrite (H12 x Hx) (H23 x Hx). reflexivity.
  Qed.

  Lemma zs_eqi_subset E1 E2 s1 s2 :
    SSAVS.subset E1 E2 -> zs_eqi E2 s1 s2 -> zs_eqi E1 s1 s2.
  Proof.
    move=> Hsub Heqi x Hx. exact: (Heqi x (SSAVS.Lemmas.mem_subset Hx Hsub)).
  Qed.

  Lemma zs_eqi_Upd E s1 s2 s3 x v :
    ~~ SSAVS.mem x E -> zs_eqi E s1 s2 ->
    ZSSAStore.Upd x v s2 s3 -> zs_eqi E s1 s3.
  Proof.
    move=> Hx Heqi HUpd y Hy. case Hyx: (y == x).
    - rewrite (eqP Hyx) in Hy. rewrite Hy in Hx. discriminate.
    - move/idP/negP: Hyx => Hyx. rewrite (ZSSAStore.acc_Upd_neq Hyx HUpd).
      exact: (Heqi _ Hy).
  Qed.

  Lemma zs_eqi_upd E s1 s2 x v :
    ~~ SSAVS.mem x E -> zs_eqi E s1 s2 ->
    zs_eqi E s1 (ZSSAStore.upd x v s2).
  Proof.
    move=> Hx Heqi. move: (ZSSAStore.Upd_upd x v s2) => HUpd.
    exact: (zs_eqi_Upd Hx Heqi HUpd).
  Qed.


  (* Slicing *)

  Lemma slice_zbexp_eval vs e s :
    eval_zbexp e s -> eval_zbexp (SSALite.slice_ebexp vs e) s.
  Proof.
    elim: e => //=.
    - move=> e1 e2 H. by case_if.
    - move=> e1 e2 ms H. by case_if.
    - move=> e1 IH1 e2 IH2 [H1 H2].
      case Hs1: (SSALite.slice_ebexp vs e1) => //=; rewrite Hs1 /= in IH1.
      + (case Hs2: (SSALite.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
      + (case Hs2: (SSALite.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
      + (case Hs2: (SSALite.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
      + (case Hs2: (SSALite.slice_ebexp vs e2) => //=); (rewrite Hs2 /= in IH2);
        move: (IH1 H1) (IH2 H2) => /=; tauto.
  Qed.

  Lemma state_eqmod_eval_zexp e s1 s2 :
    ZSEQM.state_eqmod (SSALite.vars_eexp e) s1 s2 ->
    eval_zexp e s1 = eval_zexp e s2.
  Proof.
    elim: e => //=.
    - move=> v. apply. apply: SSALite.VSLemmas.mem_singleton2. exact: eqxx.
    - move=> op e IH Heqm. rewrite (IH Heqm). reflexivity.
    - move=> op e1 IH1 e2 IH2 /ZSEQM.state_eqmod_union1 [Heqm1 Heqm2].
      rewrite (IH1 Heqm1) (IH2 Heqm2). reflexivity.
    - move=> e IH n Heqm. rewrite (IH Heqm). reflexivity.
  Qed.

  Lemma state_eqmod_eval_zexps es s1 s2 :
    ZSEQM.state_eqmod (SSALite.vars_eexps es) s1 s2 ->
    eval_zexps es s1 = eval_zexps es s2.
  Proof.
    elim: es => [| e es IH] //=. move/ZSEQM.state_eqmod_union1 => [Heqm1 Heqm2].
    rewrite (state_eqmod_eval_zexp Heqm1) (IH Heqm2). reflexivity.
  Qed.

  Lemma state_eqmod_eval_zbexp e s1 s2 :
    ZSEQM.state_eqmod (SSALite.vars_ebexp e) s1 s2 ->
    eval_zbexp e s1 -> eval_zbexp e s2.
  Proof.
    elim: e => //=.
    - move=> e1 e2 /ZSEQM.state_eqmod_union1 [Heqm1 Heqm2] H.
      rewrite -(state_eqmod_eval_zexp Heqm1) -(state_eqmod_eval_zexp Heqm2). exact: H.
    - move=> e1 e2 ms /ZSEQM.state_eqmod_union1
                [Heqm1 /ZSEQM.state_eqmod_union1 [Heqm2 Heqm3]] H.
      rewrite -(state_eqmod_eval_zexp Heqm1) -(state_eqmod_eval_zexp Heqm2)
              -(state_eqmod_eval_zexps Heqm3). exact: H.
    - move=> e1 IH1 e2 IH2 /ZSEQM.state_eqmod_union1 [Heqm1 Heqm2] [H1 H2].
      move: (IH1 Heqm1 H1) (IH2 Heqm2 H2). tauto.
  Qed.

End REPLemmas.


(** ** Properties of atomic root entailment problems *)

Section AREPLemmas.

  Lemma is_arep_trivial_valid s : is_arep_trivial s -> valid_arep s.
  Proof.
    case: s => premises conseq. rewrite /is_arep_trivial. move=> Hin s Hpre.
    apply: Hpre. assumption.
  Qed.

End AREPLemmas.


(** ** Properties of AREP simplification *)

Section AREPSimplLemmas.

  Import SSALite.

  Local Notation var := SSAVarOrder.t.

  Lemma zexps_subst_cons p r e es :
    zexps_subst p r (e::es) = zexp_subst p r e :: zexps_subst p r es.
  Proof. rewrite /zexps_subst !tmap_map. reflexivity. Qed.

  Lemma zexps_subst_cat p r es1 es2 :
    zexps_subst p r (es1 ++ es2) = zexps_subst p r es1 ++ zexps_subst p r es2.
  Proof. rewrite /zexps_subst !tmap_map. exact: map_cat. Qed.

  Lemma subst_azbexps_cons p r e es :
    subst_azbexps p r (e::es) = azbexp_subst p r e :: subst_azbexps p r es.
  Proof. rewrite /subst_azbexps !tmap_map. reflexivity. Qed.

  Lemma subst_azbexps_cat p r es1 es2 :
    subst_azbexps p r (es1 ++ es2) = subst_azbexps p r es1 ++ subst_azbexps p r es2.
  Proof. rewrite /subst_azbexps !tmap_map. exact: map_cat. Qed.

  Lemma zexp_subst_valid (e p r : zexp) s :
    eval_zexp p s = eval_zexp r s ->
    eval_zexp e s = eval_zexp (zexp_subst p r e) s.
  Proof.
    elim: e => /=.
    - move=> v Hev. case H: (@Evar SSAVarOrder.T v == p).
      + rewrite -(eqP H) /= in Hev. exact: Hev.
      + reflexivity.
    - move=> n Hev. case H: (Econst SSAVarOrder.T n == p).
      + rewrite -(eqP H) /= in Hev. exact: Hev.
      + reflexivity.
    - move=> op e IH Hev. case H: (Eunop op e == p).
      + rewrite -(eqP H) /= in Hev. exact: Hev.
      + rewrite /=. rewrite (IH Hev). reflexivity.
    - move=> op e1 IH1 e2 IH2 Hev. case H: (Ebinop op e1 e2 == p).
      + rewrite -(eqP H) /= in Hev. exact: Hev.
      + rewrite /=. rewrite (IH1 Hev) (IH2 Hev). reflexivity.
    - move=> e IH n Hev. case H: (Epow e n == p).
      + rewrite -(eqP H) /= in Hev. exact: Hev.
      + rewrite /=. rewrite (IH Hev). reflexivity.
  Qed.

  Lemma zexps_subst_valid (es : seq zexp) (p r : zexp) s :
    eval_zexp p s = eval_zexp r s ->
    eval_zexps es s = eval_zexps (zexps_subst p r es) s.
  Proof.
    elim: es => [| e es IH] //=. move=> Hpr. rewrite zexps_subst_cons /=.
    rewrite (zexp_subst_valid _ Hpr) (IH Hpr). reflexivity.
  Qed.

  Lemma azbexp_subst_valid e p r s :
    eval_zexp p s = eval_zexp r s ->
    eval_azbexp e s <-> eval_azbexp (azbexp_subst p r e) s.
  Proof.
    case: e.
    - move=> e1 e2 /= Hev. rewrite -!(zexp_subst_valid _ Hev). tauto.
    - move=> e1 e2 ms /= Hev. rewrite -!(zexp_subst_valid _ Hev) -(zexps_subst_valid _ Hev).
      tauto.
  Qed.

  Lemma subst_azbexps_valid es p r s :
    eval_zexp p s = eval_zexp r s ->
    (forall e, e \in es -> eval_azbexp e s) <->
    (forall e, e \in (subst_azbexps p r es) -> eval_azbexp e s).
  Proof.
    move=> Hpr. elim: es => [| e es IH] //=. rewrite subst_azbexps_cons. split.
    - move=> Hev f Hin_f. rewrite in_cons in Hin_f. case/orP: Hin_f => Hin_f.
      + rewrite (eqP Hin_f). apply/(azbexp_subst_valid e Hpr). apply: Hev.
        rewrite in_cons eqxx orTb. exact: is_true_true.
      + have Hev': (forall e : azbexp, e \in es -> eval_azbexp e s).
        { move=> g Hin_g; apply: Hev. rewrite in_cons Hin_g orbT.
          exact: is_true_true. }
        case: IH => IH1 IH2. exact: (IH1 Hev' _ Hin_f).
    - move=> Hev f Hin_f. rewrite in_cons in Hin_f. case/orP: Hin_f => Hin_f.
      + rewrite (eqP Hin_f). apply/(azbexp_subst_valid e Hpr). apply: Hev.
        rewrite in_cons eqxx orTb. exact: is_true_true.
      + have Hev': (forall e : azbexp_eqType, e \in subst_azbexps p r es ->
                                                    eval_azbexp e s).
        { move=> g Hin_g; apply: Hev. rewrite in_cons Hin_g orbT.
          exact: is_true_true. }
        case: IH => IH1 IH2. exact: (IH2 Hev' _ Hin_f).
  Qed.

  Lemma separate_some_eval (v : var) (e : zexp) (pat : zexp) (r : zexp) s :
    separate v e pat = Some r ->
    eval_zexp e s = eval_zexp pat s ->
    eval_zexp (Evar v) s = eval_zexp r s.
  Proof.
    elim: e pat r => //=.
    - move=> v' pat r.
      (* It is weird that `case Hv: (v' == v)` does not work as expected without
         the following rewriting with Coq 8.15.2. *)
      move: (Logic.eq_refl (if v' == v then Some pat else None)) => ->.
      case Hv: (v' == v); last by done. case=> ->. move/eqP: Hv => ->. by apply.
    - case. move=> e IH pat r. case Hmem: (SSAVS.mem v (vars_zexp e)); last by done.
      move=> Hsep /= Hev. apply: (IH _ _ Hsep) => /=. rewrite -Hev. ring.
    - case; [| | done].
      + move=> e1 IH1 e2 IH2 pat r.
        (case Hmem1: (SSAVS.mem v (vars_zexp e1)); case Hmem2: (SSAVS.mem v (vars_zexp e2)));
        [done | | | done].
        * move=> Hsep /= Hev. apply: (IH1 _ _ Hsep) => /=. rewrite -Hev. ring.
        * move=> Hsep /= Hev. apply: (IH2 _ _ Hsep) => /=. rewrite -Hev. ring.
      + move=> e1 IH1 e2 IH2 pat r.
        (case Hmem1: (SSAVS.mem v (vars_zexp e1)); case Hmem2: (SSAVS.mem v (vars_zexp e2)));
        [done | | | done].
        * move=> Hsep /= Hev. apply: (IH1 _ _ Hsep) => /=. rewrite -Hev. ring.
        * move=> Hsep /= Hev. apply: (IH2 _ _ Hsep) => /=. rewrite -Hev. ring.
  Qed.

  Lemma get_rewrite_pattern_eval e v r s :
    get_rewrite_pattern e = Some (v, r) ->
    eval_zexp e s = 0%Z ->
    eval_zexp (Evar v) s = eval_zexp r s.
  Proof.
    rewrite /get_rewrite_pattern.
    case: (SSAVS.cardinal
             (SSAVS.filter
                (fun v0 : SSAVS.elt => num_occurrence v0 e == 1) (single_variables e)) == 0);
      first by done.
    case: (SSAVS.min_elt
             (SSAVS.filter
                (fun v0 : SSAVS.elt => num_occurrence v0 e == 1) (single_variables e)));
      last by done.
    move=> v'. case Hsep: (separate v' e (econst Z.zero)); last by done.
    case=> ? ?; subst. move=> Hev. exact: (separate_some_eval Hsep Hev).
  Qed.

  Ltac mytac :=
    repeat match goal with
           | H : Some (_, _) = Some (_, _) |- _ =>
             case: H => ? ?; subst => /=
           | H : match ?e with | Evar _ => _ | _ => _ end = _ |- _ =>
             repeat match goal with
                    | H1 : context f [e] |- _ => move: H1
                    end;
             case: e => //=; intros
           | H : match ?e with | Eadd => _ | _ => _ end = _ |- _ =>
             repeat match goal with
                    | H1 : context f [e] |- _ => move: H1
                    end;
             case: e => //=; intros
           | H : ?l = ?r |- ?r = ?l => symmetry; assumption
           | H : ?l = ?r |- ?l = ?r => assumption
           | |- ?e = ?e => reflexivity
           | |- context f [(?n + ?m - ?m)%Z] => rewrite Z.add_simpl_r
           | H : ?l = ?r |- context f [?l] => rewrite H /=; clear H
           | H : ?l = ?r |- context f [?r] => rewrite -H /=; clear H
           | s : ZSSAStore.t, H1 : get_rewrite_pattern ?e = Some _,
                 H2 : _ = _ |- _ =>
               let H := fresh in
               let HH := fresh in
               (have H: (eval_zexp e s = 0%Z) by (simpl; rewrite -H2; ring));
               (move: (get_rewrite_pattern_eval H1 H) => /= HH);
               clear H1 H
           end.

  Lemma is_assignment_equal e p r s :
    is_assignment e = Some (p, r) ->
    eval_azbexp e s -> eval_zexp (evar p) s = eval_zexp r s.
  Proof.
    case: e => //=. move=> left right.
    (case: left; case: right => //=); intros; mytac; by done.
  Qed.

  Corollary subst_assignment_valid e p r e' s :
    is_assignment e = Some (p, r) -> eval_azbexp e s ->
    eval_azbexp e' s <-> eval_azbexp (azbexp_subst (evar p) r e') s.
  Proof.
    move=> His Hev. exact: (azbexp_subst_valid _ (is_assignment_equal His Hev)).
  Qed.


  Lemma simplify_arep_rec_cons_is_assignment visited e es q p r :
    is_assignment e = Some (p, r) ->
    simplify_arep_rec visited (e::es) q =
    simplify_arep_rec (subst_azbexps (evar p) r visited)
                      (subst_azbexps (evar p) r es)
                      (azbexp_subst (evar p) r q).
  Proof.
    move=> Ha.
    dcase (simplify_arep_rec (subst_azbexps (evar p) r visited)
                             (subst_azbexps (evar p) r es)
                             (azbexp_subst (evar p) r q)) => [[visited' q'] Hs].
    move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_arep_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_arep_rec_complete.
    apply: (R_simplify_arep_rec_2 _ _ _ _ _ _ _ _ Ha _ H). reflexivity.
  Qed.

  Lemma simplify_arep_rec_cons_not_assignment visited e es q :
    is_assignment e = None ->
    simplify_arep_rec visited (e::es) q =
    simplify_arep_rec (e::visited) es q.
  Proof.
    move=> Ha. dcase (simplify_arep_rec (e :: visited) es q) => [[visited' q'] Hs].
    move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_arep_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_arep_rec_complete.
    apply: (R_simplify_arep_rec_1 _ _ _ _ _ _ Ha _ H). reflexivity.
  Qed.

  Lemma simplify_arep_rec_empty visited q :
    simplify_arep_rec visited [::] q = (rev visited, q).
  Proof. reflexivity. Qed.

  Lemma simplify_arep_rec_sound pre ps q ps' q' :
    simplify_arep_rec pre ps q = (ps', q') ->
    (forall s,
        (forall e : azbexp, e \in ps' -> eval_azbexp e s) ->
        eval_azbexp q' s) ->
    (forall s,
        (forall e : azbexp, e \in pre ++ ps -> eval_azbexp e s) ->
        eval_azbexp q s).
  Proof.
    have ->: ps' = (ps', q').1 by reflexivity.
    have ->: q' = (ps', q').2 by reflexivity.
    move: (ps', q'). clear ps' q'. eapply simplify_arep_rec_ind.
    - move=> {pre ps q} pre ps q Hps [ps' q'] [] ? ?; subst => /=.
      move=> Hs s Hev. rewrite cats0 in Hev. apply: Hs.
      move=> e Hin; apply: Hev. rewrite mem_rev in Hin. assumption.
    - move=> {pre ps q} pre ps q e es Hps Ha IH [ps' q']  /= Hrec Hs s He.
      apply: (IH _ Hrec Hs). move=> f Hin. apply: He. rewrite mem_cat in_cons.
      rewrite mem_cat in_cons in Hin. (case/orP: Hin; [case/orP|] => -> //=);
                                        rewrite !orbT; exact: is_true_true.
    - move=> {pre ps q} pre ps q e es Hps pat rep Ha IH [ps' q'] /= Hrec Hs s He.
      have Hes: eval_azbexp e s.
      { apply: He. rewrite mem_cat in_cons eqxx /=. by rewrite orbT. }
      move: (is_assignment_equal Ha Hes) => Hpr.
      apply/(subst_assignment_valid q Ha Hes). apply: (IH _ Hrec Hs).
      move=> f. rewrite -subst_azbexps_cat. move: f.
      apply/(subst_azbexps_valid (pre++es) Hpr). move=> f Hin.
      apply: He. rewrite mem_cat in_cons. rewrite mem_cat in Hin.
      case/orP: Hin => -> //=; rewrite !orbT; exact: is_true_true.
  Qed.


  Lemma simplify_arep_sound (s : arep) :
    valid_arep (simplify_arep s) -> valid_arep s.
  Proof.
    rewrite /valid_arep. case: s => ps q /=. rewrite /simplify_arep /=.
    dcase (simplify_arep_rec [::] ps q) => [[ps' q'] Hs] /=.
    rewrite -(cat0s ps). exact: (simplify_arep_rec_sound Hs).
  Qed.


  (* Rewrite an expression if the pattern appears in the expression *)

  Lemma subst_azbexps_vars_cache_cons p r vspr e es :
    subst_azbexps_vars_cache p r vspr (e::es) =
    azbexp_subst_vars_cache p r vspr e :: subst_azbexps_vars_cache p r vspr es.
  Proof. rewrite /subst_azbexps_vars_cache !tmap_map. reflexivity. Qed.

  Lemma subst_azbexps_vars_cache_cat p r vspr es1 es2 :
    subst_azbexps_vars_cache p r vspr (es1 ++ es2) =
    subst_azbexps_vars_cache p r vspr es1 ++ subst_azbexps_vars_cache p r vspr es2.
  Proof. rewrite /subst_azbexps_vars_cache !tmap_map. exact: map_cat. Qed.

  Lemma subst_assignment_vars_cache_valid e p r e' vspr s :
    is_assignment e = Some (p, r) -> eval_azbexp e s ->
    eval_azbexp e'.2 s <-> eval_azbexp (azbexp_subst_vars_cache p r vspr e').2 s.
  Proof.
    move=> His Hev. rewrite /azbexp_subst_vars_cache. case: (SSAVS.mem p e'.1) => /=.
    - exact: (azbexp_subst_valid _ (is_assignment_equal His Hev)).
    - tauto.
  Qed.

  Lemma subst_azbexps_vars_cache_valid es p r vspr s :
    eval_zexp (evar p) s = eval_zexp r s ->
    (forall e, e \in (split es).2 -> eval_azbexp e s) <->
    (forall e, e \in (split (subst_azbexps_vars_cache p r vspr es)).2 ->
                     eval_azbexp e s).
  Proof.
    move=> H. elim: es => [| [el er] es IH] //=.
    rewrite subst_azbexps_vars_cache_cons. case Hses: (split es) => [esl esr] /=.
    case Hsube: (azbexp_subst_vars_cache p r vspr (el, er)) => [sel ser].
    case Hsubes: (split (subst_azbexps_vars_cache p r vspr es)) => [sesl sesr] /=.
    case: IH => [IH1 IH2]. split=> Hs e Hin.
    - case/orP: Hin=> Hin.
      + move: Hsube. rewrite /azbexp_subst_vars_cache /=.
        case: (SSAVS.mem p el) => /=.
        * case=> ? ?; subst. rewrite (eqP Hin).
          apply/(@azbexp_subst_valid er _ _ _ H). apply: Hs. by rewrite in_cons eqxx.
        * case=> ? ?; subst. apply: Hs. by rewrite in_cons Hin.
      + apply: IH1.
        * rewrite Hses /=. move=> f Hinf; apply: Hs. by rewrite in_cons Hinf orbT.
        * rewrite Hsubes /=. assumption.
    - case/orP: Hin=> Hin.
      + move: Hsube. rewrite /azbexp_subst_vars_cache /=.
        case: (SSAVS.mem p el) => /=.
        * case=> ? ?; subst. rewrite (eqP Hin).
          apply/(@azbexp_subst_valid er _ _ _ H). apply: Hs. by rewrite in_cons eqxx.
        * case=> ? ?; subst. apply: Hs. by rewrite in_cons Hin.
      + apply: IH2.
        * rewrite Hsubes /=. move=> f Hinf; apply: Hs. by rewrite in_cons Hinf orbT.
        * rewrite Hses /=. assumption.
  Qed.

  Lemma simplify_arep_vars_cache_rec_cons_is_assignment visited ve ves q p r :
    is_assignment ve.2 = Some (p, r) ->
    simplify_arep_vars_cache_rec visited (ve::ves) q =
    simplify_arep_vars_cache_rec (subst_azbexps_vars_cache p r ve.1 visited)
                                 (subst_azbexps_vars_cache p r ve.1 ves)
                                 (azbexp_subst_vars_cache p r ve.1 q).
  Proof.
    move=> Ha.
    dcase (simplify_arep_vars_cache_rec (subst_azbexps_vars_cache p r ve.1 visited)
                                         (subst_azbexps_vars_cache p r ve.1 ves)
                                         (azbexp_subst_vars_cache p r ve.1 q)) =>
    [[visited' q'] Hs]. move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_arep_vars_cache_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_arep_vars_cache_rec_complete.
    exact: (R_simplify_arep_vars_cache_rec_2 _ _ _ _ _ (Logic.eq_refl _) _ _ Ha _ H).
  Qed.

  Lemma simplify_arep_vars_cache_rec_cons_not_assignment visited ve ves q :
    is_assignment ve.2 = None ->
    simplify_arep_vars_cache_rec visited (ve::ves) q =
    simplify_arep_vars_cache_rec (ve::visited) ves q.
  Proof.
    move=> Ha. dcase (simplify_arep_vars_cache_rec (ve :: visited) ves q) =>
               [[visited' q'] Hs]. move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_arep_vars_cache_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_arep_vars_cache_rec_complete.
    exact: (R_simplify_arep_vars_cache_rec_1 _ _ _ _ _ (Logic.eq_refl _) Ha _ H).
  Qed.

  Lemma simplify_arep_vars_cache_rec_empty visited q :
    simplify_arep_vars_cache_rec visited [::] q = (rev visited, q).
  Proof. reflexivity. Qed.

  Lemma simplify_arep_vars_cache_rec_sound pre ps q ps' q' :
    simplify_arep_vars_cache_rec pre ps q = (ps', q') ->
    (forall s,
        (forall e : azbexp, e \in (split ps').2 -> eval_azbexp e s) ->
        eval_azbexp q'.2 s) ->
    (forall s,
        (forall e : azbexp, e \in (split (pre ++ ps)).2 -> eval_azbexp e s) ->
        eval_azbexp q.2 s).
  Proof.
    have ->: ps' = (ps', q').1 by reflexivity.
    have ->: q' = (ps', q').2 by reflexivity.
    move: (ps', q'). clear ps' q'. eapply simplify_arep_vars_cache_rec_ind.
    - move=> {pre ps q} pre ps q Hps [ps' q'] [] ? ?; subst => /=.
      move=> Hs s Hev. rewrite cats0 in Hev. apply: Hs.
      move=> e Hin; apply: Hev. rewrite in_split_rev_r in Hin. assumption.
    - move=> {pre ps q} pre ps q e es Hps Ha IH [ps' q']  /= Hrec Hs s He.
      apply: (IH _ Hrec Hs). move=> f Hin. apply: He.
      rewrite 2!split_cat 2!mem_cat in Hin *. rewrite split_cons in_cons.
      rewrite Bool.orb_assoc. rewrite (Bool.orb_comm _ (f == e.2)).
      rewrite -in_cons. rewrite split_cons /= in Hin. assumption.
    - move=> {pre ps q} pre ps q e es Hps pat rep Ha IH [ps' q'] /= Hrec Hs s He.
      have Hes: eval_azbexp (e.2) s.
      { apply: He. rewrite split_cat mem_cat split_cons in_cons eqxx orbT /=.
        reflexivity. }
      move: (is_assignment_equal Ha Hes) => Hpr.
      apply/(subst_assignment_vars_cache_valid _ _ Ha Hes). apply: (IH _ Hrec Hs).
      move=> f. rewrite -subst_azbexps_vars_cache_cat. move: f.
      apply/(subst_azbexps_vars_cache_valid (pre++es) _ Hpr). move=> f Hin.
      apply: He. rewrite 2!split_cat 2!mem_cat in Hin *.
      rewrite split_cons in_cons. rewrite (Bool.orb_comm (f == e.2)).
      rewrite Bool.orb_assoc. by rewrite Hin.
  Qed.


  Lemma split_map_pair_azbexp_with_vars (es : seq azbexp) :
    (split (map pair_azbexp_with_vars es)).2 = es.
  Proof.
    elim: es => [| e es IH] //=. move: IH.
    dcase (split [seq pair_azbexp_with_vars i | i <- es]) => [[vs es'] Hs].
    rewrite Hs /=. move=> ->. reflexivity.
  Qed.

  Lemma simplify_arep_vars_cache_sound (s : arep) :
    valid_arep (simplify_arep_vars_cache s) -> valid_arep s.
  Proof.
    rewrite /valid_arep. case: s => ps q /=. rewrite /simplify_arep_vars_cache /=.
    rewrite tmap_map.
    dcase (simplify_arep_vars_cache_rec [::] [seq pair_azbexp_with_vars i | i <- ps]
                                         (pair_azbexp_with_vars q)) => [[vs_ps' vs_q'] Hsp].
    rewrite Hsp /=. move=> H s Hs.
    apply: (simplify_arep_vars_cache_rec_sound Hsp H). rewrite cat0s.
    rewrite split_map_pair_azbexp_with_vars. assumption.
  Qed.

End AREPSimplLemmas.


(** ** Properties of the conversion from REP to AREP *)

Section REP2AREPLemmas.

  Lemma split_zbexp_mem ze s :
    eval_zbexp ze s ->
    forall pe, pe \in split_zbexp ze -> eval_azbexp pe s.
  Proof.
    elim: ze => //=.
    - move=> ze1 ze2 Hze pe. case/orP=> [/eqP -> | H]; [assumption | discriminate].
    - move=> ze1 ze2 zm Hpe pe. case/orP=> [/eqP -> | H];
                                             [assumption | discriminate].
    - move=> ze1 IH1 ze2 IH2 [Hze1 Hze2] pe. rewrite mem_cat. case/orP=> Hmem.
      + exact: (IH1 Hze1 _ Hmem).
      + exact: (IH2 Hze2 _ Hmem).
  Qed.

  Lemma split_zbexp_all ze s :
    (forall pe, pe \in split_zbexp ze -> eval_azbexp pe s) ->
    eval_zbexp ze s.
  Proof.
    elim: ze => //=.
    - move=> ze1 ze2 Hpe. apply: (Hpe (Seq ze1 ze2)). by rewrite in_cons eqxx.
    - move=> ze1 ze2 zm Hpe. apply: (Hpe (Seqmod ze1 ze2 zm)).
        by rewrite in_cons eqxx.
    - move=> ze1 IH1 ze2 IH2 Hpe. split.
      + apply: IH1 => pe Hmem. apply: Hpe. by rewrite mem_cat Hmem.
      + apply: IH2 => pe Hmem. apply: Hpe. by rewrite mem_cat Hmem orbT.
  Qed.

  Lemma areps_of_rep_equiv_full zs :
    (forall ps, ps \in areps_of_rep zs -> valid_arep ps) <->
      (forall ps, ps \in areps_of_rep_full zs -> valid_arep ps).
  Proof.
    case: zs => premises conseq. rewrite /areps_of_rep. split=> H ps Hmem.
    - case Htr: (is_arep_trivial ps).
      + exact: (is_arep_trivial_valid Htr).
      + apply: H. rewrite mem_filter Htr /=. assumption.
    - apply: H. rewrite mem_filter in Hmem. move/andP: Hmem => [_ H]. assumption.
  Qed.

  Lemma areps_of_rep_full_sound zs :
    (forall ps, ps \in areps_of_rep_full zs -> valid_arep ps) ->
    valid_rep zs.
  Proof.
    case: zs => zf zq. elim: zq zf => //=.
    - move=> e1 e2 zf /= Hps s /= Hzf. rewrite /areps_of_rep_full /= in Hps.
      apply: (Hps {| apremises := split_zbexp zf; aconseq := Seq e1 e2 |});
        first by rewrite in_cons eqxx.
      move=> {Hps} pe /= Hmem. exact: (split_zbexp_mem Hzf Hmem).
    - move=> e1 e2 m zf Hps s /= Hzf. rewrite /areps_of_rep_full /= in Hps.
      apply: (Hps {| apremises := split_zbexp zf; aconseq := Seqmod e1 e2 m |});
        first by rewrite in_cons eqxx.
      move=> {Hps} pe /= Hmem. exact: (split_zbexp_mem Hzf Hmem).
    - move=> e1 IH1 e2 IH2 zf Hps s /= Hzf. rewrite /areps_of_rep_full /= in Hps.
      rewrite tmap_map in Hps. split.
      + apply: (IH1 zf _ s Hzf) => /=. rewrite /areps_of_rep_full tmap_map.
        move=> ps Hin. apply: Hps. rewrite map_cat mem_cat. apply/orP; left.
        assumption.
      + apply: (IH2 zf _ s Hzf) => /=. rewrite /areps_of_rep_full tmap_map.
        move=> ps Hin. apply: Hps. rewrite map_cat mem_cat. apply/orP; right.
        assumption.
  Qed.

  Theorem areps_of_rep_sound zs :
    (forall ps, ps \in areps_of_rep zs -> valid_arep ps) ->
    valid_rep zs.
  Proof.
    move=> H. apply: areps_of_rep_full_sound. apply/areps_of_rep_equiv_full.
    assumption.
  Qed.

  Theorem areps_of_rep_simplified_sound o zs :
    (forall ps, ps \in areps_of_rep_simplified o zs -> valid_arep ps) ->
    valid_rep zs.
  Proof.
    move=> H. apply: areps_of_rep_sound. move=> ps Hin.
    case Ho: (vars_cache_in_rewrite_assignments o).
    - apply: simplify_arep_vars_cache_sound. apply: H.
      rewrite /areps_of_rep_simplified Ho. rewrite tmap_map.
      apply: map_f. assumption.
    - apply: simplify_arep_sound. apply: H.
      rewrite /areps_of_rep_simplified Ho. rewrite tmap_map.
      apply: map_f. assumption.
  Qed.

End REP2AREPLemmas.
