
(** Ideal membership problem together with the validator of CAS answers. *)

From Coq Require Import List Arith ZArith String Lia BinaryString.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder Nats ZAriths Seqs Store Tactics Compatibility FSets.
From BitBlasting Require Import State.
From Cryptoline Require Import Options DSL SSA ZSSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** An atomic root entailment problem is a root entailment where the
    consequence contains no conjunction. *)
Section AtomicRootEntailment.

  (* Atomic zbexp *)

  Inductive azbexp : Type :=
  | Seq : ZSSA.zexp -> ZSSA.zexp -> azbexp
  | Seqmod : ZSSA.zexp -> ZSSA.zexp -> seq ZSSA.zexp -> azbexp.

  Definition azbexp_eqn (e1 e2 : azbexp) : bool :=
    match e1, e2 with
    | Seq e1 e2, Seq e3 e4 => (Eeq e1 e2) == (Eeq e3 e4)
    | Seqmod e1 e2 ms1, Seqmod e3 e4 ms2 => (Eeqmod e1 e2 ms1) == (Eeqmod e3 e4 ms2)
    | _, _ => false
    end.

  Definition string_of_azbexp (e : azbexp) : string :=
    match e with
    | Seq e1 e2 =>
        (ZSSA.string_of_zexp e1 ++ " = " ++ ZSSA.string_of_zexp e2)%string
    | Seqmod e1 e2 ms =>
        (ZSSA.string_of_zexp e1 ++ " = " ++ ZSSA.string_of_zexp e2
                             ++ "(mod [" ++ ZSSA.string_of_zexps ", " ms ++ "])")%string
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
  Canonical azbexp_eqType := Eval hnf in EqType azbexp azbexp_eqMixin.

  Definition eval_azbexp (e : azbexp) (s : ZSSAStore.t) : Prop :=
    match e with
    | Seq e1 e2 => ZSSA.eval_zbexp (Eeq e1 e2) s
    | Seqmod e1 e2 ms => ZSSA.eval_zbexp (Eeqmod e1 e2 ms) s
    end.

  (** Atomic root entailment problem *)
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
  Canonical arep_eqType := Eval hnf in EqType arep arep_eqMixin.

  Definition valid_arep (s : arep) : Prop :=
    forall st : ZSSAStore.t,
      (forall e : azbexp, e \in (apremises s) -> eval_azbexp e st) ->
      eval_azbexp (aconseq s) st.

  (* Check if an atomic root entailment problem is trivial. *)
  Definition is_arep_trivial (s : arep) : bool :=
    aconseq s \in apremises s.

  Lemma is_arep_trivial_valid s : is_arep_trivial s -> valid_arep s.
  Proof.
    case: s => premises conseq. rewrite /is_arep_trivial. move=> Hin s Hpre.
    apply: Hpre. assumption.
  Qed.

End AtomicRootEntailment.



From Coq Require Import Recdef.

(* Simplification of arep *)
Section AtomicRootEntailmentSimpl.

  Import SSA ZSSA.

  Local Notation var := SSAVarOrder.t.

  Fixpoint zexp_subst (p : ZSSA.zexp) (r : ZSSA.zexp) (e : ZSSA.zexp) :=
    if e == p then r
    else match e with
         | Eunop op e => Eunop op (zexp_subst p r e)
         | Ebinop op e1 e2 => Ebinop op  (zexp_subst p r e1) (zexp_subst p r e2)
         | Epow e n => Epow (zexp_subst p r e) n
         | _ => e
         end.

  Definition zexps_subst (p : ZSSA.zexp) (r : ZSSA.zexp) (es : seq ZSSA.zexp) :=
    tmap (zexp_subst p r) es.

  Definition azbexp_subst (p : ZSSA.zexp) (r : ZSSA.zexp) (e : azbexp) :=
    match e with
    | Seq e1 e2 => Seq (zexp_subst p r e1) (zexp_subst p r e2)
    | Seqmod e1 e2 ms => Seqmod (zexp_subst p r e1) (zexp_subst p r e2)
                                (zexps_subst p r ms)
    end.

  Definition subst_azbexps (p r : zexp) (es : seq azbexp) : seq azbexp :=
    tmap (azbexp_subst p r) es.

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

  Lemma zexp_subst_valid (e p r : ZSSA.zexp) s :
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

  Lemma zexps_subst_valid (es : seq ZSSA.zexp) (p r : ZSSA.zexp) s :
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

  Definition is_assignment (e : azbexp) : option (ssavar * ZSSA.zexp) :=
    match e with
    | Seq (Evar v) e => Some (v, e)
    | Seq e (Evar v) => Some (v, e)
    | Seq (Ebinop Eadd (Evar v) el) er => Some (v, Ebinop Esub er el)
    | Seq el (Ebinop Eadd (Evar v) er) => Some (v, Ebinop Esub el er)
    | Seq e1 e2 => get_rewrite_pattern (esub e1 e2)
    | Seqmod _ _ _ => None
    end.

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



  Definition size_lt {A : Type} (es1 es2 : seq A) : Prop :=
    (size es1 < size es2)%coq_nat.

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


  Definition simplify_arep (s : arep) : arep :=
    let (ps, q) := simplify_arep_rec [::] (apremises s) (aconseq s) in
    {| apremises := ps; aconseq := q |}.

  Lemma simplify_arep_sound (s : arep) :
    valid_arep (simplify_arep s) -> valid_arep s.
  Proof.
    rewrite /valid_arep. case: s => ps q /=. rewrite /simplify_arep /=.
    dcase (simplify_arep_rec [::] ps q) => [[ps' q'] Hs] /=.
    rewrite -(cat0s ps). exact: (simplify_arep_rec_sound Hs).
  Qed.



  (* Rewrite an expression if the pattern appears in the expression *)

  Definition azbexp_subst_vars_cache
             (p : ssavar) (r : ZSSA.zexp) vspr (ve : SSAVS.t * azbexp) :=
    let vs := ve.1 in
    let e := ve.2 in
    if SSAVS.mem p vs then (SSAVS.remove p (SSAVS.union vs vspr),
                            azbexp_subst (evar p) r e)
    else ve.

  Definition subst_azbexps_vars_cache
             (p : ssavar) (r : ZSSA.zexp) vspr (ves : seq (SSAVS.t * azbexp)) :=
    tmap (azbexp_subst_vars_cache p r vspr) ves.

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


  Definition vars_azbexp (e : azbexp) : SSAVS.t :=
    match e with
    | Seq e1 e2 => SSAVS.union (vars_eexp e1) (vars_eexp e2)
    | Seqmod e1 e2 ms => SSAVS.union (SSAVS.union (vars_eexp e1) (vars_eexp e2))
                                     (vars_eexps ms)
    end.

  Definition pair_azbexp_with_vars (e : azbexp) : SSAVS.t * azbexp :=
    (vars_azbexp e, e).

  Lemma split_map_pair_azbexp_with_vars (es : seq azbexp) :
    (split (map pair_azbexp_with_vars es)).2 = es.
  Proof.
    elim: es => [| e es IH] //=. move: IH.
    dcase (split [seq pair_azbexp_with_vars i | i <- es]) => [[vs es'] Hs].
    rewrite Hs /=. move=> ->. reflexivity.
  Qed.

  Definition simplify_arep_vars_cache (s : arep) : arep :=
    let vs_ps := tmap pair_azbexp_with_vars (apremises s) in
    let vs_q := pair_azbexp_with_vars (aconseq s) in
    let (vs_ps', vs_q') := simplify_arep_vars_cache_rec [::] vs_ps vs_q in
    {| apremises := (split vs_ps').2; aconseq := vs_q'.2 |}.

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

End AtomicRootEntailmentSimpl.



(* Convert rep to arep *)

Section REP2AREP.

  Fixpoint split_zbexp (e : ZSSA.zbexp) : seq azbexp :=
    match e with
    | Etrue => [::]
    | Eeq e1 e2 => [::Seq e1 e2]
    | Eeqmod e1 e2 ms => [::Seqmod e1 e2 ms]
    | Eand e1 e2 => split_zbexp e1 ++ split_zbexp e2
    end.

  Definition areps_of_rep_full (s : ZSSA.rep) : seq arep :=
    let premises := split_zbexp (ZSSA.premise s) in
    let conseqs := split_zbexp (ZSSA.conseq s) in
    tmap (fun conseq => {| apremises := premises; aconseq := conseq |}) conseqs.

  (* Remove trivial atomic root entailment problems at the end of this conversion. *)
  Definition areps_of_rep (s : ZSSA.rep) : seq arep :=
    let areps := areps_of_rep_full s in
    List.filter (fun s => ~~ (is_arep_trivial s)) areps.

  Definition areps_of_rep_simplified (o : options) (s : ZSSA.rep) : seq arep :=
    if vars_cache_in_rewrite_assignments o then tmap simplify_arep_vars_cache (areps_of_rep s)
    else tmap simplify_arep (areps_of_rep s).

  Lemma split_zbexp_mem ze s :
    ZSSA.eval_zbexp ze s ->
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
    ZSSA.eval_zbexp ze s.
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
    ZSSA.valid_rep zs.
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
    ZSSA.valid_rep zs.
  Proof.
    move=> H. apply: areps_of_rep_full_sound. apply/areps_of_rep_equiv_full.
    assumption.
  Qed.

  Theorem areps_of_rep_simplified_sound o zs :
    (forall ps, ps \in areps_of_rep_simplified o zs -> valid_arep ps) ->
    ZSSA.valid_rep zs.
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

End REP2AREP.



From Coq Require Import Ring_polynom.

(*
  R := Z
  rO := 0
  rI := 1
  radd := Z.add
  rmul := Z.mul
  rsub := Z.sub
  ropp := Z.opp
  C := Z
  cO := 0
  cI := 1
  cadd := Z.add
  cmul := Z.mul
  csub := Z.sub
  copp := Z.opp
  ceqb := Z.eqb
  phi := id
  req := Z.eq
  Cpow := Z
  Cp_phi := Z.of_N
  rpow := Z.pow
  cdiv := Z.quotrem
  RelationClasses.Equivalence req := RelationClasses.eq_equivalence
  ring_eq_ext := Zeqe.
  ring_theory := Zth
  almost_ring_theory := Zath
  power_theory := Zpower_theory
  ring_morph := Zrm
  div_theory := Zdt
  sign_theory := Zst
*)
Section ZRing.

  Local Open Scope Z_scope.

  (* Lemmas about the morphism from C to R *)
  Lemma Zrm_eqb_eq : forall x y : Z, Z.eqb x y -> Z.eq (id x) (id y).
  Proof. move=> x y /Z.eqb_eq. by apply. Qed.

  (* A ring_morph (identity function) from C to R *)
  Definition Zrm :=
    IDmorph 0 1 Z.add Z.mul Z.sub Z.opp RelationClasses.eq_equivalence
            Z.eqb Zrm_eqb_eq.

  (* almost_ring_theory *)
  Definition Zath := Rth_ARth RelationClasses.eq_equivalence Zeqe Zth.

  (* Lemma for sign_theory *)
  Lemma Zsign_spec : forall c c' : Z, get_signZ c = Some c' -> Z.eqb c (Z.opp c').
  Proof.
    move=> x y. rewrite /get_signZ. case: x => //=. move=> p [] <- /=.
    exact: Pos.eqb_refl.
  Qed.

  (* A sign_theory. The built-in sign_theory get_signZ_th relies on an old
     comparison function Zeq_bool. *)
  Definition Zst := @mksign_th Z Z.opp Z.eqb get_signZ Zsign_spec.

  (* div_theory *)
  Definition Zdt := Ztriv_div_th Zsth id.

  (* *)

  Definition Znorm_subst : PExpr Z -> Pol Z :=
    @norm_subst Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb Z.quotrem 0 [::].

  Definition ZPeq : Pol Z -> Pol Z -> bool := @Peq Z Z.eqb.

  Definition ZPEeval : seq Z -> PExpr Z -> Z :=
    @PEeval Z 0 1 Z.add Z.mul Z.sub Z.opp Z id Z Z.of_N Z.pow.

  Definition Zinterp_PElist :=
    @interp_PElist Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eq
                   Z id Z Z.of_N Z.pow.

  Definition Zmk_monpol_list :=
    @mk_monpol_list Z 0 1 Z.add Z.mul Z.sub Z.opp
                    Z.eqb Z.quotrem.

  Definition ZPeq_ok :=
    @Peq_ok Z 0 1 Z.add Z.mul Z.sub Z.opp
            Z.eq RelationClasses.eq_equivalence Zeqe
            Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb id
            Zrm.

  Definition ZPeq_spec :=
    @Peq_spec Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eq RelationClasses.eq_equivalence Zeqe
              Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb id Zrm.

  Definition Znorm_subst_spec :=
    @norm_subst_spec Z 0 1 Z.add Z.mul Z.sub Z.opp
                     Z.eq RelationClasses.eq_equivalence Zeqe Zath
                     Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb id Zrm
                     Z Z.of_N Z.pow Zpower_theory Z.quotrem Zdt.

  Definition Zring_rw_correct :=
    @ring_rw_correct Z 0 1 Z.add Z.mul Z.sub Z.opp
                     Z.eq RelationClasses.eq_equivalence Zeqe Zath
                     Z 0 1 Z.add Z.mul Z.sub
                     Z.opp Z.eqb id Zrm
                     Z Z.of_N Z.pow Zpower_theory
                     Z.quotrem Zdt get_signZ Zst.

  Definition ZPphi_dev_ok :=
    @Pphi_dev_ok Z 0 1 Z.add Z.mul Z.sub Z.opp
                 Z.eq RelationClasses.eq_equivalence Zeqe Zath
                 Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb id Zrm get_signZ Zst.

  Definition ZPExpr_eq := Field_theory.PExpr_eq Z.eqb.

  (* Two polynomials are syntactically equal after normalization *)
  Definition zpexpr_eqb (p1 p2 : PExpr Z) : bool :=
    ZPeq (Znorm_subst p1) (Znorm_subst p2).

  Lemma zpexpr_eq_zpeeval s e1 e2 :
    ZPExpr_eq e1 e2 -> ZPEeval s e1 = ZPEeval s e2.
  Proof.
    elim: e1 e2 => //=.
    - move=> c [] //=. move=> d Heq. apply/Z.eqb_eq. assumption.
    - move=> j [] //=. move=> k Heq. move/Pos.eqb_eq: Heq => ->. reflexivity.
    - move=> e1 IH1 e2 IH2 [] //=. move=> e3 e4. case Heq13: (ZPExpr_eq e1 e3) => //=.
      move=> Heq24. rewrite (IH1 _ Heq13) (IH2 _ Heq24). reflexivity.
    - move=> e1 IH1 e2 IH2 [] //=. move=> e3 e4. case Heq13: (ZPExpr_eq e1 e3) => //=.
      move=> Heq24. rewrite (IH1 _ Heq13) (IH2 _ Heq24). reflexivity.
    - move=> e1 IH1 e2 IH2 [] //=. move=> e3 e4. case Heq13: (ZPExpr_eq e1 e3) => //=.
      move=> Heq24. rewrite (IH1 _ Heq13) (IH2 _ Heq24). reflexivity.
    - move=> e1 IH1 [] //=. move=> e2 Heq. rewrite (IH1 _ Heq). reflexivity.
    - move=> e1 IH1 n [] //=. move=> e2 m. case Heq: (n =? m)%num => //=.
      move=> Heq12. rewrite (IH1 _ Heq12). move/N.eqb_eq: Heq => ->. reflexivity.
  Qed.

  Fixpoint zpexpr_all0 l (ps : seq (PExpr Z)) : Prop :=
    match ps with
    | [::] => True
    | hd::tl => ZPEeval l hd = 0 /\ zpexpr_all0 l tl
    end.

  Lemma zpexpr_all0_cons l e es :
    zpexpr_all0 l (e::es) <-> ZPEeval l e = 0 /\ zpexpr_all0 l es.
  Proof. done. Qed.

  Lemma zpexpr_all0_rcons l es e :
    zpexpr_all0 l (rcons es e) <-> zpexpr_all0 l es /\ ZPEeval l e = 0.
  Proof.
    elim: es e => [| hd tl IH] //=.
    - move=> e. tauto.
    - move=> e. move: (IH e) => [H1 H2]. tauto.
  Qed.

  Lemma zpexpr_all0_cat l es1 es2 :
    zpexpr_all0 l (es1 ++ es2) <-> zpexpr_all0 l es1 /\ zpexpr_all0 l es2.
  Proof.
    elim: es1 es2 => [| e1 es1 IH] //=.
    - tauto.
    - move=> es2. move: (IH es2) => [H1 H2]. tauto.
  Qed.

  Lemma zpexpr_all0_rev l es : zpexpr_all0 l (rev es) <-> zpexpr_all0 l es.
  Proof.
    elim: es => [| e es IH] //=. rewrite rev_cons. rewrite zpexpr_all0_rcons. tauto.
  Qed.

  Lemma zpexpr_all0_in l ps p :
    zpexpr_all0 l ps -> List.In p ps -> ZPEeval l p = 0%Z.
  Proof.
    elim: ps => [| e es IH] //=. move=> [H1 H2] [] H.
    - rewrite -H. assumption.
    - exact: (IH H2 H).
  Qed.

  (* (\forall p \in ps, p = 0) -> q1 = q2 *)
  Definition zpimply_eq ps q1 q2 :=
    forall l : list Z,
      zpexpr_all0 l ps -> ZPEeval l q1 = ZPEeval l q2.

  Lemma ZPEeval0 l : ZPEeval l PEO = 0.
  Proof. reflexivity. Qed.

  Lemma ZPEeval1 l : ZPEeval l PEI = 1.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_const l c : ZPEeval l (PEc c) = c.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_add l e1 e2 : ZPEeval l (PEadd e1 e2) = ZPEeval l e1 + ZPEeval l e2.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_sub l e1 e2 : ZPEeval l (PEsub e1 e2) = ZPEeval l e1 - ZPEeval l e2.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_mul l e1 e2 : ZPEeval l (PEmul e1 e2) = ZPEeval l e1 * ZPEeval l e2.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_opp l e : ZPEeval l (PEopp e) = - ZPEeval l e.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_pow l e n : ZPEeval l (PEpow e n) = Z.pow (ZPEeval l e) (Z.of_N n).
  Proof. reflexivity. Qed.

  Definition peadds {A : Type} es : PExpr A := foldl (@PEadd A) PEO es.

  Definition pemuls {A : Type} (es1 es2 : seq (PExpr A)) :=
    mapr (fun '(x, y) => PEmul x y) (zipr es1 es2).

  Lemma peadds_rcons {A : Type} ms (m : PExpr A) :
    peadds (rcons ms m) = PEadd (peadds ms) m.
  Proof. rewrite /peadds. rewrite foldl_rcons. reflexivity. Qed.

  Lemma pemulss0 {A : Type} (xs : seq (PExpr A)) : pemuls xs nil = nil.
  Proof. by case: xs. Qed.

  Lemma pemuls0s {A : Type} (ys : seq (PExpr A)) : pemuls nil ys = nil.
  Proof. by case: ys. Qed.

  Lemma pemuls_cons {A : Type} (x : PExpr A) xs y ys :
    pemuls (x::xs) (y::ys) = (PEmul x y)::(pemuls xs ys).
  Proof. rewrite /pemuls. rewrite zipr_cons mapr_rcons. reflexivity. Qed.

  Lemma pemuls_rcons {A : Type} (xs : seq (PExpr A)) x ys y :
    size xs = size ys ->
    pemuls (rcons xs x) (rcons ys y) = rcons (pemuls xs ys) (PEmul x y).
  Proof.
    move=> Hs. rewrite /pemuls (zipr_rcons _ _ Hs). rewrite mapr_cons. reflexivity.
  Qed.

  Lemma pemuls_cat {A : Type} (xs1 : seq (PExpr A)) xs2 ys1 ys2 :
    size xs1 = size ys1 ->
    pemuls (xs1 ++ xs2) (ys1 ++ ys2) = (pemuls xs1 ys1) ++ (pemuls xs2 ys2).
  Proof.
    move=> Hs. rewrite /pemuls. rewrite (zipr_cat _ _ Hs). rewrite mapr_cat. reflexivity.
  Qed.

  Definition ZPEevals l (es : seq (PExpr Z)) := map (ZPEeval l) es.

  Lemma ZPEevals_cons l e es : ZPEevals l (e::es) = (ZPEeval l e)::(ZPEevals l es).
  Proof. done. Qed.

  Lemma ZPEevals_rcons l es e : ZPEevals l (rcons es e) = rcons (ZPEevals l es) (ZPEeval l e).
  Proof.
    elim: es e => [| hd tl IH] e //=. rewrite IH. reflexivity.
  Qed.

  Lemma ZPEevals_cat l es1 es2 : ZPEevals l (es1 ++ es2) = (ZPEevals l es1) ++ (ZPEevals l es2).
  Proof.
    elim: es1 es2 => [| e1 es1 IH1] es2 //=. rewrite IH1. reflexivity.
  Qed.

  Lemma ZPEeval_peadds l es : ZPEeval l (peadds es) = zadds (ZPEevals l es).
  Proof.
    move: es. apply: last_ind => [| es e IH] //=. rewrite ZPEevals_rcons.
    rewrite peadds_rcons zadds_rcons /=. rewrite IH. reflexivity.
  Qed.

  Lemma ZPEevals_pemuls l es1 es2 :
    ZPEevals l (pemuls es1 es2) = zmuls2 (ZPEevals l es1) (ZPEevals l es2).
  Proof.
    elim: es1 es2 => [| e1 es1 IH] [| e2 es2] //=.
    rewrite pemuls_cons /=. rewrite IH zmuls2_cons. reflexivity.
  Qed.

  Lemma ZPEeval_peadds_cons l e es :
    ZPEeval l (peadds (e::es)) = ZPEeval l e + ZPEeval l (peadds es).
  Proof.
    move: es e; apply: last_ind => [| es e IH] hd //=.
    - rewrite Z.add_0_r. reflexivity.
    - rewrite -rcons_cons. rewrite !peadds_rcons /=. rewrite IH. ring.
  Qed.

  Lemma ZPEeval_peadds_rcons l es e :
    ZPEeval l (peadds (rcons es e)) = ZPEeval l (peadds es) + ZPEeval l e .
  Proof. rewrite peadds_rcons /=. rewrite Z.add_comm. reflexivity. Qed.


  (* zpexpr_bounded: variables in a PExpr Z are bounded by some positive *)

  Fixpoint zpexpr_bounded (pe : PExpr Z) (g : positive) : Prop :=
    match pe with
   | PEO => true
   | PEI => true
   | PEc c => true
   | PEX j => (j < g)%positive
   | PEadd pe1 pe2
   | PEsub pe1 pe2
   | PEmul pe1 pe2 => zpexpr_bounded pe1 g /\ zpexpr_bounded pe2 g
   | PEopp pe1 => zpexpr_bounded pe1 g
   | PEpow pe1 n => zpexpr_bounded pe1 g
    end.

  Fixpoint zpexprs_bounded (pes : seq (PExpr Z)) (g : positive) : Prop :=
    match pes with
    | [::] => True
    | hd::tl => zpexpr_bounded hd g /\ zpexprs_bounded tl g
    end.

  Lemma zpexpr_bounded_ge_bounded g g' pe :
    (g <= g')%positive -> zpexpr_bounded pe g -> zpexpr_bounded pe g'.
  Proof.
    elim: pe g g' => //=.
    - move=> p g g' Hle Hlt. exact: (Pos.lt_le_trans _ _ _ Hlt Hle).
    - move=> e1 IH1 e2 IH2 g g' Hle [H1g H2g].
      split; [exact: (IH1 _ _ Hle H1g) | exact: (IH2 _ _ Hle H2g)].
    - move=> e1 IH1 e2 IH2 g g' Hle [H1g H2g].
      split; [exact: (IH1 _ _ Hle H1g) | exact: (IH2 _ _ Hle H2g)].
    - move=> e1 IH1 e2 IH2 g g' Hle [H1g H2g].
      split; [exact: (IH1 _ _ Hle H1g) | exact: (IH2 _ _ Hle H2g)].
  Qed.

  Lemma zpexprs_bounded_ge_bounded g g' pes :
    (g <= g')%positive -> zpexprs_bounded pes g -> zpexprs_bounded pes g'.
  Proof.
    elim: pes => [| pe pes IH] //= Hg [He Hes]. split.
    - exact: (zpexpr_bounded_ge_bounded Hg He).
    - exact: (IH Hg Hes).
  Qed.

  Lemma zpexprs_bounded_cons z zs g :
    zpexprs_bounded (z::zs) g <-> zpexpr_bounded z g /\ zpexprs_bounded zs g.
  Proof. reflexivity. Qed.

  Lemma zpexprs_bounded_rcons zs z g :
    zpexprs_bounded (rcons zs z) g <-> zpexprs_bounded zs g /\ zpexpr_bounded z g.
  Proof. elim: zs => [| hd tl IH] => //=; tauto. Qed.

  Lemma zpexprs_bounded_cat zs1 zs2 g :
    zpexprs_bounded (zs1 ++ zs2) g <-> zpexprs_bounded zs1 g /\ zpexprs_bounded zs2 g.
  Proof. elim: zs1 => [| z1 zs1 IH] > //=; tauto. Qed.

  Lemma zpexpr_bounded_peadds zs g :
    zpexpr_bounded (peadds zs) g <-> zpexprs_bounded zs g.
  Proof.
    move: zs. apply: last_ind => [| zs z IH] //=.
    rewrite peadds_rcons /=. rewrite zpexprs_bounded_rcons. tauto.
  Qed.

  Lemma zpexprs_bounded_pemuls xs ys g :
    zpexprs_bounded xs g -> zpexprs_bounded ys g -> zpexprs_bounded (pemuls xs ys) g.
  Proof.
    elim: xs ys => [| x xs IHx] [| y ys] //=. move: (IHx ys).
    rewrite pemuls_cons zpexprs_bounded_cons /=. tauto.
  Qed.

  (* Utilities *)

  Definition zpexpr_is_zero (e : PExpr Z) : bool :=
    match e with
    | PEO => true
    | PEc n => n == 0
    | _ => false
    end.

End ZRing.



Section BinList.

  Variable A : Type.
  Variable default : A.

  Local Notation snth := (seq.nth default).
  Local Notation bnth := (BinList.nth default).
  Local Notation bjump := (@BinList.jump A).

  Lemma bjump_nil (p : positive) : bjump p [::] = [::].
  Proof.
    elim: p => //=.
    - move=> p IH. rewrite 2!IH. reflexivity.
    - move=> p IH. rewrite 2!IH. reflexivity.
  Qed.

  Lemma bnth_nil (p : positive) : bnth p [::] = default.
  Proof.
    elim: p => //=.
    - move=> p IH. rewrite bjump_nil. exact: IH.
    - move=> p IH. rewrite bjump_nil. exact: IH.
  Qed.

  Lemma snth_bjump (p : positive) (n : nat) (l : list A) :
    snth (bjump p l) n = snth l (n + Pos.to_nat p).
  Proof.
    elim: p n l => /=.
    - move=> p IH n l. rewrite 2!IH. rewrite nth_tl. rewrite Pos2Nat.inj_xI.
      rewrite -Nat.double_twice. rewrite -(addnA n) -(addnA n) addn1. reflexivity.
    - move=> p IH n j. rewrite 2!IH. rewrite Pos2Nat.inj_xO -Nat.double_twice.
      rewrite -addnA. reflexivity.
    - move=> n l. exact: nth_tl.
  Qed.

  Lemma bnth_snth (p : positive) (l : list A) : bnth p l = snth l (Pos.to_nat p - 1).
  Proof.
    elim: p l => /=.
    - move=> p IH l. case: l => [| hd tl] /=.
      + rewrite bjump_nil bnth_nil nth_nil. reflexivity.
      + rewrite IH. rewrite snth_bjump. rewrite Pos2Nat.inj_xI.
        rewrite -(addn1 (2 * Pos.to_nat p)). rewrite -subnBA; last by done.
        rewrite subnn subn0. rewrite nth_cons;
                               last by (rewrite muln_gt0 (pos_to_nat_is_pos p)).
        rewrite (addnBAC _ (pos_to_nat_is_pos p)).
        rewrite muln_mul -Nat.double_twice. reflexivity.
    - move=> p IH l. rewrite IH. rewrite snth_bjump. rewrite Pos2Nat.inj_xO.
      rewrite (addnBAC _ (pos_to_nat_is_pos p)). rewrite -Nat.double_twice.
      reflexivity.
    - by case.
  Qed.

  Lemma bnth_rcons (g : positive) (l : list A) (x : A) :
    Pos.to_nat g <= size l -> bnth g (rcons l x) = bnth g l.
  Proof.
    move=> Hs. rewrite 2!bnth_snth. rewrite nth_rcons.
    case H: (Pos.to_nat g - 1 < size l); first by reflexivity. move/idP/negP: H.
    rewrite subn1. rewrite (ltn_predK (pos_to_nat_is_pos g)) Hs. discriminate.
  Qed.

  Lemma bnth_cat (g : positive) (l1 l2 : list A) :
    Pos.to_nat g <= size l1 -> bnth g (l1 ++ l2) = bnth g l1.
  Proof.
    move: l2 l1 g. apply: last_ind => [| l2 x2 IH] l1 g //=.
    - rewrite cats0. reflexivity.
    - move=> Hg. rewrite -rcons_cat. rewrite bnth_rcons.
      + exact: (IH _ _ Hg).
      + rewrite size_cat. apply: (leq_trans Hg). exact: leq_addr.
  Qed.

  Lemma bnth_rcons_last (g : positive) (l : list A) (x : A) :
    Pos.to_nat g = size l + 1 -> bnth g (rcons l x) = x.
  Proof.
    move=> Hs. rewrite bnth_snth. rewrite Hs. rewrite addn1 subn1 succnK.
    rewrite nth_rcons. rewrite (ltnn (size l)) (eqxx (size l)). reflexivity.
  Qed.

End BinList.



(** Convert a root entailment problem to an ideal membership problem. *)

Section REP2IMP.

  Local Open Scope Z_scope.

  Definition init_pos : positive := 1.

  Definition init_vm := SSAVM.empty positive.

  Definition init_vl : list Z := [::].

  Definition zpexpr_of_var (g : positive) (t : SSAVM.t positive) (v : ssavar) :
    positive * SSAVM.t positive * PExpr Z :=
    match SSAVM.find v t with
    | None => ((g + 1)%positive, SSAVM.add v g t, PEX Z g)
    | Some r => (g, t, PEX Z r)
    end.

  Definition zpexpr_of_eunop (op : eunop) : PExpr Z -> PExpr Z :=
    match op with
    | Eneg => @PEopp Z
    end.

  Definition zpexpr_of_ebinop (op : ebinop) : PExpr Z -> PExpr Z -> PExpr Z :=
    match op with
    | Eadd => @PEadd Z
    | Esub => @PEsub Z
    | Emul => @PEmul Z
    end.

  Fixpoint zpexpr_of_zexp (g : positive) (t : SSAVM.t positive) (e : ZSSA.zexp) :
    positive * SSAVM.t positive * PExpr Z :=
    match e with
    | Evar v => zpexpr_of_var g t v
    | Econst n => (g, t, PEc n)
    | Eunop op e =>
        let '(g', t', e') := zpexpr_of_zexp g t e in
        (g', t', zpexpr_of_eunop op e')
    | Ebinop op e1 e2 =>
        let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
        let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
        (g2, t2, zpexpr_of_ebinop op e1 e2)
    | Epow e n =>
        let '(g', t', e') := zpexpr_of_zexp g t e in
        (g', t', @PEpow Z e' n)
    end.

  Fixpoint zpexprs_of_zexps (g : positive) (t : SSAVM.t positive) (es : seq ZSSA.zexp) :
    positive * SSAVM.t positive * seq (PExpr Z) :=
    match es with
    | [::] => (g, t, [::])
    | hd::tl => let '(g_hd, t_hd, pe_hd) := (zpexpr_of_zexp g t hd) in
                let '(g_tl, t_tl, pe_tl) := (zpexprs_of_zexps g_hd t_hd tl) in
                (g_tl, t_tl, pe_hd::pe_tl)
    end.

  (* Create a sequence of variables of type `PExpr Z` *)
  Fixpoint pvars (g : positive) (n : nat) : seq (PExpr Z) :=
    match n with
    | O => [::]
    | S m => (PEX Z g)::(pvars (g + 1)%positive m)
    end.

  Lemma pvars_size g n : size (pvars g n) = n.
  Proof.
    elim: n g => [| n IHn] //=. move=> g. rewrite IHn. reflexivity.
  Qed.

  Lemma zpexprs_bounded_pvars g n :
    zpexprs_bounded (pvars g n) (g + Pos.of_nat n).
  Proof.
    elim: n g => [| n IHn] g //. split.
    - exact: Pos.lt_add_r.
    - case: n IHn => [| n IHn] //.
      rewrite -addn2. replace (n + 2)%N with ((n + 1) + 1)%N by ring.
      rewrite (addn1 n). rewrite Nat2Pos.inj_add => //.
      rewrite (Pos.add_comm (Pos.of_nat n.+1)). rewrite Pos.add_assoc.
      exact: IHn.
  Qed.

  Definition zpexpr_of_premise (g : positive) (t : SSAVM.t positive) (e : azbexp) :
    positive * SSAVM.t positive * PExpr Z :=
    match e with
    | Seq e1 e2 =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      (g2, t2, PEsub e1 e2)
    | Seqmod e1 e2 ms =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      let '(gms, tms, pms) := zpexprs_of_zexps g2 t2 ms in
      let pks := pvars gms (size ms) in
      let g' := if size ms == 0%N then gms
                else (gms + Pos.of_nat (size ms))%positive in
      (g', tms, PEsub (PEsub e1 e2) (peadds (pemuls pks pms)))
    end.

  Fixpoint zpexprs_of_premises (g : positive) (t : SSAVM.t positive) (es : seq azbexp) :
    positive * SSAVM.t positive * seq (PExpr Z) :=
    match es with
    | [::] => (g, t, [::])
    | e::es => let '(g_hd, t_hd, es_hd) := zpexpr_of_premise g t e in
               let '(g_tl, t_tl, es_tl) := zpexprs_of_premises g_hd t_hd es in
               (g_tl, t_tl, es_hd::es_tl)
    end.

  Definition zpexpr_of_conseq (g : positive) (t : SSAVM.t positive) (e : azbexp) :
    positive * SSAVM.t positive * PExpr Z * seq (PExpr Z) :=
    match e with
    | Seq e1 e2 =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      (g2, t2, PEsub e1 e2, [:: PEO])
    | Seqmod e1 e2 ms =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      let '(gp, tp, pms) := zpexprs_of_zexps g2 t2 ms in
      (gp, tp, PEsub e1 e2, pms)
    end.

  (* ps: polynomials that equal 0
     ms: moduli
     the goal is to prove that q = cps * ps + cms * ms for some coefficients cps and cms *)
  Definition imp_of_arep (s : arep) : positive * SSAVM.t positive * seq (PExpr Z) * seq (PExpr Z) * PExpr Z :=
    let g := init_pos in
    let t := init_vm in
    let '(g_p, t_p, ps) := zpexprs_of_premises g t (apremises s) in
    let '(g_q, t_q, q, ms) := zpexpr_of_conseq g_p t_p (aconseq s) in
    (g_q, t_q, ps, ms, q).

  Lemma zpexpr_of_eunop_zpeeval op vl pe :
    ZPEeval vl (zpexpr_of_eunop op pe) = SSA.eval_eunop op (ZPEeval vl pe).
  Proof. by case: op. Qed.

  Lemma zpexpr_of_ebinop_zpeeval op vl pe1 pe2 :
    ZPEeval vl (zpexpr_of_ebinop op pe1 pe2) =
    SSA.eval_ebinop op (ZPEeval vl pe1) (ZPEeval vl pe2).
  Proof. by case: op. Qed.



  (* Conversion with valuation list *)

  (* vl: list of integers of which i-th of vl is the value of i-th variable
     in polynomials under a specific store *)
  Definition zpexpr_of_var_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (v : ssavar) :
    list Z * positive * SSAVM.t positive * PExpr Z :=
    match SSAVM.find v t with
    | None => (rcons vl (ZSSAStore.acc v s), (g + 1)%positive, SSAVM.add v g t, PEX Z g)
    | Some r => (vl, g, t, PEX Z r)
    end.

  Lemma zpexpr_of_var_vl_novl st vl g t v vl' g' t' pe :
    zpexpr_of_var_vl st vl g t v = (vl', g', t', pe) ->
    zpexpr_of_var g t v = (g', t', pe).
  Proof.
    rewrite /zpexpr_of_var_vl /zpexpr_of_var. case: (SSAVM.find v t).
    - move=> ? [] ? ? ? ?; by subst.
    - case=> ? ? ? ?; by subst.
  Qed.

  Fixpoint zpexpr_of_zexp_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (e : ZSSA.zexp) :
    list Z * positive * SSAVM.t positive * PExpr Z :=
    match e with
    | Evar v => zpexpr_of_var_vl s vl g t v
    | Econst n => (vl, g, t, PEc n)
    | Eunop op e =>
        let '(vl', g', t', e') := zpexpr_of_zexp_vl s vl g t e in
        (vl', g', t', zpexpr_of_eunop op e')
    | Ebinop op e1 e2 =>
        let '(vl1, g1, t1, e1) := zpexpr_of_zexp_vl s vl g t e1 in
        let '(vl2, g2, t2, e2) := zpexpr_of_zexp_vl s vl1 g1 t1 e2 in
        (vl2, g2, t2, zpexpr_of_ebinop op e1 e2)
    | Epow e n =>
        let '(vl', g', t', e') := zpexpr_of_zexp_vl s vl g t e in
        (vl', g', t', @PEpow Z e' n)
    end.

  Fixpoint zpexprs_of_zexps_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (es : seq ZSSA.zexp) :
    list Z * positive * SSAVM.t positive * seq (PExpr Z) :=
    match es with
    | [::] => (vl, g, t, [::])
    | hd::tl => let '(vl_hd, g_hd, t_hd, pe_hd) := zpexpr_of_zexp_vl s vl g t hd in
                let '(vl_tl, g_tl, t_tl, pe_tl) := zpexprs_of_zexps_vl s vl_hd g_hd t_hd tl in
                (vl_tl, g_tl, t_tl, pe_hd::pe_tl)
    end.

  Lemma zpexpr_of_zexp_vl_novl st vl g t e vl' g' t' pe :
    zpexpr_of_zexp_vl st vl g t e = (vl', g', t', pe) ->
    zpexpr_of_zexp g t e = (g', t', pe).
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> ? ? ? ? ? ? ? ?; exact: zpexpr_of_var_vl_novl.
    - move=> ? ? ? ? ? ? ? ? [] ? ? ? ?; by subst.
    - move=> op e IH ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) =>
      [[[[vl' g'] t'] pe'] Hvl]. case=> ? ? ? ?; subst. rewrite (IH _ _ _ _ _ _ _ Hvl).
      reflexivity.
    - move=> op e1 IH1 e2 IH2 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      case=> ? ? ? ?; subst. rewrite (IH1 _ _ _ _ _ _ _ Hvl1) (IH2 _ _ _ _ _ _ _ Hvl2).
      reflexivity.
    - move=> e IH n ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl1 g1] t1] pe1] Hvl1].
      case=> ? ? ? ?; subst. rewrite (IH _ _ _ _ _ _ _ Hvl1). reflexivity.
  Qed.

  Lemma zpexprs_of_zexps_vl_novl st vl g t es vl' g' t' pes :
    zpexprs_of_zexps_vl st vl g t es = (vl', g', t', pes) ->
    zpexprs_of_zexps g t es = (g', t', pes).
  Proof.
    elim: es st vl g t vl' g' t' pes => [| e es IH] st vl g t vl' g' t' pes //=.
    - case=> ? ? ? ?; subst. reflexivity.
    - dcase (zpexpr_of_zexp_vl st vl g t e) => [[[[vl_hd g_hd] t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps_vl st vl_hd g_hd t_hd es) => [[[[vl_tl g_tl] t_tl] pe_tl] Htl].
      case=> ? ? ? ?; subst. rewrite (zpexpr_of_zexp_vl_novl Hhd).
      rewrite (IH _ _ _ _ _ _ _ _ Htl). reflexivity.
  Qed.

  Definition zpexpr_of_premise_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (e : azbexp) (pf : eval_azbexp e s) :
    list Z * positive * SSAVM.t positive * PExpr Z.
  Proof.
    move: pf. case: e => [e1 e2 _ | e1 e2 ms pf].
    - (* e = Seq e1 e2. *)
      move: (zpexpr_of_zexp_vl s vl g t e1) => [[[vl1 g1] t1] pe1].
      move: (zpexpr_of_zexp_vl s vl1 g1 t1 e2) => [[[vl2 g2] t2] pe2].
      exact: (vl2, g2, t2, PEsub pe1 pe2).
    - (* e = Seqmod e1 e2 ms *)
      move: (zpexpr_of_zexp_vl s vl g t e1) => [[[vl1 g1] t1] pe1].
      move: (zpexpr_of_zexp_vl s vl1 g1 t1 e2) => [[[vl2 g2] t2] pe2].
      move: (zpexprs_of_zexps_vl s vl2 g2 t2 ms) => [[[vlms gms] tms] pms].
      move: (pvars gms (size ms)) => pks.
      pose (g' := if size ms == 0%N then gms
                  else (gms + Pos.of_nat (size ms))%positive).
      exact: (vlms ++ (xchoose_zeqms_ext pf), g', tms,
               PEsub (PEsub pe1 pe2) (peadds (pemuls pks pms))).
  Defined.

(*
  Definition zpexpr_of_premise_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (e : azbexp) (pf : eval_azbexp e s) :
    list Z * positive * SSAVM.t positive * PExpr Z :=
    match e with
    | Seq e1 e2 =>
      let '(vl1, g1, t1, e1) := zpexpr_of_zexp_vl s vl g t e1 in
      let '(vl2, g2, t2, e2) := zpexpr_of_zexp_vl s vl1 g1 t1 e2 in
      (vl2, g2, t2, PEsub e1 e2)
    | Seqmod e1 e2 p =>
      let vp := if (ZSSA.eval_zexp p s) == 0 then
                  0
                else
                  (Z.div ((ZSSA.eval_zexp e1 s) - (ZSSA.eval_zexp e2 s))
                         (ZSSA.eval_zexp p s)) in
      let '(vl1, g1, t1, e1) := zpexpr_of_zexp_vl s vl g t e1 in
      let '(vl2, g2, t2, e2) := zpexpr_of_zexp_vl s vl1 g1 t1 e2 in
      let '(vlp, gp, tp, p) := zpexpr_of_zexp_vl s vl2 g2 t2 p in
      (rcons vlp vp, (gp + 1)%positive, tp, PEsub (PEsub e1 e2) (PEmul (PEX Z gp) p))
    end.
 *)

  Lemma zpexpr_of_premise_vl_novl st vl g t e vl' g' t' pe (pf : eval_azbexp e st) :
    @zpexpr_of_premise_vl st vl g t e pf = (vl', g', t', pe) ->
    zpexpr_of_premise g t e = (g', t', pe).
  Proof.
    elim: e vl g t vl' g' t' pe pf => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe pf.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      case=> ? ? ? ?; subst. rewrite (zpexpr_of_zexp_vl_novl Hvl1)
                                     (zpexpr_of_zexp_vl_novl Hvl2).
      reflexivity.
    - move=> e1 e2 ms ivl ig it ovl og ot pe pf.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hvlms].
      case=> ? ? ? ?; subst.
      rewrite (zpexpr_of_zexp_vl_novl Hvl1) (zpexpr_of_zexp_vl_novl Hvl2)
              (zpexprs_of_zexps_vl_novl Hvlms).
      reflexivity.
  Qed.

  Definition pf_hd s hd tl (pf : forall e : azbexp, e \in hd :: tl -> eval_azbexp e s) :
    eval_azbexp hd s.
  Proof.
    move: (pf hd). rewrite mem_head. apply. exact: is_true_true.
  Defined.

  Definition pf_tl s hd tl (pf : forall e : azbexp, e \in hd :: tl -> eval_azbexp e s) :
    forall e : azbexp, e \in tl -> eval_azbexp e s.
  Proof.
    move=> e Hmem; apply: pf. rewrite in_cons. rewrite Hmem orbT. exact: is_true_true.
  Defined.

  Fixpoint zpexprs_of_premises_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (es : seq azbexp) (pf : forall e : azbexp, e \in es -> eval_azbexp e s) {struct es} :
    list Z * positive * SSAVM.t positive * seq (PExpr Z).
  Proof.
    move: pf. case: es => [| e es] pf.
    - exact: (vl, g, t, [::]).
    - move: (@zpexpr_of_premise_vl s vl g t e (pf_hd pf)) =>
            [[[vl_hd g_hd] t_hd] es_hd].
      move: (zpexprs_of_premises_vl s vl_hd g_hd t_hd es (pf_tl pf)) =>
            [[[vl_tl g_tl] t_tl] es_tl].
      exact: (vl_tl, g_tl, t_tl, es_hd::es_tl).
  Defined.

  (*
  Fixpoint zpexprs_of_premises_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (es : seq azbexp) :
    list Z * positive * SSAVM.t positive * seq (PExpr Z) :=
    match es with
    | [::] => (vl, g, t, [::])
    | e::es =>
      let '(vl_hd, g_hd, t_hd, es_hd) := zpexpr_of_premise_vl s vl g t e in
      let '(vl_tl, g_tl, t_tl, es_tl) := zpexprs_of_premises_vl s vl_hd g_hd t_hd es in
      (vl_tl, g_tl, t_tl, es_hd::es_tl)
    end.
   *)

  Lemma zpexprs_of_premises_vl_novl st vl g t es vl' g' t' pes (pf : forall e : azbexp, e \in es -> eval_azbexp e st) :
    @zpexprs_of_premises_vl st vl g t es pf = (vl', g', t', pes) ->
    zpexprs_of_premises g t es = (g', t', pes).
  Proof.
    elim: es vl g t vl' g' t' pes pf => [| hd tl IH] ivl ig it ovl og ot pes pf /=.
    - by case=> ? ? ? ?; subst.
    - dcase (@zpexpr_of_premise_vl st ivl ig it hd (pf_hd pf)) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (@zpexprs_of_premises_vl st vl1 g1 t1 tl (pf_tl pf)) => [[[[vl2 g2] t2] pe2] Hvl2].
      case=> ? ? ? ?; subst. rewrite (zpexpr_of_premise_vl_novl Hvl1).
      rewrite (IH _ _ _ _ _ _ _ _ Hvl2). reflexivity.
  Qed.

  Definition zpexpr_of_conseq_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (e : azbexp) :
    list Z * positive * SSAVM.t positive * PExpr Z * seq (PExpr Z) :=
    match e with
    | Seq e1 e2 =>
      let '(vl1, g1, t1, e1) := zpexpr_of_zexp_vl s vl g t e1 in
      let '(vl2, g2, t2, e2) := zpexpr_of_zexp_vl s vl1 g1 t1 e2 in
      (vl2, g2, t2, PEsub e1 e2, [:: PEO])
    | Seqmod e1 e2 ms =>
      let '(vl1, g1, t1, e1) := zpexpr_of_zexp_vl s vl g t e1 in
      let '(vl2, g2, t2, e2) := zpexpr_of_zexp_vl s vl1 g1 t1 e2 in
      let '(vlms, gms, tms, pms) := zpexprs_of_zexps_vl s vl2 g2 t2 ms in
      (vlms, gms, tms, PEsub e1 e2, pms)
    end.

  Lemma zpexpr_of_conseq_vl_novl st vl g t e vl' g' t' pe pms :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pms) ->
    zpexpr_of_conseq g t e = (g', t', pe, pms).
  Proof.
    elim: e vl g t vl' g' t' pe pms => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe pms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      case=> ? ? ? ? ?; subst.
      rewrite (zpexpr_of_zexp_vl_novl Hvl1) (zpexpr_of_zexp_vl_novl Hvl2).
      reflexivity.
    - move=> e1 e2 ms ivl ig it ovl og ot pe pms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hvlms].
      case=> ? ? ? ? ?; subst.
      rewrite (zpexpr_of_zexp_vl_novl Hvl1) (zpexpr_of_zexp_vl_novl Hvl2)
              (zpexprs_of_zexps_vl_novl Hvlms).
      reflexivity.
  Qed.

  (* ps: polynomials that equal 0
     ms: moduli
     the goal is to prove that q = cps * ps + cms * m for some coefficients cps and cms *)
  Definition imp_of_arep_vl (st : ZSSAStore.t) (s : arep) (pf : forall e : azbexp, e \in apremises s -> eval_azbexp e st) :
    list Z * positive * SSAVM.t positive * seq (PExpr Z) * seq (PExpr Z) * PExpr Z :=
    let g := init_pos in
    let t := init_vm in
    let vl := init_vl in
    let '(vl_p, g_p, t_p, ps) := @zpexprs_of_premises_vl st init_vl g t (apremises s) pf in
    let '(vl_q, g_q, t_q, q, ms) := @zpexpr_of_conseq_vl st vl_p g_p t_p (aconseq s) in
    (vl_q, g_q, t_q, ps, ms, q).

  Lemma imp_of_arep_vl_novl st sp vl g t pps pm pq (pf : forall e : azbexp, e \in apremises sp -> eval_azbexp e st) :
    @imp_of_arep_vl st sp pf = (vl, g, t, pps, pm, pq) ->
    imp_of_arep sp = (g, t, pps, pm, pq).
  Proof.
    rewrite /imp_of_arep_vl /imp_of_arep.
    dcase (@zpexprs_of_premises_vl st init_vl init_pos init_vm (apremises sp) pf) =>
    [[[[vl_p g_p] t_p] opps] Hvl_p].
    dcase (zpexpr_of_conseq_vl st vl_p g_p t_p (aconseq sp)) =>
    [[[[[vl_q g_q] t_q] opm] opq] Hvl_q].
    case=> ? ? ? ? ? ?; subst. rewrite (zpexprs_of_premises_vl_novl Hvl_p).
    rewrite (zpexpr_of_conseq_vl_novl Hvl_q). reflexivity.
  Qed.



  (* newer_than_vm *)

  Definition newer_than_vm (g : positive) (t : SSAVM.t positive) : Prop :=
    forall (v : ssavar) (pv : positive), SSAVM.find v t = Some pv ->
                                         (pv < g)%positive.

  Lemma init_newer_than_vm : newer_than_vm init_pos init_vm.
  Proof.
    move=> v pv Hfind. rewrite SSAVM.Lemmas.empty_o in Hfind. discriminate.
  Qed.

  Lemma newer_than_vm_add_var g t v :
    newer_than_vm g t -> newer_than_vm (g + 1) (SSAVM.add v g t).
  Proof.
    move=> Hnew x px Hfind. case Hxv: (x == v).
    - rewrite (SSAVM.Lemmas.find_add_eq Hxv) in Hfind. case: Hfind => <-.
      exact: Pos.lt_add_r.
    - move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv) in Hfind.
      move: (Hnew _ _ Hfind) => Hlt. apply: (Pos.lt_trans _ _ _ Hlt).
      exact: Pos.lt_add_r.
  Qed.

  Lemma newer_than_vm_add_r g n t : newer_than_vm g t -> newer_than_vm (g + n) t.
  Proof.
    move=> Hnew x px Hfind. move: (Hnew _ _ Hfind) => Hlt. exact: (pos_lt_add_r _ Hlt).
  Qed.

  Lemma zpexpr_of_var_newer g t v g' t' pe :
    zpexpr_of_var g t v = (g', t', pe) -> newer_than_vm g t -> newer_than_vm g' t'.
  Proof.
    rewrite /zpexpr_of_var. case: (SSAVM.find v t).
    - move=> ? [] ? ? ? ?; subst. assumption.
    - case=> ? ? ? ?; subst. exact: newer_than_vm_add_var.
  Qed.

  Lemma zpexpr_of_zexp_newer g t e g' t' pe :
    zpexpr_of_zexp g t e = (g', t', pe) -> newer_than_vm g t -> newer_than_vm g' t'.
  Proof.
    elim: e g t g' t' pe => /=.
    - move=> v ig it og ot pe Hzp Hnew. exact: (zpexpr_of_var_newer Hzp Hnew).
    - move=> ? ? ? ? ? ? [] ? ? ? Hnew; subst. assumption.
    - move=> op e IH ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e) => [[[g t] pe] Hzp]. case=> ? ? ? Hnew; subst.
      exact: (IH _ _ _ _ _ Hzp Hnew).
    - move=> op e1 IH1 e2 IH2 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? Hnew; subst. apply: (IH2 _ _ _ _ _ Hzp2).
      exact: (IH1 _ _ _ _ _ Hzp1).
    - move=> e IH n ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e) => [[[g t] pe] Hzp]. case=> ? ? ? Hnew; subst.
      exact: (IH _ _ _ _ _ Hzp Hnew).
  Qed.

  Lemma zpexprs_of_zexps_newer g t es g' t' pes :
    zpexprs_of_zexps g t es = (g', t', pes) -> newer_than_vm g t -> newer_than_vm g' t'.
  Proof.
    elim: es g t g' t' pes => [| e es IH] //= g t g' t' pes.
    - case=> ? ? ?; subst. by apply.
    - dcase (zpexpr_of_zexp g t e) => [[[g_hd t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps g_hd t_hd es) => [[[g_tl t_tl] pe_tl] Htl].
      case=> ? ? ?; subst. move=> Hnew. apply: (IH _ _ _ _ _ Htl).
      exact: (zpexpr_of_zexp_newer Hhd Hnew).
  Qed.

  Lemma zpexpr_of_premise_newer g t e g' t' pe :
    zpexpr_of_premise g t e = (g', t', pe) -> newer_than_vm g t -> newer_than_vm g' t'.
  Proof.
    elim: e g t g' t' pe => /=.
    - move=> e1 e2 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? Hnew; subst. apply: (zpexpr_of_zexp_newer Hzp2).
      exact: (zpexpr_of_zexp_newer Hzp1).
    - move=> e1 e2 ms ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexprs_of_zexps g2 t2 ms) => [[[gms tms] pems] Hzpms].
      case=> ? ? ? Hnew; subst. move: Hzpms. case: ms => [| m ms] //=.
      + case=> ? ? ?; subst. apply: (zpexpr_of_zexp_newer Hzp2).
        exact: (zpexpr_of_zexp_newer Hzp1).
      + dcase (zpexpr_of_zexp g2 t2 m) => [[[gm_hd tm_hd] pem_hd] Hmhd].
        dcase (zpexprs_of_zexps gm_hd tm_hd ms) => [[[gm_tl tm_tl] pem_tl] Hmtl].
        case=> ? ? ?; subst. rewrite -/(Pos.of_nat (size ms).+1).
        apply: newer_than_vm_add_r. apply: (zpexprs_of_zexps_newer Hmtl).
        apply: (zpexpr_of_zexp_newer Hmhd). apply: (zpexpr_of_zexp_newer Hzp2).
        exact: (zpexpr_of_zexp_newer Hzp1).
  Qed.

  Lemma zpexprs_of_premises_newer g t es g' t' pes :
    zpexprs_of_premises g t es = (g', t', pes) ->
    newer_than_vm g t -> newer_than_vm g' t'.
  Proof.
    elim: es g t g' t' pes => [| e es IH] ig it og ot opes /=.
    - case=> ? ? ? Hnew; subst. assumption.
    - dcase (zpexpr_of_premise ig it e) => [[[g_hd t_hd] es_hd] Hzp_hd].
      dcase (zpexprs_of_premises g_hd t_hd es) => [[[g_tl t_tl] es_tl] Hzp_tl].
      case=> ? ? ? Hnew; subst. apply: (IH _ _ _ _ _ Hzp_tl).
      exact: (zpexpr_of_premise_newer Hzp_hd Hnew).
  Qed.

  Lemma zpexpr_of_conseq_newer g t e g' t' pe pms :
    zpexpr_of_conseq g t e = (g', t', pe, pms) ->
    newer_than_vm g t -> newer_than_vm g' t'.
  Proof.
    elim: e g t g' t' pe pms => /=.
    - move=> e1 e2 ig it og ot ope opms.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? ? Hnew; subst. apply: (zpexpr_of_zexp_newer Hzp2).
      exact: (zpexpr_of_zexp_newer Hzp1).
    - move=> e1 e2 e3 ig it og ot ope opms.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexprs_of_zexps g2 t2 e3) => [[[gms tms] pems] Hzpms].
      case=> ? ? ? ? Hnew; subst. apply: (zpexprs_of_zexps_newer Hzpms).
      apply: (zpexpr_of_zexp_newer Hzp2). exact: (zpexpr_of_zexp_newer Hzp1).
  Qed.



  (* Generator grows *)

  Lemma zpexpr_of_var_gen g t v g' t' pe :
    zpexpr_of_var g t v = (g', t', pe) -> (g <= g')%positive.
  Proof.
    rewrite /zpexpr_of_var. case: (SSAVM.find v t).
    - move=> ? [] ? ? ?; subst. exact: Pos.le_refl.
    - case=> ? ? ?; subst. exact: pos_le_add_diag_r.
  Qed.

  Lemma zpexpr_of_zexp_gen g t e g' t' pe :
    zpexpr_of_zexp g t e = (g', t', pe) -> (g <= g')%positive.
  Proof.
    elim: e g t g' t' pe => /=.
    - move=> v ig it og ot pe Hzp. exact: (zpexpr_of_var_gen Hzp).
    - move=> ? ? ? ? ? ? [] ? ? ?; subst. exact: Pos.le_refl.
    - move=> op e IH ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e) => [[[g t] pe] Hzp]. case=> ? ? ?; subst.
      exact: (IH _ _ _ _ _ Hzp).
    - move=> op e1 IH1 e2 IH2 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ?; subst. apply: (Pos.le_trans _ _ _ _ (IH2 _ _ _ _ _ Hzp2)).
      exact: (IH1 _ _ _ _ _ Hzp1).
    - move=> e IH n ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e) => [[[g t] pe] Hzp]. case=> ? ? ?; subst.
      exact: (IH _ _ _ _ _ Hzp).
  Qed.

  Lemma zpexprs_of_zexps_gen g t es g' t' pes :
    zpexprs_of_zexps g t es = (g', t', pes) -> (g <= g')%positive.
  Proof.
    elim: es g t g' t' pes => [| e es IH] //= g t g' t' pes.
    - case=> ? ? ?; subst. exact: Pos.le_refl.
    - dcase (zpexpr_of_zexp g t e) => [[[g_hd t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps g_hd t_hd es) => [[[g_tl t_tl] pe_tl] Htl].
      case=> ? ? ?; subst. apply: (Pos.le_trans _ _ _ _ (IH _ _ _ _ _ Htl)).
      exact: (zpexpr_of_zexp_gen Hhd).
  Qed.

  Lemma zpexpr_of_premise_gen g t e g' t' pe :
    zpexpr_of_premise g t e = (g', t', pe) -> (g <= g')%positive.
  Proof.
    elim: e g t g' t' pe => /=.
    - move=> e1 e2 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ?; subst. exact: (Pos.le_trans _ _ _
                                                (zpexpr_of_zexp_gen Hzp1)
                                                (zpexpr_of_zexp_gen Hzp2)).
    - move=> e1 e2 ms ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexprs_of_zexps g2 t2 ms) => [[[gms tms] pems] Hzpms].
      case=> ? ? ?; subst. move: Hzpms. case: ms => [| m ms] //=.
      + case=> ? ? ?; subst. apply: (Pos.le_trans _ _ _ _ (zpexpr_of_zexp_gen Hzp2)).
        exact: (zpexpr_of_zexp_gen Hzp1).
      + dcase (zpexpr_of_zexp g2 t2 m) => [[[gm_hd tm_hd] pem_hd] Hmhd].
        dcase (zpexprs_of_zexps gm_hd tm_hd ms) => [[[gm_tl tm_tl] pem_tl] Hmtl].
        case=> ? ? ?; subst. rewrite -/(Pos.of_nat (size ms).+1).
        apply: pos_le_add_r.
        apply: (Pos.le_trans _ _ _ _ (zpexprs_of_zexps_gen Hmtl)).
        apply: (Pos.le_trans _ _ _ _ (zpexpr_of_zexp_gen Hmhd)).
        apply: (Pos.le_trans _ _ _ _ (zpexpr_of_zexp_gen Hzp2)).
        exact: (zpexpr_of_zexp_gen Hzp1).
  Qed.

  Lemma zpexprs_of_premises_gen g t es g' t' pes :
    zpexprs_of_premises g t es = (g', t', pes) -> (g <= g')%positive.
  Proof.
    elim: es g t g' t' pes => [| hd tl IH] /=.
    - move=> ig it og ot opes [] ? ? ?; subst. exact: Pos.le_refl.
    - move=> ig it og ot opes.
      dcase (zpexpr_of_premise ig it hd) => [[[g_hd t_hd] es_hd] Hpe_hd].
      dcase (zpexprs_of_premises g_hd t_hd tl) => [[[g_tl t_tl] es_tl] Hpe_tl].
      case=> ? ? ?; subst. exact: (Pos.le_trans _ _ _
                                                (zpexpr_of_premise_gen Hpe_hd)
                                                (IH _ _ _ _ _ Hpe_tl)).
  Qed.



  (* Prefix of vl *)

  Lemma zpexpr_of_var_vl_prefix st vl g t v vl' g' t' pe :
    zpexpr_of_var_vl st vl g t v = (vl', g', t', pe) -> prefix_of vl vl'.
  Proof.
    rewrite /zpexpr_of_var_vl. case: (SSAVM.find v t).
    - move=> ? [] ? ? ? ?; subst. exact: prefix_of_refl.
    - case=> ? ? ? ?; subst. apply: prefix_of_rcons. exact: prefix_of_refl.
  Qed.

  Lemma zpexpr_of_zexp_vl_prefix_of st vl g t e vl' g' t' pe :
    zpexpr_of_zexp_vl st vl g t e = (vl', g', t', pe) -> prefix_of vl vl'.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> v ivl ig it ovl og ot pe Hzp. exact: (zpexpr_of_var_vl_prefix Hzp).
    - move=> n ivl ig it ovl og ot pe [] ? ? ? ?; subst. exact: prefix_of_refl.
    - move=> op e IH ivl ig it ovl og ot ope.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl g] t] pe] Hzp].
      case=> ? ? ? ?; subst. exact: (IH _ _ _ _ _ _ _ Hzp).
    - move=> op e1 IH1 e2 IH2 ivl ig it ovl og ot ope.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hzp2].
      case=> ? ? ? ?; subst. apply: (prefix_of_trans _ (IH2 _ _ _ _ _ _ _ Hzp2)).
      exact: (IH1 _ _ _ _ _ _ _ Hzp1).
    - move=> e IH n ivl ig it ovl og ot ope.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl g] t] pe] Hzp].
      case=> ? ? ? ?; subst. exact: (IH _ _ _ _ _ _ _ Hzp).
  Qed.

  Lemma zpexprs_of_zexps_vl_prefix_of st vl g t es vl' g' t' pes :
    zpexprs_of_zexps_vl st vl g t es = (vl', g', t', pes) -> prefix_of vl vl'.
  Proof.
    elim: es st vl g t vl' g' t' pes => [| e es IH] //= st vl g t vl' g' t' pes.
    - case=> ? ? ? ?; subst. exact: prefix_of_refl.
    - dcase (zpexpr_of_zexp_vl st vl g t e) => [[[[vl_hd g_hd] t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps_vl st vl_hd g_hd t_hd es) => [[[[vl_tl g_tl] t_tl] pe_tl] Htl].
      case=> ? ? ? ?; subst. apply: (prefix_of_trans _ (IH _ _ _ _ _ _ _ _ Htl)).
      exact: (zpexpr_of_zexp_vl_prefix_of Hhd).
  Qed.

  Lemma zpexpr_of_premise_vl_prefix_of st vl g t e vl' g' t' pe pf :
    @zpexpr_of_premise_vl st vl g t e pf = (vl', g', t', pe) -> prefix_of vl vl'.
  Proof.
    elim: e vl g t vl' g' t' pe pf => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope _.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ?; subst.
      exact: (prefix_of_trans (zpexpr_of_zexp_vl_prefix_of Hpe1)
                              (zpexpr_of_zexp_vl_prefix_of Hpe2)).
    - move=> e1 e2 ms ivl ig it ovl og ot opes opf.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hpems].
      case=> ? ? ? ?; subst. apply: prefix_of_cat.
      apply: (prefix_of_trans _ (zpexprs_of_zexps_vl_prefix_of Hpems)).
      apply: (prefix_of_trans _ (zpexpr_of_zexp_vl_prefix_of Hpe2)).
      exact: (zpexpr_of_zexp_vl_prefix_of Hpe1).
  Qed.

  Lemma zpexprs_of_premises_vl_prefix_of st vl g t es vl' g' t' pes pf :
    @zpexprs_of_premises_vl st vl g t es pf = (vl', g', t', pes) -> prefix_of vl vl'.
  Proof.
    elim: es vl g t vl' g' t' pes pf => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes opf [] ? ? ? ?; subst. exact: prefix_of_refl.
    - move=> ivl ig it ovl og ot opes opf.
      dcase (@zpexpr_of_premise_vl st ivl ig it hd (pf_hd opf)) =>
      [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (@zpexprs_of_premises_vl st vl_hd g_hd t_hd tl (pf_tl opf)) =>
      [[[[vl_tl g_tl] t_tl] es_tl] Hpe_tl].
      case=> ? ? ? ?; subst. apply: (prefix_of_trans _ (IH _ _ _ _ _ _ _ _ Hpe_tl)).
      exact: (zpexpr_of_premise_vl_prefix_of Hpe_hd).
  Qed.

  Lemma zpexpr_of_conseq_vl_prefix_of st vl g t e vl' g' t' pe pms :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pms) -> prefix_of vl vl'.
  Proof.
    elim: e vl g t vl' g' t' pe pms => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope opms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ?; subst.
      exact: (prefix_of_trans (zpexpr_of_zexp_vl_prefix_of Hpe1)
                              (zpexpr_of_zexp_vl_prefix_of Hpe2)).
    - move=> e1 e2 ms ivl ig it ovl og ot opes opms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hpems].
      case=> ? ? ? ? ?; subst.
      apply: (prefix_of_trans _ (zpexprs_of_zexps_vl_prefix_of Hpems)).
      apply: (prefix_of_trans _ (zpexpr_of_zexp_vl_prefix_of Hpe2)).
      exact: (zpexpr_of_zexp_vl_prefix_of Hpe1).
  Qed.



  (* size of vl is bounded *)

  Definition vl_size_bounded (vl : list Z) (g : positive) : Prop :=
    size vl = (Pos.to_nat g - 1)%N.

  Lemma init_vl_size_bounded : vl_size_bounded init_vl init_pos.
  Proof. reflexivity. Qed.

  Lemma find_bounded_by_vl vl g t v pv :
    newer_than_vm g t -> vl_size_bounded vl g -> SSAVM.find v t = Some pv ->
    (Pos.to_nat pv <= size vl)%N.
  Proof.
    rewrite /vl_size_bounded => Hnew Hsize Hfind. rewrite Hsize.
    move: (Hnew v pv Hfind) => Hlt. move/(Pos2Nat.inj_lt _ _): Hlt => Hlt.
    move/lt_ltn: Hlt => Hlt. exact: (ltn_leq_sub Hlt).
  Qed.

  Lemma rcons_vl_size_bounded vl v g :
    vl_size_bounded vl g -> vl_size_bounded (rcons vl v) (g + 1).
  Proof.
    rewrite /vl_size_bounded=> Hsize. rewrite size_rcons Hsize. rewrite subn1.
    rewrite Pos2Nat.inj_add. rewrite -addn_add -addnBA; last by done.
    rewrite addn0 (prednK (pos_to_nat_is_pos g)). reflexivity.
  Qed.

  Lemma cat_vl_size_bounded vl1 vl2 g :
    size vl2 == 0%N = false -> vl_size_bounded vl1 g ->
    vl_size_bounded (vl1 ++ vl2) (g + Pos.of_nat (size vl2)).
  Proof.
    move: vl2 vl1 g. apply: last_ind=> [| vl2 v IH] vl1 g //= Hs Hb1.
    clear Hs. rewrite -rcons_cat. rewrite size_rcons -addn1.
    case: vl2 IH => [| v2 vl2] //= IH.
    - rewrite cats0. apply: rcons_vl_size_bounded. assumption.
    - rewrite -/(Pos.of_nat (size vl2 + 1).+1).
      rewrite -/(Pos.of_nat (size vl2).+1) in IH.
      have Hs: (size vl2).+1 <> 0%N.
      { move=> Hs. apply: (Nat.neq_succ_0 (size vl2)). assumption. }
      rewrite -addn1. rewrite Nat2Pos.inj_add => //=.
      + rewrite Pos.add_assoc. apply: rcons_vl_size_bounded.
        rewrite addn1. apply: (IH _ _ _ Hb1). apply/eqP. assumption.
      + rewrite addn1. assumption.
  Qed.

  Lemma zpexpr_of_var_vl_size_bounded st vl g t v vl' g' t' pe :
    zpexpr_of_var_vl st vl g t v = (vl', g', t', pe) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    rewrite /zpexpr_of_var_vl. case: (SSAVM.find v t).
    - by move=> ? [] ? ? ? ?; subst.
    - case=> ? ? ? ?; subst. move=> Hsize. exact: rcons_vl_size_bounded.
  Qed.

  Lemma zpexpr_of_zexp_vl_size_bounded st vl g t e vl' g' t' pe :
    zpexpr_of_zexp_vl st vl g t e = (vl', g', t', pe) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> v ivl ig it ovl og ot pe Hvl Hsize.
      exact: (zpexpr_of_var_vl_size_bounded Hvl Hsize).
    - move=> n ivl ig it ovl og ot pe. case=> ? ? ? ? Hsize; subst. assumption.
    - move=> op e IH ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl' g'] t'] pe'] Hpe].
      case=> ? ? ? ? Hsize; subst. exact: (IH _ _ _ _ _ _ _ Hpe Hsize).
    - move=> op e1 IH1 e2 IH2 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? Hsize; subst. apply: (IH2 _ _ _ _ _ _ _ Hpe2).
      exact: (IH1 _ _ _ _ _ _ _ Hpe1).
    - move=> e IH n ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl' g'] t'] pe'] Hpe].
      case=> ? ? ? ? Hsize; subst. exact: (IH _ _ _ _ _ _ _ Hpe Hsize).
  Qed.

  Lemma zpexprs_of_zexps_vl_size_bounded st vl g t es vl' g' t' pes :
    zpexprs_of_zexps_vl st vl g t es = (vl', g', t', pes) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: es st vl g t vl' g' t' pes => [| e es IH] //= st vl g t vl' g' t' pes.
    - case=> ? ? ? ?; subst. by apply.
    - dcase (zpexpr_of_zexp_vl st vl g t e) => [[[[vl_hd g_hd] t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps_vl st vl_hd g_hd t_hd es) => [[[[vl_tl g_tl] t_tl] pe_tl] Htl].
      case=> ? ? ? ?; subst. move=> Hb. apply: (IH _ _ _ _ _ _ _ _ Htl).
      exact: (zpexpr_of_zexp_vl_size_bounded Hhd).
  Qed.

  Lemma zpexpr_of_premise_vl_size_bounded st vl g t e vl' g' t' pe pf :
    @zpexpr_of_premise_vl st vl g t e pf = (vl', g', t', pe) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: e vl g t vl' g' t' pe pf => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope _.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? Hsize; subst. apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
      exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
    - move=> e1 e2 ms ivl ig it ovl og ot opes opf.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hpems].
      case=> ? ? ? ? Hsize; subst. move: (size_xchoose_zeqms_ext opf) => /= Hxs.
      case Hs: (size ms == 0%N).
      + move/eqP: Hs => Hs. move: (size0nil Hs) => ?; subst. case: Hpems => ? ? ? ?; subst.
        move: (size0nil Hxs) => Hxnil. rewrite Hxnil cats0.
        apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
        exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
      + rewrite ZSSA.size_eval_zexps in Hxs. rewrite -Hxs in Hs *.
        apply: (cat_vl_size_bounded Hs).
        apply: (zpexprs_of_zexps_vl_size_bounded Hpems).
        apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
        exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
  Qed.

  Lemma zpexprs_of_premises_vl_size_bounded st vl g t es vl' g' t' pes pf :
    @zpexprs_of_premises_vl st vl g t es pf = (vl', g', t', pes) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: es vl g t vl' g' t' pes pf => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes _ [] ? ? ? ? Hsize; subst. assumption.
    - move=> ivl ig it ovl og ot opes opf.
      dcase (@zpexpr_of_premise_vl st ivl ig it hd (pf_hd opf)) =>
      [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (@zpexprs_of_premises_vl st vl_hd g_hd t_hd tl (pf_tl opf)) =>
      [[[[vl_tl g_tl] t_tl] es_tl] Hpe_tl].
      case=> ? ? ? ? Hsize; subst. apply: (IH _ _ _ _ _ _ _ _ Hpe_tl).
      exact: (zpexpr_of_premise_vl_size_bounded Hpe_hd).
  Qed.

  Lemma zpexpr_of_conseq_vl_size_bounded st vl g t e vl' g' t' pe pms :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pms) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: e vl g t vl' g' t' pe pms => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope opms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ? Hsize; subst. apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
      exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
    - move=> e1 e2 ms ivl ig it ovl og ot opes opms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hpems].
      case=> ? ? ? ? ? Hsize; subst.
      apply: (zpexprs_of_zexps_vl_size_bounded Hpems).
      apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
      exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
  Qed.



  (* zpexpr_of_zexp and pexpr_bounded *)

  Lemma zpexpr_of_var_zpexpr_bounded g t v g' t' pe :
    zpexpr_of_var g t v = (g', t', pe) -> newer_than_vm g t -> zpexpr_bounded pe g'.
  Proof.
    rewrite /zpexpr_of_var. case Hfind: (SSAVM.find v t).
    - case=> ? ? ? Hnew; subst. rewrite /=. exact: (Hnew _ _ Hfind).
    - case=> ? ? ? Hnew; subst. rewrite /=. exact: Pos.lt_add_r.
  Qed.

  Lemma zpexpr_of_zexp_zpexpr_bounded g t e g' t' pe :
    zpexpr_of_zexp g t e = (g', t', pe) -> newer_than_vm g t -> zpexpr_bounded pe g'.
  Proof.
    elim: e g t g' t' pe => /=.
    - move=> v ig it og ot ope Hnew Hzp.
      exact: (zpexpr_of_var_zpexpr_bounded Hnew Hzp).
    - move=> n ig it og ot ope [] ? ? ? Hnew; subst => /=. done.
    - move=> op e IH ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e) => [[[g'] t'] pe'] Hpe.
      case=> ? ? ? Hnew; subst. rewrite /zpexpr_of_eunop. case: op => /=.
      exact: (IH _ _ _ _ _ Hpe Hnew).
    - move=> op e1 IH1 e2 IH2 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hpe2].
      case=> ? ? ? Hnew; subst. move: (zpexpr_of_zexp_newer Hpe1 Hnew) => Hnew11.
      rewrite /zpexpr_of_ebinop.
      case: op => /=;
        by (split;
            [apply: (zpexpr_bounded_ge_bounded (zpexpr_of_zexp_gen Hpe2));
             exact: (IH1 _ _ _ _ _ Hpe1 Hnew) |
             exact: (IH2 _ _ _ _ _ Hpe2 Hnew11)]).
    - move=> e IH n ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e) => [[[g'] t'] pe'] Hpe.
      case=> ? ? ? Hnew; subst. exact: (IH _ _ _ _ _ Hpe Hnew).
  Qed.

  Lemma zpexprs_of_zexps_zpexprs_bounded g t es g' t' pes :
    zpexprs_of_zexps g t es = (g', t', pes) -> newer_than_vm g t -> zpexprs_bounded pes g'.
  Proof.
    elim: es g t g' t' pes => [| e es IH] g t g' t' pes //=.
    - case=> ? ? ?; subst. done.
    - dcase (zpexpr_of_zexp g t e) => [[[g_hd t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps g_hd t_hd es) => [[[g_tl t_tl] pe_tl] Htl].
      case=> ? ? ?; subst. move=> Hnew /=. split.
      + apply: (zpexpr_bounded_ge_bounded _ (zpexpr_of_zexp_zpexpr_bounded Hhd Hnew)).
        exact: (zpexprs_of_zexps_gen Htl).
      + apply: (IH _ _ _ _ _ Htl). exact: (zpexpr_of_zexp_newer Hhd Hnew).
  Qed.

  Lemma zpexpr_of_premise_zpexpr_bounded g t e g' t' pe :
    zpexpr_of_premise g t e = (g', t', pe) -> newer_than_vm g t ->
    zpexpr_bounded pe g'.
  Proof.
    elim: e g t g' t' pe => /=.
    - move=> e1 e2 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? Hnew; subst. move: (zpexpr_of_zexp_gen Hzp2) => Hg1. split.
      + apply: (zpexpr_bounded_ge_bounded Hg1).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
      + apply: (zpexpr_of_zexp_zpexpr_bounded Hzp2).
        exact: (zpexpr_of_zexp_newer Hzp1 Hnew).
    - move=> e1 e2 ms ig it og ot opes.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexprs_of_zexps g2 t2 ms) => [[[gms tms] pems] Hzpms].
      case=> ? ? ? Hnew; subst.

      move: (zpexpr_of_zexp_newer Hzp1 Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer Hzp2 Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_gen Hzp2) => Hg12.
      move: (zpexprs_of_zexps_gen Hzpms) => Hg2ms.
      case Hs: (size ms == 0%N).
      + move: (size0nil (eqP Hs)) => ?; subst. case: Hzpms => ? ? ?; subst. repeat split.
        * apply: (zpexpr_bounded_ge_bounded Hg12).
          exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
        * apply: (zpexpr_bounded_ge_bounded Hg2ms).
          exact: (zpexpr_of_zexp_zpexpr_bounded Hzp2 Hnew1).
      + move: (Pos.le_trans _ _ _ Hg12 Hg2ms) => Hg1ms.
        move: (@pos_le_add_r _ _ (Pos.of_nat (size ms))%positive Hg1ms) => Hg1mssucc.
        move: (@pos_le_add_r _ _ (Pos.of_nat (size ms))%positive Hg2ms) => Hg2mssucc.
        repeat split.
        * apply: (zpexpr_bounded_ge_bounded Hg1mssucc).
          exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
        * apply: (zpexpr_bounded_ge_bounded Hg2mssucc).
          exact: (zpexpr_of_zexp_zpexpr_bounded Hzp2 Hnew1).
        * rewrite zpexpr_bounded_peadds. apply: zpexprs_bounded_pemuls.
          -- exact: zpexprs_bounded_pvars.
          -- apply: (zpexprs_bounded_ge_bounded (@pos_le_add_diag_r gms (Pos.of_nat (size ms)))).
             exact: (zpexprs_of_zexps_zpexprs_bounded Hzpms Hnew2).
  Qed.

  Lemma zpexprs_of_premises_zpexprs_bounded g t es g' t' pes :
    zpexprs_of_premises g t es = (g', t', pes) -> newer_than_vm g t ->
    zpexprs_bounded pes g'.
  Proof.
    elim: es g t g' t' pes => [| hd tl IH] /=.
    - move=> ig it og ot opes [] ? ? ? Hnew; subst. done.
    - move=> ig it og ot opes.
      dcase (zpexpr_of_premise ig it hd) => [[[g_hd t_hd] es_hd] Hpe_hd].
      dcase (zpexprs_of_premises g_hd t_hd tl) => [[[g_tl t_tl] es_tl] Hpe_tl].
      case=> ? ? ? Hnew; subst. split.
      + apply: (zpexpr_bounded_ge_bounded (zpexprs_of_premises_gen Hpe_tl)).
        exact: (zpexpr_of_premise_zpexpr_bounded Hpe_hd).
      + apply: (IH _ _ _ _ _ Hpe_tl). exact: (zpexpr_of_premise_newer Hpe_hd).
  Qed.

  Lemma zpexpr_of_conseq_zpexpr_bounded_e g t e g' t' pe pms :
    zpexpr_of_conseq g t e = (g', t', pe, pms) -> newer_than_vm g t ->
    zpexpr_bounded pe g'.
  Proof.
    elim: e g t g' t' pe pms => /=.
    - move=> e1 e2 ig it og ot ope opms.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? ? Hnew; subst. move: (zpexpr_of_zexp_gen Hzp2) => Hg1. split.
      + apply: (zpexpr_bounded_ge_bounded Hg1).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
      + apply: (zpexpr_of_zexp_zpexpr_bounded Hzp2).
        exact: (zpexpr_of_zexp_newer Hzp1 Hnew).
    - move=> e1 e2 ms ig it og ot opes opms.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexprs_of_zexps g2 t2 ms) => [[[gms tms] pems] Hzpms].
      case=> ? ? ? ? Hnew; subst.
      move: (zpexpr_of_zexp_newer Hzp1 Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer Hzp2 Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_gen Hzp2) => Hg12.
      move: (zpexprs_of_zexps_gen Hzpms) => Hg2ms.
      move: (Pos.le_trans _ _ _ Hg12 Hg2ms) => Hg1ms. repeat split.
      + apply: (zpexpr_bounded_ge_bounded Hg1ms).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
      + apply: (zpexpr_bounded_ge_bounded Hg2ms).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp2 Hnew1).
  Qed.

  Lemma zpexpr_of_conseq_zpexpr_bounded_m g t e g' t' pe pms :
    zpexpr_of_conseq g t e = (g', t', pe, pms) -> newer_than_vm g t ->
    zpexprs_bounded pms g'.
  Proof.
    elim: e g t g' t' pe pms => /=.
    - move=> e1 e2 ig it og ot ope opms.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? ? Hnew; subst. done.
    - move=> e1 e2 ms ig it og ot ope opms.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexprs_of_zexps g2 t2 ms) => [[[gms tms] pems] Hzpms].
      case=> ? ? ? ? Hnew; subst.
      move: (zpexpr_of_zexp_newer Hzp1 Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer Hzp2 Hnew1) => Hnew2.
      exact: (zpexprs_of_zexps_zpexprs_bounded Hzpms Hnew2).
  Qed.



  (* Relate prefix_of, vl_size_bounded, zpexpr_bounded, and ZPEval *)

  Lemma prefix_of_zpeeval vl1 vl2 g pe :
    prefix_of vl1 vl2 -> vl_size_bounded vl1 g -> zpexpr_bounded pe g ->
    ZPEeval vl1 pe = ZPEeval vl2 pe.
  Proof.
    elim: pe vl1 vl2 g => //=.
    - move=> v vl1 vl2 g Hpre Hvl Hlt. rewrite 2!bnth_snth.
      apply: (prefix_of_nth _ Hpre). rewrite Hvl. apply: lt_ltn. rewrite !subn1.
      apply/(Nat.pred_lt_mono (Pos.to_nat v) (Pos.to_nat g) (@pos2nat_is_nonzero v)).
      apply/Pos2Nat.inj_lt. assumption.
    - move=> e1 IH1 e2 IH2 vl1 vl2 g Hpre Hvl [Hb1 Hb2].
      rewrite (IH1 _ _ _ Hpre Hvl Hb1) (IH2 _ _ _ Hpre Hvl Hb2). reflexivity.
    - move=> e1 IH1 e2 IH2 vl1 vl2 g Hpre Hvl [Hb1 Hb2].
      rewrite (IH1 _ _ _ Hpre Hvl Hb1) (IH2 _ _ _ Hpre Hvl Hb2). reflexivity.
    - move=> e1 IH1 e2 IH2 vl1 vl2 g Hpre Hvl [Hb1 Hb2].
      rewrite (IH1 _ _ _ Hpre Hvl Hb1) (IH2 _ _ _ Hpre Hvl Hb2). reflexivity.
    - move=> e IH vl1 vl2 g Hpre Hvl Hb. by rewrite (IH _ _ _ Hpre Hvl Hb).
    - move=> e IH n vl1 vl2 g Hpre Hvl Hb. by rewrite (IH _ _ _ Hpre Hvl Hb).
  Qed.

  Lemma prefix_of_zpeevals vl1 vl2 g pes :
    prefix_of vl1 vl2 -> vl_size_bounded vl1 g -> zpexprs_bounded pes g ->
    ZPEevals vl1 pes = ZPEevals vl2 pes.
  Proof.
    elim: pes vl1 vl2 g => [| pe pes IH] vl1 vl2 g //=.
    move=> Hpre Hvlb [Hpe Hpes].
    rewrite (prefix_of_zpeeval Hpre Hvlb Hpe) (IH _ _ _ Hpre Hvlb Hpes).
    reflexivity.
  Qed.

  Lemma rcons_zpeeval vl v g pe :
    vl_size_bounded vl g -> zpexpr_bounded pe g ->
    ZPEeval vl pe = ZPEeval (rcons vl v) pe.
  Proof.
    move=> Hsize Hbounded. apply: (prefix_of_zpeeval _ Hsize Hbounded).
    apply: prefix_of_rcons. exact: prefix_of_refl.
  Qed.

  Lemma prefix_of_zpexpr_all0 vl1 vl2 g pes :
    prefix_of vl1 vl2 -> vl_size_bounded vl1 g -> zpexprs_bounded pes g ->
    zpexpr_all0 vl1 pes -> zpexpr_all0 vl2 pes.
  Proof.
    elim: pes vl1 vl2 g => [| hd tl IH] //=.
    move=> vl1 vl2 g Hpre Hsize1 [Hzb_hd Hzb_tl] [Heval_hd Heval_tl]. split.
    - rewrite -(prefix_of_zpeeval Hpre Hsize1 Hzb_hd). assumption.
    - exact: (IH _ _ _ Hpre Hsize1 Hzb_tl Heval_tl).
  Qed.



  (* Consistency between store and vl *)

  Definition consistent (st : ZSSAStore.t) (vl : list Z) (t : SSAVM.t positive) :=
    forall (v : ssavar) (pv : positive),
      SSAVM.find v t = Some pv -> ZSSAStore.acc v st = BinList.nth 0 pv vl.

  Lemma init_consistent st : consistent st init_vl init_vm.
  Proof.
    move=> v pv Hfind. rewrite SSAVM.Lemmas.empty_o in Hfind. discriminate.
  Qed.

  Lemma consistent_zpeeval_some st vl t v pv :
    consistent st vl t -> SSAVM.find v t = Some pv ->
    ZPEeval vl (PEX Z pv) = ZSSAStore.acc v st.
  Proof. move=> Hcon Hfind. rewrite (Hcon v pv Hfind). reflexivity. Qed.

  Lemma zpeeval_rcons_last vl g v :
    vl_size_bounded vl g -> ZPEeval (rcons vl v) (PEX Z g) = v.
  Proof.
    move=> Hsize /=. rewrite bnth_rcons_last; first reflexivity.
    rewrite Hsize subn1 addn1 prednK; first reflexivity. exact: (pos_to_nat_is_pos g).
  Qed.

  Lemma rcons_consistent st vl g t x :
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st (rcons vl x) t.
  Proof.
    move=> Hnew Hsize Hcon v pv Hfind.
    rewrite (Hcon v pv Hfind) bnth_rcons; first reflexivity.
    exact: (find_bounded_by_vl Hnew Hsize Hfind).
   Qed.

  Lemma cat_consistent st vl1 vl2 g t :
    newer_than_vm g t -> vl_size_bounded vl1 g ->
    consistent st vl1 t -> consistent st (vl1 ++ vl2) t.
  Proof.
    move: vl2 vl1 st g t. apply: last_ind => [| vl2 v2 IH] vl1 st g t //=.
    - rewrite cats0. done.
    - move=> Hnew Hvl Hcon. rewrite -rcons_cat. case Hs: (size vl2 == 0)%N.
      + move: (size0nil (eqP Hs)) => ?; subst. rewrite cats0.
        exact: (rcons_consistent _ Hnew Hvl Hcon).
      + apply: (rcons_consistent (g:=(g + Pos.of_nat (size vl2))%positive)).
        * apply: newer_than_vm_add_r. assumption.
        * apply: (cat_vl_size_bounded Hs). assumption.
        * exact: (IH _ _ _ _ Hnew Hvl Hcon).
  Qed.

  Lemma rcons_add_consistent st vl g t v :
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    consistent st (rcons vl (ZSSAStore.acc v st)) (SSAVM.add v g t).
  Proof.
    move=> Hnew Hsize Hcon x px. case Hxv: (x == v).
    - rewrite (SSAVM.Lemmas.find_add_eq Hxv). case=> ?; subst. rewrite bnth_snth.
      rewrite -Hsize. replace (size vl) with (size (rcons vl (ZSSAStore.acc v st))).-1;
                        last by rewrite size_rcons -pred_Sn; reflexivity.
      rewrite nth_last last_rcons. rewrite (eqP Hxv). reflexivity.
    - move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv)=> Hfind.
      rewrite (Hcon _ _ Hfind). move: (Hnew _ _ Hfind) => Hpxg.
      rewrite bnth_rcons; first reflexivity.
      rewrite Hsize. move/Pos2Nat.inj_lt: Hpxg => Hpxg. move/ltP: Hpxg => Hpxg.
      exact: (ltn_leq_sub Hpxg).
  Qed.

  Lemma zpexpr_of_var_vl_consistent st vl g t v vl' g' t' pe :
    zpexpr_of_var_vl st vl g t v = (vl', g', t', pe) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    rewrite /zpexpr_of_var_vl. case Hfind: (SSAVM.find v t).
    - case=> ? ? ? ? Hnew Hsize Hcon; subst. exact: Hcon.
    - case=> ? ? ? ? Hnew Hsize Hcon; subst.
      exact: (rcons_add_consistent Hnew Hsize Hcon).
  Qed.

  Lemma zpexpr_of_zexp_vl_consistent st vl g t e vl' g' t' pe :
    zpexpr_of_zexp_vl st vl g t e = (vl', g', t', pe) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> v ivl ig it ovl og ot pe Hvl Hnew Hsize Hcon.
      exact: (zpexpr_of_var_vl_consistent Hvl Hnew Hsize Hcon).
    - move=> n ivl ig it ovl og ot pe. case=> ? ? ? ? Hnew Hsize Hcon; subst.
      exact: Hcon.
    - move=> op e IH ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl' g'] t'] pe'] Hpe].
      case=> ? ? ? ? Hnew Hsize Hcon; subst.
      exact: (IH _ _ _ _ _ _ _ Hpe Hnew Hsize Hcon).
    - move=> op e1 IH1 e2 IH2 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? Hnew Hsize Hcon; subst. apply: (IH2 _ _ _ _ _ _ _ Hpe2).
      + exact: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew).
      + exact: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize).
      + exact: (IH1 _ _ _ _ _ _ _ Hpe1 Hnew Hsize Hcon).
    - move=> e IH n ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl' g'] t'] pe'] Hpe].
      case=> ? ? ? ? Hnew Hsize Hcon; subst.
      exact: (IH _ _ _ _ _ _ _ Hpe Hnew Hsize Hcon).
  Qed.

  Lemma zpexprs_of_zexps_vl_consistent st vl g t es vl' g' t' pes :
    zpexprs_of_zexps_vl st vl g t es = (vl', g', t', pes) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: es st vl g t vl' g' t' pes => [| e es IH] st vl g t vl' g' t' pes //=.
    - case=> ? ? ? ?; subst. done.
    - dcase (zpexpr_of_zexp_vl st vl g t e) => [[[[vl_hd g_hd] t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps_vl st vl_hd g_hd t_hd es) => [[[[vl_tl g_tl] t_tl] pe_tl] Htl].
      case=> ? ? ? ?; subst. move=> Hnew_g Hvl_g Hcon.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hhd) Hnew_g) => Hnew_ghd.
      move: (zpexpr_of_zexp_vl_size_bounded Hhd Hvl_g) => Hvl_ghd.
      apply: (IH _ _ _ _ _ _ _ _ Htl Hnew_ghd Hvl_ghd).
      exact: (zpexpr_of_zexp_vl_consistent Hhd Hnew_g Hvl_g Hcon).
  Qed.

  Lemma zpexpr_of_premise_vl_consistent st vl g t e vl' g' t' pe pf :
    @zpexpr_of_premise_vl st vl g t e pf = (vl', g', t', pe) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: e vl g t vl' g' t' pe pf => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe _.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case => ? ? ? ? Hnew Hsize Hcon; subst.
      apply: (zpexpr_of_zexp_vl_consistent Hpe2).
      + exact: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew).
      + exact: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize).
      + exact: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon).
    - move=> e1 e2 ms ivl ig it ovl og ot pe pf.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hpems].
      case => ? ? ? ? Hnew Hsize Hcon; subst.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexprs_of_zexps_newer (zpexprs_of_zexps_vl_novl Hpems) Hnew2) => Hnewms.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      move: (zpexprs_of_zexps_vl_size_bounded Hpems Hsize2) => Hsizems.
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      move: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1 Hcon1) => Hcon2.
      move: (zpexprs_of_zexps_vl_consistent Hpems Hnew2 Hsize2 Hcon2) => Hconms.
      exact: (cat_consistent _ Hnewms Hsizems Hconms).
  Qed.

  Lemma zpexprs_of_premises_vl_consistent st vl g t es vl' g' t' pes pf :
    @zpexprs_of_premises_vl st vl g t es pf = (vl', g', t', pes) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: es vl g t vl' g' t' pes pf => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes _ [] ? ? ? ? Hnew Hsize Hcon; subst. assumption.
    - move=> ivl ig it ovl og ot opes opf.
      dcase (@zpexpr_of_premise_vl st ivl ig it hd (pf_hd opf))
      => [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (@zpexprs_of_premises_vl st vl_hd g_hd t_hd tl (pf_tl opf)) =>
      [[[[vl_tl g_tl] t_tl] es_tl] Hpe_tl]. case=> ? ? ? ? Hnew Hsize Hcon; subst.
      apply: (IH _ _ _ _ _ _ _ _ Hpe_tl).
      + exact: (zpexpr_of_premise_newer (zpexpr_of_premise_vl_novl Hpe_hd) Hnew).
      + exact: (zpexpr_of_premise_vl_size_bounded Hpe_hd).
      + exact: (zpexpr_of_premise_vl_consistent Hpe_hd Hnew Hsize Hcon).
  Qed.

  Lemma zpexpr_of_conseq_vl_consistent st vl g t e vl' g' t' pe pms :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pms) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: e vl g t vl' g' t' pe pms => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe pms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ? Hnew Hsize Hcon; subst.
      apply: (zpexpr_of_zexp_vl_consistent Hpe2).
      + exact: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew).
      + exact: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize).
      + exact: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon).
    - move=> e1 e2 ms ivl ig it ovl og ot pe pms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hpems].
      case => ? ? ? ? ? Hnew Hsize Hcon; subst.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      apply: (zpexprs_of_zexps_vl_consistent Hpems Hnew2 Hsize2).
      apply: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1).
      exact: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon).
  Qed.

  Lemma imp_of_arep_vl_consistent st sp vl g t ps m q pf :
    @imp_of_arep_vl st sp pf = (vl, g, t, ps, m, q) ->
    consistent st vl t.
  Proof.
    rewrite /imp_of_arep_vl.
    dcase (@zpexprs_of_premises_vl st init_vl init_pos init_vm (apremises sp) pf) =>
    [[[[vl_p g_p] t_p] ps_p] Hpe_p].
    dcase (zpexpr_of_conseq_vl st vl_p g_p t_p (aconseq sp)) =>
    [[[[[vl_q g_q] t_q] oq] om] Hpe_q].
    case=> ? ? ? ? ? ?; subst.
    move: (zpexprs_of_premises_newer (zpexprs_of_premises_vl_novl Hpe_p)
                                     init_newer_than_vm) => Hnew_p.
    move: (zpexprs_of_premises_vl_size_bounded Hpe_p init_vl_size_bounded) => Hsize_p.
    apply: (zpexpr_of_conseq_vl_consistent Hpe_q Hnew_p Hsize_p).
    apply: (zpexprs_of_premises_vl_consistent
              Hpe_p init_newer_than_vm init_vl_size_bounded).
    exact: init_consistent.
  Qed.



  (* Relate ZPEeval and ZSSA.eval_zexp *)

  Lemma zpexpr_of_var_vl_zpeeval_some st vl g t v vl' g' t' pe pv :
    consistent st vl t -> SSAVM.find v t = Some pv ->
    zpexpr_of_var_vl st vl g t v = (vl', g', t', pe) ->
    ZPEeval vl' pe = ZSSAStore.acc v st.
  Proof.
    move=> Hcon Hfind. rewrite /zpexpr_of_var_vl. rewrite Hfind.
    case=> ? ? ? ?; subst. exact: (consistent_zpeeval_some Hcon Hfind).
  Qed.

  Lemma zpexpr_of_var_vl_zpeeval_none st vl g t v vl' g' t' pe :
    vl_size_bounded vl g -> SSAVM.find v t = None ->
    zpexpr_of_var_vl st vl g t v = (vl', g', t', pe) ->
    ZPEeval vl' pe = ZSSAStore.acc v st.
  Proof.
    move=> Hsize Hfind. rewrite /zpexpr_of_var_vl. rewrite Hfind.
    case=> ? ? ? ?; subst. exact: (zpeeval_rcons_last _ Hsize).
  Qed.

  Lemma zpexpr_of_var_vl_zpeeval st vl g t v vl' g' t' pe :
    vl_size_bounded vl g -> consistent st vl t ->
    zpexpr_of_var_vl st vl g t v = (vl', g', t', pe) ->
    ZPEeval vl' pe = ZSSAStore.acc v st.
  Proof.
    move=> Hsize Hcon Hvl. case Hfind: (SSAVM.find v t).
    - exact: (zpexpr_of_var_vl_zpeeval_some Hcon Hfind Hvl).
    - exact: (zpexpr_of_var_vl_zpeeval_none Hsize Hfind Hvl).
  Qed.

  Lemma zpexpr_of_zexp_vl_zpeeval st vl g t e vl' g' t' pe :
    zpexpr_of_zexp_vl st vl g t e = (vl', g', t', pe) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    ZPEeval vl' pe = ZSSA.eval_zexp e st.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> v ivl ig it ovl og ot pe Hvl Hnew Hsize Hcon.
      exact: (zpexpr_of_var_vl_zpeeval Hsize Hcon Hvl).
    - move=> n ivl ig it ovl og ot pe [] ? ? ? ? Hnew Hsize Hcon; subst. reflexivity.
    - move=> op e IH ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl' g'] t'] pe'] Hpe].
      case=> ? ? ? ? Hnew Hsize Hcon; subst.
      rewrite -(IH _ _ _ _ _ _ _ Hpe Hnew Hsize Hcon). exact: zpexpr_of_eunop_zpeeval.
    - move=> op e1 IH1 e2 IH2 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? Hnew Hsize Hcon; subst.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      move: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1 Hcon1) => Hcon2.
      rewrite -(IH2 _ _ _ _ _ _ _ Hpe2 Hnew1 Hsize1 Hcon1).
      rewrite -(IH1 _ _ _ _ _ _ _ Hpe1 Hnew Hsize Hcon).
      rewrite (@prefix_of_zpeeval vl1 ovl g1 pe1).
      + exact: zpexpr_of_ebinop_zpeeval.
      + exact: (zpexpr_of_zexp_vl_prefix_of Hpe2).
      + assumption.
      + exact: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe1) Hnew).
    - move=> e IH n ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e) => [[[[vl' g'] t'] pe'] Hpe].
      case=> ? ? ? ? Hnew Hsize Hcon; subst.
      rewrite -(IH _ _ _ _ _ _ _ Hpe Hnew Hsize Hcon). reflexivity.
  Qed.

  Lemma zpexprs_of_zexps_vl_zpeevals st vl g t es vl' g' t' pes :
    zpexprs_of_zexps_vl st vl g t es = (vl', g', t', pes) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    ZPEevals vl' pes = ZSSA.eval_zexps es st.
  Proof.
    elim: es st vl g t vl' g' t' pes => [| e es IH] st vl g t vl' g' t' pes //=.
    - case=> ? ? ? ?; subst. done.
    - dcase (zpexpr_of_zexp_vl st vl g t e) => [[[[vl_hd g_hd] t_hd] pe_hd] Hhd].
      dcase (zpexprs_of_zexps_vl st vl_hd g_hd t_hd es) => [[[[vl_tl g_tl] t_tl] pe_tl] Htl].
      case=> ? ? ? ?; subst. move=> Hnew Hvl Hcon /=.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hhd) Hnew) => Hnew_hd.
      move: (zpexpr_of_zexp_vl_size_bounded Hhd Hvl) => Hvl_hd.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hhd) Hnew) => Hbd_hd.
      move: (zpexpr_of_zexp_vl_consistent Hhd Hnew Hvl Hcon) => Hcon_hd.
      move: (zpexprs_of_zexps_vl_prefix_of Htl) => Hpre_hd.
      (* rewrite `ZPEeval vl' pe_hd` *)
      move: (zpexpr_of_zexp_vl_zpeeval Hhd Hnew Hvl Hcon).
      rewrite (prefix_of_zpeeval Hpre_hd Hvl_hd Hbd_hd) => ->.
      (* rewrite `ZPEevals vl' pe_tl` *)
      move: (IH _ _ _ _ _ _ _ _ Htl Hnew_hd Hvl_hd Hcon_hd) => ->.
      reflexivity.
  Qed.

  Lemma zpeevals_pvars vlms gms ks :
    vl_size_bounded vlms gms ->
    ZPEevals (vlms ++ ks) (pvars gms (size ks)) = ks.
  Proof.
    elim: ks vlms gms => [| k ks IH] vlms gms //=. move=> Hvl.
    rewrite -cat_rcons. rewrite (IH _ _ (rcons_vl_size_bounded _ Hvl)).
    rewrite /vl_size_bounded in Hvl. rewrite bnth_cat.
    - rewrite bnth_rcons_last; first reflexivity. rewrite Hvl.
      rewrite subnK; first reflexivity. exact: pos_to_nat_is_pos.
    - rewrite size_rcons Hvl. rewrite -addn1.
      rewrite subnK; first exact: leqnn. exact: pos_to_nat_is_pos.
  Qed.

  Lemma zpexpr_of_premise_vl_zpeeval st vl g t e vl' g' t' pe pf :
    @zpexpr_of_premise_vl st vl g t e pf = (vl', g', t', pe) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    ZPEeval vl' pe = 0 <-> eval_azbexp e st.
  Proof.
    elim: e vl g t vl' g' t' pe pf => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe _.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case => ? ? ? ? Hnew Hsize Hcon; subst; simpl.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hzb1.
      move: (zpexpr_of_zexp_vl_prefix_of Hpe2) => Hprefix_of12.
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe2 Hnew1 Hsize1 Hcon1).
      rewrite -(prefix_of_zpeeval Hprefix_of12 Hsize1 Hzb1).
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe1 Hnew Hsize Hcon).
      split; [exact: Zminus_eq | exact: Zeq_minus].
    - move=> e1 e2 ms ivl ig it ovl og ot pe pf.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 ms) => [[[[vlms gms] tms] pems] Hpems].
      case => ? ? ? ? Hnew Hsize Hcon; subst.
      set ks := xchoose_zeqms_ext pf.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      move: (zpexprs_of_zexps_vl_size_bounded Hpems Hsize2) => Hsizems.
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      move: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1 Hcon1) => Hcon2.
      move: (zpexpr_of_zexp_gen (zpexpr_of_zexp_vl_novl Hpe2)) => Hg12.
      move: (zpexprs_of_zexps_gen (zpexprs_of_zexps_vl_novl Hpems)) => Hg2ms.
      move: (Pos.le_trans _ _ _ Hg12 Hg2ms) => Hg1ms.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe1) Hnew) =>
      Hzb11.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) =>
      Hzb22.
      move: (zpexprs_of_zexps_zpexprs_bounded (zpexprs_of_zexps_vl_novl Hpems) Hnew2) =>
      Hzb3ms.
      move: (zpexpr_bounded_ge_bounded Hg1ms Hzb11) => Hzb1ms.
      move: (zpexpr_bounded_ge_bounded Hg2ms Hzb22) => Hzb2ms.
      move: (zpexpr_of_zexp_vl_prefix_of Hpe2) => Hprefix_of12.
      move: (zpexprs_of_zexps_vl_prefix_of Hpems) => Hprefix_of2ms.
      move: (prefix_of_trans Hprefix_of12 Hprefix_of2ms) => Hprefix_of1ms.
      move: (prefix_of_cat ks (prefix_of_refl vlms)) => Hprefix_ofvlms.

      rewrite /zeqms /=.
      rewrite ZPEeval_peadds ZPEevals_pemuls.

      (* rewrite pe1 *)
      rewrite -(prefix_of_zpeeval Hprefix_ofvlms Hsizems Hzb1ms).
      rewrite -(prefix_of_zpeeval Hprefix_of1ms Hsize1 Hzb11).
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe1 Hnew Hsize Hcon).

      (* rewrite pe2 *)
      rewrite -(prefix_of_zpeeval Hprefix_ofvlms Hsizems Hzb2ms).
      rewrite -(prefix_of_zpeeval Hprefix_of2ms Hsize2 Hzb22).
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe2 Hnew1 Hsize1 Hcon1).

      (* rewrite pems *)
      move: (size_xchoose_zeqms_ext pf). rewrite ZSSA.size_eval_zexps => Hsize_ks.
      rewrite -Hsize_ks. rewrite (zpeevals_pvars _ Hsizems).
      rewrite -(prefix_of_zpeevals Hprefix_ofvlms Hsizems Hzb3ms).
      rewrite (zpexprs_of_zexps_vl_zpeevals Hpems Hnew2 Hsize2 Hcon2).
      (* *)
      split.
      + move=> H; exists ks. apply/eqP. exact: (Zminus_eq _ _ H).
      + move=> _. rewrite -xchoose_zeqms_ext_sound. exact: Z.sub_diag.
  Qed.

  Lemma zpexprs_of_premises_vl_zpeeval st vl g t es vl' g' t' pes pf :
    @zpexprs_of_premises_vl st vl g t es pf = (vl', g', t', pes) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    (forall e : azbexp, e \in es -> eval_azbexp e st) ->
    zpexpr_all0 vl' pes.
  Proof.
    elim: es vl g t vl' g' t' pes pf => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes _ [] ? ? ? ? Hnew Hsize Hcon Hsz; subst. done.
    - move=> ivl ig it ovl og ot opes opf.
      dcase (@zpexpr_of_premise_vl st ivl ig it hd (pf_hd opf)) =>
      [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (@zpexprs_of_premises_vl st vl_hd g_hd t_hd tl (pf_tl opf)) =>
      [[[[vl_tl g_tl] t_tl] es_tl] Hpe_tl].
      case=> ? ? ? ? Hnew Hsize Hcon Hsz; subst. split.
      + move: (zpexprs_of_premises_vl_prefix_of Hpe_tl) => Hprefix_of_hd.
        move: (zpexpr_of_premise_vl_size_bounded Hpe_hd Hsize) => Hsize_hd.
        move: (zpexpr_of_premise_zpexpr_bounded (zpexpr_of_premise_vl_novl Hpe_hd)
                                                Hnew) => Hbounded_hd.
        rewrite -(prefix_of_zpeeval Hprefix_of_hd Hsize_hd Hbounded_hd).
        apply/(zpexpr_of_premise_vl_zpeeval Hpe_hd Hnew Hsize Hcon). apply: Hsz.
        by rewrite in_cons eqxx.
      + move: (zpexpr_of_premise_newer (zpexpr_of_premise_vl_novl Hpe_hd) Hnew) =>
        Hnew_hd. move: (zpexpr_of_premise_vl_size_bounded Hpe_hd Hsize) => Hsize_hd.
        move: (zpexpr_of_premise_vl_consistent Hpe_hd Hnew Hsize Hcon) => Hcon_hd.
        apply: (IH _ _ _ _ _ _ _ _ Hpe_tl Hnew_hd Hsize_hd Hcon_hd). move=> e Hin.
        apply: Hsz. by rewrite in_cons Hin orbT.
  Qed.

  Lemma zpexpr_of_conseq_vl_eval_azbexp st vl g t e vl' g' t' pe pms :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pms) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    (exists ks : seq Z, ZPEeval vl' pe = zadds (zmuls2 ks (ZPEevals vl' pms))) ->
    eval_azbexp e st.
  Proof.
    elim: e vl g t vl' g' t' pe pms => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope opms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ? Hnew Hsize Hcon [ks Heq]; subst.
      rewrite /= in Heq. rewrite zadds_zmuls2_all0_r in Heq; last by done.
      move: (Zminus_eq _ _ Heq) => {Heq}.
      (* rewrite pe1 *)
      move: (zpexpr_of_zexp_vl_prefix_of Hpe2) => Hpre1o.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hzb1.
      rewrite -(prefix_of_zpeeval Hpre1o Hsize1 Hzb1).
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe1 Hnew Hsize Hcon).
      (* rewrite pe2 *)
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe2 Hnew1 Hsize1 Hcon1).
      (**)
      by apply.
    - move=> e1 e2 e3 ivl ig it ovl og ot ope opms.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexprs_of_zexps_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case=> ? ? ? ? ? Hnew Hsize Hcon [ks Heq]; subst. exists ks.
      rewrite /= in Heq. move: Heq.
      (* rewrite pe1 *)
      move: (zpexpr_of_zexp_vl_prefix_of Hpe2) => Hpre12.
      move: (zpexprs_of_zexps_vl_prefix_of Hpe3) => Hpre2o.
      move: (prefix_of_trans Hpre12 Hpre2o) => Hpre1o.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hzb1.
      rewrite -(prefix_of_zpeeval Hpre1o Hsize1 Hzb1).
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe1 Hnew Hsize Hcon).
      (* rewrite pe2 *)
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hzb2.
      rewrite -(prefix_of_zpeeval Hpre2o Hsize2 Hzb2).
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe2 Hnew1 Hsize1 Hcon1).
      (* rewrite opm *)
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1 Hcon1) => Hcon2.
      rewrite (zpexprs_of_zexps_vl_zpeevals Hpe3 Hnew2 Hsize2 Hcon2).
      (* *)
      intro; apply/eqP; assumption.
  Qed.



  (* Convert store to vl *)

  Definition vl_of_store (st : ZSSAStore.t) (sp : arep) (pf : forall e : azbexp, e \in apremises sp -> eval_azbexp e st) :
    list Z :=
    let '(vl, _, _, _, _, _) := @imp_of_arep_vl st sp pf in
    vl.

  Lemma vl_of_store_premises st sp g t ps m q :
    imp_of_arep sp = (g, t, ps, m, q) ->
    forall pf : (forall e : azbexp, e \in apremises sp -> eval_azbexp e st),
    zpexpr_all0 (@vl_of_store st sp pf) ps.
  Proof.
    case: sp => [pres post] /=. rewrite /vl_of_store. move=> Himp pf.
    dcase (@imp_of_arep_vl st {| apremises := pres; aconseq := post |} pf) =>
            [[[[[[ovl og] ot] ops] om] oq] Hpe].
    rewrite (imp_of_arep_vl_novl Hpe) in Himp. case: Himp=> ? ? ? ? ?; subst.
    move: Hpe; rewrite /imp_of_arep_vl /=.
    dcase (@zpexprs_of_premises_vl st init_vl init_pos init_vm pres pf) =>
    [[[[vl_p g_p] t_p] ps_p] Hpe_p].
    dcase (zpexpr_of_conseq_vl st vl_p g_p t_p post) =>
    [[[[[vl_q g_q] t_q] q_q] m_q] Hpe_q].
    case=> ? ? ? ? ? ?; subst.
    apply: (prefix_of_zpexpr_all0
              (zpexpr_of_conseq_vl_prefix_of Hpe_q)
              (zpexprs_of_premises_vl_size_bounded Hpe_p init_vl_size_bounded)
              (zpexprs_of_premises_zpexprs_bounded (zpexprs_of_premises_vl_novl Hpe_p)
                                                   init_newer_than_vm)).
    exact: (zpexprs_of_premises_vl_zpeeval
              Hpe_p init_newer_than_vm init_vl_size_bounded (init_consistent _) pf).
  Qed.

  Lemma vl_of_store_conseq st sp g t ps ms q :
    imp_of_arep sp = (g, t, ps, ms, q) ->
    forall pf : (forall e : azbexp, e \in apremises sp -> eval_azbexp e st),
    (exists ks, ZPEeval (@vl_of_store st sp pf) q = zadds (zmuls2 ks (ZPEevals (@vl_of_store st sp pf) ms))) ->
    eval_azbexp (aconseq sp) st.
  Proof.
    case: sp => [pres post] /=. rewrite /vl_of_store.
    move=> Himp pf.
    dcase (@imp_of_arep_vl st {| apremises := pres; aconseq := post |} pf) =>
    [[[[[[ovl og] ot] ops] om] oq] Hpe].
    rewrite (imp_of_arep_vl_novl Hpe) in Himp. case: Himp=> ? ? ? ? ?; subst.
    move: Hpe; rewrite /imp_of_arep_vl /=.
    dcase (@zpexprs_of_premises_vl st init_vl init_pos init_vm pres pf) =>
    [[[[vl_p g_p] t_p] ps_p] Hpe_p].
    dcase (zpexpr_of_conseq_vl st vl_p g_p t_p post) =>
    [[[[[vl_q g_q] t_q] q_q] m_q] Hpe_q].
    case=> ? ? ? ? ? ?; subst. move=> Heval.
    move: (zpexprs_of_premises_newer (zpexprs_of_premises_vl_novl Hpe_p)
                                     init_newer_than_vm) => Hnew_p.
    move: (zpexprs_of_premises_vl_size_bounded Hpe_p init_vl_size_bounded) => Hsize_p.
    move: (zpexprs_of_premises_vl_consistent
             Hpe_p init_newer_than_vm init_vl_size_bounded (init_consistent _)) =>
    Hcon_p.
    exact: (zpexpr_of_conseq_vl_eval_azbexp Hpe_q Hnew_p Hsize_p Hcon_p Heval).
  Qed.

End REP2IMP.


Module PS <: SsrFSet := FSets.MakeTreeSet PositiveOrder.

Section PExprAux.

  Variable C : Type.

  Variable ceq : C -> C -> bool.

  Fixpoint vars_pexpr (e : PExpr C) : PS.t :=
    match e with
    | PEO
    | PEI
    | PEc _ => PS.empty
    | PEX j => PS.singleton j
    | PEopp e => vars_pexpr e
    | PEadd e1 e2
    | PEsub e1 e2
    | PEmul e1 e2 => PS.union (vars_pexpr e1) (vars_pexpr e2)
    | PEpow e _ => vars_pexpr e
    end.

  Fixpoint subst_pexpr (p r e : PExpr C) : PExpr C :=
    if Field_theory.PExpr_eq ceq e p then r
    else match e with
         | PEadd e1 e2 => PEadd (subst_pexpr p r e1) (subst_pexpr p r e2)
         | PEsub e1 e2 => PEsub (subst_pexpr p r e1) (subst_pexpr p r e2)
         | PEmul e1 e2 => PEmul (subst_pexpr p r e1) (subst_pexpr p r e2)
         | PEopp e => PEopp (subst_pexpr p r e)
         | PEpow e n => PEpow (subst_pexpr p r e) n
         | _ => e
         end.

  Definition subst_pexprs (p r : PExpr C) (es : seq (PExpr C)) : seq (PExpr C) :=
    tmap (subst_pexpr p r) es.

  Lemma subst_pexprs_cons p r e es :
    subst_pexprs p r (e::es) = subst_pexpr p r e :: subst_pexprs p r es.
  Proof. rewrite /subst_pexprs !tmap_map /=. reflexivity. Qed.

  Lemma subst_pexprs_cat p r es1 es2 :
    subst_pexprs p r (es1 ++ es2) = subst_pexprs p r es1 ++ subst_pexprs p r es2.
  Proof. rewrite /subst_pexprs !tmap_map /=. exact: map_cat. Qed.

  Fixpoint pexpr_single_variables (e : PExpr C) :=
    match e with
    | PEO
    | PEI
    | PEc _ => PS.empty
    | PEX j => PS.singleton j
    | PEopp e => pexpr_single_variables e
    | PEadd e1 e2 => PS.union (pexpr_single_variables e1) (pexpr_single_variables e2)
    | PEsub e1 e2 => PS.union (pexpr_single_variables e1) (pexpr_single_variables e2)
    | PEmul _ _ => PS.empty
    | PEpow _ _ => PS.empty
    end.

  Fixpoint pexpr_num_occurrence (v : positive) (e : PExpr C) :=
    match e with
    | PEI
    | PEO
    | PEc _ => 0
    | PEX j => if j == v then 1 else 0
    | PEopp e => pexpr_num_occurrence v e
    | PEadd e1 e2
    | PEsub e1 e2
    | PEmul e1 e2 => pexpr_num_occurrence v e1 + pexpr_num_occurrence v e2
    | PEpow e _ => pexpr_num_occurrence v e
    end.

  Fixpoint pexpr_separate (v : positive) (e : PExpr C) (pat : PExpr C) {struct e} :=
    match e with
    | PEO
    | PEI
    | PEc _ => None
    | PEX j => if j == v then Some pat
               else None
    | PEopp e => if PS.mem v (vars_pexpr e) then pexpr_separate v e (PEopp pat)
                 else None
    | PEadd e1 e2 =>
       let in1 := PS.mem v (vars_pexpr e1) in
       let in2 := PS.mem v (vars_pexpr e2) in
       match in1, in2 with
       | true, false => pexpr_separate v e1 (PEsub pat e2)
       | false, true => pexpr_separate v e2 (PEsub pat e1)
       | _, _ => None
       end
    | PEsub e1 e2 =>
       let in1 := PS.mem v (vars_pexpr e1) in
       let in2 := PS.mem v (vars_pexpr e2) in
       match in1, in2 with
       | true, false => pexpr_separate v e1 (PEadd pat e2)
       | false, true => pexpr_separate v e2 (PEsub e1 pat)
       | _, _ => None
       end
    | PEmul _ _ => None
    | PEpow _ _ => None
    end.

  Definition pexpr_get_rewrite_pattern (e : PExpr C) :=
    let candidates := PS.filter (fun v => pexpr_num_occurrence v e == 1) (pexpr_single_variables e) in
    if PS.cardinal candidates == 0 then
      None
    else
      match PS.min_elt candidates with
      | None => None
      | Some v =>
          match pexpr_separate v e PEO with
          | None => None
          | Some pat =>
              Some (v, pat)
          end
      end.

  (* Do not add too many cases in this function.
     Otherwise it will take much more time in proving zpexpr_is_assignment_equal. *)
  Definition pexpr_is_assignment (e : PExpr C) : option (positive * PExpr C) :=
    match e with
    (* v - e = 0, e - v = 0; v = e*)
    | PEsub (PEX j) e
    | PEsub e (PEX j) => Some (j, e)
    (* v + e = 0, e + v = 0; v = -e *)
    | PEadd (PEX j) e
    | PEadd e (PEX j) => Some (j, PEopp e)
    (* v + e1 = e2, e2 = v + e1 *)
    | PEsub (PEadd (PEX j) e1) e2
    | PEsub e2 (PEadd (PEX j) e1) => Some (j, PEsub e2 e1)
    (* others *)
    | _ => pexpr_get_rewrite_pattern e
    end.

  (* String outputs *)

  Variable string_of_zero : string.
  Variable string_of_identity : string.
  Variable string_of_const : C -> string.

  Fixpoint string_of_pexpr (e : PExpr C) : string :=
    match e with
    | PEO => string_of_zero
    | PEI => string_of_identity
    | PEc c => string_of_const c
    | PEX j => BinaryString.of_pos j
    | PEopp e => ("- " ++ string_of_pexpr' e)%string
    | PEadd e1 e2 => (string_of_pexpr' e1 ++ " + " ++ string_of_pexpr' e2)%string
    | PEsub e1 e2 => (string_of_pexpr' e1 ++ " - " ++ string_of_pexpr' e2)%string
    | PEmul e1 e2 => (string_of_pexpr' e1 ++ " * " ++ string_of_pexpr' e2)%string
    | PEpow e n => (string_of_pexpr' e ++ " ^ " ++ BinaryString.of_N n)%string
    end
  with
  string_of_pexpr' (e : PExpr C) : string :=
    match e with
    | PEO => string_of_zero
    | PEI => string_of_identity
    | PEc c => string_of_const c
    | PEX j => BinaryString.of_pos j
    | PEopp e => ("(- " ++ string_of_pexpr e ++ ")")%string
    | PEadd e1 e2 => ("(" ++ string_of_pexpr e1 ++ " + " ++ string_of_pexpr e2 ++ ")")%string
    | PEsub e1 e2 => ("(" ++ string_of_pexpr e1 ++ " - " ++ string_of_pexpr e2 ++ ")")%string
    | PEmul e1 e2 => ("(" ++ string_of_pexpr e1 ++ " * " ++ string_of_pexpr e2 ++ ")")%string
    | PEpow e n => ("(" ++ string_of_pexpr e ++ " ^ " ++ BinaryString.of_N n ++ ")")%string
    end.

End PExprAux.

Definition string_of_zpexpr := string_of_pexpr "0" "1" BinaryString.of_Z.


Section IdealMembershipRewriting.

  Ltac simplify_zpeeval :=
    repeat match goal with
           | H : context f [ZPEeval _ PEO] |- _ => rewrite ZPEeval0 in H
           | H : context f [ZPEeval _ PEI] |- _ => rewrite ZPEeval1 in H
           | H : context f [ZPEeval _ (PEc _)] |- _ => rewrite ZPEeval_const in H
           | H : context f [ZPEeval _ (PEopp _)] |- _ => rewrite ZPEeval_opp in H
           | H : context f [ZPEeval _ (PEadd _ _)] |- _ => rewrite ZPEeval_add in H
           | H : context f [ZPEeval _ (PEsub _ _)] |- _ => rewrite ZPEeval_sub in H
           | H : context f [ZPEeval _ (PEmul _ _)] |- _ => rewrite ZPEeval_mul in H
           | H : context f [ZPEeval _ (PEpow _ _)] |- _ => rewrite ZPEeval_pow in H
           | |- context f [ZPEeval _ PEO] => rewrite ZPEeval0
           | |- context f [ZPEeval _ PEI] => rewrite ZPEeval1
           | |- context f [ZPEeval _ (PEc _)] => rewrite ZPEeval_const
           | |- context f [ZPEeval _ (PEopp _)] => rewrite ZPEeval_opp
           | |- context f [ZPEeval _ (PEadd _ _)] => rewrite ZPEeval_add
           | |- context f [ZPEeval _ (PEsub _ _)] => rewrite ZPEeval_sub
           | |- context f [ZPEeval _ (PEmul _ _)] => rewrite ZPEeval_mul
           | |- context f [ZPEeval _ (PEpow _ _)] => rewrite ZPEeval_pow
           end.

  (* Simplification of `Pexpr Z` *)

  Fixpoint simplify_zpexpr (e : PExpr Z) : PExpr Z :=
    match e with
    | PEO => e
    | PEI => e
    | PEc c => if c == 0%Z then PEO
               else if c == 1%Z then PEI
                    else e
    | PEX _ => e
    | PEopp e => let e' := simplify_zpexpr e in
                 match e' with
                 | PEopp e'' => e''
                 | _ => PEopp e'
                 end
    | PEadd e1 e2 => let e1' := simplify_zpexpr e1 in
                     let e2' := simplify_zpexpr e2 in
                     match e1', e2' with
                     | PEO, _ => e2'
                     | _, PEO => e1'
                     | _, _ => PEadd e1' e2'
                     end
    | PEsub e1 e2 => let e1' := simplify_zpexpr e1 in
                     let e2' := simplify_zpexpr e2 in
                     match e1', e2' with
                     | PEO, PEopp e2'' => e2''
                     | PEO, _ => PEopp e2'
                     | _, PEO => e1'
                     | _, PEopp e2'' => PEadd e1' e2''
                     | _, _ => PEsub e1' e2'
                     end
    | PEmul e1 e2 => let e1' := simplify_zpexpr e1 in
                     let e2' := simplify_zpexpr e2 in
                     match e1', e2' with
                     | PEO, _ => PEO
                     | PEI, _ => e2'
                     | _, PEO => PEO
                     | _, PEI => e1'
                     | _, _ => PEmul e1' e2'
                     end
    | PEpow e n => let e' := simplify_zpexpr e in
                   if n == 0%num then PEI
                   else if n == 1%num then e'
                        else match e' with
                             | PEO => PEO
                             | PEI => PEI
                             | _ => PEpow e' n
                             end
    end.

  Ltac tac :=
    repeat match goal with
           | H : match ?x with _ => _ end = _ |- _ =>
               destruct x; try solve [inversion H]
           end.

  Ltac mytac :=
    repeat match goal with
           | |- context f [if ?e then _ else _] =>
               let H := fresh in
               dcase e; case; [move/eqP => ?; subst|] => //
           end.

  Lemma simplify_zpexpr_zpeeval s e : ZPEeval s (simplify_zpexpr e) = ZPEeval s e.
  Proof.
    elim: e => //=.
    - move=> c. mytac; reflexivity.
    - move=> e1 IH1 e2 IH2. case He1: (simplify_zpexpr e1);
        (rewrite He1 in IH1; rewrite -IH1 -IH2; case: (simplify_zpexpr e2); intros;
            simplify_zpeeval; ring).
    - move=> e1 IH1 e2 IH2. case He1: (simplify_zpexpr e1);
        (rewrite He1 in IH1; rewrite -IH1 -IH2; case: (simplify_zpexpr e2); intros;
            simplify_zpeeval; ring).
    - move=> e1 IH1 e2 IH2. case He1: (simplify_zpexpr e1);
        (rewrite He1 in IH1; rewrite -IH1 -IH2; case: (simplify_zpexpr e2); intros;
            simplify_zpeeval; ring).
    - move=> e IH. case He: (simplify_zpexpr e);
        (rewrite He in IH; rewrite -IH; simplify_zpeeval; ring).
    - move=> e IH n. case Hn0: (n == 0%num).
      + rewrite (eqP Hn0). simplify_zpeeval. rewrite Z.pow_0_r. reflexivity.
      + case Hn1: (n == 1%num).
        * rewrite (eqP Hn1). rewrite IH. rewrite Z.pow_1_r. reflexivity.
        * have Hngt0: (0 < Z.of_N n)%Z.
          { replace 0%Z with (Z.of_N 0)%Z by reflexivity.
            apply/N2Z.inj_lt. apply/N.lt_nge. move=> Hne. move/negP: Hn0; apply.
            apply/eqP. move/N.le_0_r: Hne. by apply. }
          case He: (simplify_zpexpr e); rewrite He in IH; rewrite -IH; simplify_zpeeval;
            try ring.
          -- symmetry. exact: (Z.pow_0_l _ Hngt0).
          -- rewrite (Z.pow_1_l _ (Z.lt_le_incl _ _ Hngt0)). reflexivity.
  Qed.

  Lemma simplify_zpexpr_all0 s es :
    zpexpr_all0 s (map simplify_zpexpr es) <-> zpexpr_all0 s es.
  Proof.
    elim: es => [| e es [IH1 IH2]] //=.
    rewrite simplify_zpexpr_zpeeval. split.
    - move=> [He Hes]. move: (IH1 Hes) => {} Hes. tauto.
    - move=> [He Hes]. move: (IH2 Hes) => {} Hes. tauto.
  Qed.


  (* Substitution of `PExpr Z` *)

  Definition subst_zpexpr (p r e : PExpr Z) : PExpr Z := subst_pexpr Z.eqb p r e.

  Definition subst_zpexprs (p r : PExpr Z) (es : seq (PExpr Z)) : seq (PExpr Z) :=
    subst_pexprs Z.eqb p r es.

  Definition subst_zpexprs_cons
    : forall p r e es, subst_zpexprs p r (e::es) = subst_zpexpr p r e::subst_zpexprs p r es
    := subst_pexprs_cons Z.eqb.

  Definition subst_zpexprs_cat
    : forall p r es1 es2, subst_zpexprs p r (es1 ++ es2) =
                            subst_zpexprs p r es1 ++ subst_zpexprs p r es2
    := subst_pexprs_cat Z.eqb.


  (* Rewriting *)

  Definition zpexpr_is_assignment (e : PExpr Z) : option (positive * PExpr Z) :=
    match pexpr_is_assignment e with
    | None => None
    | Some (p, r) => Some (p, simplify_zpexpr r)
    end.

  Function simplify_generator_rec
           (visited : seq (PExpr Z)) (ps : seq (PExpr Z)) (q : PExpr Z)
           {wf (@size_lt (PExpr Z)) ps} :=
    match ps with
    | [::] => (rev visited, q)
    | e::es =>
        match zpexpr_is_assignment e with
        | None => simplify_generator_rec (e::visited) es q
        | Some (p, r) => simplify_generator_rec
                           (subst_zpexprs (PEX Z p) r visited)
                           (subst_zpexprs (PEX Z p) r es)
                           (subst_zpexpr (PEX Z p) r q)
        end
    end.
  Proof.
    - move=> _ ps _ e es ? [p' r'] p r [] ? ? Ha.
      rewrite /size_lt /subst_zpexprs /subst_pexprs tmap_map size_map /=.
      exact: Nat.lt_succ_diag_r.
    - move=> _ ps _ e es ? Ha. rewrite /size_lt /=. exact: Nat.lt_succ_diag_r.
    - exact: (well_founded_ltof (seq (PExpr Z)) size).
  Defined.

  Local Opaque ZPEeval.

  Lemma zpexpr_subst_valid (e p r : PExpr Z) s :
    ZPEeval s p = ZPEeval s r ->
    ZPEeval s e = ZPEeval s (subst_zpexpr p r e).
  Proof.
    elim: e => /=.
    - reflexivity.
    - reflexivity.
    - case: p => //=. move=> c1 c2 Hev. case H: (c2 =? c1)%Z => //=.
      move/Z.eqb_eq: H => ->. assumption.
    - case: p => //=. move=> c1 c2 Hev. case H: (c2 =? c1)%positive => //=.
      move/Pos.eqb_eq: H => ->. assumption.
    - case: p => //=; simplify_zpeeval.
      + move=> e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> c e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> j e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        case Heq31: (Field_theory.PExpr_eq Z.eqb e3 e1) => //=.
        * rewrite (zpexpr_eq_zpeeval s Heq31) in IH1 *.
          case Heq42: (Field_theory.PExpr_eq Z.eqb e4 e2) => //=.
          -- rewrite (zpexpr_eq_zpeeval s Heq42). exact: Hev.
          -- simplify_zpeeval. rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
        * simplify_zpeeval. rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 IH1 e3 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 n1 e2 IH1 e3 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
    - case: p => //=.
      + move=> e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> c e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> j e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        case Heq31: (Field_theory.PExpr_eq Z.eqb e3 e1) => //=.
        * rewrite (zpexpr_eq_zpeeval s Heq31) in IH1 *.
          case Heq42: (Field_theory.PExpr_eq Z.eqb e4 e2) => //=.
          -- rewrite (zpexpr_eq_zpeeval s Heq42). exact: Hev.
          -- simplify_zpeeval. rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
        * simplify_zpeeval. rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 IH1 e3 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 n1 e2 IH1 e3 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
    - case: p => //=.
      + move=> e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> c e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> j e1 IH1 e2 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 e3 IH1 e4 IH2 Hev; simplify_zpeeval.
        case Heq31: (Field_theory.PExpr_eq Z.eqb e3 e1) => //=.
        * rewrite (zpexpr_eq_zpeeval s Heq31) in IH1 *.
          case Heq42: (Field_theory.PExpr_eq Z.eqb e4 e2) => //=.
          -- rewrite (zpexpr_eq_zpeeval s Heq42). exact: Hev.
          -- simplify_zpeeval. rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
        * simplify_zpeeval. rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 e2 IH1 e3 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
      + move=> e1 n1 e2 IH1 e3 IH2 Hev; simplify_zpeeval.
        rewrite -(IH1 Hev) -(IH2 Hev). reflexivity.
    - case: p => //=.
      + move=> e IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> c e IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> j e IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 e3 IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 e3 IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 e3 IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 IH Hev; simplify_zpeeval.
        case Heq21: (Field_theory.PExpr_eq Z.eqb e2 e1) => //=.
        * rewrite (zpexpr_eq_zpeeval s Heq21) in IH *. exact: Hev.
        * simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> p n e IH Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
    - case: p => //=.
      + move=> e IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> c e IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> j e IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 e3 IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 e3 IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 e3 IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 e2 IH n Hev; simplify_zpeeval. rewrite -(IH Hev). reflexivity.
      + move=> e1 n e2 IH m Hev; simplify_zpeeval.
        case Heqmn: (m =? n)%num => //=.
        * move/N.eqb_eq: Heqmn => ?; subst.
          case Heq21: (Field_theory.PExpr_eq Z.eqb e2 e1).
          -- rewrite (zpexpr_eq_zpeeval s Heq21) in IH *. exact: Hev.
          -- simplify_zpeeval. rewrite -(IH Hev). reflexivity.
        * simplify_zpeeval. rewrite -(IH Hev). reflexivity.
  Qed.

  Lemma zpexpr_subst_all0 (p r : PExpr Z) (es : seq (PExpr Z)) s :
    ZPEeval s p = ZPEeval s r ->
    zpexpr_all0 s es <-> zpexpr_all0 s (subst_zpexprs p r es).
  Proof.
    elim: es => [| e es IH] //=. move=> Hpr. rewrite subst_zpexprs_cons.
    move: (IH Hpr) => {IH} [H1 H2]. rewrite zpexpr_all0_cons.
    rewrite -(zpexpr_subst_valid e Hpr). tauto.
  Qed.

  Lemma zpexpr_separate_some_eval
        (v : positive) (e : PExpr Z) (pat : PExpr Z) (r : PExpr Z) s :
    pexpr_separate v e pat = Some r ->
    ZPEeval s e = ZPEeval s pat ->
    ZPEeval s (PEX Z v) = ZPEeval s r.
  Proof.
    elim: e pat r => //=.
    - move=> v' pat r. case Hv: (v' == v); last by done.
      case=> ->.  rewrite (eqP Hv). move=> ->. reflexivity.
    - move=> e1 IH1 e2 IH2 pat r.
      (case Hmem1: (PS.mem v (vars_pexpr e1)); case Hmem2: (PS.mem v (vars_pexpr e2)));
      [done | | | done].
      + move=> Hsep /= Hev. apply: (IH1 _ _ Hsep) => /=. simplify_zpeeval. rewrite -Hev. ring.
      + move=> Hsep /= Hev. apply: (IH2 _ _ Hsep) => /=. simplify_zpeeval. rewrite -Hev. ring.
    - move=> e1 IH1 e2 IH2 pat r.
      (case Hmem1: (PS.mem v (vars_pexpr e1)); case Hmem2: (PS.mem v (vars_pexpr e2)));
      [done | | | done].
      + move=> Hsep /= Hev. apply: (IH1 _ _ Hsep) => /=. simplify_zpeeval. rewrite -Hev. ring.
      + move=> Hsep /= Hev. apply: (IH2 _ _ Hsep) => /=. simplify_zpeeval. rewrite -Hev. ring.
    - move=> e IH pat r. case Hmem: (PS.mem v (vars_pexpr e)); last by done.
      move=> Hsep /= Hev. apply: (IH _ _ Hsep) => /=. simplify_zpeeval. rewrite -Hev. ring.
  Qed.

  Lemma zpexpr_get_rewrite_pattern_eval e v r s :
    pexpr_get_rewrite_pattern e = Some (v, r) ->
    ZPEeval s e = 0%Z ->
    ZPEeval s (PEX Z v) = ZPEeval s r.
  Proof.
    rewrite /pexpr_get_rewrite_pattern.
    case: (PS.cardinal
             (PS.filter
                (fun v0 : PS.elt => pexpr_num_occurrence v0 e == 1) (pexpr_single_variables e)) == 0);
      first by done.
    case: (PS.min_elt
             (PS.filter
                (fun v0 : PS.elt => pexpr_num_occurrence v0 e == 1) (pexpr_single_variables e)));
      last by done.
    move=> v'. case Hsep: (pexpr_separate v' e PEO); last by done.
    case=> ? ?; subst. move=> Hev. exact: (zpexpr_separate_some_eval Hsep Hev).
  Qed.

  Ltac mytac ::=
    repeat match goal with
           | H : Some (_, _) = Some (_, _) |- _ =>
             case: H => ? ?; subst => /=
           | H : match ?e with | PEX _ => _ | _ => _ end = _ |- _ =>
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
           | H : ?l = 0%Z |- context f [?l] => rewrite H /=
           | H1 : pexpr_get_rewrite_pattern ?e = Some _,
               H2 : ZPEeval ?s ?e = 0%Z |- _ =>
               let H := fresh in
               (move: (zpexpr_get_rewrite_pattern_eval H1 H2) => /= H);
               clear H1
           | H : context f [ZPEeval _ PEO] |- _ => rewrite ZPEeval0 in H
           | H : context f [ZPEeval _ PEI] |- _ => rewrite ZPEeval1 in H
           | H : context f [ZPEeval _ (PEc _)] |- _ => rewrite ZPEeval_const in H
           | H : context f [ZPEeval _ (PEopp _)] |- _ => rewrite ZPEeval_opp in H
           | H : context f [ZPEeval _ (PEadd _ _)] |- _ => rewrite ZPEeval_add in H
           | H : context f [ZPEeval _ (PEsub _ _)] |- _ => rewrite ZPEeval_sub in H
           | H : context f [ZPEeval _ (PEmul _ _)] |- _ => rewrite ZPEeval_mul in H
           | H : context f [ZPEeval _ (PEpow _ _)] |- _ => rewrite ZPEeval_pow in H
           | |- context f [ZPEeval _ PEO] => rewrite ZPEeval0
           | |- context f [ZPEeval _ PEI] => rewrite ZPEeval1
           | |- context f [ZPEeval _ (PEc _)] => rewrite ZPEeval_const
           | |- context f [ZPEeval _ (PEopp _)] => rewrite ZPEeval_opp
           | |- context f [ZPEeval _ (PEadd _ _)] => rewrite ZPEeval_add
           | |- context f [ZPEeval _ (PEsub _ _)] => rewrite ZPEeval_sub
           | |- context f [ZPEeval _ (PEmul _ _)] => rewrite ZPEeval_mul
           | |- context f [ZPEeval _ (PEpow _ _)] => rewrite ZPEeval_pow
           end.

  Lemma zpexpr_is_assignment_equal e p r s :
    zpexpr_is_assignment e = Some (p, r) ->
    ZPEeval s e = 0%Z -> ZPEeval s (PEX Z p) = ZPEeval s r.
  Proof.
    rewrite /zpexpr_is_assignment. dcase (pexpr_is_assignment e); case=> //=.
    move=> [p' r'] => He [] ? ?; subst. rewrite simplify_zpexpr_zpeeval. move: He.
    case: e => //=.
    - move=> v. intros. by mytac.
    - move=> left right.
      (case: left; case: right => //=); intros; mytac; by lia.
    - move=> left right.
      (case: left; case: right => //=); intros; mytac; by lia.
    - move=> e; intros. mytac; by lia.
  Qed.

  Corollary zpexpr_subst_assignment_valid e p r e' s :
    zpexpr_is_assignment e = Some (p, r) -> ZPEeval s e = 0%Z ->
    ZPEeval s e' = ZPEeval s (subst_zpexpr (PEX Z p) r e').
  Proof.
    move=> His Hev. exact: (zpexpr_subst_valid _ (zpexpr_is_assignment_equal His Hev)).
  Qed.

  Lemma simplify_generator_rec_cons_is_assignment visited e es q p r :
    zpexpr_is_assignment e = Some (p, r) ->
    simplify_generator_rec visited (e::es) q =
      simplify_generator_rec (subst_zpexprs (PEX Z p) r visited)
                             (subst_zpexprs (PEX Z p) r es)
                             (subst_zpexpr (PEX Z p) r q).
  Proof.
    move=> Ha.
    dcase (simplify_generator_rec
             (subst_zpexprs (PEX Z p) r visited) (subst_zpexprs (PEX Z p) r es)
             (subst_zpexpr (PEX Z p) r q)) => [[visited' q'] Hs].
    move: (Logic.eq_sym Hs) => {} Hs.
    move: (R_simplify_generator_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_generator_rec_complete.
    apply: (R_simplify_generator_rec_2 _ _ _ _ _ _ _ _ Ha _ H). reflexivity.
  Qed.

  Lemma simplify_generator_rec_cons_not_assignment visited e es q :
    zpexpr_is_assignment e = None ->
    simplify_generator_rec visited (e::es) q =
    simplify_generator_rec (e::visited) es q.
  Proof.
    move=> Ha. dcase (simplify_generator_rec (e :: visited) es q) => [[visited' q'] Hs].
    move: (Logic.eq_sym Hs) => {} Hs.
    move: (R_simplify_generator_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_generator_rec_complete.
    apply: (R_simplify_generator_rec_1 _ _ _ _ _ _ Ha _ H). reflexivity.
  Qed.

  Lemma simplify_generator_rec_empty visited q :
    simplify_generator_rec visited [::] q = (rev visited, q).
  Proof. reflexivity. Qed.

  Lemma simplify_generator_rec_sound pre ps q ps' q' ms cms :
    simplify_generator_rec pre ps q = (ps', q') ->
    zpimply_eq ps' q' (peadds (pemuls cms ms)) ->
    zpimply_eq (rev pre ++ ps) q (peadds (pemuls cms ms)).
  Proof.
    have ->: ps' = (ps', q').1 by reflexivity.
    have ->: q' = (ps', q').2 by reflexivity.
    move: (ps', q'). clear ps' q'. eapply simplify_generator_rec_ind.
    - move=> {pre ps q} pre ps q Hps [ps' q'] [] ? ?; subst => /=.
      rewrite cats0. move=> Hs s Hev. apply: (Hs s). assumption.
    - move=> {pre ps q} pre ps q e es Hps Ha IH [ps' q']  /= Hrec Hs s He.
      apply: (IH _ Hrec Hs). rewrite rev_cons cat_rcons. assumption.
    - move=> {pre ps q} pre ps q e es Hps pat rep Ha IH [ps' q'] /= Hrec Hs s He.
      have He0: (ZPEeval s e = 0%Z).
      { apply: (zpexpr_all0_in He). apply: in_or_app. right. exact: in_eq. }
      rewrite (zpexpr_subst_assignment_valid q Ha He0). apply: (IH _ Hrec Hs).
      move/zpexpr_all0_cat: He => [Hpre Hees]. move/zpexpr_all0_rev: Hpre => Hpre.
      move/zpexpr_all0_cons: Hees => [He Hes]. apply/zpexpr_all0_cat.
      move: (zpexpr_is_assignment_equal Ha He0) => Hpr. split.
      + apply/zpexpr_all0_rev. move/(zpexpr_subst_all0 _ Hpr): Hpre. by apply.
      + move/(zpexpr_subst_all0 _ Hpr): Hes. by apply.
  Qed.

  Definition simplify_generator ps q : seq (PExpr Z) * PExpr Z :=
    let '(ps', q') := simplify_generator_rec
                        [::] (tmap simplify_zpexpr ps) (simplify_zpexpr q) in
    (ps', q').

  Lemma simplify_generator_sound ps q ps' q' ms cms :
    simplify_generator ps q = (ps', q') ->
    zpimply_eq ps' q' (peadds (pemuls cms ms)) ->
    zpimply_eq ps q (peadds (pemuls cms ms)).
  Proof.
    rewrite /simplify_generator. rewrite tmap_map.
    dcase (simplify_generator_rec [::] (map simplify_zpexpr ps) (simplify_zpexpr q)) =>
            [[ps1 q1] Himp]. case=> ? ?; subst. move=> Heq.
    move: (simplify_generator_rec_sound Himp Heq). rewrite cat0s.
    move=> H s Hps. move/simplify_zpexpr_all0: Hps => Hps.
    move: (H s Hps). rewrite simplify_zpexpr_zpeeval. by apply.
  Qed.


  (* Substitution with caches of appearing variables *)

  Definition subst_zpexpr_vars_cache
             (p : positive) (r : PExpr Z) vspr (ve : PS.t * PExpr Z) :=
    let vs := ve.1 in
    let e := ve.2 in
    if PS.mem p vs then (PS.remove p (PS.union vs vspr),
                            subst_zpexpr (PEX Z p) r e)
    else ve.

  Definition subst_zpexprs_vars_cache
             (p : positive) (r : PExpr Z) vspr (ves : seq (PS.t * PExpr Z)) :=
    tmap (subst_zpexpr_vars_cache p r vspr) ves.

  Lemma zpexpr_subst_vars_cache_valid e p r vspr s :
    ZPEeval s (PEX Z p) = ZPEeval s r ->
    ZPEeval s e.2 = ZPEeval s (subst_zpexpr_vars_cache p r vspr e).2.
  Proof.
    move=> Hev. rewrite /subst_zpexpr_vars_cache. case: (PS.mem p e.1) => /=.
    - exact: (zpexpr_subst_valid _ Hev).
    - tauto.
  Qed.

  Lemma zpexpr_subst_vars_cache_all0 p r vspr ves s :
    ZPEeval s (PEX Z p) = ZPEeval s r ->
    zpexpr_all0 s (split ves).2 <->
      zpexpr_all0 s (split (subst_zpexprs_vars_cache p r vspr ves)).2.
  Proof.
    elim: ves => [| [vse e] ves IH] //=. move=> Hpr. move: (IH Hpr) => {IH} [H1 H2].
    rewrite /subst_zpexprs_vars_cache
            tmap_map /= -tmap_map -/(subst_zpexprs_vars_cache p r vspr ves).
    dcase (split ves) => [[vses es] Hves].
    dcase (subst_zpexpr_vars_cache p r vspr (vse, e)) => [[vse' e'] Hsube].
    dcase (split (subst_zpexprs_vars_cache p r vspr ves)) => [[vses' es'] Hsubes] /=.
    rewrite Hves /= in H1 H2. rewrite Hsubes /= in H1 H2. split.
    - move=> [He Hes]. move: (zpexpr_subst_vars_cache_valid (vse, e) vspr Hpr).
      rewrite Hsube /= => <-. tauto.
    - move=> [He' Hes']. move: (zpexpr_subst_vars_cache_valid (vse, e) vspr Hpr).
      rewrite Hsube /= => ->. tauto.
  Qed.

  Lemma subst_zpexprs_vars_cache_cat es1 es2 p r vspr :
    subst_zpexprs_vars_cache p r vspr (es1 ++ es2) =
    subst_zpexprs_vars_cache p r vspr es1 ++ subst_zpexprs_vars_cache p r vspr es2.
  Proof. rewrite /subst_zpexprs_vars_cache. rewrite !tmap_map. exact: map_cat. Qed.

  Corollary zpexpr_subst_vars_cache_assignment_valid (ve : PS.t * PExpr Z) p r vspr ve' s :
    zpexpr_is_assignment ve.2 = Some (p, r) -> ZPEeval s ve.2 = 0%Z ->
    ZPEeval s ve'.2 = ZPEeval s (subst_zpexpr_vars_cache p r vspr ve').2.
  Proof.
    move=> His Hev. move: (zpexpr_is_assignment_equal His Hev) => Hpr.
    exact: (zpexpr_subst_vars_cache_valid _ _ Hpr).
  Qed.

  Function simplify_generator_vars_cache_rec
           (visited : seq (PS.t * PExpr Z)) (ps : seq (PS.t * PExpr Z))
           (q : (PS.t * PExpr Z))
           {wf (@size_lt (PS.t * PExpr Z)) ps} :=
    match ps with
    | [::] => (rev visited, q)
    | ve::ves =>
      match zpexpr_is_assignment ve.2 with
      | None => simplify_generator_vars_cache_rec (ve::visited) ves q
      | Some (p, r) => simplify_generator_vars_cache_rec
                         (subst_zpexprs_vars_cache p r ve.1 visited)
                         (subst_zpexprs_vars_cache p r ve.1 ves)
                         (subst_zpexpr_vars_cache p r ve.1 q)
      end
    end.
  Proof.
    - move=> _ ps _ e es ? [p' r'] p r [] ? ? Ha.
      rewrite /size_lt /subst_zpexprs_vars_cache /subst_zpexpr_vars_cache tmap_map size_map /=.
      exact: Nat.lt_succ_diag_r.
    - move=> _ ps _ e es ? Ha. rewrite /size_lt /=. exact: Nat.lt_succ_diag_r.
    - exact: (well_founded_ltof (seq (PS.t * PExpr Z)) size).
  Defined.

  Lemma simplify_generator_vars_cache_rec_cons_is_assignment visited ve ves q p r :
    zpexpr_is_assignment ve.2 = Some (p, r) ->
    simplify_generator_vars_cache_rec visited (ve::ves) q =
      simplify_generator_vars_cache_rec
        (subst_zpexprs_vars_cache p r ve.1 visited)
        (subst_zpexprs_vars_cache p r ve.1 ves)
        (subst_zpexpr_vars_cache p r ve.1 q).
  Proof.
    move=> Ha.
    dcase (simplify_generator_vars_cache_rec
             (subst_zpexprs_vars_cache p r ve.1 visited)
             (subst_zpexprs_vars_cache p r ve.1 ves)
             (subst_zpexpr_vars_cache p r ve.1 q)) =>
    [[visited' q'] Hs]. move: (Logic.eq_sym Hs) => {} Hs.
    move: (R_simplify_generator_vars_cache_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_generator_vars_cache_rec_complete.
    exact: (R_simplify_generator_vars_cache_rec_2 _ _ _ _ _ (Logic.eq_refl _) _ _ Ha _ H).
  Qed.

  Lemma simplify_generator_vars_cache_rec_cons_not_assignment visited ve ves q :
    zpexpr_is_assignment ve.2 = None ->
    simplify_generator_vars_cache_rec visited (ve::ves) q =
    simplify_generator_vars_cache_rec (ve::visited) ves q.
  Proof.
    move=> Ha. dcase (simplify_generator_vars_cache_rec (ve :: visited) ves q) =>
               [[visited' q'] Hs]. move: (Logic.eq_sym Hs) => {} Hs.
    move: (R_simplify_generator_vars_cache_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_generator_vars_cache_rec_complete.
    exact: (R_simplify_generator_vars_cache_rec_1 _ _ _ _ _ (Logic.eq_refl _) Ha _ H).
  Qed.

  Lemma simplify_generator_vars_cache_rec_empty visited q :
    simplify_generator_vars_cache_rec visited [::] q = (rev visited, q).
  Proof. reflexivity. Qed.

  Lemma simplify_generator_vars_cache_rec_sound vpre vps vq vps' vq' cms ms :
    simplify_generator_vars_cache_rec vpre vps vq = (vps', vq') ->
    zpimply_eq (split vps').2 vq'.2 (peadds (pemuls cms ms)) ->
    zpimply_eq (rev (split vpre).2 ++ (split vps).2) vq.2 (peadds (pemuls cms ms)).
  Proof.
    have ->: vps' = (vps', vq').1 by reflexivity.
    have ->: vq' = (vps', vq').2 by reflexivity.
    move: (vps', vq'). clear vps' vq'. eapply simplify_generator_vars_cache_rec_ind.
    - move=> {vpre vps vq} vpre vps vq Hvps [vps' vq'] [] ? ?; subst => /=.
      rewrite cats0. move=> Hs s Hev. apply: (Hs s). rewrite split_rev /=.
      assumption.
    - move=> {vpre vps vq} vpre vps vq ve ves Hps Ha IH [vps' vq']  // Hrec Hs s He.
      apply: (IH _ Hrec Hs). rewrite split_cons rev_cons.
      rewrite !zpexpr_all0_cat in He *. move: He => [He1 He2].
      rewrite split_cons /= in He2. move: He2 => [He2 He3]. rewrite zpexpr_all0_rcons.
      tauto.
    - move=> {vpre vps vq} vpre vps vq ve ves Hps p r Ha IH [vps' vq'] // Hrec Hs s He.
      rewrite zpexpr_all0_cat split_cons zpexpr_all0_cons in He.
      move: He => [He1 [He2 He3]]. simpl in Hs.
      rewrite (zpexpr_subst_vars_cache_assignment_valid ve.1 vq Ha He2).
      apply: (IH _ Hrec Hs). rewrite zpexpr_all0_cat.
      rewrite zpexpr_all0_rev. move: (zpexpr_is_assignment_equal Ha He2) => Hpr.
      rewrite zpexpr_all0_rev in He1. split.
      + move/(zpexpr_subst_vars_cache_all0 ve.1 _ Hpr): He1. by apply.
      + move/(zpexpr_subst_vars_cache_all0 ve.1 _ Hpr): He3. by apply.
  Qed.

  Definition pair_zpexpr_with_vars (e : PExpr Z) : PS.t * PExpr Z :=
    (vars_pexpr e, e).

  Lemma split_map_pair_zpexpr_with_vars (es : seq (PExpr Z)) :
    (split (map pair_zpexpr_with_vars es)).2 = es.
  Proof.
    elim: es => [| e es IH] //=. move: IH.
    dcase (split [seq pair_zpexpr_with_vars i | i <- es]) => [[vs es'] Hs].
    rewrite Hs /=. move=> ->. reflexivity.
  Qed.

  Definition simplify_generator_vars_cache ps q : seq (PExpr Z) * PExpr Z :=
    let vs_ps := tmap pair_zpexpr_with_vars (tmap simplify_zpexpr ps) in
    let vs_q := pair_zpexpr_with_vars (simplify_zpexpr q) in
    let '(vs_ps', vs_q') := simplify_generator_vars_cache_rec [::] vs_ps vs_q in
    ((split vs_ps').2, vs_q'.2).

  Lemma simplify_generator_vars_cache_sound ps q ps' q' ms cms :
    simplify_generator_vars_cache ps q = (ps', q') ->
    zpimply_eq ps' q' (peadds (pemuls cms ms)) ->
    zpimply_eq ps q (peadds (pemuls cms ms)).
  Proof.
    rewrite /simplify_generator_vars_cache.
    dcase (simplify_generator_vars_cache_rec
             [::] (tmap pair_zpexpr_with_vars (tmap simplify_zpexpr ps))
             (pair_zpexpr_with_vars (simplify_zpexpr q))) => [[vps' vq'] Hsimp].
    case=> ? ?; subst. move=> Heq.
    move: (simplify_generator_vars_cache_rec_sound Hsimp Heq).
    rewrite tmap_map. rewrite split_map_pair_zpexpr_with_vars cat0s => Heq2.
    move=> s Hps. rewrite -(Heq2 s).
    - rewrite /pair_zpexpr_with_vars /=. rewrite simplify_zpexpr_zpeeval.
      reflexivity.
    - rewrite tmap_map. apply/simplify_zpexpr_all0. assumption.
  Qed.

End IdealMembershipRewriting.


Section Validator.

  Local Open Scope Z_scope.

  (** Validate the answer (cps, cms) of an ideal membership problem given as a
      tuple (ps, ms, q), i.e., check if q = cps * ps + cms * ms. *)
  Definition validate_imp_answer ps ms q cps cms : bool :=
    (size ps == size cps) && (size ms == size cms) &&
    zpexpr_eqb q (PEadd (peadds (pemuls cps ps)) (peadds (pemuls cms ms))).

  (* If q = cps * ps + cms * ms and for each p \in ps, p = 0, then q = cms * ms *)
  Lemma validated_imp_imply_eq ps ms q cps cms :
    validate_imp_answer ps ms q cps cms ->
    zpimply_eq ps q (peadds (pemuls cms ms)).
  Proof.
    move/andP=> [Hs Heq] l Heq0.
    (* Convert the syntactical equality in the hypotheses to semantic equality *)
    rewrite /zpexpr_eqb /ZPeq in Heq. move: (ZPeq_ok Heq) => {}Heq.
    move: (Heq l) => {}Heq.
    (* Convert Pol evaluation to PExpr evaluation *)
    move: Heq. rewrite -Znorm_subst_spec; try done.
    rewrite -Znorm_subst_spec; try done.
    (* rewrite q = cps * ps + cms * ms *)
    rewrite -/ZPEeval. move=> ->.
    (* Induction on ps *)
    rewrite /=. case: ps cps Hs Heq0 => [| hd tl] //=.
    - (* ps = [::] *) by case.
    - (* ps = hd::tl *) case=> //=. move=> cs_hd. (* cs = cs_hd::cs_tl *)
      elim: tl => [| tl_hd tl_tl IH] //=.
      + (* ps = [:: hd] *) case=> //=. (* cs = cs_hd *)
        move=> _ [-> _]. rewrite Z.mul_0_r !Z.add_0_l. reflexivity.
      + (* ps = hd::tl_hd::tl_tl *) case => //=. (* cs = cs_hd::cs_tl_hd::cs_tl_tl *)
        move=> cs_tl_hd cs_tl_tl. move=> Hsize [Hhd [Htl_hd Htl_tl]].
        move: (IH cs_tl_tl) => {IH}. rewrite !pemuls_cons.
        rewrite !ZPEeval_peadds_cons /=. rewrite Hhd. rewrite Htl_hd !Z.mul_0_r !Z.add_0_l.
        move=> ->; first reflexivity.
        * rewrite -addn2 -(addn2 (size cs_tl_tl)) eqn_add2r in Hsize.
          move/andP: Hsize => [/eqP -> /eqP ->]. rewrite !eqxx. done.
        * split; [reflexivity | exact: Htl_tl].
  Qed.

  Lemma zimply_eq_valid_arep sp g t ps ms q cms :
    imp_of_arep sp = (g, t, ps, ms, q) -> zpimply_eq ps q (peadds (pemuls cms ms)) ->
    valid_arep sp.
  Proof.
    move=> Hpoly Himp st Hzpre. move: (Himp (@vl_of_store st sp Hzpre)) => {}Himp.
    move: (vl_of_store_premises Hpoly Hzpre) => Hall0.
    move: (Himp Hall0) => Hqcm. apply: (vl_of_store_conseq Hpoly).
    exists (ZPEevals (@vl_of_store st sp Hzpre) cms).
    rewrite Hqcm. rewrite ZPEeval_peadds ZPEevals_pemuls. reflexivity.
  Qed.

  (* If the answer of an ideal membership problem reduced from an atomic root
     entailment problem are verified by the validator, the atomic root
     entailment problem is valid *)
  Theorem validated_imp_valid_arep s g t ps ms q cps cms :
    imp_of_arep s = (g, t, ps, ms, q) ->
    validate_imp_answer ps ms q cps cms ->
    valid_arep s.
  Proof.
    move=> Hpoly Hch. exact: (zimply_eq_valid_arep Hpoly (validated_imp_imply_eq Hch)).
  Qed.


  Lemma simplify_generator_validate_zpimply ps q ms cps cms ps' q' :
    simplify_generator ps q = (ps', q') ->
    validate_imp_answer ps' ms q' cps cms ->
    zpimply_eq ps q (peadds (pemuls cms ms)).
  Proof.
    move=> Hsim Hvd. move: (validated_imp_imply_eq Hvd) => Himp.
    exact: (simplify_generator_sound Hsim Himp).
  Qed.

  (* If the answer of a simplified ideal membership problem reduced from an
     atomic root entailment problem are verified by the validator, the atomic
     root entailment problem is valid *)
  Theorem validated_simplified_imp_valid_arep s g t ps ms q ps' q' cps cms :
    imp_of_arep s = (g, t, ps, ms, q) ->
    simplify_generator ps q = (ps', q') ->
    validate_imp_answer ps' ms q' cps cms ->
    valid_arep s.
  Proof.
    move=> Hpoly Hsim Hch. apply: (zimply_eq_valid_arep Hpoly).
    move: (validated_imp_imply_eq Hch). exact: (simplify_generator_sound Hsim).
  Qed.

  Theorem validated_simplified_imp_vars_cache_valid_arep s g t ps ms q ps' q' cps cms :
    imp_of_arep s = (g, t, ps, ms, q) ->
    simplify_generator_vars_cache ps q = (ps', q') ->
    validate_imp_answer ps' ms q' cps cms ->
    valid_arep s.
  Proof.
    move=> Hpoly Hsim Hch. apply: (zimply_eq_valid_arep Hpoly).
    move: (validated_imp_imply_eq Hch). exact: (simplify_generator_vars_cache_sound Hsim).
  Qed.

End Validator.
