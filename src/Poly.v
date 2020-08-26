
From Coq Require Import List Arith ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder Nats ZAriths Seqs Store Tactics.
From BitBlasting Require Import State.
From Cryptoline Require Import Options DSL SSA ZSSA.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section PSpec.

  (* Singleton zbexp *)

  Inductive szbexp : Type :=
  | Seq : ZSSA.zexp -> ZSSA.zexp -> szbexp
  | Seqmod : ZSSA.zexp -> ZSSA.zexp -> ZSSA.zexp -> szbexp.

  Definition szbexp_eqn (e1 e2 : szbexp) : bool :=
    match e1, e2 with
    | Seq e1 e2, Seq e3 e4 => (Eeq e1 e2) == (Eeq e3 e4)
    | Seqmod e1 e2 p1, Seqmod e3 e4 p2 => (Eeqmod e1 e2 p1) == (Eeqmod e3 e4 p2)
    | _, _ => false
    end.

  Lemma szbexp_eqn_eq (e1 e2 : szbexp) : szbexp_eqn e1 e2 -> e1 = e2.
  Proof.
    elim: e1 e2 => [e1 e2 | e1 e2 p1] [] //=.
    - by move=> ? ? /eqP [] -> ->.
    - by move=> ? ? ? /eqP [] -> -> ->.
  Qed.

  Lemma szbexp_eqn_refl (e : szbexp) : szbexp_eqn e e.
  Proof. by elim: e => /=. Qed.

  Lemma szbexp_eqn_sym {e1 e2 : szbexp} : szbexp_eqn e1 e2 -> szbexp_eqn e2 e1.
  Proof. move=> H; rewrite (szbexp_eqn_eq H); exact: szbexp_eqn_refl. Qed.

  Lemma szbexp_eqn_trans {e1 e2 e3 : szbexp} :
    szbexp_eqn e1 e2 -> szbexp_eqn e2 e3 -> szbexp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (szbexp_eqn_eq H1) (szbexp_eqn_eq H2).
    exact: szbexp_eqn_refl.
  Qed.

  Lemma szbexp_eqP (e1 e2 : szbexp) : reflect (e1 = e2) (szbexp_eqn e1 e2).
  Proof.
    case H: (szbexp_eqn e1 e2).
    - apply: ReflectT. exact: (szbexp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: szbexp_eqn_refl.
  Qed.

  Definition szbexp_eqMixin := EqMixin szbexp_eqP.
  Canonical szbexp_eqType := Eval hnf in EqType szbexp szbexp_eqMixin.

  Definition eval_szbexp (e : szbexp) (s : ZSSAStore.t) : Prop :=
    match e with
    | Seq e1 e2 => ZSSA.eval_zbexp (Eeq e1 e2) s
    | Seqmod e1 e2 p => ZSSA.eval_zbexp (Eeqmod e1 e2 p) s
    end.

  (* Algebraic specification as polynomial equations *)

  Record pspec : Type := mkPolySpec { ppremises : seq szbexp;
                                      pconseq : szbexp }.

  Definition pspec_eqn (ps1 ps2 : pspec) : bool :=
    (ppremises ps1 == ppremises ps2) && (pconseq ps1 == pconseq ps2).

  Lemma pspec_eqn_eq ps1 ps2 : pspec_eqn ps1 ps2 -> ps1 = ps2.
  Proof.
    case: ps1 => [pres1 post1]. case: ps2 => [pres2 post2]. rewrite /pspec_eqn /=.
    move/andP=> [/eqP -> /eqP ->]. reflexivity.
  Qed.

  Lemma pspec_eqn_refl ps : pspec_eqn ps ps.
  Proof. by rewrite /pspec_eqn 2!eqxx. Qed.

  Lemma pspec_eqP (ps1 ps2 : pspec) : reflect (ps1 = ps2) (pspec_eqn ps1 ps2).
  Proof.
    case H: (pspec_eqn ps1 ps2).
    - apply: ReflectT. exact: (pspec_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: pspec_eqn_refl.
  Qed.

  Definition pspec_eqMixin := EqMixin pspec_eqP.
  Canonical pspec_eqType := Eval hnf in EqType pspec pspec_eqMixin.

  Definition valid_pspec (s : pspec) : Prop :=
    forall st : ZSSAStore.t,
      (forall e : szbexp, e \in (ppremises s) -> eval_szbexp e st) ->
      eval_szbexp (pconseq s) st.

End PSpec.



From Coq Require Import Recdef.

(* Simplification of pspec *)
Section PSpecSimpl.

  Import SSA ZSSA.

  Local Notation var := SSAVarOrder.t.

  Fixpoint zexp_subst (p : ZSSA.zexp) (r : ZSSA.zexp) (e : ZSSA.zexp) :=
    if e == p then r
    else match e with
         | Eunop op e => Eunop op (zexp_subst p r e)
         | Ebinop op e1 e2 => Ebinop op  (zexp_subst p r e1) (zexp_subst p r e2)
         | _ => e
         end.

  Definition szbexp_subst (p : ZSSA.zexp) (r : ZSSA.zexp) (e : szbexp) :=
    match e with
    | Seq e1 e2 => Seq (zexp_subst p r e1) (zexp_subst p r e2)
    | Seqmod e1 e2 e3 => Seqmod (zexp_subst p r e1) (zexp_subst p r e2)
                                (zexp_subst p r e3)
    end.

  Definition subst_szbexps (p r : zexp) (es : seq szbexp) : seq szbexp :=
    map (szbexp_subst p r) es.

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
  Qed.

  Lemma szbexp_subst_valid e p r s :
    eval_zexp p s = eval_zexp r s ->
    eval_szbexp e s <-> eval_szbexp (szbexp_subst p r e) s.
  Proof.
    case: e.
    - move=> e1 e2 /= Hev. rewrite -!(zexp_subst_valid _ Hev). tauto.
    - move=> e1 e2 e3 /= Hev. rewrite -!(zexp_subst_valid _ Hev). tauto.
  Qed.

  Lemma subst_szbexps_cat es1 es2 p r :
    subst_szbexps p r (es1 ++ es2) = subst_szbexps p r es1 ++ subst_szbexps p r es2.
  Proof. rewrite /subst_szbexps. exact: map_cat. Qed.

  Lemma subst_szbexps_valid es p r s :
    eval_zexp p s = eval_zexp r s ->
    (forall e, e \in es -> eval_szbexp e s) <->
    (forall e, e \in (subst_szbexps p r es) -> eval_szbexp e s).
  Proof.
    move=> Hpr. elim: es => [| e es IH] //=. split.
    - move=> Hev f Hin_f. rewrite in_cons in Hin_f. case/orP: Hin_f => Hin_f.
      + rewrite (eqP Hin_f). apply/(szbexp_subst_valid e Hpr). apply: Hev.
        rewrite in_cons eqxx orTb. exact: is_true_true.
      + have Hev': (forall e : szbexp, e \in es -> eval_szbexp e s).
        { move=> g Hin_g; apply: Hev. rewrite in_cons Hin_g orbT.
          exact: is_true_true. }
        case: IH => IH1 IH2. exact: (IH1 Hev' _ Hin_f).
    - move=> Hev f Hin_f. rewrite in_cons in Hin_f. case/orP: Hin_f => Hin_f.
      + rewrite (eqP Hin_f). apply/(szbexp_subst_valid e Hpr). apply: Hev.
        rewrite in_cons eqxx orTb. exact: is_true_true.
      + have Hev': (forall e : szbexp_eqType, e \in subst_szbexps p r es ->
                                                    eval_szbexp e s).
        { move=> g Hin_g; apply: Hev. rewrite in_cons Hin_g orbT.
          exact: is_true_true. }
        case: IH => IH1 IH2. exact: (IH2 Hev' _ Hin_f).
  Qed.



  Definition is_assignment (e : szbexp) : option (ssavar * ZSSA.zexp) :=
    match e with
    | Seq (Evar v) e => Some (v, e)
    | Seq e (Evar v) => Some (v, e)
    | Seq (Ebinop Eadd (Evar v) el) er => Some (v, Ebinop Esub er el)
    | Seq el (Ebinop Eadd (Evar v) er) => Some (v, Ebinop Esub el er)
    | Seq _ _ => None
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
           end.

  Lemma is_assignment_equal e p r s :
    is_assignment e = Some (p, r) ->
    eval_szbexp e s -> eval_zexp (evar p) s = eval_zexp r s.
  Proof.
    case: e => //=. move=> left right.
    (case: left; case: right => //=); intros; by mytac.
  Qed.

  Corollary subst_assignment_valid e p r e' s :
    is_assignment e = Some (p, r) -> eval_szbexp e s ->
    eval_szbexp e' s <-> eval_szbexp (szbexp_subst (evar p) r e') s.
  Proof.
    move=> His Hev. exact: (szbexp_subst_valid _ (is_assignment_equal His Hev)).
  Qed.



  Definition size_lt {A : Type} (es1 es2 : seq A) : Prop :=
    (size es1 < size es2)%coq_nat.

  Function simplify_pspec_rec
          (visited : seq szbexp) (premises : seq szbexp) (conseq : szbexp)
          {wf (@size_lt szbexp) premises} :=
    match premises with
    | [::] => (rev visited, conseq)
    | e::es =>
      match is_assignment e with
      | None => simplify_pspec_rec (e::visited) es conseq
      | Some (p, r) => simplify_pspec_rec (subst_szbexps (evar p) r visited)
                                          (subst_szbexps (evar p) r es)
                                          (szbexp_subst (evar p) r conseq)
      end
    end.
  Proof.
    - move=> _ premises _ e es ? [p' r'] p r [] ? ? Ha.
      rewrite /size_lt /subst_szbexps size_map /=. exact: Nat.lt_succ_diag_r.
    - move=> _ premises _ e es ? Ha. rewrite /size_lt /=. exact: Nat.lt_succ_diag_r.
    - exact: (well_founded_ltof (seq szbexp) size).
  Defined.

  Lemma simplify_pspec_rec_cons_is_assignment visited e es q p r :
    is_assignment e = Some (p, r) ->
    simplify_pspec_rec visited (e::es) q =
    simplify_pspec_rec (subst_szbexps (evar p) r visited)
                       (subst_szbexps (evar p) r es)
                       (szbexp_subst (evar p) r q).
  Proof.
    move=> Ha.
    dcase (simplify_pspec_rec (subst_szbexps (evar p) r visited)
                              (subst_szbexps (evar p) r es)
                              (szbexp_subst (evar p) r q)) => [[visited' q'] Hs].
    move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_pspec_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_pspec_rec_complete.
    apply: (R_simplify_pspec_rec_2 _ _ _ _ _ _ _ _ Ha _ H). reflexivity.
  Qed.

  Lemma simplify_pspec_rec_cons_not_assignment visited e es q :
    is_assignment e = None ->
    simplify_pspec_rec visited (e::es) q =
    simplify_pspec_rec (e::visited) es q.
  Proof.
    move=> Ha. dcase (simplify_pspec_rec (e :: visited) es q) => [[visited' q'] Hs].
    move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_pspec_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_pspec_rec_complete.
    apply: (R_simplify_pspec_rec_1 _ _ _ _ _ _ Ha _ H). reflexivity.
  Qed.

  Lemma simplify_pspec_rec_empty visited q :
    simplify_pspec_rec visited [::] q = (rev visited, q).
  Proof. reflexivity. Qed.

  Lemma simplify_pspec_rec_sound pre ps q ps' q' :
    simplify_pspec_rec pre ps q = (ps', q') ->
    (forall s,
        (forall e : szbexp, e \in ps' -> eval_szbexp e s) ->
        eval_szbexp q' s) ->
    (forall s,
        (forall e : szbexp, e \in pre ++ ps -> eval_szbexp e s) ->
        eval_szbexp q s).
  Proof.
    have ->: ps' = (ps', q').1 by reflexivity.
    have ->: q' = (ps', q').2 by reflexivity.
    move: (ps', q'). clear ps' q'. eapply simplify_pspec_rec_ind.
    - move=> {pre ps q} pre ps q Hps [ps' q'] [] ? ?; subst => /=.
      move=> Hs s Hev. rewrite cats0 in Hev. apply: Hs.
      move=> e Hin; apply: Hev. rewrite mem_rev in Hin. assumption.
    - move=> {pre ps q} pre ps q e es Hps Ha IH [ps' q']  /= Hrec Hs s He.
      apply: (IH _ Hrec Hs). move=> f Hin. apply: He. rewrite mem_cat in_cons.
      rewrite mem_cat in_cons in Hin. (case/orP: Hin; [case/orP|] => -> //=);
                                        rewrite !orbT; exact: is_true_true.
    - move=> {pre ps q} pre ps q e es Hps pat rep Ha IH [ps' q'] /= Hrec Hs s He.
      have Hes: eval_szbexp e s.
      { apply: He. rewrite mem_cat in_cons eqxx /=. by rewrite orbT. }
      move: (is_assignment_equal Ha Hes) => Hpr.
      apply/(subst_assignment_valid q Ha Hes). apply: (IH _ Hrec Hs).
      move=> f. rewrite -subst_szbexps_cat. move: f.
      apply/(subst_szbexps_valid (pre++es) Hpr). move=> f Hin.
      apply: He. rewrite mem_cat in_cons. rewrite mem_cat in Hin.
      case/orP: Hin => -> //=; rewrite !orbT; exact: is_true_true.
  Qed.


  Definition simplify_pspec (s : pspec) : pspec :=
    let (ps, q) := simplify_pspec_rec [::] (ppremises s) (pconseq s) in
    {| ppremises := ps; pconseq := q |}.

  Lemma simplify_pspec_sound (s : pspec) :
    valid_pspec (simplify_pspec s) -> valid_pspec s.
  Proof.
    rewrite /valid_pspec. case: s => ps q /=. rewrite /simplify_pspec /=.
    dcase (simplify_pspec_rec [::] ps q) => [[ps' q'] Hs] /=.
    rewrite -(cat0s ps). exact: (simplify_pspec_rec_sound Hs).
  Qed.



  (* Rewrite an expression if the pattern appears in the expression *)

  Definition szbexp_subst_vars_cache
             (p : ssavar) (r : ZSSA.zexp) vspr (ve : SSAVS.t * szbexp) :=
    let vs := ve.1 in
    let e := ve.2 in
    if SSAVS.mem p vs then (SSAVS.remove p (SSAVS.union vs vspr),
                            szbexp_subst (evar p) r e)
    else ve.

  Definition subst_szbexps_vars_cache
             (p : ssavar) (r : ZSSA.zexp) vspr (ves : seq (SSAVS.t * szbexp)) :=
    map (szbexp_subst_vars_cache p r vspr) ves.

  Lemma subst_assignment_vars_cache_valid e p r e' vspr s :
    is_assignment e = Some (p, r) -> eval_szbexp e s ->
    eval_szbexp e'.2 s <-> eval_szbexp (szbexp_subst_vars_cache p r vspr e').2 s.
  Proof.
    move=> His Hev. rewrite /szbexp_subst_vars_cache. case: (SSAVS.mem p e'.1) => /=.
    - exact: (szbexp_subst_valid _ (is_assignment_equal His Hev)).
    - tauto.
  Qed.

  Lemma subst_szbexps_vars_cache_cat es1 es2 p r vspr :
    subst_szbexps_vars_cache p r vspr (es1 ++ es2) =
    subst_szbexps_vars_cache p r vspr es1 ++ subst_szbexps_vars_cache p r vspr es2.
  Proof. rewrite /subst_szbexps_vars_cache. exact: map_cat. Qed.

  Lemma subst_szbexps_vars_cache_valid es p r vspr s :
    eval_zexp (evar p) s = eval_zexp r s ->
    (forall e, e \in (split es).2 -> eval_szbexp e s) <->
    (forall e, e \in (split (subst_szbexps_vars_cache p r vspr es)).2 ->
                     eval_szbexp e s).
  Proof.
    move=> H. elim: es => [| [el er] es IH] //=. case Hses: (split es) => [esl esr] /=.
    case Hsube: (szbexp_subst_vars_cache p r vspr (el, er)) => [sel ser].
    case Hsubes: (split (subst_szbexps_vars_cache p r vspr es)) => [sesl sesr] /=.
    case: IH => [IH1 IH2]. split=> Hs e Hin.
    - case/orP: Hin=> Hin.
      + move: Hsube. rewrite /szbexp_subst_vars_cache /=.
        case: (SSAVS.mem p el) => /=.
        * case=> ? ?; subst. rewrite (eqP Hin).
          apply/(@szbexp_subst_valid er _ _ _ H). apply: Hs. by rewrite in_cons eqxx.
        * case=> ? ?; subst. apply: Hs. by rewrite in_cons Hin.
      + apply: IH1.
        * rewrite Hses /=. move=> f Hinf; apply: Hs. by rewrite in_cons Hinf orbT.
        * rewrite Hsubes /=. assumption.
    - case/orP: Hin=> Hin.
      + move: Hsube. rewrite /szbexp_subst_vars_cache /=.
        case: (SSAVS.mem p el) => /=.
        * case=> ? ?; subst. rewrite (eqP Hin).
          apply/(@szbexp_subst_valid er _ _ _ H). apply: Hs. by rewrite in_cons eqxx.
        * case=> ? ?; subst. apply: Hs. by rewrite in_cons Hin.
      + apply: IH2.
        * rewrite Hsubes /=. move=> f Hinf; apply: Hs. by rewrite in_cons Hinf orbT.
        * rewrite Hses /=. assumption.
  Qed.

  Function simplify_pspec_vars_cache_rec
           (visited : seq (SSAVS.t * szbexp)) (premises : seq (SSAVS.t * szbexp))
           (conseq : (SSAVS.t * szbexp))
           {wf (@size_lt (SSAVS.t * szbexp)) premises} :=
    match premises with
    | [::] => (rev visited, conseq)
    | ve::ves =>
      match is_assignment ve.2 with
      | None => simplify_pspec_vars_cache_rec (ve::visited) ves conseq
      | Some (p, r) =>
        simplify_pspec_vars_cache_rec (subst_szbexps_vars_cache p r ve.1 visited)
                                      (subst_szbexps_vars_cache p r ve.1 ves)
                                      (szbexp_subst_vars_cache p r ve.1 conseq)
      end
    end.
  Proof.
    - move=> _ premises _ ve ves ? [p' r'] p r [] ? ? Ha.
      rewrite /size_lt /subst_szbexps size_map /=. exact: Nat.lt_succ_diag_r.
    - move=> _ premises _ e es ? Ha. rewrite /size_lt /=. exact: Nat.lt_succ_diag_r.
    - exact: (well_founded_ltof (seq (SSAVS.t * szbexp)) size).
  Defined.

  Lemma simplify_pspec_vars_cache_rec_cons_is_assignment visited ve ves q p r :
    is_assignment ve.2 = Some (p, r) ->
    simplify_pspec_vars_cache_rec visited (ve::ves) q =
    simplify_pspec_vars_cache_rec (subst_szbexps_vars_cache p r ve.1 visited)
                                  (subst_szbexps_vars_cache p r ve.1 ves)
                                  (szbexp_subst_vars_cache p r ve.1 q).
  Proof.
    move=> Ha.
    dcase (simplify_pspec_vars_cache_rec (subst_szbexps_vars_cache p r ve.1 visited)
                                         (subst_szbexps_vars_cache p r ve.1 ves)
                                         (szbexp_subst_vars_cache p r ve.1 q)) =>
    [[visited' q'] Hs]. move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_pspec_vars_cache_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_pspec_vars_cache_rec_complete.
    exact: (R_simplify_pspec_vars_cache_rec_2 _ _ _ _ _ (Logic.eq_refl _) _ _ Ha _ H).
  Qed.

  Lemma simplify_pspec_vars_cache_rec_cons_not_assignment visited ve ves q :
    is_assignment ve.2 = None ->
    simplify_pspec_vars_cache_rec visited (ve::ves) q =
    simplify_pspec_vars_cache_rec (ve::visited) ves q.
  Proof.
    move=> Ha. dcase (simplify_pspec_vars_cache_rec (ve :: visited) ves q) =>
               [[visited' q'] Hs]. move: (Logic.eq_sym Hs) => {Hs} Hs.
    move: (R_simplify_pspec_vars_cache_rec_correct Hs) => {Hs} H.
    symmetry. apply: R_simplify_pspec_vars_cache_rec_complete.
    exact: (R_simplify_pspec_vars_cache_rec_1 _ _ _ _ _ (Logic.eq_refl _) Ha _ H).
  Qed.

  Lemma simplify_pspec_vars_cache_rec_empty visited q :
    simplify_pspec_vars_cache_rec visited [::] q = (rev visited, q).
  Proof. reflexivity. Qed.

  Lemma simplify_pspec_vars_cache_rec_sound pre ps q ps' q' :
    simplify_pspec_vars_cache_rec pre ps q = (ps', q') ->
    (forall s,
        (forall e : szbexp, e \in (split ps').2 -> eval_szbexp e s) ->
        eval_szbexp q'.2 s) ->
    (forall s,
        (forall e : szbexp, e \in (split (pre ++ ps)).2 -> eval_szbexp e s) ->
        eval_szbexp q.2 s).
  Proof.
    have ->: ps' = (ps', q').1 by reflexivity.
    have ->: q' = (ps', q').2 by reflexivity.
    move: (ps', q'). clear ps' q'. eapply simplify_pspec_vars_cache_rec_ind.
    - move=> {pre ps q} pre ps q Hps [ps' q'] [] ? ?; subst => /=.
      move=> Hs s Hev. rewrite cats0 in Hev. apply: Hs.
      move=> e Hin; apply: Hev. rewrite in_split_rev_r in Hin. assumption.
    - move=> {pre ps q} pre ps q e es Hps Ha IH [ps' q']  /= Hrec Hs s He.
      apply: (IH _ Hrec Hs). move=> f Hin. apply: He.
      rewrite 2!split_cat 2!mem_cat in Hin *. rewrite split_cons in_cons.
      rewrite Bool.orb_assoc. rewrite (Bool.orb_comm _ (f == e.2)).
      rewrite -in_cons. rewrite split_cons /= in Hin. assumption.
    - move=> {pre ps q} pre ps q e es Hps pat rep Ha IH [ps' q'] /= Hrec Hs s He.
      have Hes: eval_szbexp (e.2) s.
      { apply: He. rewrite split_cat mem_cat split_cons in_cons eqxx orbT /=.
        reflexivity. }
      move: (is_assignment_equal Ha Hes) => Hpr.
      apply/(subst_assignment_vars_cache_valid _ _ Ha Hes). apply: (IH _ Hrec Hs).
      move=> f. rewrite -subst_szbexps_vars_cache_cat. move: f.
      apply/(subst_szbexps_vars_cache_valid (pre++es) _ Hpr). move=> f Hin.
      apply: He. rewrite 2!split_cat 2!mem_cat in Hin *.
      rewrite split_cons in_cons. rewrite (Bool.orb_comm (f == e.2)).
      rewrite Bool.orb_assoc. by rewrite Hin.
  Qed.


  Definition vars_szbexp (e : szbexp) : SSAVS.t :=
    match e with
    | Seq e1 e2 => SSAVS.union (vars_eexp e1) (vars_eexp e2)
    | Seqmod e1 e2 e3 => SSAVS.union (SSAVS.union (vars_eexp e1) (vars_eexp e2))
                                     (vars_eexp e3)
    end.

  Definition pair_with_vars (e : szbexp) : SSAVS.t * szbexp :=
    (vars_szbexp e, e).

  Lemma split_map_pair_with_vars (es : seq szbexp) :
    (split (map pair_with_vars es)).2 = es.
  Proof.
    elim: es => [| e es IH] //=. move: IH.
    dcase (split [seq pair_with_vars i | i <- es]) => [[vs es'] Hs].
    rewrite Hs /=. move=> ->. reflexivity.
  Qed.

  Definition simplify_pspec_vars_cache (s : pspec) : pspec :=
    let vs_ps := map pair_with_vars (ppremises s) in
    let vs_q := pair_with_vars (pconseq s) in
    let (vs_ps', vs_q') := simplify_pspec_vars_cache_rec [::] vs_ps vs_q in
    {| ppremises := (split vs_ps').2; pconseq := vs_q'.2 |}.

  Lemma simplify_pspec_vars_cache_sound (s : pspec) :
    valid_pspec (simplify_pspec_vars_cache s) -> valid_pspec s.
  Proof.
    rewrite /valid_pspec. case: s => ps q /=. rewrite /simplify_pspec_vars_cache /=.
    dcase (simplify_pspec_vars_cache_rec [::] [seq pair_with_vars i | i <- ps]
                                         (pair_with_vars q)) => [[vs_ps' vs_q'] Hsp].
    rewrite Hsp /=. move=> H s Hs.
    apply: (simplify_pspec_vars_cache_rec_sound Hsp H). rewrite cat0s.
    rewrite split_map_pair_with_vars. assumption.
  Qed.

End PSpecSimpl.



(* Convert zspec to pspec *)

Section ZSpec2Spec.

  Fixpoint split_zbexp (e : ZSSA.zbexp) : seq szbexp :=
    match e with
    | Etrue => [::]
    | Eeq e1 e2 => [::Seq e1 e2]
    | Eeqmod e1 e2 p => [::Seqmod e1 e2 p]
    | Eand e1 e2 => split_zbexp e1 ++ split_zbexp e2
    end.

  Definition pspecs_of_zspec (s : ZSSA.zspec) : seq pspec :=
    let premises := split_zbexp (ZSSA.zspre s) in
    let conseqs := split_zbexp (ZSSA.zspost s) in
    map (fun conseq => {| ppremises := premises; pconseq := conseq |}) conseqs.

  Definition pspecs_of_zspec_simplified (o : options) (s : ZSSA.zspec) : seq pspec :=
    if vars_cache_in_rewrite_assignments o then
      map simplify_pspec_vars_cache (pspecs_of_zspec s)
    else
      map simplify_pspec (pspecs_of_zspec s).

  Lemma split_zbexp_mem ze s :
    ZSSA.eval_zbexp ze s ->
    forall pe, pe \in split_zbexp ze -> eval_szbexp pe s.
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
    (forall pe, pe \in split_zbexp ze -> eval_szbexp pe s) ->
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

  Theorem pspecs_of_zspec_sound zs :
    (forall ps, ps \in pspecs_of_zspec zs -> valid_pspec ps) ->
    ZSSA.valid_zspec zs.
  Proof.
    case: zs => zf zq. elim: zq zf => //=.
    - move=> e1 e2 zf /= Hps s /= Hzf. rewrite /pspecs_of_zspec /= in Hps.
      apply: (Hps {| ppremises := split_zbexp zf; pconseq := Seq e1 e2 |});
        first by rewrite in_cons eqxx.
      move=> {Hps} pe /= Hmem. exact: (split_zbexp_mem Hzf Hmem).
    - move=> e1 e2 m zf Hps s /= Hzf. rewrite /pspecs_of_zspec /= in Hps.
      apply: (Hps {| ppremises := split_zbexp zf; pconseq := Seqmod e1 e2 m |});
        first by rewrite in_cons eqxx.
      move=> {Hps} pe /= Hmem. exact: (split_zbexp_mem Hzf Hmem).
    - move=> e1 IH1 e2 IH2 zf Hps s /= Hzf. rewrite /pspecs_of_zspec /= in Hps.
      split.
      + apply: (IH1 zf _ s Hzf) => /=. move=> ps Hin. apply: Hps.
        rewrite map_cat mem_cat. apply/orP; left. assumption.
      + apply: (IH2 zf _ s Hzf) => /=. move=> ps Hin. apply: Hps.
        rewrite map_cat mem_cat. apply/orP; right. assumption.
  Qed.

  Theorem pspecs_of_zspec_simplified_sound o zs :
    (forall ps, ps \in pspecs_of_zspec_simplified o zs -> valid_pspec ps) ->
    ZSSA.valid_zspec zs.
  Proof.
    move=> H. apply: pspecs_of_zspec_sound. move=> ps Hin.
    case Ho: (vars_cache_in_rewrite_assignments o).
    - apply: simplify_pspec_vars_cache_sound. apply: H.
      rewrite /pspecs_of_zspec_simplified Ho. apply: map_f. assumption.
    - apply: simplify_pspec_sound. apply: H.
      rewrite /pspecs_of_zspec_simplified Ho. apply: map_f. assumption.
  Qed.

End ZSpec2Spec.



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

  Fixpoint zpexpr_all0 l (ps : seq (PExpr Z)) : Prop :=
    match ps with
    | [::] => True
    | hd::tl => ZPEeval l hd = 0 /\ zpexpr_all0 l tl
    end.

  (* (\forall p \in ps, p = 0) -> q1 = q2 *)
  Definition zpimply_eq ps q1 q2 :=
    forall l : list Z,
      zpexpr_all0 l ps -> ZPEeval l q1 = ZPEeval l q2.

  Lemma ZPEeval_sub l e1 e2 : ZPEeval l (PEsub e1 e2) = ZPEeval l e1 - ZPEeval l e2.
  Proof. reflexivity. Qed.

  Lemma ZPEeval_mul l e1 e2 : ZPEeval l (PEmul e1 e2) = ZPEeval l e1 * ZPEeval l e2.
  Proof. reflexivity. Qed.

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

  Lemma bnth_rcons_last (g : positive) (l : list A) (x : A) :
    Pos.to_nat g = size l + 1 -> bnth g (rcons l x) = x.
  Proof.
    move=> Hs. rewrite bnth_snth. rewrite Hs. rewrite addn1 subn1 succnK.
    rewrite nth_rcons. rewrite (ltnn (size l)) (eqxx (size l)). reflexivity.
  Qed.

End BinList.



(* Convert polynomial equations to polynomials *)

Section PExpr.

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
    end.

  Definition zpexpr_of_premise (g : positive) (t : SSAVM.t positive) (e : szbexp) :
    positive * SSAVM.t positive * PExpr Z :=
    match e with
    | Seq e1 e2 =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      (g2, t2, PEsub e1 e2)
    | Seqmod e1 e2 p =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      let '(gp, tp, p) := zpexpr_of_zexp g2 t2 p in
      ((gp + 1)%positive, tp, PEsub (PEsub e1 e2) (PEmul (PEX Z gp) p))
    end.

  Fixpoint zpexprs_of_premises (g : positive) (t : SSAVM.t positive) (es : seq szbexp) :
    positive * SSAVM.t positive * seq (PExpr Z) :=
    match es with
    | [::] => (g, t, [::])
    | e::es => let '(g_hd, t_hd, es_hd) := zpexpr_of_premise g t e in
               let '(g_tl, t_tl, es_tl) := zpexprs_of_premises g_hd t_hd es in
               (g_tl, t_tl, es_hd::es_tl)
    end.

  Definition zpexpr_of_conseq (g : positive) (t : SSAVM.t positive) (e : szbexp) :
    positive * SSAVM.t positive * PExpr Z * PExpr Z :=
    match e with
    | Seq e1 e2 =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      (g2, t2, PEsub e1 e2, PEO)
    | Seqmod e1 e2 p =>
      let '(g1, t1, e1) := zpexpr_of_zexp g t e1 in
      let '(g2, t2, e2) := zpexpr_of_zexp g1 t1 e2 in
      let '(gp, tp, p) := zpexpr_of_zexp g2 t2 p in
      (gp, tp, PEsub e1 e2, p)
    end.

  (* ps: polynomials that equal 0
     m: modulus
     the goal is to prove that q = cs * ps + c * m for some coefficients cs and c *)
  Definition zpexprs_of_pspec (s : pspec) : positive * SSAVM.t positive * seq (PExpr Z) * PExpr Z * PExpr Z :=
    let g := init_pos in
    let t := init_vm in
    let '(g_p, t_p, ps) := zpexprs_of_premises g t (ppremises s) in
    let '(g_q, t_q, q, m) := zpexpr_of_conseq g_p t_p (pconseq s) in
    (g_q, t_q, ps, m, q).

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
  Qed.

  Definition zpexpr_of_premise_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (e : szbexp) :
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

  Lemma zpexpr_of_premise_vl_novl st vl g t e vl' g' t' pe :
    zpexpr_of_premise_vl st vl g t e = (vl', g', t', pe) ->
    zpexpr_of_premise g t e = (g', t', pe).
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      case=> ? ? ? ?; subst. rewrite (zpexpr_of_zexp_vl_novl Hvl1)
                                     (zpexpr_of_zexp_vl_novl Hvl2).
      reflexivity.
    - move=> e1 e2 e3 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hvl3].
      case=> ? ? ? ?; subst.
      rewrite (zpexpr_of_zexp_vl_novl Hvl1) (zpexpr_of_zexp_vl_novl Hvl2)
              (zpexpr_of_zexp_vl_novl Hvl3).
      reflexivity.
  Qed.

  Fixpoint zpexprs_of_premises_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (es : seq szbexp) :
    list Z * positive * SSAVM.t positive * seq (PExpr Z) :=
    match es with
    | [::] => (vl, g, t, [::])
    | e::es =>
      let '(vl_hd, g_hd, t_hd, es_hd) := zpexpr_of_premise_vl s vl g t e in
      let '(vl_tl, g_tl, t_tl, es_tl) := zpexprs_of_premises_vl s vl_hd g_hd t_hd es in
      (vl_tl, g_tl, t_tl, es_hd::es_tl)
    end.

  Lemma zpexprs_of_premises_vl_novl st vl g t es vl' g' t' pes :
    zpexprs_of_premises_vl st vl g t es = (vl', g', t', pes) ->
    zpexprs_of_premises g t es = (g', t', pes).
  Proof.
    elim: es vl g t vl' g' t' pes => [| hd tl IH] ivl ig it ovl og ot pes /=.
    - by case=> ? ? ? ?; subst.
    - dcase (zpexpr_of_premise_vl st ivl ig it hd) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexprs_of_premises_vl st vl1 g1 t1 tl) => [[[[vl2 g2] t2] pe2] Hvl2].
      case=> ? ? ? ?; subst. rewrite (zpexpr_of_premise_vl_novl Hvl1).
      rewrite (IH _ _ _ _ _ _ _ Hvl2). reflexivity.
  Qed.

  Definition zpexpr_of_conseq_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (e : szbexp) :
    list Z * positive * SSAVM.t positive * PExpr Z * PExpr Z :=
    match e with
    | Seq e1 e2 =>
      let '(vl1, g1, t1, e1) := zpexpr_of_zexp_vl s vl g t e1 in
      let '(vl2, g2, t2, e2) := zpexpr_of_zexp_vl s vl1 g1 t1 e2 in
      (vl2, g2, t2, PEsub e1 e2, PEO)
    | Seqmod e1 e2 p =>
      let '(vl1, g1, t1, e1) := zpexpr_of_zexp_vl s vl g t e1 in
      let '(vl2, g2, t2, e2) := zpexpr_of_zexp_vl s vl1 g1 t1 e2 in
      let '(vlp, gp, tp, p) := zpexpr_of_zexp_vl s vl2 g2 t2 p in
      (vlp, gp, tp, PEsub e1 e2, p)
    end.

  Lemma zpexpr_of_conseq_vl_novl st vl g t e vl' g' t' pe pm :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pm) ->
    zpexpr_of_conseq g t e = (g', t', pe, pm).
  Proof.
    elim: e vl g t vl' g' t' pe pm => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe pm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      case=> ? ? ? ? ?; subst.
      rewrite (zpexpr_of_zexp_vl_novl Hvl1) (zpexpr_of_zexp_vl_novl Hvl2).
      reflexivity.
    - move=> e1 e2 e3 ivl ig it ovl og ot pe pm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hvl1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hvl2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hvl3].
      case=> ? ? ? ? ?; subst.
      rewrite (zpexpr_of_zexp_vl_novl Hvl1) (zpexpr_of_zexp_vl_novl Hvl2)
              (zpexpr_of_zexp_vl_novl Hvl3).
      reflexivity.
  Qed.

  (* ps: polynomials that equal 0
     m: modulus
     the goal is to prove that q = cs * ps + c * m for some coefficients cs and c *)
  Definition zpexprs_of_pspec_vl (st : ZSSAStore.t) (s : pspec) : list Z * positive * SSAVM.t positive * seq (PExpr Z) * PExpr Z * PExpr Z :=
    let g := init_pos in
    let t := init_vm in
    let vl := init_vl in
    let '(vl_p, g_p, t_p, ps) := zpexprs_of_premises_vl st init_vl g t (ppremises s) in
    let '(vl_q, g_q, t_q, q, m) := zpexpr_of_conseq_vl st vl_p g_p t_p (pconseq s) in
    (vl_q, g_q, t_q, ps, m, q).

  Lemma zpexprs_of_pspec_vl_novl st sp vl g t pps pm pq :
    zpexprs_of_pspec_vl st sp = (vl, g, t, pps, pm, pq) ->
    zpexprs_of_pspec sp = (g, t, pps, pm, pq).
  Proof.
    rewrite /zpexprs_of_pspec_vl /zpexprs_of_pspec.
    dcase (zpexprs_of_premises_vl st init_vl init_pos init_vm (ppremises sp)) =>
    [[[[vl_p g_p] t_p] opps] Hvl_p].
    dcase (zpexpr_of_conseq_vl st vl_p g_p t_p (pconseq sp)) =>
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
    - move=> e1 e2 e3 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexpr_of_zexp g2 t2 e3) => [[[g3 t3] pe3] Hzp3].
      case=> ? ? ? Hnew; subst. apply: newer_than_vm_add_r.
      apply: (zpexpr_of_zexp_newer Hzp3). apply: (zpexpr_of_zexp_newer Hzp2).
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

  Lemma zpexpr_of_conseq_newer g t e g' t' pe pm :
    zpexpr_of_conseq g t e = (g', t', pe, pm) ->
    newer_than_vm g t -> newer_than_vm g' t'.
  Proof.
    elim: e g t g' t' pe pm => /=.
    - move=> e1 e2 ig it og ot ope opm.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? ? Hnew; subst. apply: (zpexpr_of_zexp_newer Hzp2).
      exact: (zpexpr_of_zexp_newer Hzp1).
    - move=> e1 e2 e3 ig it og ot ope opm.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexpr_of_zexp g2 t2 e3) => [[[g3 t3] pe3] Hzp3].
      case=> ? ? ? ? Hnew; subst. apply: (zpexpr_of_zexp_newer Hzp3).
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
    - move=> e1 e2 e3 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexpr_of_zexp g2 t2 e3) => [[[g3 t3] pe3] Hzp3].
      case=> ? ? ?; subst. apply: pos_le_add_r.
      apply: (Pos.le_trans _ _ _ _ (zpexpr_of_zexp_gen Hzp3)).
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
  Qed.

  Lemma zpexpr_of_premise_vl_prefix_of st vl g t e vl' g' t' pe :
    zpexpr_of_premise_vl st vl g t e = (vl', g', t', pe) -> prefix_of vl vl'.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ?; subst.
      exact: (prefix_of_trans (zpexpr_of_zexp_vl_prefix_of Hpe1)
                              (zpexpr_of_zexp_vl_prefix_of Hpe2)).
    - move=> e1 e2 e3 ivl ig it ovl og ot ope.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case=> ? ? ? ?; subst. apply: prefix_of_rcons.
      apply: (prefix_of_trans _ (zpexpr_of_zexp_vl_prefix_of Hpe3)).
      apply: (prefix_of_trans _ (zpexpr_of_zexp_vl_prefix_of Hpe2)).
      exact: (zpexpr_of_zexp_vl_prefix_of Hpe1).
  Qed.

  Lemma zpexprs_of_premises_vl_prefix_of st vl g t es vl' g' t' pes :
    zpexprs_of_premises_vl st vl g t es = (vl', g', t', pes) -> prefix_of vl vl'.
  Proof.
    elim: es vl g t vl' g' t' pes => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes [] ? ? ? ?; subst. exact: prefix_of_refl.
    - move=> ivl ig it ovl og ot opes.
      dcase (zpexpr_of_premise_vl st ivl ig it hd) =>
      [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (zpexprs_of_premises_vl st vl_hd g_hd t_hd tl) =>
      [[[[vl_tl g_tl] t_tl] es_tl] Hpe_tl].
      case=> ? ? ? ?; subst. apply: (prefix_of_trans _ (IH _ _ _ _ _ _ _ Hpe_tl)).
      exact: (zpexpr_of_premise_vl_prefix_of Hpe_hd).
  Qed.

  Lemma zpexpr_of_conseq_vl_prefix_of st vl g t e vl' g' t' pe pm :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pm) -> prefix_of vl vl'.
  Proof.
    elim: e vl g t vl' g' t' pe pm => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope opm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ?; subst.
      exact: (prefix_of_trans (zpexpr_of_zexp_vl_prefix_of Hpe1)
                              (zpexpr_of_zexp_vl_prefix_of Hpe2)).
    - move=> e1 e2 e3 ivl ig it ovl og ot ope opm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case=> ? ? ? ? ?; subst.
      apply: (prefix_of_trans _ (zpexpr_of_zexp_vl_prefix_of Hpe3)).
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
  Qed.

  Lemma zpexpr_of_premise_vl_size_bounded st vl g t e vl' g' t' pe :
    zpexpr_of_premise_vl st vl g t e = (vl', g', t', pe) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? Hsize; subst. apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
      exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
    - move=> e1 e2 e3 ivl ig it ovl og ot ope.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case=> ? ? ? ? Hsize; subst. apply: rcons_vl_size_bounded.
      apply: (zpexpr_of_zexp_vl_size_bounded Hpe3).
      apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
      exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
  Qed.

  Lemma zpexprs_of_premises_vl_size_bounded st vl g t es vl' g' t' pes :
    zpexprs_of_premises_vl st vl g t es = (vl', g', t', pes) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: es vl g t vl' g' t' pes => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes [] ? ? ? ? Hsize; subst. assumption.
    - move=> ivl ig it ovl og ot opes.
      dcase (zpexpr_of_premise_vl st ivl ig it hd) =>
      [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (zpexprs_of_premises_vl st vl_hd g_hd t_hd tl) =>
      [[[[vl_tl g_tl] t_tl] es_tl] Hpe_tl].
      case=> ? ? ? ? Hsize; subst. apply: (IH _ _ _ _ _ _ _ Hpe_tl).
      exact: (zpexpr_of_premise_vl_size_bounded Hpe_hd).
  Qed.

  Lemma zpexpr_of_conseq_vl_size_bounded st vl g t e vl' g' t' pe pm :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pm) -> vl_size_bounded vl g ->
    vl_size_bounded vl' g'.
  Proof.
    elim: e vl g t vl' g' t' pe pm => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope opm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ? Hsize; subst. apply: (zpexpr_of_zexp_vl_size_bounded Hpe2).
      exact: (zpexpr_of_zexp_vl_size_bounded Hpe1).
    - move=> e1 e2 e3 ivl ig it ovl og ot ope opm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case=> ? ? ? ? ? Hsize; subst.
      apply: (zpexpr_of_zexp_vl_size_bounded Hpe3).
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
    - move=> e1 e2 e3 ig it og ot ope.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexpr_of_zexp g2 t2 e3) => [[[g3 t3] pe3] Hzp3].
      case=> ? ? ? Hnew; subst.
      move: (zpexpr_of_zexp_newer Hzp1 Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer Hzp2 Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_gen Hzp2) => Hg12.
      move: (zpexpr_of_zexp_gen Hzp3) => Hg23.
      move: (Pos.le_trans _ _ _ Hg12 Hg23) => {Hg12} Hg13.
      move: (@pos_le_add_r _ _ 1%positive Hg13) => {Hg13} Hg13succ.
      move: (@pos_le_add_r _ _ 1%positive Hg23) => {Hg23} Hg23succ. repeat split.
      + apply: (zpexpr_bounded_ge_bounded Hg13succ).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
      + apply: (zpexpr_bounded_ge_bounded Hg23succ).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp2 Hnew1).
      + simpl. exact: Pos.lt_add_r.
      + apply: (zpexpr_bounded_ge_bounded (@pos_le_add_diag_r g3 1)).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp3 Hnew2).
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

  Lemma zpexpr_of_conseq_zpexpr_bounded_e g t e g' t' pe pm :
    zpexpr_of_conseq g t e = (g', t', pe, pm) -> newer_than_vm g t ->
    zpexpr_bounded pe g'.
  Proof.
    elim: e g t g' t' pe pm => /=.
    - move=> e1 e2 ig it og ot ope opm.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? ? Hnew; subst. move: (zpexpr_of_zexp_gen Hzp2) => Hg1. split.
      + apply: (zpexpr_bounded_ge_bounded Hg1).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
      + apply: (zpexpr_of_zexp_zpexpr_bounded Hzp2).
        exact: (zpexpr_of_zexp_newer Hzp1 Hnew).
    - move=> e1 e2 e3 ig it og ot ope opm.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexpr_of_zexp g2 t2 e3) => [[[g3 t3] pe3] Hzp3].
      case=> ? ? ? ? Hnew; subst.
      move: (zpexpr_of_zexp_newer Hzp1 Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer Hzp2 Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_gen Hzp2) => Hg12.
      move: (zpexpr_of_zexp_gen Hzp3) => Hg23.
      move: (Pos.le_trans _ _ _ Hg12 Hg23) => Hg13. repeat split.
      + apply: (zpexpr_bounded_ge_bounded Hg13).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp1 Hnew).
      + apply: (zpexpr_bounded_ge_bounded Hg23).
        exact: (zpexpr_of_zexp_zpexpr_bounded Hzp2 Hnew1).
  Qed.

  Lemma zpexpr_of_conseq_zpexpr_bounded_m g t e g' t' pe pm :
    zpexpr_of_conseq g t e = (g', t', pe, pm) -> newer_than_vm g t ->
    zpexpr_bounded pm g'.
  Proof.
    elim: e g t g' t' pe pm => /=.
    - move=> e1 e2 ig it og ot ope opm.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      case=> ? ? ? ? Hnew; subst. done.
    - move=> e1 e2 e3 ig it og ot ope opm.
      dcase (zpexpr_of_zexp ig it e1) => [[[g1 t1] pe1] Hzp1].
      dcase (zpexpr_of_zexp g1 t1 e2) => [[[g2 t2] pe2] Hzp2].
      dcase (zpexpr_of_zexp g2 t2 e3) => [[[g3 t3] pe3] Hzp3].
      case=> ? ? ? ? Hnew; subst.
      move: (zpexpr_of_zexp_newer Hzp1 Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer Hzp2 Hnew1) => Hnew2.
      exact: (zpexpr_of_zexp_zpexpr_bounded Hzp3 Hnew2).
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
  Qed.

  Lemma zpexpr_of_premise_vl_consistent st vl g t e vl' g' t' pe :
    zpexpr_of_premise_vl st vl g t e = (vl', g', t', pe) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case => ? ? ? ? Hnew Hsize Hcon; subst.
      apply: (zpexpr_of_zexp_vl_consistent Hpe2).
      + exact: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew).
      + exact: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize).
      + exact: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon).
    - move=> e1 e2 e3 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case => ? ? ? ? Hnew Hsize Hcon; subst.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe3) Hnew2) => Hnew3.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe3 Hsize2) => Hsize3.
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      move: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1 Hcon1) => Hcon2.
      move: (zpexpr_of_zexp_vl_consistent Hpe3 Hnew2 Hsize2 Hcon2) => Hcon3.
      exact: (rcons_consistent _ Hnew3 Hsize3 Hcon3).
  Qed.

  Lemma zpexprs_of_premises_vl_consistent st vl g t es vl' g' t' pes :
    zpexprs_of_premises_vl st vl g t es = (vl', g', t', pes) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: es vl g t vl' g' t' pes => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes [] ? ? ? ? Hnew Hsize Hcon; subst. assumption.
    - move=> ivl ig it ovl og ot opes.
      dcase (zpexpr_of_premise_vl st ivl ig it hd)
      => [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (zpexprs_of_premises_vl st vl_hd g_hd t_hd tl) =>
      [[[[vl_tl g_tl] t_tl] es_tl] Hpe_tl]. case=> ? ? ? ? Hnew Hsize Hcon; subst.
      apply: (IH _ _ _ _ _ _ _ Hpe_tl).
      + exact: (zpexpr_of_premise_newer (zpexpr_of_premise_vl_novl Hpe_hd) Hnew).
      + exact: (zpexpr_of_premise_vl_size_bounded Hpe_hd).
      + exact: (zpexpr_of_premise_vl_consistent Hpe_hd Hnew Hsize Hcon).
  Qed.

  Lemma zpexpr_of_conseq_vl_consistent st vl g t e vl' g' t' pe pm :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pm) ->
    newer_than_vm g t -> vl_size_bounded vl g ->
    consistent st vl t -> consistent st vl' t'.
  Proof.
    elim: e vl g t vl' g' t' pe pm => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe pm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ? Hnew Hsize Hcon; subst.
      apply: (zpexpr_of_zexp_vl_consistent Hpe2).
      + exact: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew).
      + exact: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize).
      + exact: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon).
    - move=> e1 e2 e3 ivl ig it ovl og ot pe pm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case => ? ? ? ? ? Hnew Hsize Hcon; subst.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      apply: (zpexpr_of_zexp_vl_consistent Hpe3 Hnew2 Hsize2).
      apply: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1).
      exact: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon).
  Qed.

  Lemma zpexprs_of_pspec_vl_consistent st sp vl g t ps m q :
    zpexprs_of_pspec_vl st sp = (vl, g, t, ps, m, q) ->
    consistent st vl t.
  Proof.
    rewrite /zpexprs_of_pspec_vl.
    dcase (zpexprs_of_premises_vl st init_vl init_pos init_vm (ppremises sp)) =>
    [[[[vl_p g_p] t_p] ps_p] Hpe_p].
    dcase (zpexpr_of_conseq_vl st vl_p g_p t_p (pconseq sp)) =>
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
  Qed.

  Lemma zpexpr_of_premise_vl_zpeeval st vl g t e vl' g' t' pe :
    zpexpr_of_premise_vl st vl g t e = (vl', g', t', pe) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    ZPEeval vl' pe = 0 <-> eval_szbexp e st.
  Proof.
    elim: e vl g t vl' g' t' pe => /=.
    - move=> e1 e2 ivl ig it ovl og ot pe.
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
    - move=> e1 e2 e3 ivl ig it ovl og ot pe.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case => ? ? ? ? Hnew Hsize Hcon; subst.
      set m := (if ZSSA.eval_zexp e3 st == 0
                then 0
                else (ZSSA.eval_zexp e1 st - ZSSA.eval_zexp e2 st)
                       / ZSSA.eval_zexp e3 st).
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe1) Hnew) => Hnew1.
      move: (zpexpr_of_zexp_newer (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) => Hnew2.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe1 Hsize) => Hsize1.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe2 Hsize1) => Hsize2.
      move: (zpexpr_of_zexp_vl_size_bounded Hpe3 Hsize2) => Hsize3.
      move: (zpexpr_of_zexp_vl_consistent Hpe1 Hnew Hsize Hcon) => Hcon1.
      move: (zpexpr_of_zexp_vl_consistent Hpe2 Hnew1 Hsize1 Hcon1) => Hcon2.
      move: (zpexpr_of_zexp_gen (zpexpr_of_zexp_vl_novl Hpe2)) => Hg12.
      move: (zpexpr_of_zexp_gen (zpexpr_of_zexp_vl_novl Hpe3)) => Hg23.
      move: (Pos.le_trans _ _ _ Hg12 Hg23) => Hg13.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe1) Hnew) =>
      Hzb11.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe2) Hnew1) =>
      Hzb22.
      move: (zpexpr_of_zexp_zpexpr_bounded (zpexpr_of_zexp_vl_novl Hpe3) Hnew2) =>
      Hzb33.
      move: (zpexpr_bounded_ge_bounded Hg13 Hzb11) => Hzb13.
      move: (zpexpr_bounded_ge_bounded Hg23 Hzb22) => Hzb23.
      move: (zpexpr_of_zexp_vl_prefix_of Hpe2) => Hprefix_of12.
      move: (zpexpr_of_zexp_vl_prefix_of Hpe3) => Hprefix_of23.
      move: (prefix_of_trans Hprefix_of12 Hprefix_of23) => Hprefix_of13.
      rewrite 2!ZPEeval_sub ZPEeval_mul.
      (* remove rcons *)
      rewrite -(rcons_zpeeval m Hsize3 Hzb13).
      rewrite -(rcons_zpeeval m Hsize3 Hzb23).
      rewrite -(rcons_zpeeval m Hsize3 Hzb33).
      rewrite (zpeeval_rcons_last _ Hsize3).
      (* rewrite pe1 *)
      rewrite -(prefix_of_zpeeval Hprefix_of13 Hsize1 Hzb11).
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe1 Hnew Hsize Hcon).
      (* rewrite pe2 *)
      rewrite -(prefix_of_zpeeval Hprefix_of23 Hsize2 Hzb22).
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe2 Hnew1 Hsize1 Hcon1).
      (* rewrite pe3 *)
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe3 Hnew2 Hsize2 Hcon2).
      (* *)
      split.
      + move=> H. exists m. exact: (Zminus_eq _ _ H).
      + move=> [m' H]. rewrite /m. case H3: (ZSSA.eval_zexp e3 st == 0).
        * rewrite (eqP H3) in H. rewrite H. rewrite Z.mul_0_r Z.mul_0_l. reflexivity.
        * rewrite H. move/eqP: H3 => H3. rewrite /m (Z.div_mul _ _ H3).
          apply: Zeq_minus. reflexivity.
  Qed.

  Lemma zpexprs_of_premises_vl_zpeeval st vl g t es vl' g' t' pes :
    zpexprs_of_premises_vl st vl g t es = (vl', g', t', pes) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    (forall e : szbexp, e \in es -> eval_szbexp e st) ->
    zpexpr_all0 vl' pes.
  Proof.
    elim: es vl g t vl' g' t' pes => [| hd tl IH] /=.
    - move=> ivl ig it ovl og ot opes [] ? ? ? ? Hnew Hsize Hcon Hsz; subst. done.
    - move=> ivl ig it ovl og ot opes.
      dcase (zpexpr_of_premise_vl st ivl ig it hd) =>
      [[[[vl_hd g_hd] t_hd] es_hd] Hpe_hd].
      dcase (zpexprs_of_premises_vl st vl_hd g_hd t_hd tl) =>
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
        apply: (IH _ _ _ _ _ _ _ Hpe_tl Hnew_hd Hsize_hd Hcon_hd). move=> e Hin.
        apply: Hsz. by rewrite in_cons Hin orbT.
  Qed.

  Lemma zpexpr_of_conseq_vl_eval_szbexp st vl g t e vl' g' t' pe pm :
    zpexpr_of_conseq_vl st vl g t e = (vl', g', t', pe, pm) ->
    newer_than_vm g t -> vl_size_bounded vl g -> consistent st vl t ->
    (exists c : Z, ZPEeval vl' pe = c * ZPEeval vl' pm) ->
    eval_szbexp e st.
  Proof.
    elim: e vl g t vl' g' t' pe pm => /=.
    - move=> e1 e2 ivl ig it ovl og ot ope opm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      case=> ? ? ? ? ? Hnew Hsize Hcon [c Heq]; subst.
      rewrite /= Z.mul_0_r in Heq. move: (Zminus_eq _ _ Heq).
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
    - move=> e1 e2 e3 ivl ig it ovl og ot ope opm.
      dcase (zpexpr_of_zexp_vl st ivl ig it e1) => [[[[vl1 g1] t1] pe1] Hpe1].
      dcase (zpexpr_of_zexp_vl st vl1 g1 t1 e2) => [[[[vl2 g2] t2] pe2] Hpe2].
      dcase (zpexpr_of_zexp_vl st vl2 g2 t2 e3) => [[[[vl3 g3] t3] pe3] Hpe3].
      case=> ? ? ? ? ? Hnew Hsize Hcon [c Heq]; subst. exists c.
      rewrite /= in Heq. move: Heq.
      (* rewrite pe1 *)
      move: (zpexpr_of_zexp_vl_prefix_of Hpe2) => Hpre12.
      move: (zpexpr_of_zexp_vl_prefix_of Hpe3) => Hpre2o.
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
      rewrite (zpexpr_of_zexp_vl_zpeeval Hpe3 Hnew2 Hsize2 Hcon2).
      (* *)
      by apply.
  Qed.



  (* Convert store to vl *)

  Definition vl_of_store (st : ZSSAStore.t) (sp : pspec) : list Z :=
    let '(vl, _, _, _, _, _) := zpexprs_of_pspec_vl st sp in
    vl.

  Lemma vl_of_store_premises st sp g t ps m q :
    zpexprs_of_pspec sp = (g, t, ps, m, q) ->
    (forall e : szbexp, e \in ppremises sp -> eval_szbexp e st) ->
    zpexpr_all0 (vl_of_store st sp) ps.
  Proof.
    case: sp => [pres post] /=. rewrite /vl_of_store.
    dcase (zpexprs_of_pspec_vl st {| ppremises := pres; pconseq := post |}) =>
    [[[[[[ovl og] ot] ops] om] oq] Hpe].
    rewrite (zpexprs_of_pspec_vl_novl Hpe). case=> ? ? ? ? ?; subst.
    move: Hpe; rewrite /zpexprs_of_pspec_vl /=.
    dcase (zpexprs_of_premises_vl st init_vl init_pos init_vm pres) =>
    [[[[vl_p g_p] t_p] ps_p] Hpe_p].
    dcase (zpexpr_of_conseq_vl st vl_p g_p t_p post) =>
    [[[[[vl_q g_q] t_q] q_q] m_q] Hpe_q].
    case=> ? ? ? ? ? ?; subst. move=> Heval.
    apply: (prefix_of_zpexpr_all0
              (zpexpr_of_conseq_vl_prefix_of Hpe_q)
              (zpexprs_of_premises_vl_size_bounded Hpe_p init_vl_size_bounded)
              (zpexprs_of_premises_zpexprs_bounded (zpexprs_of_premises_vl_novl Hpe_p)
                                                   init_newer_than_vm)).
    exact: (zpexprs_of_premises_vl_zpeeval
              Hpe_p init_newer_than_vm init_vl_size_bounded (init_consistent _)
              Heval).
  Qed.

  Lemma vl_of_store_conseq st sp g t ps m q :
    zpexprs_of_pspec sp = (g, t, ps, m, q) ->
    (exists c, ZPEeval (vl_of_store st sp) q = (c * ZPEeval (vl_of_store st sp) m)) ->
    eval_szbexp (pconseq sp) st.
  Proof.
    case: sp => [pres post] /=. rewrite /vl_of_store.
    dcase (zpexprs_of_pspec_vl st {| ppremises := pres; pconseq := post |}) =>
    [[[[[[ovl og] ot] ops] om] oq] Hpe].
    rewrite (zpexprs_of_pspec_vl_novl Hpe). case=> ? ? ? ? ?; subst.
    move: Hpe; rewrite /zpexprs_of_pspec_vl /=.
    dcase (zpexprs_of_premises_vl st init_vl init_pos init_vm pres) =>
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
    exact: (zpexpr_of_conseq_vl_eval_szbexp Hpe_q Hnew_p Hsize_p Hcon_p Heval).
  Qed.

End PExpr.



Section Checker.

  Definition combine_coefficients (cs : seq (PExpr Z)) (ps : seq (PExpr Z))
  : seq (PExpr Z) :=
    map (fun '(c, p) => PEmul c p) (zip cs ps).

  Fixpoint sum_polys (ps : seq (PExpr Z)) : PExpr Z :=
    match ps with
    | [::] => PEO
    | hd::tl => PEadd hd (sum_polys tl)
    end.

  (* Two polynomials are syntactically equal after normalization *)
  Definition zpexpr_eqb (p1 p2 : PExpr Z) : bool :=
    ZPeq (Znorm_subst p1) (Znorm_subst p2).

  (* Check if q = cs * ps + c * m *)
  Definition coefficients_checker ps m q cs c : bool :=
    (size ps == size cs) &&
    zpexpr_eqb q (PEadd (sum_polys (combine_coefficients cs ps)) (PEmul c m)).

  (* If q = cs * ps + c * m and for each p \in ps, p = 0, then q = c * m *)
  Lemma checker_imply_eq ps m q cs c :
    coefficients_checker ps m q cs c ->
    zpimply_eq ps q (PEmul c m).
  Proof.
    move/andP=> [Hs Heq] l Heq0. rewrite /ZPEeval.
    (* Convert the syntactical equality in the hypotheses to semantic equality *)
    rewrite /zpexpr_eqb /ZPeq in Heq. move: (ZPeq_ok Heq) => {Heq} Heq.
    move: (Heq l) => {Heq} Heq.
    (* Convert Pol evaluation to PExpr evaluation *)
    move: Heq. rewrite -Znorm_subst_spec; try done.
    rewrite -Znorm_subst_spec; try done.
    (* rewrite q = cs * ps + c * m *)
    move=> ->.
    (* Induction on ps *)
    rewrite /=. case: ps cs Hs Heq0 => [| hd tl] //=.
    - (* ps = [::] *) by case.
    - (* ps = hd::tl *) case=> //=. move=> cs_hd. (* cs = cs_hd::cs_tl *)
      elim: tl => [| tl_hd tl_tl IH] //=.
      + (* ps = [:: hd] *) case=> //=. (* cs = cs_hd *) rewrite /ZPEeval.
        move=> _ [-> _]. rewrite Z.mul_0_r !Z.add_0_l. reflexivity.
      + (* ps = hd::tl_hd::tl_tl *) case => //=. (* cs = cs_hd::cs_tl_hd::cs_tl_tl *)
        move=> cs_tl_hd cs_tl_tl. rewrite /ZPEeval=> Hsize [Hhd [Htl_hd Htl_tl]].
        rewrite Hhd in IH *. rewrite Htl_hd !Z.mul_0_r !Z.add_0_l.
        rewrite Z.mul_0_r in IH. rewrite -{2}(IH cs_tl_tl).
        * rewrite !Z.add_0_l. reflexivity.
        * rewrite -addn2 -(addn2 (size cs_tl_tl)) eqn_add2r in Hsize.
            by rewrite (eqP Hsize).
        * split; [exact: Hhd | exact: Htl_tl].
  Qed.

  Lemma zimply_eq_valid_pspec sp g t ps m q c :
    zpexprs_of_pspec sp = (g, t, ps, m, q) -> zpimply_eq ps q (PEmul c m) ->
    valid_pspec sp.
  Proof.
    move=> Hpoly Himp st Hzpre. move: (Himp (vl_of_store st sp)) => {Himp} Himp.
    move: (vl_of_store_premises Hpoly Hzpre) => Hall0.
    move: (Himp Hall0) => Hqcm. apply: (vl_of_store_conseq Hpoly).
    exists (ZPEeval (vl_of_store st sp) c). exact: Hqcm.
  Qed.

  (* If the coefficients are verified by the checker, the pspec is valid *)
  Theorem checker_valid_pspec s g t ps m q cs c :
    zpexprs_of_pspec s = (g, t, ps, m, q) ->
    coefficients_checker ps m q cs c ->
    valid_pspec s.
  Proof.
    move=> Hpoly Hch. exact: (zimply_eq_valid_pspec Hpoly (checker_imply_eq Hch)).
  Qed.


  (* Tail-recursive checker *)

  Definition combine_coefficients_tr (cs : seq (PExpr Z)) (ps : seq (PExpr Z))
  : seq (PExpr Z) :=
    mapr (fun '(c, p) => PEmul c p) (zip cs ps).

  Fixpoint sum_polys_rec res (ps : seq (PExpr Z)) : PExpr Z :=
    match ps with
    | [::] => res
    | hd::tl => sum_polys_rec (PEadd res hd) tl
    end.

  Definition sum_polys_tr (ps : seq (PExpr Z)) : PExpr Z :=
    match ps with
    | [::] => PEO
    | hd::tl => sum_polys_rec hd tl
    end.

  Lemma combine_coefficients_tr_cons c cs p ps :
    combine_coefficients_tr (c::cs) (p::ps) = rcons (combine_coefficients_tr cs ps)
                                                    (PEmul c p).
  Proof.
    rewrite /combine_coefficients_tr. rewrite NBitsOp.zip_cons.
    rewrite mapr_cons. reflexivity.
  Qed.

  Lemma sum_polys_rec_rcons res ps p :
    sum_polys_rec res (rcons ps p) = PEadd (sum_polys_rec res ps) p.
  Proof. by elim: ps res p => [| hd tl IH] //=. Qed.

  Lemma sum_polys_tr_rcons ps p :
    0 < size ps ->
    sum_polys_tr (rcons ps p) = PEadd (sum_polys_tr ps) p.
  Proof.
    rewrite /sum_polys_tr. case: ps => [| hd tl] //=.
    move=> _. rewrite sum_polys_rec_rcons. reflexivity.
  Qed.

  (* Check if q = cs * ps + c * m *)
  Definition coefficients_checker_tr ps m q cs c : bool :=
    (size ps == size cs) &&
    zpexpr_eqb q (PEadd (sum_polys_tr (combine_coefficients_tr cs ps)) (PEmul c m)).

  (* If q = cs * ps + c * m and for each p \in ps, p = 0, then q = c * m *)
  Lemma checker_tr_imply_eq ps m q cs c :
    coefficients_checker_tr ps m q cs c ->
    zpimply_eq ps q (PEmul c m).
  Proof.
    move/andP=> [Hs Heq] l Heq0. rewrite /ZPEeval.
    (* Convert the syntactical equality in the hypotheses to semantic equality *)
    rewrite /zpexpr_eqb /ZPeq in Heq. move: (ZPeq_ok Heq) => {Heq} Heq.
    move: (Heq l) => {Heq} Heq.
    (* Convert Pol evaluation to PExpr evaluation *)
    move: Heq. rewrite -Znorm_subst_spec; try done.
    rewrite -Znorm_subst_spec; try done.
    (* rewrite q = cs * ps + c * m *)
    move=> ->.
    (* Induction on ps *)
    rewrite /=. case: ps cs Hs Heq0 => [| hd tl] //=.
    - (* ps = [::] *) by case.
    - (* ps = hd::tl *) case=> //=. move=> cs_hd. (* cs = cs_hd::cs_tl *)
      elim: tl => [| tl_hd tl_tl IH] //=.
      + (* ps = [:: hd] *) case=> //=. (* cs = cs_hd *) rewrite /ZPEeval.
        move=> _ [-> _]. rewrite Z.mul_0_r !Z.add_0_l. reflexivity.
      + (* ps = hd::tl_hd::tl_tl *) case => //=. (* cs = cs_hd::cs_tl_hd::cs_tl_tl *)
        move=> cs_tl_hd cs_tl_tl. rewrite /ZPEeval=> Hsize [Hhd [Htl_hd Htl_tl]].
        apply/Z.add_move_r. rewrite Z.sub_diag.
        have Hseq: (size tl_tl) = (size cs_tl_tl).
        { rewrite -addn2 -(addn2 (size cs_tl_tl)) eqn_add2r in Hsize.
          exact: (eqP Hsize). }
        have Hssucc: (size tl_tl).+1 == (size cs_tl_tl).+1 by rewrite Hseq.
        move: (IH cs_tl_tl Hssucc (conj Hhd Htl_tl)) => H.
        move/Z.add_move_r: H. rewrite Z.sub_diag => H.
        move: H. rewrite !combine_coefficients_tr_cons.
        case Hs0: (0 < size (combine_coefficients_tr cs_tl_tl tl_tl)).
        * rewrite (sum_polys_tr_rcons _ Hs0) /=. rewrite Hhd Z.mul_0_r Z.add_0_r.
          rewrite sum_polys_tr_rcons /=; last by rewrite size_rcons.
          rewrite Hhd Z.mul_0_r Z.add_0_r.
          rewrite (sum_polys_tr_rcons _ Hs0) /=. rewrite Htl_hd Z.mul_0_r Z.add_0_r.
          by apply.
        * move/idP/negP: Hs0. rewrite -eqn0Ngt. move/eqP=> Hs.
          move: (size0nil Hs) => -> /=. rewrite Hhd Htl_hd.
          rewrite !Z.mul_0_r. reflexivity.
  Qed.

  (* If the coefficients are verified by the checker, the pspec is valid *)
  Theorem checker_tr_valid_pspec s g t ps m q cs c :
    zpexprs_of_pspec s = (g, t, ps, m, q) ->
    coefficients_checker_tr ps m q cs c ->
    valid_pspec s.
  Proof.
    move=> Hpoly Hch. exact: (zimply_eq_valid_pspec Hpoly (checker_tr_imply_eq Hch)).
  Qed.

End Checker.
