
From Coq Require Import List ZArith FSets OrderedType String Decimal DecimalString Btauto.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State BBCommon.
From ssrlib Require Import Var SsrOrder FMaps ZAriths Tactics Lists FSets Seqs Strings.
From Cryptoline Require Import Options DSLRaw DSLFull SSAFull.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** Variable substitution for instructions *)

Section VarSubst.

  Import SSAFull.

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

  Fixpoint subst_eexp p r e :=
    match e with
    | Evar v => if v == p then r else e
    | Econst _ => e
    | Eunop op e => eunary op (subst_eexp p r e)
    | Ebinop op e1 e2 => ebinary op (subst_eexp p r e1) (subst_eexp p r e2)
    | Epow e n => epow (subst_eexp p r e) n
    end.

  Fixpoint subst_rexp p r e :=
    match e with
    | Rvar v => if v == p then r else e
    | Rconst _ _ => e
    | Runop w op e => runary w op (subst_rexp p r e)
    | Rbinop w op e1 e2 => rbinary w op (subst_rexp p r e1) (subst_rexp p r e2)
    | Ruext w e i => ruext w (subst_rexp p r e) i
    | Rsext w e i => rsext w (subst_rexp p r e) i
    end.

  Fixpoint subst_eexps p r es :=
    match es with
    | [::] => [::]
    | e::es => (subst_eexp p r e)::(subst_eexps p r es)
    end.

  Fixpoint subst_ebexp p r e :=
    match e with
    | Etrue => e
    | Eeq e1 e2 => Eeq (subst_eexp p r e1) (subst_eexp p r e2)
    | Eeqmod e1 e2 ms => Eeqmod (subst_eexp p r e1) (subst_eexp p r e2) (subst_eexps p r ms)
    | Eand e1 e2 => Eand (subst_ebexp p r e1) (subst_ebexp p r e2)
    end.

  Fixpoint subst_rbexp p r e :=
    match e with
    | Rtrue => e
    | Req w e1 e2 => Req w (subst_rexp p r e1) (subst_rexp p r e2)
    | Rcmp w op e1 e2 => Rcmp w op (subst_rexp p r e1) (subst_rexp p r e2)
    | Rneg e => Rneg (subst_rbexp p r e)
    | Rand e1 e2 => Rand (subst_rbexp p r e1) (subst_rbexp p r e2)
    | Ror e1 e2 => Ror (subst_rbexp p r e1) (subst_rbexp p r e2)
    end.

  Definition subst_bexp p r e :=
    (subst_ebexp p (eexp_of_atom r) (fst e), subst_rbexp p (rexp_of_atom r) (snd e)).

  Definition subst_atom p r (a : SSAFull.atom) :=
    match a with
    | Avar v => if v == p then r else a
    | Aconst _ _ => a
    end.

  Definition subst_instr p r i :=
    match i with
    | Imov v a => Imov v (subst_atom p r a)
    | Ishl v a n => Ishl v (subst_atom p r a) n
    | Icshl v1 v2 a1 a2 n => Icshl v1 v2 (subst_atom p r a1) (subst_atom p r a2) n
    | Inondet v t => i
    | Icmov v c a1 a2 => Icmov v c (subst_atom p r a1) (subst_atom p r a2)
    | Inop => i
    | Inot v t a => Inot v t (subst_atom p r a)
    | Iadd v a1 a2 => Iadd v (subst_atom p r a1) (subst_atom p r a2)
    | Iadds c v a1 a2 => Iadds c v (subst_atom p r a1) (subst_atom p r a2)
    | Iadc v a1 a2 y => Iadc v (subst_atom p r a1) (subst_atom p r a2) y
    | Iadcs c v a1 a2 y => Iadcs c v (subst_atom p r a1) (subst_atom p r a2) y
    | Isub v a1 a2 => Isub v (subst_atom p r a1) (subst_atom p r a2)
    | Isubc c v a1 a2 => Isubc c v (subst_atom p r a1) (subst_atom p r a2)
    | Isubb c v a1 a2 => Isubb c v (subst_atom p r a1) (subst_atom p r a2)
    | Isbc v a1 a2 y => Isbc v (subst_atom p r a1) (subst_atom p r a2) y
    | Isbcs c v a1 a2 y => Isbcs c v (subst_atom p r a1) (subst_atom p r a2) y
    | Isbb v a1 a2 y => Isbb v (subst_atom p r a1) (subst_atom p r a2) y
    | Isbbs c v a1 a2 y => Isbbs c v (subst_atom p r a1) (subst_atom p r a2) y
    | Imul v a1 a2 => Imul v (subst_atom p r a1) (subst_atom p r a2)
    | Imull vh vl a1 a2 => Imull vh vl (subst_atom p r a1) (subst_atom p r a2)
    | Imulj v a1 a2 => Imulj v (subst_atom p r a1) (subst_atom p r a2)
    | Isplit vh vl a n => Isplit vh vl (subst_atom p r a) n
    | Iand v t a1 a2 => Iand v t (subst_atom p r a1) (subst_atom p r a2)
    | Ior v t a1 a2 => Ior v t (subst_atom p r a1) (subst_atom p r a2)
    | Ixor v t a1 a2 => Ixor v t (subst_atom p r a1) (subst_atom p r a2)
    | Icast v t a => Icast v t (subst_atom p r a)
    | Ivpc v t a => Ivpc v t (subst_atom p r a)
    | Ijoin v ah al => Ijoin v (subst_atom p r ah) (subst_atom p r al)
    | Icut e => Icut (subst_bexp p r e)
    | Iassert e => Iassert (subst_bexp p r e)
    | Iassume e => Iassume (subst_bexp p r e)
    end.

  Definition subst_program p r prog := tmap (subst_instr p r) prog.

End VarSubst.


Section Extra.

  Import SSAFull.

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


(* Rewrite mov statements in AST level - to be implemented for optimization *)

Section RewriteMov.

  Import SSAFull.

  Definition rewrite_mov (s : spec) : spec := s.

  Lemma rewrite_mov_vars s : SSAVS.Equal (vars_spec (rewrite_mov s)) (vars_spec s).
  Proof. reflexivity. Qed.

  Lemma rewrite_mov_sound s :
    well_formed_ssa_spec s ->
    valid_spec (rewrite_mov s) -> valid_spec s.
  Proof. move=> _. by apply. Qed.

  Lemma rewrite_mov_complete s :
    well_formed_ssa_spec s ->
    valid_spec s -> valid_spec (rewrite_mov s).
  Proof. move=> _. by apply. Qed.

  Lemma rewrite_mov_well_formed_ssa s :
    well_formed_ssa_spec s ->
    well_formed_ssa_spec (rewrite_mov s).
  Proof. by apply. Qed.

  Lemma rewrite_mov_succ_typenv s :
    well_formed_ssa_spec s ->
    SSATE.Equal
             (program_succ_typenv (sprog (rewrite_mov s)) (sinputs (rewrite_mov s)))
             (program_succ_typenv (sprog s) (sinputs s)).
  Proof. reflexivity. Qed.

End RewriteMov.


(* Convert SSAFull without Iassert and Icut statements to SSA *)

From Cryptoline Require SSA.

Section SSA2Lite.

  Import SSA.
  Import SSAFull.


  (* Programs containing neither cut nor assert statements *)

  Definition program_is_lite (p : SSAFull.program) : bool :=
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
    program_is_lite p = (SSAFull.program_has_no_cut p) && (program_has_no_assert p).
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


  (* Conversion from SSAFull to SSA *)

  Definition ssa2lite_instr (i : SSAFull.instr) : SSA.instr :=
    match i with
    | Imov v a => SSA.Imov v a
    | Ishl v a n => SSA.Ishl v a n
    | Icshl v1 v2 a1 a2 n => SSA.Icshl v1 v2 a1 a2 n
    | Inondet v t => SSA.Inondet v t
    | Icmov v c a1 a2 => SSA.Icmov v c a1 a2
    | Inop => SSA.Inop
    | Inot v t a => SSA.Inot v t a
    | Iadd v a1 a2 => SSA.Iadd v a1 a2
    | Iadds c v a1 a2 => SSA.Iadds c v a1 a2
    | Iadc v a1 a2 y => SSA.Iadc v a1 a2 y
    | Iadcs c v a1 a2 y => SSA.Iadcs c v a1 a2 y
    | Isub v a1 a2 => SSA.Isub v a1 a2
    | Isubc c v a1 a2 => SSA.Isubc c v a1 a2
    | Isubb c v a1 a2 => SSA.Isubb c v a1 a2
    | Isbc v a1 a2 y => SSA.Isbc v a1 a2 y
    | Isbcs c v a1 a2 y => SSA.Isbcs c v a1 a2 y
    | Isbb v a1 a2 y => SSA.Isbb v a1 a2 y
    | Isbbs c v a1 a2 y => SSA.Isbbs c v a1 a2 y
    | Imul v a1 a2 => SSA.Imul v a1 a2
    | Imull vh vl a1 a2 => SSA.Imull vh vl a1 a2
    | Imulj v a1 a2 => SSA.Imulj v a1 a2
    | Isplit vh vl a n => SSA.Isplit vh vl a n
    | Iand v t a1 a2 => SSA.Iand v t a1 a2
    | Ior v t a1 a2 => SSA.Ior v t a1 a2
    | Ixor v t a1 a2 => SSA.Ixor v t a1 a2
    | Icast v t a => SSA.Icast v t a
    | Ivpc v t a => SSA.Ivpc v t a
    | Ijoin v ah al => SSA.Ijoin v ah al
    | Icut e => SSA.Inop
    | Iassert e => SSA.Inop
    | Iassume e => SSA.Iassume e
    end.

  Definition ssa2lite_program (p : SSAFull.program) : SSA.program :=
    tmap ssa2lite_instr p.

  Definition ssa2lite_spec (s : SSAFull.spec) : SSA.spec :=
    {| SSA.sinputs := sinputs s;
       SSA.spre := spre s;
       SSA.sprog := ssa2lite_program (sprog s);
       SSA.spost := spost s |}.


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
    SSAVS.Equal (SSA.lvs_instr (ssa2lite_instr i)) (lvs_instr i).
  Proof. by case: i => //=. Qed.

  Lemma ssa2lite_instr_vars_subset i :
    SSAVS.subset (SSA.vars_instr (ssa2lite_instr i)) (vars_instr i).
  Proof. case: i => //=; intros; exact: VSLemmas.subset_refl. Qed.

  Lemma ssa2lite_program_vars_subset p :
    SSAVS.subset (SSA.vars_program (ssa2lite_program p)) (vars_program p).
  Proof.
    elim: p => [| i p IH] //=. rewrite ssa2lite_program_cons /=.
    exact: (VSLemmas.union_subsets (ssa2lite_instr_vars_subset i) IH).
  Qed.

  Lemma ssa2lite_spec_vars_subset s :
    SSAVS.subset (SSA.vars_spec (ssa2lite_spec s)) (vars_spec s).
  Proof.
    rewrite /ssa2lite_spec /SSA.vars_spec /vars_spec. case: s => E f p g /=.
    apply: (VSLemmas.union_subsets (VSLemmas.subset_refl _)).
    apply: (VSLemmas.union_subsets _ (VSLemmas.subset_refl _)).
    exact: (ssa2lite_program_vars_subset p).
  Qed.

  Lemma ssa2lite_instr_vars_equal E i :
    well_formed_instr E i ->
    SSAVS.Equal (SSAVS.union (vars_env E) (SSA.vars_instr (ssa2lite_instr i)))
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
    SSAVS.Equal (SSAVS.union (vars_env E) (SSA.vars_program (ssa2lite_program p)))
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
                      (SSAVS.union (SSAVS.union (vars_env E) (lvs_instr i)) (SSA.vars_program (ssa2lite_program p))))
         (SSAVS.union (SSAVS.union (vars_env E) (vars_instr i)) (SSA.vars_program (ssa2lite_program p))).
    { rewrite vars_instr_split. by VSLemmas.dp_Equal. }
    rewrite -VSLemmas.P.union_assoc. rewrite (ssa2lite_instr_vars_equal Hwfi).
    reflexivity.
  Qed.

  Lemma ssa2lite_spec_vars_equal s :
    well_formed_spec s ->
    SSAVS.Equal (SSAVS.union (vars_env (SSA.sinputs (ssa2lite_spec s))) (SSA.vars_spec (ssa2lite_spec s)))
                (SSAVS.union (vars_env (sinputs s)) (vars_spec s)).
  Proof.
    case: s => E f p g /=. rewrite /well_formed_spec /ssa2lite_spec /SSA.vars_spec /vars_spec /=.
    move=> /andP [/andP [_ Hwfp] _].
    have ->:
         SSAVS.Equal
         (SSAVS.union (vars_env E)
                      (SSAVS.union (SSA.vars_bexp f)
                                   (SSAVS.union (SSA.vars_program (ssa2lite_program p)) (SSA.vars_bexp g))))
         (SSAVS.union (SSA.vars_bexp f)
                      (SSAVS.union (SSA.vars_bexp g)
                                   (SSAVS.union (vars_env E) (SSA.vars_program (ssa2lite_program p)))))
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
    SSA.instr_succ_typenv (ssa2lite_instr i) E = instr_succ_typenv i E.
  Proof. by case: i. Qed.

  Lemma ssa2lite_program_succ_typenv E p :
    SSA.program_succ_typenv (ssa2lite_program p) E = program_succ_typenv p E.
  Proof.
    elim: p E => [| i p IH] E //=. rewrite ssa2lite_program_cons /=.
    rewrite ssa2lite_instr_succ_typenv. exact: IH.
  Qed.

  Lemma ssa2lite_spec_succ_typenv s :
    SSA.program_succ_typenv (SSA.sprog (ssa2lite_spec s)) (SSA.sinputs (ssa2lite_spec s))
    = SSAFull.program_succ_typenv (SSAFull.sprog s) (SSAFull.sinputs s).
  Proof. case: s => E f p g. exact: ssa2lite_program_succ_typenv. Qed.


  (* Evaluation *)

  Lemma ssa2lite_instr_sound E i s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    SSA.eval_instr E (ssa2lite_instr i) s1 s2 ->
    eval_instr E i (OK s1) (OK s2).
  Proof.
    (case: i => //=); intros; SSA.eval_instr_elim;
    repeat match goal with
           | H : context [SSA.atyp] |- _ =>
               change SSA.atyp with atyp in H
           | H : context [SSA.eval_atom] |- _ =>
               change SSA.eval_atom with eval_atom in H
           end; try (eval_instr_intro; assumption).
    apply: (EInondet _ H1). assumption.
  Qed.

  Lemma ssa2lite_instr_complete E i s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    eval_instr E i (OK s1) (OK s2) ->
    SSA.eval_instr E (ssa2lite_instr i) s1 s2.
  Proof.
    (case: i => //=); intros; eval_instr_elim;
    repeat match goal with
           | H : context [atyp] |- _ =>
               change atyp with SSA.atyp in H
           | H : context [eval_atom] |- _ =>
               change eval_atom with SSA.eval_atom in H
           end; try (SSA.eval_instr_intro; assumption).
    apply: (SSA.EInondet _ H1). assumption.
  Qed.

  Lemma ssa2lite_instr_eval E i s1 s2 :
    ~~ is_cut i && ~~ is_assert i ->
    SSA.eval_instr E (ssa2lite_instr i) s1 s2 <->
      eval_instr E i (OK s1) (OK s2).
  Proof.
    by intuition auto using ssa2lite_instr_sound, ssa2lite_instr_complete.
  Qed.

  Lemma ssa2lite_program_sound E p s1 s2 :
    program_is_lite p ->
    SSA.eval_program E (ssa2lite_program p) s1 s2 ->
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
    SSA.eval_program E (ssa2lite_program p) s1 s2.
  Proof.
    elim: p E s1 s2 => [| i p IH] E s1 s2 //=.
    - move=> _. inversion_clear 1. apply: SSA.Enil. simpl; assumption.
    - rewrite program_is_lite_cons ssa2lite_program_cons. move/andP=> /= [Hi Hp] Hevip.
      move: (program_is_lite_eval_program_cons_ok Hi Hp Hevip) => [s3 [Hevi Hevp]].
      apply: (SSA.Econs (ssa2lite_instr_complete Hi Hevi)).
      rewrite ssa2lite_instr_succ_typenv. exact: (IH _ _ _ Hp Hevp).
  Qed.

  Lemma ssa2lite_spec_sound s :
    spec_is_lite s ->
    SSA.valid_spec (ssa2lite_spec s) ->
    SSAFull.valid_spec s.
  Proof.
    case: s => E f p g /=.
    rewrite /SSA.valid_spec /valid_spec /valid_spec_ok /valid_spec_err
            /ssa2lite_spec /=.
    move=> Hnca Hv. rewrite ssa2lite_program_succ_typenv in Hv. split.
    - move=> s1 s2 Hco Hevf Hevp. apply: (Hv _ _ Hco Hevf).
      exact: (ssa2lite_program_complete Hnca Hevp).
    - move=> s Hco Hevf Hevp. move: (program_is_lite_eval_program_ok_exists Hnca Hevp) => [t H].
      discriminate.
  Qed.

  Lemma ssa2lite_spec_complete s :
    spec_is_lite s ->
    SSAFull.valid_spec s ->
    SSA.valid_spec (ssa2lite_spec s).
  Proof.
    case: s => E f p g /=. rewrite /SSA.valid_spec /valid_spec /valid_spec_ok /valid_spec_err
                                   /ssa2lite_spec /=.
    move=> Hnca [Hvok Hverr]. rewrite ssa2lite_program_succ_typenv.
    move=> s1 s2 Hco Hevf Hevp. apply: (Hvok _ _ Hco Hevf).
    exact: (ssa2lite_program_sound Hnca Hevp).
  Qed.


  (* Well-formedness *)

  Lemma ssa2lite_instr_well_formed E i :
    ~~ is_cut i && ~~ is_assert i ->
    SSA.well_formed_instr E (ssa2lite_instr i) = SSAFull.well_formed_instr E i.
  Proof. by case: i => //=. Qed.

  Lemma ssa2lite_program_well_formed E p :
    program_is_lite p ->
    SSA.well_formed_program E (ssa2lite_program p) = SSAFull.well_formed_program E p.
  Proof.
    elim: p E => [| i p IH] E //=. rewrite program_is_lite_cons => /andP [Hncai Hncap].
    rewrite ssa2lite_program_cons /=. rewrite (ssa2lite_instr_well_formed _ Hncai).
    rewrite (IH _ Hncap). rewrite ssa2lite_instr_succ_typenv. reflexivity.
  Qed.

  Lemma ssa2lite_instr_unchanged vs i :
    SSA.ssa_vars_unchanged_instr vs (ssa2lite_instr i) =
      SSAFull.ssa_vars_unchanged_instr vs i.
  Proof. by case: i => //=. Qed.

  Lemma ssa2lite_program_unchanged vs p :
    SSA.ssa_vars_unchanged_program vs (ssa2lite_program p) =
      SSAFull.ssa_vars_unchanged_program vs p.
  Proof.
    elim: p => [| i p IH] //=.
    rewrite ssa2lite_program_cons.
    rewrite SSAFull.ssa_unchanged_program_cons SSA.ssa_unchanged_program_cons.
    rewrite ssa2lite_instr_unchanged IH. reflexivity.
  Qed.

  Lemma ssa2lite_program_single_assignment p :
    SSA.ssa_single_assignment (ssa2lite_program p) = SSAFull.ssa_single_assignment p.
  Proof.
    elim: p => [| i p IH] //=. rewrite ssa2lite_program_cons /=.
    rewrite ssa2lite_instr_lvs ssa2lite_program_unchanged IH. reflexivity.
  Qed.

  Lemma ssa2lite_program_well_formed_ssa E p :
    program_is_lite p ->
    SSA.well_formed_ssa_program E (ssa2lite_program p) =
      SSAFull.well_formed_ssa_program E p.
  Proof.
    elim: p E => [| i p IH] E //=.
    rewrite program_is_lite_cons; move/andP => [Hncai Hncap].
    rewrite ssa2lite_program_cons /SSAFull.well_formed_ssa_program / SSA.well_formed_ssa_program /=.
    rewrite (ssa2lite_instr_well_formed _ Hncai).
    rewrite ssa2lite_instr_succ_typenv (ssa2lite_program_well_formed _ Hncap).
    rewrite SSAFull.ssa_unchanged_program_cons SSA.ssa_unchanged_program_cons
            ssa2lite_instr_unchanged ssa2lite_program_unchanged.
    rewrite ssa2lite_instr_lvs ssa2lite_program_unchanged.
    rewrite ssa2lite_program_single_assignment. reflexivity.
  Qed.

  Lemma ssa2lite_spec_well_formed s :
    spec_is_lite s ->
    SSA.well_formed_spec (ssa2lite_spec s) = SSAFull.well_formed_spec s.
  Proof.
    case: s => E f p g. rewrite /spec_is_lite /SSAFull.well_formed_spec /SSA.well_formed_spec /=.
    move=> Hpl. rewrite ssa2lite_program_succ_typenv.
    replace (SSA.well_formed_bexp E f) with (SSAFull.well_formed_bexp E f) by reflexivity.
    replace (SSA.well_formed_bexp (program_succ_typenv p E) g) with
      (SSAFull.well_formed_bexp (program_succ_typenv p E) g) by reflexivity.
    rewrite (ssa2lite_program_well_formed _ Hpl) /=.
    reflexivity.
  Qed.

  Lemma ssa2lite_spec_well_formed_ssa s :
    spec_is_lite s ->
    SSA.well_formed_ssa_spec (ssa2lite_spec s) = SSAFull.well_formed_ssa_spec s.
  Proof.
    case: s => E f p g. rewrite /SSAFull.well_formed_ssa_spec /SSA.well_formed_ssa_spec /=.
    move=> Hsl. rewrite (ssa2lite_spec_well_formed Hsl).
    rewrite ssa2lite_program_unchanged. rewrite ssa2lite_program_single_assignment.
    reflexivity.
  Qed.

End SSA2Lite.
