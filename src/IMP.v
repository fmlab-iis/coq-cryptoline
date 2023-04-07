
(** * Ideal membership problem (IMP) together with the validator of CAS answers *)

From Coq Require Import List Arith ZArith String Lia BinaryString Ring_polynom.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import EqVar Types EqOrder Nats ZAriths Seqs Store Tactics Compatibility EqFSets.
From BitBlasting Require Import State.
From Cryptoline Require Import Options DSLLite SSALite REP ZPoly.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** ** Conversion from an atomic root entailment problem to an ideal membership problem *)

Section AREP2IMP.

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

  Fixpoint zpexpr_of_zexp (g : positive) (t : SSAVM.t positive) (e : REP.zexp) :
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

  Fixpoint zpexprs_of_zexps (g : positive) (t : SSAVM.t positive) (es : seq REP.zexp) :
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

End AREP2IMP.


(** ** Help functions for the simplification of ideal membership problems *)

Module PS <: EqFSet := EqFSets.MakeTreeSet PositiveOrder.

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
    (* v = 0 *)
    | PEX j => Some (j, PEO)
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


(** ** Simplification of ideal membership problems *)

Section IdealMembershipRewriting.

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


  (* Substitution of `PExpr Z` *)

  Definition subst_zpexpr (p r e : PExpr Z) : PExpr Z := subst_pexpr Z.eqb p r e.

  Definition subst_zpexprs (p r : PExpr Z) (es : seq (PExpr Z)) : seq (PExpr Z) :=
    subst_pexprs Z.eqb p r es.


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

  Definition simplify_generator ps q : seq (PExpr Z) * PExpr Z :=
    let '(ps', q') := simplify_generator_rec
                        [::] (tmap simplify_zpexpr ps) (simplify_zpexpr q) in
    (ps', q').


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

  Definition pair_zpexpr_with_vars (e : PExpr Z) : PS.t * PExpr Z :=
    (vars_pexpr e, e).

  Definition simplify_generator_vars_cache ps q : seq (PExpr Z) * PExpr Z :=
    let vs_ps := tmap pair_zpexpr_with_vars (tmap simplify_zpexpr ps) in
    let vs_q := pair_zpexpr_with_vars (simplify_zpexpr q) in
    let '(vs_ps', vs_q') := simplify_generator_vars_cache_rec [::] vs_ps vs_q in
    ((split vs_ps').2, vs_q'.2).

End IdealMembershipRewriting.


(** ** Validation of answers from CAS *)

Section Validator.

  (** Validate the answer (cps, cms) of an ideal membership problem given as a
      tuple (ps, ms, q), i.e., check if q = cps * ps + cms * ms. *)
  Definition validate_imp_answer ps ms q cps cms : bool :=
    (size ps == size cps) && (size ms == size cms) &&
    zpexpr_eqb q (PEadd (peadds (pemuls cps ps)) (peadds (pemuls cms ms))).

End Validator.


(** ** Properties of the conversion from AREP to IMP *)

Section AREP2IMPLemmas.

  Local Open Scope Z_scope.

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

  Lemma zpexpr_of_eunop_zpeeval op vl pe :
    ZPEeval vl (zpexpr_of_eunop op pe) = SSALite.eval_eunop op (ZPEeval vl pe).
  Proof. by case: op. Qed.

  Lemma zpexpr_of_ebinop_zpeeval op vl pe1 pe2 :
    ZPEeval vl (zpexpr_of_ebinop op pe1 pe2) =
    SSALite.eval_ebinop op (ZPEeval vl pe1) (ZPEeval vl pe2).
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

  Fixpoint zpexpr_of_zexp_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (e : REP.zexp) :
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

  Fixpoint zpexprs_of_zexps_vl (s : ZSSAStore.t) (vl : list Z) (g : positive) (t : SSAVM.t positive) (es : seq REP.zexp) :
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
      let vp := if (REP.eval_zexp p s) == 0 then
                  0
                else
                  (Z.div ((REP.eval_zexp e1 s) - (REP.eval_zexp e2 s))
                         (REP.eval_zexp p s)) in
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
      + rewrite REP.size_eval_zexps in Hxs. rewrite -Hxs in Hs *.
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


  (* Relate ZPEeval and REP.eval_zexp *)

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
    ZPEeval vl' pe = REP.eval_zexp e st.
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
    ZPEevals vl' pes = REP.eval_zexps es st.
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
      move: (size_xchoose_zeqms_ext pf). rewrite REP.size_eval_zexps => Hsize_ks.
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

End AREP2IMPLemmas.


(** ** Properties of PExpr substitution *)

Section PExprAuxLemmas.

  Variable C : Type.

  Variable ceq : C -> C -> bool.

  Local Notation subst_pexpr := (@subst_pexpr C ceq).
  Local Notation subst_pexprs := (@subst_pexprs C ceq).

  Lemma subst_pexprs_cons p r e es :
    subst_pexprs p r (e::es) = subst_pexpr p r e :: subst_pexprs p r es.
  Proof. rewrite /subst_pexprs !tmap_map /=. reflexivity. Qed.

  Lemma subst_pexprs_cat p r es1 es2 :
    subst_pexprs p r (es1 ++ es2) = subst_pexprs p r es1 ++ subst_pexprs p r es2.
  Proof. rewrite /subst_pexprs !tmap_map /=. exact: map_cat. Qed.

End PExprAuxLemmas.


(** ** Properties of the simplification of IMP *)

Section IMPRewritingLemmas.

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


  Definition subst_zpexprs_cons
    : forall p r e es, subst_zpexprs p r (e::es) = subst_zpexpr p r e::subst_zpexprs p r es
    := subst_pexprs_cons Z.eqb.

  Definition subst_zpexprs_cat
    : forall p r es1 es2, subst_zpexprs p r (es1 ++ es2) =
                            subst_zpexprs p r es1 ++ subst_zpexprs p r es2
    := subst_pexprs_cat Z.eqb.


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
      rewrite -> !zpexpr_all0_cat in *. move: He => [He1 He2].
      rewrite split_cons /= in He2. move: He2 => [He2 He3]. rewrite zpexpr_all0_rcons.
      tauto.
    - move=> {vpre vps vq} vpre vps vq ve ves Hps p r Ha IH [vps' vq'] // Hrec Hs s He.
      rewrite -> zpexpr_all0_cat in He. rewrite split_cons in He.
      move: He => [He1 /= [He2 He3]]. simpl in Hs.
      rewrite (zpexpr_subst_vars_cache_assignment_valid ve.1 vq Ha He2).
      apply: (IH _ Hrec Hs). rewrite zpexpr_all0_cat.
      rewrite zpexpr_all0_rev. move: (zpexpr_is_assignment_equal Ha He2) => Hpr.
      rewrite -> zpexpr_all0_rev in He1. split.
      + move/(zpexpr_subst_vars_cache_all0 ve.1 _ Hpr): He1. by apply.
      + move/(zpexpr_subst_vars_cache_all0 ve.1 _ Hpr): He3. by apply.
  Qed.

  Lemma split_map_pair_zpexpr_with_vars (es : seq (PExpr Z)) :
    (split (map pair_zpexpr_with_vars es)).2 = es.
  Proof.
    elim: es => [| e es IH] //=. move: IH.
    dcase (split [seq pair_zpexpr_with_vars i | i <- es]) => [[vs es'] Hs].
    rewrite Hs /=. move=> ->. reflexivity.
  Qed.

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

End IMPRewritingLemmas.


(** ** Properties of the CAS answer validation *)

Section ValidatorLemmas.

  Local Open Scope Z_scope.

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

End ValidatorLemmas.
