open BinInt
open BinNums
open BinPos
open Bool
open Datatypes
open List0
open Options0
open Ring_polynom
open Seqs
open Var
open ZAriths
open Eqtype
open Seq
open Ssrbool
open Ssrnat

let __ = let rec f _ = Obj.repr f in Obj.repr f

type azbexp =
| Seq of SSA.SSA.eexp * SSA.SSA.eexp
| Seqmod of SSA.SSA.eexp * SSA.SSA.eexp * SSA.SSA.eexp list

(** val azbexp_eqn : azbexp -> azbexp -> bool **)

let azbexp_eqn e1 e2 =
  match e1 with
  | Seq (e3, e4) ->
    (match e2 with
     | Seq (e5, e6) ->
       eq_op (DSL.ebexp_eqType SSAVarOrder.coq_T)
         (Obj.magic (DSL.Eeq (e3, e4))) (Obj.magic (DSL.Eeq (e5, e6)))
     | Seqmod (_, _, _) -> false)
  | Seqmod (e3, e4, ms1) ->
    (match e2 with
     | Seq (_, _) -> false
     | Seqmod (e5, e6, ms2) ->
       eq_op (DSL.ebexp_eqType SSAVarOrder.coq_T)
         (Obj.magic (DSL.Eeqmod (e3, e4, ms1)))
         (Obj.magic (DSL.Eeqmod (e5, e6, ms2))))

(** val azbexp_eqP : azbexp -> azbexp -> reflect **)

let azbexp_eqP e1 e2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if azbexp_eqn e1 e2 then _evar_0_ __ else _evar_0_0 __

(** val azbexp_eqMixin : azbexp Equality.mixin_of **)

let azbexp_eqMixin =
  { Equality.op = azbexp_eqn; Equality.mixin_of__1 = azbexp_eqP }

(** val azbexp_eqType : Equality.coq_type **)

let azbexp_eqType =
  Obj.magic azbexp_eqMixin

type arep = { apremises : azbexp list; aconseq : azbexp }

(** val is_arep_trivial : arep -> bool **)

let is_arep_trivial s =
  in_mem (Obj.magic s.aconseq)
    (mem (seq_predType azbexp_eqType) (Obj.magic s.apremises))

(** val zexp_subst :
    SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp -> DSL.eexp **)

let rec zexp_subst p r e =
  if eq_op SSA.SSA.eexp_eqType (Obj.magic e) (Obj.magic p)
  then r
  else (match e with
        | DSL.Eunop (op0, e0) -> DSL.Eunop (op0, (zexp_subst p r e0))
        | DSL.Ebinop (op0, e1, e2) ->
          DSL.Ebinop (op0, (zexp_subst p r e1), (zexp_subst p r e2))
        | DSL.Epow (e0, n) -> DSL.Epow ((zexp_subst p r e0), n)
        | _ -> e)

(** val zexps_subst :
    SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp list -> DSL.eexp list **)

let zexps_subst p r es =
  map (zexp_subst p r) es

(** val azbexp_subst : SSA.SSA.eexp -> SSA.SSA.eexp -> azbexp -> azbexp **)

let azbexp_subst p r = function
| Seq (e1, e2) -> Seq ((zexp_subst p r e1), (zexp_subst p r e2))
| Seqmod (e1, e2, ms) ->
  Seqmod ((zexp_subst p r e1), (zexp_subst p r e2), (zexps_subst p r ms))

(** val subst_azbexps :
    SSA.SSA.eexp -> SSA.SSA.eexp -> azbexp list -> azbexp list **)

let subst_azbexps p r es =
  map (azbexp_subst p r) es

(** val single_variables : SSA.SSA.eexp -> SSAVS.t **)

let rec single_variables = function
| DSL.Evar v -> SSAVS.singleton v
| DSL.Econst _ -> SSAVS.empty
| DSL.Eunop (_, e0) -> single_variables e0
| DSL.Ebinop (op0, e1, e2) ->
  if (||) (eq_op DSL.ebinop_eqType (Obj.magic op0) (Obj.magic DSL.Eadd))
       (eq_op DSL.ebinop_eqType (Obj.magic op0) (Obj.magic DSL.Esub))
  then SSAVS.union (single_variables e1) (single_variables e2)
  else SSAVS.empty
| DSL.Epow (e0, _) -> single_variables e0

(** val num_occurrence : SSAVarOrder.t -> SSA.SSA.eexp -> int **)

let rec num_occurrence v = function
| DSL.Evar x -> if eq_op SSAVarOrder.coq_T x v then Pervasives.succ 0 else 0
| DSL.Econst _ -> 0
| DSL.Eunop (_, e0) -> num_occurrence v e0
| DSL.Ebinop (_, e1, e2) -> addn (num_occurrence v e1) (num_occurrence v e2)
| DSL.Epow (e0, _) -> num_occurrence v e0

(** val separate :
    Equality.sort -> SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp option **)

let rec separate v e pat =
  match e with
  | DSL.Evar x -> if eq_op SSAVarOrder.coq_T x v then Some pat else None
  | DSL.Eunop (_, e0) ->
    if SSAVS.mem v (SSA.SSA.vars_eexp e0)
    then separate v e0 (SSA.SSA.eneg pat)
    else None
  | DSL.Ebinop (op0, e1, e2) ->
    let in1 = SSAVS.mem v (SSA.SSA.vars_eexp e1) in
    let in2 = SSAVS.mem v (SSA.SSA.vars_eexp e2) in
    (match op0 with
     | DSL.Eadd ->
       if in1
       then if in2 then None else separate v e1 (SSA.SSA.esub pat e2)
       else if in2 then separate v e2 (SSA.SSA.esub pat e1) else None
     | DSL.Esub ->
       if in1
       then if in2 then None else separate v e1 (SSA.SSA.eadd pat e2)
       else if in2 then separate v e2 (SSA.SSA.esub e1 pat) else None
     | DSL.Emul -> None)
  | _ -> None

(** val get_rewrite_pattern :
    SSA.SSA.eexp -> (SSAVS.elt * SSA.SSA.eexp) option **)

let get_rewrite_pattern e =
  let candidates =
    SSAVS.filter (fun v ->
      eq_op nat_eqType (Obj.magic num_occurrence v e)
        (Obj.magic (Pervasives.succ 0))) (single_variables e)
  in
  if eq_op nat_eqType (Obj.magic SSAVS.cardinal candidates) (Obj.magic 0)
  then None
  else (match SSAVS.min_elt candidates with
        | Some v ->
          (match separate v e (SSA.SSA.econst Z.zero) with
           | Some pat -> Some (v, pat)
           | None -> None)
        | None -> None)

(** val is_assignment : azbexp -> (ssavar * SSA.SSA.eexp) option **)

let is_assignment = function
| Seq (e1, e2) ->
  (match e1 with
   | DSL.Evar v -> Some (v, e2)
   | DSL.Econst _ ->
     (match e2 with
      | DSL.Evar v -> Some (v, e1)
      | DSL.Ebinop (e0, e3, er) ->
        (match e0 with
         | DSL.Eadd ->
           (match e3 with
            | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
         | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
      | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
   | DSL.Eunop (_, _) ->
     (match e2 with
      | DSL.Evar v -> Some (v, e1)
      | DSL.Ebinop (e4, e5, er) ->
        (match e4 with
         | DSL.Eadd ->
           (match e5 with
            | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
         | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
      | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
   | DSL.Ebinop (e0, e3, el) ->
     (match e0 with
      | DSL.Eadd ->
        (match e3 with
         | DSL.Evar v ->
           (match e2 with
            | DSL.Evar v0 -> Some (v0, e1)
            | _ -> Some (v, (DSL.Ebinop (DSL.Esub, e2, el))))
         | DSL.Econst _ ->
           (match e2 with
            | DSL.Evar v -> Some (v, e1)
            | DSL.Ebinop (e4, e5, er) ->
              (match e4 with
               | DSL.Eadd ->
                 (match e5 with
                  | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
               | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
         | DSL.Eunop (_, _) ->
           (match e2 with
            | DSL.Evar v -> Some (v, e1)
            | DSL.Ebinop (e6, e7, er) ->
              (match e6 with
               | DSL.Eadd ->
                 (match e7 with
                  | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
               | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
         | DSL.Ebinop (_, _, _) ->
           (match e2 with
            | DSL.Evar v -> Some (v, e1)
            | DSL.Ebinop (e7, e8, er) ->
              (match e7 with
               | DSL.Eadd ->
                 (match e8 with
                  | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
               | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
         | DSL.Epow (_, _) ->
           (match e2 with
            | DSL.Evar v -> Some (v, e1)
            | DSL.Ebinop (e5, e6, er) ->
              (match e5 with
               | DSL.Eadd ->
                 (match e6 with
                  | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
               | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2)))
      | _ ->
        (match e2 with
         | DSL.Evar v -> Some (v, e1)
         | DSL.Ebinop (e4, e5, er) ->
           (match e4 with
            | DSL.Eadd ->
              (match e5 with
               | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
               | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
         | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2)))
   | DSL.Epow (_, _) ->
     (match e2 with
      | DSL.Evar v -> Some (v, e1)
      | DSL.Ebinop (e3, e4, er) ->
        (match e3 with
         | DSL.Eadd ->
           (match e4 with
            | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, e1, er)))
            | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
         | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2))
      | _ -> get_rewrite_pattern (SSA.SSA.esub e1 e2)))
| Seqmod (_, _, _) -> None

(** val simplify_arep_rec :
    azbexp list -> azbexp list -> azbexp -> azbexp list * azbexp **)

let rec simplify_arep_rec visited premises conseq0 =
  match premises with
  | [] -> ((rev visited), conseq0)
  | a :: l ->
    (match is_assignment a with
     | Some a0 ->
       let (a1, b) = a0 in
       simplify_arep_rec (subst_azbexps (SSA.SSA.evar a1) b visited)
         (subst_azbexps (SSA.SSA.evar a1) b l)
         (azbexp_subst (SSA.SSA.evar a1) b conseq0)
     | None -> simplify_arep_rec (a :: visited) l conseq0)

(** val simplify_arep : arep -> arep **)

let simplify_arep s =
  let (ps, q) = simplify_arep_rec [] s.apremises s.aconseq in
  { apremises = ps; aconseq = q }

(** val azbexp_subst_vars_cache :
    ssavar -> SSA.SSA.eexp -> SSAVS.t -> (SSAVS.t * azbexp) ->
    SSAVS.t * azbexp **)

let azbexp_subst_vars_cache p r vspr ve =
  let vs = fst ve in
  let e = snd ve in
  if SSAVS.mem p vs
  then ((SSAVS.remove p (SSAVS.union vs vspr)),
         (azbexp_subst (SSA.SSA.evar p) r e))
  else ve

(** val subst_azbexps_vars_cache :
    ssavar -> SSA.SSA.eexp -> SSAVS.t -> (SSAVS.t * azbexp) list ->
    (SSAVS.t * azbexp) list **)

let subst_azbexps_vars_cache p r vspr ves =
  map (azbexp_subst_vars_cache p r vspr) ves

(** val simplify_arep_vars_cache_rec :
    (SSAVS.t * azbexp) list -> (SSAVS.t * azbexp) list -> (SSAVS.t * azbexp)
    -> (SSAVS.t * azbexp) list * (SSAVS.t * azbexp) **)

let rec simplify_arep_vars_cache_rec visited premises conseq0 =
  match premises with
  | [] -> ((rev visited), conseq0)
  | a :: l ->
    (match is_assignment (snd a) with
     | Some a0 ->
       let (a1, b) = a0 in
       simplify_arep_vars_cache_rec
         (subst_azbexps_vars_cache a1 b (fst a) visited)
         (subst_azbexps_vars_cache a1 b (fst a) l)
         (azbexp_subst_vars_cache a1 b (fst a) conseq0)
     | None -> simplify_arep_vars_cache_rec (a :: visited) l conseq0)

(** val vars_azbexp : azbexp -> SSAVS.t **)

let vars_azbexp = function
| Seq (e1, e2) -> SSAVS.union (SSA.SSA.vars_eexp e1) (SSA.SSA.vars_eexp e2)
| Seqmod (e1, e2, ms) ->
  SSAVS.union (SSAVS.union (SSA.SSA.vars_eexp e1) (SSA.SSA.vars_eexp e2))
    (SSA.SSA.vars_eexps ms)

(** val pair_with_vars : azbexp -> SSAVS.t * azbexp **)

let pair_with_vars e =
  ((vars_azbexp e), e)

(** val simplify_arep_vars_cache : arep -> arep **)

let simplify_arep_vars_cache s =
  let vs_ps = map pair_with_vars s.apremises in
  let vs_q = pair_with_vars s.aconseq in
  let (vs_ps', vs_q') = simplify_arep_vars_cache_rec [] vs_ps vs_q in
  { apremises = (snd (split vs_ps')); aconseq = (snd vs_q') }

(** val split_zbexp : SSA.SSA.ebexp -> azbexp list **)

let rec split_zbexp = function
| DSL.Etrue -> []
| DSL.Eeq (e1, e2) -> (Seq (e1, e2)) :: []
| DSL.Eeqmod (e1, e2, ms) -> (Seqmod (e1, e2, ms)) :: []
| DSL.Eand (e1, e2) -> cat (split_zbexp e1) (split_zbexp e2)

(** val areps_of_rep_full : ZSSA.ZSSA.rep -> arep list **)

let areps_of_rep_full s =
  let premises = split_zbexp s.ZSSA.ZSSA.premise in
  let conseqs = split_zbexp s.ZSSA.ZSSA.conseq in
  map (fun conseq0 -> { apremises = premises; aconseq = conseq0 }) conseqs

(** val areps_of_rep : ZSSA.ZSSA.rep -> arep list **)

let areps_of_rep s =
  let areps = areps_of_rep_full s in
  filter (fun s0 -> negb (is_arep_trivial s0)) areps

(** val areps_of_rep_simplified : options -> ZSSA.ZSSA.rep -> arep list **)

let areps_of_rep_simplified o s =
  if o.vars_cache_in_rewrite_assignments
  then map simplify_arep_vars_cache (areps_of_rep s)
  else map simplify_arep (areps_of_rep s)

(** val coq_Znorm_subst : coq_Z coq_PExpr -> coq_Z coq_Pol **)

let coq_Znorm_subst =
  norm_subst Z0 (Zpos Coq_xH) Z.add Z.mul Z.sub Z.opp Z.eqb Z.quotrem 0 []

(** val coq_ZPeq : coq_Z coq_Pol -> coq_Z coq_Pol -> bool **)

let coq_ZPeq =
  coq_Peq Z.eqb

(** val peadds : 'a1 coq_PExpr list -> 'a1 coq_PExpr **)

let peadds es =
  foldl (fun x x0 -> PEadd (x, x0)) PEO es

(** val pemuls :
    'a1 coq_PExpr list -> 'a1 coq_PExpr list -> 'a1 coq_PExpr list **)

let pemuls es1 es2 =
  mapr (fun pat -> let (x, y) = pat in PEmul (x, y)) (zipr es1 es2)

(** val zpexpr_is_zero : coq_Z coq_PExpr -> bool **)

let zpexpr_is_zero = function
| PEO -> true
| PEc n -> eq_op coq_Z_eqType (Obj.magic n) (Obj.magic Z0)
| _ -> false

(** val init_pos : positive **)

let init_pos =
  Coq_xH

(** val init_vm : positive SSAVM.t **)

let init_vm =
  SSAVM.empty

(** val zpexpr_of_var :
    positive -> positive SSAVM.t -> ssavar -> (positive * positive
    SSAVM.t) * coq_Z coq_PExpr **)

let zpexpr_of_var g t0 v =
  match SSAVM.find v t0 with
  | Some r -> ((g, t0), (PEX r))
  | None -> (((Pos.add g Coq_xH), (SSAVM.add v g t0)), (PEX g))

(** val zpexpr_of_eunop : DSL.eunop -> coq_Z coq_PExpr -> coq_Z coq_PExpr **)

let zpexpr_of_eunop _ x =
  PEopp x

(** val zpexpr_of_ebinop :
    DSL.ebinop -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr **)

let zpexpr_of_ebinop op0 x x0 =
  match op0 with
  | DSL.Eadd -> PEadd (x, x0)
  | DSL.Esub -> PEsub (x, x0)
  | DSL.Emul -> PEmul (x, x0)

(** val zpexpr_of_zexp :
    positive -> positive SSAVM.t -> SSA.SSA.eexp -> (positive * positive
    SSAVM.t) * coq_Z coq_PExpr **)

let rec zpexpr_of_zexp g t0 = function
| DSL.Evar v -> zpexpr_of_var g t0 v
| DSL.Econst n -> ((g, t0), (PEc n))
| DSL.Eunop (op0, e0) ->
  let (p, e') = zpexpr_of_zexp g t0 e0 in (p, (zpexpr_of_eunop op0 e'))
| DSL.Ebinop (op0, e1, e2) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in (p0, (zpexpr_of_ebinop op0 e3 e4))
| DSL.Epow (e0, n) ->
  let (p, e') = zpexpr_of_zexp g t0 e0 in (p, (PEpow (e', n)))

(** val zpexprs_of_zexps :
    positive -> positive SSAVM.t -> SSA.SSA.eexp list -> (positive * positive
    SSAVM.t) * coq_Z coq_PExpr list **)

let rec zpexprs_of_zexps g t0 = function
| [] -> ((g, t0), [])
| hd :: tl ->
  let (p, pe_hd) = zpexpr_of_zexp g t0 hd in
  let (g_hd, t_hd) = p in
  let (p0, pe_tl) = zpexprs_of_zexps g_hd t_hd tl in (p0, (pe_hd :: pe_tl))

(** val pvars : positive -> int -> coq_Z coq_PExpr list **)

let rec pvars g n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> (PEX g) :: (pvars (Pos.add g Coq_xH) m))
    n

(** val zpexpr_of_premise :
    positive -> positive SSAVM.t -> azbexp -> (positive * positive
    SSAVM.t) * coq_Z coq_PExpr **)

let zpexpr_of_premise g t0 = function
| Seq (e1, e2) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in (p0, (PEsub (e3, e4)))
| Seqmod (e1, e2, ms) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in
  let (g2, t2) = p0 in
  let (p1, pms) = zpexprs_of_zexps g2 t2 ms in
  let (gms, tms) = p1 in
  let pks = pvars gms (size ms) in
  let g' =
    if eq_op nat_eqType (Obj.magic size ms) (Obj.magic 0)
    then gms
    else Pos.add gms (Pos.of_nat (size ms))
  in
  ((g', tms), (PEsub ((PEsub (e3, e4)), (peadds (pemuls pks pms)))))

(** val zpexprs_of_premises :
    positive -> positive SSAVM.t -> azbexp list -> (positive * positive
    SSAVM.t) * coq_Z coq_PExpr list **)

let rec zpexprs_of_premises g t0 = function
| [] -> ((g, t0), [])
| e :: es0 ->
  let (p, es_hd) = zpexpr_of_premise g t0 e in
  let (g_hd, t_hd) = p in
  let (p0, es_tl) = zpexprs_of_premises g_hd t_hd es0 in
  (p0, (es_hd :: es_tl))

(** val zpexpr_of_conseq :
    positive -> positive SSAVM.t -> azbexp -> ((positive * positive
    SSAVM.t) * coq_Z coq_PExpr) * coq_Z coq_PExpr list **)

let zpexpr_of_conseq g t0 = function
| Seq (e1, e2) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in
  ((p0, (PEsub (e3, e4))), (PEO :: []))
| Seqmod (e1, e2, ms) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in
  let (g2, t2) = p0 in
  let (p1, pms) = zpexprs_of_zexps g2 t2 ms in ((p1, (PEsub (e3, e4))), pms)

(** val imp_of_arep :
    arep -> (((positive * positive SSAVM.t) * coq_Z coq_PExpr list) * coq_Z
    coq_PExpr list) * coq_Z coq_PExpr **)

let imp_of_arep s =
  let (p, ps) = zpexprs_of_premises init_pos init_vm s.apremises in
  let (g_p, t_p) = p in
  let (p0, ms) = zpexpr_of_conseq g_p t_p s.aconseq in
  let (p1, q) = p0 in (((p1, ps), ms), q)

(** val zpexpr_eqb : coq_Z coq_PExpr -> coq_Z coq_PExpr -> bool **)

let zpexpr_eqb p1 p2 =
  coq_ZPeq (coq_Znorm_subst p1) (coq_Znorm_subst p2)

(** val validate_imp_answer :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z
    coq_PExpr list -> coq_Z coq_PExpr list -> bool **)

let validate_imp_answer ps ms q cps cms =
  (&&)
    ((&&) (eq_op nat_eqType (Obj.magic size ps) (Obj.magic size cps))
      (eq_op nat_eqType (Obj.magic size ms) (Obj.magic size cms)))
    (zpexpr_eqb q (PEadd ((peadds (pemuls cps ps)),
      (peadds (pemuls cms ms)))))
