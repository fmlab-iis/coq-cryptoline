open BinInt
open BinNums
open BinPos
open Datatypes
open List0
open Options0
open Ring_polynom
open Seqs
open Var
open ZAriths
open Eqtype
open Seq
open Ssrnat

type azbexp =
| Seq of SSA.SSA.eexp * SSA.SSA.eexp
| Seqmod of SSA.SSA.eexp * SSA.SSA.eexp * SSA.SSA.eexp

type arep = { apremises : azbexp list; aconseq : azbexp }

(** val zexp_subst :
    SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp -> DSL.eexp **)

let rec zexp_subst p r e =
  if eq_op SSA.SSA.eexp_eqType (Obj.magic e) (Obj.magic p)
  then r
  else (match e with
        | DSL.Eunop (op, e0) -> DSL.Eunop (op, (zexp_subst p r e0))
        | DSL.Ebinop (op, e1, e2) ->
          DSL.Ebinop (op, (zexp_subst p r e1), (zexp_subst p r e2))
        | _ -> e)

(** val azbexp_subst : SSA.SSA.eexp -> SSA.SSA.eexp -> azbexp -> azbexp **)

let azbexp_subst p r = function
| Seq (e1, e2) -> Seq ((zexp_subst p r e1), (zexp_subst p r e2))
| Seqmod (e1, e2, e3) ->
  Seqmod ((zexp_subst p r e1), (zexp_subst p r e2), (zexp_subst p r e3))

(** val subst_azbexps :
    SSA.SSA.eexp -> SSA.SSA.eexp -> azbexp list -> azbexp list **)

let subst_azbexps p r es =
  map (azbexp_subst p r) es

(** val is_assignment : azbexp -> (ssavar * SSA.SSA.eexp) option **)

let is_assignment = function
| Seq (el, er) ->
  (match el with
   | DSL.Evar v -> Some (v, er)
   | DSL.Econst _ ->
     (match er with
      | DSL.Evar v -> Some (v, el)
      | DSL.Ebinop (e0, e1, er0) ->
        (match e0 with
         | DSL.Eadd ->
           (match e1 with
            | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, el, er0)))
            | _ -> None)
         | _ -> None)
      | _ -> None)
   | DSL.Eunop (_, _) ->
     (match er with
      | DSL.Evar v -> Some (v, el)
      | DSL.Ebinop (e2, e3, er0) ->
        (match e2 with
         | DSL.Eadd ->
           (match e3 with
            | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, el, er0)))
            | _ -> None)
         | _ -> None)
      | _ -> None)
   | DSL.Ebinop (e0, e1, el0) ->
     (match e0 with
      | DSL.Eadd ->
        (match e1 with
         | DSL.Evar v ->
           (match er with
            | DSL.Evar v0 -> Some (v0, el)
            | _ -> Some (v, (DSL.Ebinop (DSL.Esub, er, el0))))
         | DSL.Econst _ ->
           (match er with
            | DSL.Evar v -> Some (v, el)
            | DSL.Ebinop (e2, e3, er0) ->
              (match e2 with
               | DSL.Eadd ->
                 (match e3 with
                  | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, el, er0)))
                  | _ -> None)
               | _ -> None)
            | _ -> None)
         | DSL.Eunop (_, _) ->
           (match er with
            | DSL.Evar v -> Some (v, el)
            | DSL.Ebinop (e4, e5, er0) ->
              (match e4 with
               | DSL.Eadd ->
                 (match e5 with
                  | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, el, er0)))
                  | _ -> None)
               | _ -> None)
            | _ -> None)
         | DSL.Ebinop (_, _, _) ->
           (match er with
            | DSL.Evar v -> Some (v, el)
            | DSL.Ebinop (e5, e6, er0) ->
              (match e5 with
               | DSL.Eadd ->
                 (match e6 with
                  | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, el, er0)))
                  | _ -> None)
               | _ -> None)
            | _ -> None))
      | _ ->
        (match er with
         | DSL.Evar v -> Some (v, el)
         | DSL.Ebinop (e2, e3, er0) ->
           (match e2 with
            | DSL.Eadd ->
              (match e3 with
               | DSL.Evar v -> Some (v, (DSL.Ebinop (DSL.Esub, el, er0)))
               | _ -> None)
            | _ -> None)
         | _ -> None)))
| Seqmod (_, _, _) -> None

(** val simplify_arep_rec :
    azbexp list -> azbexp list -> azbexp -> azbexp list * azbexp **)

let rec simplify_arep_rec visited premises conseq0 =
  match premises with
  | [] -> ((rev visited), conseq0)
  | e :: es ->
    (match is_assignment e with
     | Some p0 ->
       let (p, r) = p0 in
       simplify_arep_rec (subst_azbexps (SSA.SSA.evar p) r visited)
         (subst_azbexps (SSA.SSA.evar p) r es)
         (azbexp_subst (SSA.SSA.evar p) r conseq0)
     | None -> simplify_arep_rec (e :: visited) es conseq0)

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
  | ve :: ves ->
    (match is_assignment (snd ve) with
     | Some p0 ->
       let (p, r) = p0 in
       simplify_arep_vars_cache_rec
         (subst_azbexps_vars_cache p r (fst ve) visited)
         (subst_azbexps_vars_cache p r (fst ve) ves)
         (azbexp_subst_vars_cache p r (fst ve) conseq0)
     | None -> simplify_arep_vars_cache_rec (ve :: visited) ves conseq0)

(** val vars_azbexp : azbexp -> SSAVS.t **)

let vars_azbexp = function
| Seq (e1, e2) -> SSAVS.union (SSA.SSA.vars_eexp e1) (SSA.SSA.vars_eexp e2)
| Seqmod (e1, e2, e3) ->
  SSAVS.union (SSAVS.union (SSA.SSA.vars_eexp e1) (SSA.SSA.vars_eexp e2))
    (SSA.SSA.vars_eexp e3)

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
| DSL.Eeqmod (e1, e2, p) -> (Seqmod (e1, e2, p)) :: []
| DSL.Eand (e1, e2) -> cat (split_zbexp e1) (split_zbexp e2)

(** val areps_of_rep : ZSSA.ZSSA.rep -> arep list **)

let areps_of_rep s =
  let premises = split_zbexp s.ZSSA.ZSSA.premise in
  let conseqs = split_zbexp s.ZSSA.ZSSA.conseq in
  map (fun conseq0 -> { apremises = premises; aconseq = conseq0 }) conseqs

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

let zpexpr_of_ebinop op x x0 =
  match op with
  | DSL.Eadd -> PEadd (x, x0)
  | DSL.Esub -> PEsub (x, x0)
  | DSL.Emul -> PEmul (x, x0)

(** val zpexpr_of_zexp :
    positive -> positive SSAVM.t -> SSA.SSA.eexp -> (positive * positive
    SSAVM.t) * coq_Z coq_PExpr **)

let rec zpexpr_of_zexp g t0 = function
| DSL.Evar v -> zpexpr_of_var g t0 v
| DSL.Econst n -> ((g, t0), (PEc n))
| DSL.Eunop (op, e0) ->
  let (p, e') = zpexpr_of_zexp g t0 e0 in (p, (zpexpr_of_eunop op e'))
| DSL.Ebinop (op, e1, e2) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in (p0, (zpexpr_of_ebinop op e3 e4))

(** val zpexpr_of_premise :
    positive -> positive SSAVM.t -> azbexp -> (positive * positive
    SSAVM.t) * coq_Z coq_PExpr **)

let zpexpr_of_premise g t0 = function
| Seq (e1, e2) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in (p0, (PEsub (e3, e4)))
| Seqmod (e1, e2, p) ->
  let (p0, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p0 in
  let (p1, e4) = zpexpr_of_zexp g1 t1 e2 in
  let (g2, t2) = p1 in
  let (p2, p3) = zpexpr_of_zexp g2 t2 p in
  let (gp, tp) = p2 in
  (((Pos.add gp Coq_xH), tp), (PEsub ((PEsub (e3, e4)), (PEmul ((PEX gp),
  p3)))))

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
    SSAVM.t) * coq_Z coq_PExpr) * coq_Z coq_PExpr **)

let zpexpr_of_conseq g t0 = function
| Seq (e1, e2) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in ((p0, (PEsub (e3, e4))), PEO)
| Seqmod (e1, e2, p) ->
  let (p0, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p0 in
  let (p1, e4) = zpexpr_of_zexp g1 t1 e2 in
  let (g2, t2) = p1 in
  let (p2, p3) = zpexpr_of_zexp g2 t2 p in ((p2, (PEsub (e3, e4))), p3)

(** val imp_of_arep :
    arep -> (((positive * positive SSAVM.t) * coq_Z coq_PExpr list) * coq_Z
    coq_PExpr) * coq_Z coq_PExpr **)

let imp_of_arep s =
  let (p, ps) = zpexprs_of_premises init_pos init_vm s.apremises in
  let (g_p, t_p) = p in
  let (p0, m) = zpexpr_of_conseq g_p t_p s.aconseq in
  let (p1, q) = p0 in (((p1, ps), m), q)

(** val zpexpr_eqb : coq_Z coq_PExpr -> coq_Z coq_PExpr -> bool **)

let zpexpr_eqb p1 p2 =
  coq_ZPeq (coq_Znorm_subst p1) (coq_Znorm_subst p2)

(** val combine_coefficients_tr :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr list **)

let combine_coefficients_tr cs ps =
  mapr (fun pat -> let (c, p) = pat in PEmul (c, p)) (zip cs ps)

(** val sum_polys_rec :
    coq_Z coq_PExpr -> coq_Z coq_PExpr list -> coq_Z coq_PExpr **)

let rec sum_polys_rec res = function
| [] -> res
| hd :: tl -> sum_polys_rec (PEadd (res, hd)) tl

(** val sum_polys_tr : coq_Z coq_PExpr list -> coq_Z coq_PExpr **)

let sum_polys_tr = function
| [] -> PEO
| hd :: tl -> sum_polys_rec hd tl

(** val validate_imp_answer_tr :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z
    coq_PExpr list -> coq_Z coq_PExpr -> bool **)

let validate_imp_answer_tr ps m q cs c =
  (&&) (eq_op nat_eqType (Obj.magic size ps) (Obj.magic size cs))
    (zpexpr_eqb q (PEadd ((sum_polys_tr (combine_coefficients_tr cs ps)),
      (PEmul (c, m)))))
