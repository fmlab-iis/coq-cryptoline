open BinInt
open Bool
open DSLRaw
open Datatypes
open EqVar
open List0
open Options0
open Seqs
open String0
open Eqtype
open Seq
open Ssrbool
open Ssrnat

let __ = let rec f _ = Obj.repr f in Obj.repr f

type rep = { premise : SSALite.SSALite.ebexp; conseq : SSALite.SSALite.ebexp }

(** val string_of_zexp : eexp -> char list **)

let string_of_zexp =
  SSALite.SSALite.string_of_eexp

(** val string_of_zexps : char list -> eexp list -> char list **)

let string_of_zexps =
  SSALite.SSALite.string_of_eexps

type azbexp =
| Seq of SSALite.SSALite.eexp * SSALite.SSALite.eexp
| Seqmod of SSALite.SSALite.eexp * SSALite.SSALite.eexp
   * SSALite.SSALite.eexp list

(** val azbexp_eqn : azbexp -> azbexp -> bool **)

let azbexp_eqn e1 e2 =
  match e1 with
  | Seq (e3, e4) ->
    (match e2 with
     | Seq (e5, e6) ->
       eq_op (ebexp_eqType SSAVarOrder.coq_T) (Obj.magic (Eeq (e3, e4)))
         (Obj.magic (Eeq (e5, e6)))
     | Seqmod (_, _, _) -> false)
  | Seqmod (e3, e4, ms1) ->
    (match e2 with
     | Seq (_, _) -> false
     | Seqmod (e5, e6, ms2) ->
       eq_op (ebexp_eqType SSAVarOrder.coq_T)
         (Obj.magic (Eeqmod (e3, e4, ms1))) (Obj.magic (Eeqmod (e5, e6, ms2))))

(** val string_of_azbexp : azbexp -> char list **)

let string_of_azbexp = function
| Seq (e1, e2) ->
  append (string_of_zexp e1)
    (append (' '::('='::(' '::[]))) (string_of_zexp e2))
| Seqmod (e1, e2, ms) ->
  append (string_of_zexp e1)
    (append (' '::('='::(' '::[])))
      (append (string_of_zexp e2)
        (append ('('::('m'::('o'::('d'::(' '::('['::[]))))))
          (append (string_of_zexps (','::(' '::[])) ms) (']'::(')'::[]))))))

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
    SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp ->
    eexp **)

let rec zexp_subst p r e =
  if eq_op SSALite.SSALite.eexp_eqType (Obj.magic e) (Obj.magic p)
  then r
  else (match e with
        | Eunop (op0, e0) -> Eunop (op0, (zexp_subst p r e0))
        | Ebinop (op0, e1, e2) ->
          Ebinop (op0, (zexp_subst p r e1), (zexp_subst p r e2))
        | Epow (e0, n) -> Epow ((zexp_subst p r e0), n)
        | _ -> e)

(** val zexps_subst :
    SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp list
    -> eexp list **)

let zexps_subst p r es =
  tmap (zexp_subst p r) es

(** val azbexp_subst :
    SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> azbexp -> azbexp **)

let azbexp_subst p r = function
| Seq (e1, e2) -> Seq ((zexp_subst p r e1), (zexp_subst p r e2))
| Seqmod (e1, e2, ms) ->
  Seqmod ((zexp_subst p r e1), (zexp_subst p r e2), (zexps_subst p r ms))

(** val subst_azbexps :
    SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> azbexp list -> azbexp list **)

let subst_azbexps p r es =
  tmap (azbexp_subst p r) es

(** val single_variables : SSALite.SSALite.eexp -> SSAVS.t **)

let rec single_variables = function
| Evar v -> SSAVS.singleton v
| Eunop (_, e0) -> single_variables e0
| Ebinop (op0, e1, e2) ->
  if (||) (eq_op ebinop_eqType (Obj.magic op0) (Obj.magic Eadd))
       (eq_op ebinop_eqType (Obj.magic op0) (Obj.magic Esub))
  then SSAVS.union (single_variables e1) (single_variables e2)
  else SSAVS.empty
| _ -> SSAVS.empty

(** val num_occurrence : SSAVarOrder.t -> SSALite.SSALite.eexp -> int **)

let rec num_occurrence v = function
| Evar x -> if eq_op SSAVarOrder.coq_T x v then Pervasives.succ 0 else 0
| Econst _ -> 0
| Eunop (_, e0) -> num_occurrence v e0
| Ebinop (_, e1, e2) -> addn (num_occurrence v e1) (num_occurrence v e2)
| Epow (e0, _) -> num_occurrence v e0

(** val separate :
    Equality.sort -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp ->
    SSALite.SSALite.eexp option **)

let rec separate v e pat =
  match e with
  | Evar x -> if eq_op SSAVarOrder.coq_T x v then Some pat else None
  | Eunop (_, e0) ->
    if SSAVS.mem v (SSALite.SSALite.vars_eexp e0)
    then separate v e0 (SSALite.SSALite.eneg pat)
    else None
  | Ebinop (op0, e1, e2) ->
    let in1 = SSAVS.mem v (SSALite.SSALite.vars_eexp e1) in
    let in2 = SSAVS.mem v (SSALite.SSALite.vars_eexp e2) in
    (match op0 with
     | Eadd ->
       if in1
       then if in2 then None else separate v e1 (SSALite.SSALite.esub pat e2)
       else if in2 then separate v e2 (SSALite.SSALite.esub pat e1) else None
     | Esub ->
       if in1
       then if in2 then None else separate v e1 (SSALite.SSALite.eadd pat e2)
       else if in2 then separate v e2 (SSALite.SSALite.esub e1 pat) else None
     | Emul -> None)
  | _ -> None

(** val get_rewrite_pattern :
    SSALite.SSALite.eexp -> (SSAVS.elt * SSALite.SSALite.eexp) option **)

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
          (match separate v e (SSALite.SSALite.econst Z.zero) with
           | Some pat -> Some (v, pat)
           | None -> None)
        | None -> None)

(** val is_assignment : azbexp -> (ssavar * SSALite.SSALite.eexp) option **)

let is_assignment = function
| Seq (e1, e2) ->
  (match e1 with
   | Evar v -> Some (v, e2)
   | Econst _ ->
     (match e2 with
      | Evar v -> Some (v, e1)
      | Ebinop (e0, e3, er) ->
        (match e0 with
         | Eadd ->
           (match e3 with
            | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
         | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
      | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
   | Eunop (_, _) ->
     (match e2 with
      | Evar v -> Some (v, e1)
      | Ebinop (e4, e5, er) ->
        (match e4 with
         | Eadd ->
           (match e5 with
            | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
         | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
      | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
   | Ebinop (e0, e3, el) ->
     (match e0 with
      | Eadd ->
        (match e3 with
         | Evar v ->
           (match e2 with
            | Evar v0 -> Some (v0, e1)
            | _ -> Some (v, (Ebinop (Esub, e2, el))))
         | Econst _ ->
           (match e2 with
            | Evar v -> Some (v, e1)
            | Ebinop (e4, e5, er) ->
              (match e4 with
               | Eadd ->
                 (match e5 with
                  | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
               | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
         | Eunop (_, _) ->
           (match e2 with
            | Evar v -> Some (v, e1)
            | Ebinop (e6, e7, er) ->
              (match e6 with
               | Eadd ->
                 (match e7 with
                  | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
               | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
         | Ebinop (_, _, _) ->
           (match e2 with
            | Evar v -> Some (v, e1)
            | Ebinop (e7, e8, er) ->
              (match e7 with
               | Eadd ->
                 (match e8 with
                  | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
               | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
         | Epow (_, _) ->
           (match e2 with
            | Evar v -> Some (v, e1)
            | Ebinop (e5, e6, er) ->
              (match e5 with
               | Eadd ->
                 (match e6 with
                  | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
                  | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
               | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2)))
      | _ ->
        (match e2 with
         | Evar v -> Some (v, e1)
         | Ebinop (e4, e5, er) ->
           (match e4 with
            | Eadd ->
              (match e5 with
               | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
               | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
         | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2)))
   | Epow (_, _) ->
     (match e2 with
      | Evar v -> Some (v, e1)
      | Ebinop (e3, e4, er) ->
        (match e3 with
         | Eadd ->
           (match e4 with
            | Evar v -> Some (v, (Ebinop (Esub, e1, er)))
            | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
         | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2))
      | _ -> get_rewrite_pattern (SSALite.SSALite.esub e1 e2)))
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
       simplify_arep_rec (subst_azbexps (SSALite.SSALite.evar a1) b visited)
         (subst_azbexps (SSALite.SSALite.evar a1) b l)
         (azbexp_subst (SSALite.SSALite.evar a1) b conseq0)
     | None -> simplify_arep_rec (a :: visited) l conseq0)

(** val simplify_arep : arep -> arep **)

let simplify_arep s =
  let (ps, q) = simplify_arep_rec [] s.apremises s.aconseq in
  { apremises = ps; aconseq = q }

(** val azbexp_subst_vars_cache :
    ssavar -> SSALite.SSALite.eexp -> SSAVS.t -> (SSAVS.t * azbexp) ->
    SSAVS.t * azbexp **)

let azbexp_subst_vars_cache p r vspr ve =
  let vs = fst ve in
  let e = snd ve in
  if SSAVS.mem p vs
  then ((SSAVS.remove p (SSAVS.union vs vspr)),
         (azbexp_subst (SSALite.SSALite.evar p) r e))
  else ve

(** val subst_azbexps_vars_cache :
    ssavar -> SSALite.SSALite.eexp -> SSAVS.t -> (SSAVS.t * azbexp) list ->
    (SSAVS.t * azbexp) list **)

let subst_azbexps_vars_cache p r vspr ves =
  tmap (azbexp_subst_vars_cache p r vspr) ves

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
| Seq (e1, e2) ->
  SSAVS.union (SSALite.SSALite.vars_eexp e1) (SSALite.SSALite.vars_eexp e2)
| Seqmod (e1, e2, ms) ->
  SSAVS.union
    (SSAVS.union (SSALite.SSALite.vars_eexp e1)
      (SSALite.SSALite.vars_eexp e2)) (SSALite.SSALite.vars_eexps ms)

(** val pair_azbexp_with_vars : azbexp -> SSAVS.t * azbexp **)

let pair_azbexp_with_vars e =
  ((vars_azbexp e), e)

(** val simplify_arep_vars_cache : arep -> arep **)

let simplify_arep_vars_cache s =
  let vs_ps = tmap pair_azbexp_with_vars s.apremises in
  let vs_q = pair_azbexp_with_vars s.aconseq in
  let (vs_ps', vs_q') = simplify_arep_vars_cache_rec [] vs_ps vs_q in
  { apremises = (snd (split vs_ps')); aconseq = (snd vs_q') }

(** val split_zbexp : SSALite.SSALite.ebexp -> azbexp list **)

let rec split_zbexp = function
| Etrue -> []
| Eeq (e1, e2) -> (Seq (e1, e2)) :: []
| Eeqmod (e1, e2, ms) -> (Seqmod (e1, e2, ms)) :: []
| Eand (e1, e2) -> cat (split_zbexp e1) (split_zbexp e2)

(** val areps_of_rep_full : rep -> arep list **)

let areps_of_rep_full s =
  let premises = split_zbexp s.premise in
  let conseqs = split_zbexp s.conseq in
  tmap (fun conseq0 -> { apremises = premises; aconseq = conseq0 }) conseqs

(** val areps_of_rep : rep -> arep list **)

let areps_of_rep s =
  let areps = areps_of_rep_full s in
  List0.filter (fun s0 -> negb (is_arep_trivial s0)) areps

(** val areps_of_rep_simplified : options -> rep -> arep list **)

let areps_of_rep_simplified o s =
  if o.vars_cache_in_rewrite_assignments
  then tmap simplify_arep_vars_cache (areps_of_rep s)
  else tmap simplify_arep (areps_of_rep s)
