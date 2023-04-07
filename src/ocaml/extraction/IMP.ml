open BinInt
open BinNums
open BinPos
open BinaryString
open Bool
open DSLRaw
open Datatypes
open EqFSets
open EqVar
open Field_theory
open Int0
open List0
open REP
open Ring_polynom
open Seqs
open String0
open ZAriths
open ZPoly
open Eqtype
open Seq
open Ssrnat

type __ = Obj.t

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

(** val zpexpr_of_eunop : eunop -> coq_Z coq_PExpr -> coq_Z coq_PExpr **)

let zpexpr_of_eunop _ x =
  PEopp x

(** val zpexpr_of_ebinop :
    ebinop -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr **)

let zpexpr_of_ebinop op x x0 =
  match op with
  | Eadd -> PEadd (x, x0)
  | Esub -> PEsub (x, x0)
  | Emul -> PEmul (x, x0)

(** val zpexpr_of_zexp :
    positive -> positive SSAVM.t -> SSALite.SSALite.eexp ->
    (positive * positive SSAVM.t) * coq_Z coq_PExpr **)

let rec zpexpr_of_zexp g t0 = function
| Evar v -> zpexpr_of_var g t0 v
| Econst n -> ((g, t0), (PEc n))
| Eunop (op, e0) ->
  let (p, e') = zpexpr_of_zexp g t0 e0 in (p, (zpexpr_of_eunop op e'))
| Ebinop (op, e1, e2) ->
  let (p, e3) = zpexpr_of_zexp g t0 e1 in
  let (g1, t1) = p in
  let (p0, e4) = zpexpr_of_zexp g1 t1 e2 in (p0, (zpexpr_of_ebinop op e3 e4))
| Epow (e0, n) -> let (p, e') = zpexpr_of_zexp g t0 e0 in (p, (PEpow (e', n)))

(** val zpexprs_of_zexps :
    positive -> positive SSAVM.t -> SSALite.SSALite.eexp list ->
    (positive * positive SSAVM.t) * coq_Z coq_PExpr list **)

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

module PS = MakeTreeSet(EqOrder.PositiveOrder)

(** val vars_pexpr : 'a1 coq_PExpr -> PS.t **)

let rec vars_pexpr = function
| PEX j -> PS.singleton (Obj.magic j)
| PEadd (e1, e2) -> PS.union (vars_pexpr e1) (vars_pexpr e2)
| PEsub (e1, e2) -> PS.union (vars_pexpr e1) (vars_pexpr e2)
| PEmul (e1, e2) -> PS.union (vars_pexpr e1) (vars_pexpr e2)
| PEopp e0 -> vars_pexpr e0
| PEpow (e0, _) -> vars_pexpr e0
| _ -> PS.empty

(** val subst_pexpr :
    ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> 'a1 coq_PExpr
    -> 'a1 coq_PExpr **)

let rec subst_pexpr ceq p r e =
  if coq_PExpr_eq ceq e p
  then r
  else (match e with
        | PEadd (e1, e2) ->
          PEadd ((subst_pexpr ceq p r e1), (subst_pexpr ceq p r e2))
        | PEsub (e1, e2) ->
          PEsub ((subst_pexpr ceq p r e1), (subst_pexpr ceq p r e2))
        | PEmul (e1, e2) ->
          PEmul ((subst_pexpr ceq p r e1), (subst_pexpr ceq p r e2))
        | PEopp e0 -> PEopp (subst_pexpr ceq p r e0)
        | PEpow (e0, n) -> PEpow ((subst_pexpr ceq p r e0), n)
        | _ -> e)

(** val subst_pexprs :
    ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> 'a1 coq_PExpr
    list -> 'a1 coq_PExpr list **)

let subst_pexprs ceq p r es =
  tmap (subst_pexpr ceq p r) es

(** val pexpr_single_variables : 'a1 coq_PExpr -> PS.t **)

let rec pexpr_single_variables = function
| PEX j -> PS.singleton (Obj.magic j)
| PEadd (e1, e2) ->
  PS.union (pexpr_single_variables e1) (pexpr_single_variables e2)
| PEsub (e1, e2) ->
  PS.union (pexpr_single_variables e1) (pexpr_single_variables e2)
| PEopp e0 -> pexpr_single_variables e0
| _ -> PS.empty

(** val pexpr_num_occurrence : positive -> 'a1 coq_PExpr -> int **)

let rec pexpr_num_occurrence v = function
| PEX j ->
  if eq_op pos_eqType (Obj.magic j) (Obj.magic v)
  then Pervasives.succ 0
  else 0
| PEadd (e1, e2) ->
  addn (pexpr_num_occurrence v e1) (pexpr_num_occurrence v e2)
| PEsub (e1, e2) ->
  addn (pexpr_num_occurrence v e1) (pexpr_num_occurrence v e2)
| PEmul (e1, e2) ->
  addn (pexpr_num_occurrence v e1) (pexpr_num_occurrence v e2)
| PEopp e0 -> pexpr_num_occurrence v e0
| PEpow (e0, _) -> pexpr_num_occurrence v e0
| _ -> 0

(** val pexpr_separate :
    positive -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> 'a1 coq_PExpr option **)

let rec pexpr_separate v e pat =
  match e with
  | PEX j ->
    if eq_op pos_eqType (Obj.magic j) (Obj.magic v) then Some pat else None
  | PEadd (e1, e2) ->
    let in1 = PS.mem (Obj.magic v) (vars_pexpr e1) in
    let in2 = PS.mem (Obj.magic v) (vars_pexpr e2) in
    if in1
    then if in2 then None else pexpr_separate v e1 (PEsub (pat, e2))
    else if in2 then pexpr_separate v e2 (PEsub (pat, e1)) else None
  | PEsub (e1, e2) ->
    let in1 = PS.mem (Obj.magic v) (vars_pexpr e1) in
    let in2 = PS.mem (Obj.magic v) (vars_pexpr e2) in
    if in1
    then if in2 then None else pexpr_separate v e1 (PEadd (pat, e2))
    else if in2 then pexpr_separate v e2 (PEsub (e1, pat)) else None
  | PEopp e0 ->
    if PS.mem (Obj.magic v) (vars_pexpr e0)
    then pexpr_separate v e0 (PEopp pat)
    else None
  | _ -> None

(** val pexpr_get_rewrite_pattern :
    'a1 coq_PExpr -> (PS.elt * 'a1 coq_PExpr) option **)

let pexpr_get_rewrite_pattern e =
  let candidates =
    PS.filter (fun v ->
      eq_op nat_eqType (Obj.magic pexpr_num_occurrence v e)
        (Obj.magic (Pervasives.succ 0))) (pexpr_single_variables e)
  in
  if eq_op nat_eqType (Obj.magic PS.cardinal candidates) (Obj.magic 0)
  then None
  else (match PS.min_elt candidates with
        | Some v ->
          (match pexpr_separate (Obj.magic v) e PEO with
           | Some pat -> Some (v, pat)
           | None -> None)
        | None -> None)

(** val pexpr_is_assignment :
    'a1 coq_PExpr -> (positive * 'a1 coq_PExpr) option **)

let pexpr_is_assignment e = match e with
| PEX j -> Some (j, PEO)
| PEadd (e0, e1) ->
  (match e0 with
   | PEX j -> Some (j, (PEopp e1))
   | _ ->
     (match e1 with
      | PEX j -> Some (j, (PEopp e0))
      | _ -> Obj.magic pexpr_get_rewrite_pattern e))
| PEsub (e2, e3) ->
  (match e2 with
   | PEX j -> Some (j, e3)
   | PEadd (p, e1) ->
     (match p with
      | PEO ->
        (match e3 with
         | PEX j -> Some (j, e2)
         | PEadd (p0, e4) ->
           (match p0 with
            | PEX j -> Some (j, (PEsub (e2, e4)))
            | _ -> Obj.magic pexpr_get_rewrite_pattern e)
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | PEI ->
        (match e3 with
         | PEX j -> Some (j, e2)
         | PEadd (p0, e4) ->
           (match p0 with
            | PEX j -> Some (j, (PEsub (e2, e4)))
            | _ -> Obj.magic pexpr_get_rewrite_pattern e)
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | PEc _ ->
        (match e3 with
         | PEX j -> Some (j, e2)
         | PEadd (p0, e4) ->
           (match p0 with
            | PEX j -> Some (j, (PEsub (e2, e4)))
            | _ -> Obj.magic pexpr_get_rewrite_pattern e)
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | PEX j ->
        (match e3 with
         | PEX j0 -> Some (j0, e2)
         | _ -> Some (j, (PEsub (e3, e1))))
      | PEopp _ ->
        (match e3 with
         | PEX j -> Some (j, e2)
         | PEadd (p1, e4) ->
           (match p1 with
            | PEX j -> Some (j, (PEsub (e2, e4)))
            | _ -> Obj.magic pexpr_get_rewrite_pattern e)
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | PEpow (_, _) ->
        (match e3 with
         | PEX j -> Some (j, e2)
         | PEadd (p1, e4) ->
           (match p1 with
            | PEX j -> Some (j, (PEsub (e2, e4)))
            | _ -> Obj.magic pexpr_get_rewrite_pattern e)
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | _ ->
        (match e3 with
         | PEX j -> Some (j, e2)
         | PEadd (p2, e4) ->
           (match p2 with
            | PEX j -> Some (j, (PEsub (e2, e4)))
            | _ -> Obj.magic pexpr_get_rewrite_pattern e)
         | _ -> Obj.magic pexpr_get_rewrite_pattern e))
   | PEsub (_, _) ->
     (match e3 with
      | PEX j -> Some (j, e2)
      | PEadd (p1, e1) ->
        (match p1 with
         | PEX j -> Some (j, (PEsub (e2, e1)))
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | _ -> Obj.magic pexpr_get_rewrite_pattern e)
   | PEmul (_, _) ->
     (match e3 with
      | PEX j -> Some (j, e2)
      | PEadd (p1, e1) ->
        (match p1 with
         | PEX j -> Some (j, (PEsub (e2, e1)))
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | _ -> Obj.magic pexpr_get_rewrite_pattern e)
   | PEopp _ ->
     (match e3 with
      | PEX j -> Some (j, e2)
      | PEadd (p0, e1) ->
        (match p0 with
         | PEX j -> Some (j, (PEsub (e2, e1)))
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | _ -> Obj.magic pexpr_get_rewrite_pattern e)
   | PEpow (_, _) ->
     (match e3 with
      | PEX j -> Some (j, e2)
      | PEadd (p0, e1) ->
        (match p0 with
         | PEX j -> Some (j, (PEsub (e2, e1)))
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | _ -> Obj.magic pexpr_get_rewrite_pattern e)
   | _ ->
     (match e3 with
      | PEX j -> Some (j, e2)
      | PEadd (p, e1) ->
        (match p with
         | PEX j -> Some (j, (PEsub (e2, e1)))
         | _ -> Obj.magic pexpr_get_rewrite_pattern e)
      | _ -> Obj.magic pexpr_get_rewrite_pattern e))
| _ -> Obj.magic pexpr_get_rewrite_pattern e

(** val string_of_pexpr :
    char list -> char list -> ('a1 -> char list) -> 'a1 coq_PExpr -> char list **)

let string_of_pexpr string_of_zero string_of_identity string_of_const =
  let rec string_of_pexpr0 = function
  | PEO -> string_of_zero
  | PEI -> string_of_identity
  | PEc c -> string_of_const c
  | PEX j -> of_pos j
  | PEadd (e1, e2) ->
    append (string_of_pexpr' e1)
      (append (' '::('+'::(' '::[]))) (string_of_pexpr' e2))
  | PEsub (e1, e2) ->
    append (string_of_pexpr' e1)
      (append (' '::('-'::(' '::[]))) (string_of_pexpr' e2))
  | PEmul (e1, e2) ->
    append (string_of_pexpr' e1)
      (append (' '::('*'::(' '::[]))) (string_of_pexpr' e2))
  | PEopp e0 -> append ('-'::(' '::[])) (string_of_pexpr' e0)
  | PEpow (e0, n) ->
    append (string_of_pexpr' e0) (append (' '::('^'::(' '::[]))) (of_N n))
  and string_of_pexpr' = function
  | PEO -> string_of_zero
  | PEI -> string_of_identity
  | PEc c -> string_of_const c
  | PEX j -> of_pos j
  | PEadd (e1, e2) ->
    append ('('::[])
      (append (string_of_pexpr0 e1)
        (append (' '::('+'::(' '::[])))
          (append (string_of_pexpr0 e2) (')'::[]))))
  | PEsub (e1, e2) ->
    append ('('::[])
      (append (string_of_pexpr0 e1)
        (append (' '::('-'::(' '::[])))
          (append (string_of_pexpr0 e2) (')'::[]))))
  | PEmul (e1, e2) ->
    append ('('::[])
      (append (string_of_pexpr0 e1)
        (append (' '::('*'::(' '::[])))
          (append (string_of_pexpr0 e2) (')'::[]))))
  | PEopp e0 ->
    append ('('::('-'::(' '::[]))) (append (string_of_pexpr0 e0) (')'::[]))
  | PEpow (e0, n) ->
    append ('('::[])
      (append (string_of_pexpr0 e0)
        (append (' '::('^'::(' '::[]))) (append (of_N n) (')'::[]))))
  in string_of_pexpr0

(** val string_of_zpexpr : coq_Z coq_PExpr -> char list **)

let string_of_zpexpr =
  string_of_pexpr ('0'::[]) ('1'::[]) of_Z

(** val simplify_zpexpr : coq_Z coq_PExpr -> coq_Z coq_PExpr **)

let rec simplify_zpexpr e = match e with
| PEc c ->
  if eq_op coq_Z_eqType (Obj.magic c) (Obj.magic Z0)
  then PEO
  else if eq_op coq_Z_eqType (Obj.magic c) (Obj.magic (Zpos Coq_xH))
       then PEI
       else e
| PEadd (e1, e2) ->
  let e1' = simplify_zpexpr e1 in
  let e2' = simplify_zpexpr e2 in
  (match e1' with
   | PEO -> e2'
   | _ -> (match e2' with
           | PEO -> e1'
           | _ -> PEadd (e1', e2')))
| PEsub (e1, e2) ->
  let e1' = simplify_zpexpr e1 in
  let e2' = simplify_zpexpr e2 in
  (match e1' with
   | PEO -> (match e2' with
             | PEopp e2'' -> e2''
             | _ -> PEopp e2')
   | _ ->
     (match e2' with
      | PEO -> e1'
      | PEopp e2'' -> PEadd (e1', e2'')
      | _ -> PEsub (e1', e2')))
| PEmul (e1, e2) ->
  let e1' = simplify_zpexpr e1 in
  let e2' = simplify_zpexpr e2 in
  (match e1' with
   | PEO -> PEO
   | PEI -> e2'
   | _ -> (match e2' with
           | PEO -> PEO
           | PEI -> e1'
           | _ -> PEmul (e1', e2')))
| PEopp e0 ->
  let e' = simplify_zpexpr e0 in
  (match e' with
   | PEopp e'' -> e''
   | _ -> PEopp e')
| PEpow (e0, n) ->
  let e' = simplify_zpexpr e0 in
  if eq_op bin_nat_eqType (Obj.magic n) (Obj.magic N0)
  then PEI
  else if eq_op bin_nat_eqType (Obj.magic n) (Obj.magic (Npos Coq_xH))
       then e'
       else (match e' with
             | PEO -> PEO
             | PEI -> PEI
             | _ -> PEpow (e', n))
| _ -> e

(** val subst_zpexpr :
    coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr **)

let subst_zpexpr p r e =
  subst_pexpr Z.eqb p r e

(** val subst_zpexprs :
    coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr list -> coq_Z
    coq_PExpr list **)

let subst_zpexprs p r es =
  subst_pexprs Z.eqb p r es

(** val zpexpr_is_assignment :
    coq_Z coq_PExpr -> (positive * coq_Z coq_PExpr) option **)

let zpexpr_is_assignment e =
  match pexpr_is_assignment e with
  | Some p0 -> let (p, r) = p0 in Some (p, (simplify_zpexpr r))
  | None -> None

(** val simplify_generator_rec :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z
    coq_PExpr list * coq_Z coq_PExpr **)

let rec simplify_generator_rec visited ps q =
  match ps with
  | [] -> ((rev visited), q)
  | a :: l ->
    (match zpexpr_is_assignment a with
     | Some a0 ->
       let (a1, b) = a0 in
       simplify_generator_rec (subst_zpexprs (PEX a1) b visited)
         (subst_zpexprs (PEX a1) b l) (subst_zpexpr (PEX a1) b q)
     | None -> simplify_generator_rec (a :: visited) l q)

(** val simplify_generator :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr list * coq_Z
    coq_PExpr **)

let simplify_generator ps q =
  simplify_generator_rec [] (tmap simplify_zpexpr ps) (simplify_zpexpr q)

(** val subst_zpexpr_vars_cache :
    positive -> coq_Z coq_PExpr -> PS.t -> (PS.t * coq_Z coq_PExpr) ->
    PS.t * coq_Z coq_PExpr **)

let subst_zpexpr_vars_cache p r vspr ve =
  let vs = fst ve in
  let e = snd ve in
  if PS.mem (Obj.magic p) vs
  then ((PS.remove (Obj.magic p) (PS.union vs vspr)),
         (subst_zpexpr (PEX p) r e))
  else ve

(** val subst_zpexprs_vars_cache :
    positive -> coq_Z coq_PExpr -> PS.t -> (PS.t * coq_Z coq_PExpr) list ->
    (PS.t * coq_Z coq_PExpr) list **)

let subst_zpexprs_vars_cache p r vspr ves =
  tmap (subst_zpexpr_vars_cache p r vspr) ves

(** val simplify_generator_vars_cache_rec :
    (PS.t * coq_Z coq_PExpr) list -> (PS.t * coq_Z coq_PExpr) list ->
    (PS.t * coq_Z coq_PExpr) -> (PS.t * coq_Z coq_PExpr) list * (PS.t * coq_Z
    coq_PExpr) **)

let rec simplify_generator_vars_cache_rec visited ps q =
  match ps with
  | [] -> ((rev visited), q)
  | a :: l ->
    (match zpexpr_is_assignment (snd a) with
     | Some a0 ->
       let (a1, b) = a0 in
       simplify_generator_vars_cache_rec
         (subst_zpexprs_vars_cache a1 b (fst a) visited)
         (subst_zpexprs_vars_cache a1 b (fst a) l)
         (subst_zpexpr_vars_cache a1 b (fst a) q)
     | None -> simplify_generator_vars_cache_rec (a :: visited) l q)

(** val pair_zpexpr_with_vars : coq_Z coq_PExpr -> PS.t * coq_Z coq_PExpr **)

let pair_zpexpr_with_vars e =
  ((vars_pexpr e), e)

(** val simplify_generator_vars_cache :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr list * coq_Z
    coq_PExpr **)

let simplify_generator_vars_cache ps q =
  let vs_ps = tmap pair_zpexpr_with_vars (tmap simplify_zpexpr ps) in
  let vs_q = pair_zpexpr_with_vars (simplify_zpexpr q) in
  let (vs_ps', vs_q') = simplify_generator_vars_cache_rec [] vs_ps vs_q in
  ((snd (split vs_ps')), (snd vs_q'))

(** val validate_imp_answer :
    coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z
    coq_PExpr list -> coq_Z coq_PExpr list -> bool **)

let validate_imp_answer ps ms q cps cms =
  (&&)
    ((&&) (eq_op nat_eqType (Obj.magic size ps) (Obj.magic size cps))
      (eq_op nat_eqType (Obj.magic size ms) (Obj.magic size cms)))
    (zpexpr_eqb q (PEadd ((peadds (pemuls cps ps)),
      (peadds (pemuls cms ms)))))
