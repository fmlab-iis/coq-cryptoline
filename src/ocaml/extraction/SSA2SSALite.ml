open DSLRaw
open Datatypes
open Seqs
open Typ
open Var

(** val eexp_of_atom : SSA.SSA.atom -> SSA.SSA.eexp **)

let eexp_of_atom = function
| Avar v -> SSA.SSA.evar v
| Aconst (ty, n) -> SSA.SSA.econst (SSA.SSA.bv2z ty n)

(** val rexp_of_atom : SSA.SSA.atom -> SSA.SSA.rexp **)

let rexp_of_atom = function
| Avar v -> SSA.SSA.rvar v
| Aconst (ty, n) -> SSA.SSA.rconst (sizeof_typ ty) n

(** val subst_eexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.eexp -> SSA.SSA.eexp **)

let rec subst_eexp m e = match e with
| Evar v -> (match SSAVM.find v m with
             | Some a -> eexp_of_atom a
             | None -> e)
| Econst _ -> e
| Eunop (op, e0) -> SSA.SSA.eunary op (subst_eexp m e0)
| Ebinop (op, e1, e2) ->
  SSA.SSA.ebinary op (subst_eexp m e1) (subst_eexp m e2)
| Epow (e0, n) -> SSA.SSA.epow (subst_eexp m e0) n

(** val subst_rexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.rexp -> SSA.SSA.rexp **)

let rec subst_rexp m e = match e with
| Rvar v -> (match SSAVM.find v m with
             | Some a -> rexp_of_atom a
             | None -> e)
| Rconst (_, _) -> e
| Runop (w, op, e0) -> SSA.SSA.runary w op (subst_rexp m e0)
| Rbinop (w, op, e1, e2) ->
  SSA.SSA.rbinary w op (subst_rexp m e1) (subst_rexp m e2)
| Ruext (w, e0, i) -> SSA.SSA.ruext w (subst_rexp m e0) i
| Rsext (w, e0, i) -> SSA.SSA.rsext w (subst_rexp m e0) i

(** val subst_eexps :
    SSA.SSA.atom SSAVM.t -> SSA.SSA.eexp list -> SSA.SSA.eexp list **)

let subst_eexps m es =
  tmap (subst_eexp m) es

(** val subst_ebexp :
    SSA.SSA.atom SSAVM.t -> SSA.SSA.ebexp -> SSA.SSA.ebexp **)

let rec subst_ebexp m e = match e with
| Etrue -> e
| Eeq (e1, e2) -> Eeq ((subst_eexp m e1), (subst_eexp m e2))
| Eeqmod (e1, e2, ms) ->
  Eeqmod ((subst_eexp m e1), (subst_eexp m e2), (subst_eexps m ms))
| Eand (e1, e2) -> Eand ((subst_ebexp m e1), (subst_ebexp m e2))

(** val subst_rbexp :
    SSA.SSA.atom SSAVM.t -> SSA.SSA.rbexp -> SSA.SSA.rbexp **)

let rec subst_rbexp m e = match e with
| Rtrue -> e
| Req (w, e1, e2) -> Req (w, (subst_rexp m e1), (subst_rexp m e2))
| Rcmp (w, op, e1, e2) -> Rcmp (w, op, (subst_rexp m e1), (subst_rexp m e2))
| Rneg e0 -> Rneg (subst_rbexp m e0)
| Rand (e1, e2) -> Rand ((subst_rbexp m e1), (subst_rbexp m e2))
| Ror (e1, e2) -> Ror ((subst_rbexp m e1), (subst_rbexp m e2))

(** val subst_bexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.bexp -> SSA.SSA.bexp **)

let subst_bexp m e =
  ((subst_ebexp m (fst e)), (subst_rbexp m (snd e)))

(** val subst_atom : SSA.SSA.atom SSAVM.t -> SSA.SSA.atom -> SSA.SSA.atom **)

let subst_atom m a = match a with
| Avar v -> (match SSAVM.find v m with
             | Some a' -> a'
             | None -> a)
| Aconst (_, _) -> a

(** val subst_instr :
    SSA.SSA.atom SSAVM.t -> SSA.SSA.instr -> SSA.SSA.instr **)

let subst_instr m i = match i with
| SSA.SSA.Imov (v, a) -> SSA.SSA.Imov (v, (subst_atom m a))
| SSA.SSA.Ishl (v, a, n) -> SSA.SSA.Ishl (v, (subst_atom m a), n)
| SSA.SSA.Icshl (v1, v2, a1, a2, n) ->
  SSA.SSA.Icshl (v1, v2, (subst_atom m a1), (subst_atom m a2), n)
| SSA.SSA.Icmov (v, c, a1, a2) ->
  SSA.SSA.Icmov (v, c, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Inot (v, t0, a) -> SSA.SSA.Inot (v, t0, (subst_atom m a))
| SSA.SSA.Iadd (v, a1, a2) ->
  SSA.SSA.Iadd (v, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Iadds (c, v, a1, a2) ->
  SSA.SSA.Iadds (c, v, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Iadc (v, a1, a2, y) ->
  SSA.SSA.Iadc (v, (subst_atom m a1), (subst_atom m a2), y)
| SSA.SSA.Iadcs (c, v, a1, a2, y) ->
  SSA.SSA.Iadcs (c, v, (subst_atom m a1), (subst_atom m a2), y)
| SSA.SSA.Isub (v, a1, a2) ->
  SSA.SSA.Isub (v, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Isubc (c, v, a1, a2) ->
  SSA.SSA.Isubc (c, v, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Isubb (c, v, a1, a2) ->
  SSA.SSA.Isubb (c, v, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Isbc (v, a1, a2, y) ->
  SSA.SSA.Isbc (v, (subst_atom m a1), (subst_atom m a2), y)
| SSA.SSA.Isbcs (c, v, a1, a2, y) ->
  SSA.SSA.Isbcs (c, v, (subst_atom m a1), (subst_atom m a2), y)
| SSA.SSA.Isbb (v, a1, a2, y) ->
  SSA.SSA.Isbb (v, (subst_atom m a1), (subst_atom m a2), y)
| SSA.SSA.Isbbs (c, v, a1, a2, y) ->
  SSA.SSA.Isbbs (c, v, (subst_atom m a1), (subst_atom m a2), y)
| SSA.SSA.Imul (v, a1, a2) ->
  SSA.SSA.Imul (v, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Imull (vh, vl, a1, a2) ->
  SSA.SSA.Imull (vh, vl, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Imulj (v, a1, a2) ->
  SSA.SSA.Imulj (v, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Isplit (vh, vl, a, n) ->
  SSA.SSA.Isplit (vh, vl, (subst_atom m a), n)
| SSA.SSA.Iand (v, t0, a1, a2) ->
  SSA.SSA.Iand (v, t0, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Ior (v, t0, a1, a2) ->
  SSA.SSA.Ior (v, t0, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Ixor (v, t0, a1, a2) ->
  SSA.SSA.Ixor (v, t0, (subst_atom m a1), (subst_atom m a2))
| SSA.SSA.Icast (v, t0, a) -> SSA.SSA.Icast (v, t0, (subst_atom m a))
| SSA.SSA.Ivpc (v, t0, a) -> SSA.SSA.Ivpc (v, t0, (subst_atom m a))
| SSA.SSA.Ijoin (v, ah, al) ->
  SSA.SSA.Ijoin (v, (subst_atom m ah), (subst_atom m al))
| SSA.SSA.Icut e -> SSA.SSA.Icut (subst_bexp m e)
| SSA.SSA.Iassert e -> SSA.SSA.Iassert (subst_bexp m e)
| SSA.SSA.Iassume e -> SSA.SSA.Iassume (subst_bexp m e)
| _ -> i

(** val subst_program :
    SSA.SSA.atom SSAVM.t -> SSA.SSA.program -> SSA.SSA.program **)

let subst_program m p =
  tmap (subst_instr m) p

(** val subst_spec : SSA.SSA.atom SSAVM.t -> SSA.SSA.spec -> SSA.SSA.spec **)

let subst_spec m s =
  { SSA.SSA.sinputs = (SSA.SSA.sinputs s); SSA.SSA.spre =
    (subst_bexp m (SSA.SSA.spre s)); SSA.SSA.sprog =
    (subst_program m (SSA.SSA.sprog s)); SSA.SSA.spost =
    (subst_bexp m (SSA.SSA.spost s)) }

(** val subst_map_instr :
    SSA.SSA.atom SSAVM.t -> SSA.SSA.instr -> SSA.SSA.atom SSAVM.t **)

let subst_map_instr m = function
| SSA.SSA.Imov (v, a) ->
  (match a with
   | Avar u ->
     (match SSAVM.find u m with
      | Some ua -> SSAVM.add v ua m
      | None -> SSAVM.add v a m)
   | Aconst (_, _) -> SSAVM.add v a m)
| _ -> m

(** val subst_map_program_rec :
    SSA.SSA.atom SSAVM.t -> SSA.SSA.program -> SSA.SSA.atom SSAVM.t **)

let rec subst_map_program_rec m = function
| [] -> m
| i :: p0 -> subst_map_program_rec (subst_map_instr m i) p0

(** val subst_map_program : SSA.SSA.program -> SSA.SSA.atom SSAVM.t **)

let subst_map_program p =
  subst_map_program_rec SSAVM.empty p

(** val subst_map_spec : SSA.SSA.spec -> SSA.SSA.atom SSAVM.t **)

let subst_map_spec s =
  subst_map_program (SSA.SSA.sprog s)

(** val rewrite_mov : SSA.SSA.spec -> SSA.SSA.spec **)

let rewrite_mov s =
  subst_spec (subst_map_spec s) s

(** val ssa2lite_instr : SSA.SSA.instr -> SSALite.SSALite.instr **)

let ssa2lite_instr = function
| SSA.SSA.Imov (v, a) -> SSALite.SSALite.Imov (v, a)
| SSA.SSA.Ishl (v, a, n) -> SSALite.SSALite.Ishl (v, a, n)
| SSA.SSA.Icshl (v1, v2, a1, a2, n) ->
  SSALite.SSALite.Icshl (v1, v2, a1, a2, n)
| SSA.SSA.Inondet (v, t0) -> SSALite.SSALite.Inondet (v, t0)
| SSA.SSA.Icmov (v, c, a1, a2) -> SSALite.SSALite.Icmov (v, c, a1, a2)
| SSA.SSA.Inot (v, t0, a) -> SSALite.SSALite.Inot (v, t0, a)
| SSA.SSA.Iadd (v, a1, a2) -> SSALite.SSALite.Iadd (v, a1, a2)
| SSA.SSA.Iadds (c, v, a1, a2) -> SSALite.SSALite.Iadds (c, v, a1, a2)
| SSA.SSA.Iadc (v, a1, a2, y) -> SSALite.SSALite.Iadc (v, a1, a2, y)
| SSA.SSA.Iadcs (c, v, a1, a2, y) -> SSALite.SSALite.Iadcs (c, v, a1, a2, y)
| SSA.SSA.Isub (v, a1, a2) -> SSALite.SSALite.Isub (v, a1, a2)
| SSA.SSA.Isubc (c, v, a1, a2) -> SSALite.SSALite.Isubc (c, v, a1, a2)
| SSA.SSA.Isubb (c, v, a1, a2) -> SSALite.SSALite.Isubb (c, v, a1, a2)
| SSA.SSA.Isbc (v, a1, a2, y) -> SSALite.SSALite.Isbc (v, a1, a2, y)
| SSA.SSA.Isbcs (c, v, a1, a2, y) -> SSALite.SSALite.Isbcs (c, v, a1, a2, y)
| SSA.SSA.Isbb (v, a1, a2, y) -> SSALite.SSALite.Isbb (v, a1, a2, y)
| SSA.SSA.Isbbs (c, v, a1, a2, y) -> SSALite.SSALite.Isbbs (c, v, a1, a2, y)
| SSA.SSA.Imul (v, a1, a2) -> SSALite.SSALite.Imul (v, a1, a2)
| SSA.SSA.Imull (vh, vl, a1, a2) -> SSALite.SSALite.Imull (vh, vl, a1, a2)
| SSA.SSA.Imulj (v, a1, a2) -> SSALite.SSALite.Imulj (v, a1, a2)
| SSA.SSA.Isplit (vh, vl, a, n) -> SSALite.SSALite.Isplit (vh, vl, a, n)
| SSA.SSA.Iand (v, t0, a1, a2) -> SSALite.SSALite.Iand (v, t0, a1, a2)
| SSA.SSA.Ior (v, t0, a1, a2) -> SSALite.SSALite.Ior (v, t0, a1, a2)
| SSA.SSA.Ixor (v, t0, a1, a2) -> SSALite.SSALite.Ixor (v, t0, a1, a2)
| SSA.SSA.Icast (v, t0, a) -> SSALite.SSALite.Icast (v, t0, a)
| SSA.SSA.Ivpc (v, t0, a) -> SSALite.SSALite.Ivpc (v, t0, a)
| SSA.SSA.Ijoin (v, ah, al) -> SSALite.SSALite.Ijoin (v, ah, al)
| SSA.SSA.Iassume e -> SSALite.SSALite.Iassume e
| _ -> SSALite.SSALite.Inop

(** val ssa2lite_program : SSA.SSA.program -> SSALite.SSALite.program **)

let ssa2lite_program p =
  tmap ssa2lite_instr p

(** val ssa2lite_spec : SSA.SSA.spec -> SSALite.SSALite.spec **)

let ssa2lite_spec s =
  { SSALite.SSALite.sinputs = (SSA.SSA.sinputs s); SSALite.SSALite.spre =
    (SSA.SSA.spre s); SSALite.SSALite.sprog =
    (ssa2lite_program (SSA.SSA.sprog s)); SSALite.SSALite.spost =
    (SSA.SSA.spost s) }
