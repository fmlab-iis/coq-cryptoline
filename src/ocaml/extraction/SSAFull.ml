open BinNat
open BinNums
open Bool
open DSLRaw
open NBitsDef
open State
open Typ
open Var
open Eqtype
open Seq

type __ = Obj.t

module SSAFull =
 DSLFull.MakeDSL(SSAVarOrder)(SSAVarOrderPrinter)(SSAVS)(SSAVM)(TypEnv.SSATE)(SSAStore)

type vmap = coq_N VM.t

(** val empty_vmap : vmap **)

let empty_vmap =
  VM.empty

(** val initial_index : coq_N **)

let initial_index =
  N0

(** val first_assigned_index : coq_N **)

let first_assigned_index =
  Npos Coq_xH

(** val get_index : var -> vmap -> coq_N **)

let get_index v m =
  match VM.find (Obj.magic v) m with
  | Some i -> i
  | None -> initial_index

(** val upd_index : var -> vmap -> vmap **)

let upd_index v m =
  match VM.find (Obj.magic v) m with
  | Some i -> VM.add (Obj.magic v) (N.add i (Npos Coq_xH)) m
  | None -> VM.add (Obj.magic v) first_assigned_index m

(** val ssa_var : vmap -> var -> ssavar **)

let ssa_var m v =
  Obj.magic (v, (get_index v m))

(** val ssa_atom : vmap -> DSLFull.DSLFull.atom -> SSAFull.atom **)

let ssa_atom m = function
| Avar v -> SSAFull.avar (ssa_var m (Obj.magic v))
| Aconst (ty, n) -> SSAFull.aconst ty n

(** val ssa_eexp : vmap -> DSLFull.DSLFull.eexp -> SSAFull.eexp **)

let rec ssa_eexp m = function
| Evar v -> SSAFull.evar (ssa_var m (Obj.magic v))
| Econst c -> SSAFull.econst c
| Eunop (op, e0) -> SSAFull.eunary op (ssa_eexp m e0)
| Ebinop (op, e1, e2) -> SSAFull.ebinary op (ssa_eexp m e1) (ssa_eexp m e2)
| Epow (e0, n) -> SSAFull.epow (ssa_eexp m e0) n

(** val ssa_eexps : vmap -> DSLFull.DSLFull.eexp list -> SSAFull.eexp list **)

let ssa_eexps m es =
  map (ssa_eexp m) es

(** val ssa_rexp : vmap -> DSLFull.DSLFull.rexp -> SSAFull.rexp **)

let rec ssa_rexp m = function
| Rvar v -> SSAFull.rvar (ssa_var m (Obj.magic v))
| Rconst (w, n) -> SSAFull.rconst w n
| Runop (w, op, e0) -> SSAFull.runary w op (ssa_rexp m e0)
| Rbinop (w, op, e1, e2) ->
  SSAFull.rbinary w op (ssa_rexp m e1) (ssa_rexp m e2)
| Ruext (w, e0, i) -> SSAFull.ruext w (ssa_rexp m e0) i
| Rsext (w, e0, i) -> SSAFull.rsext w (ssa_rexp m e0) i

(** val ssa_ebexp : vmap -> DSLFull.DSLFull.ebexp -> SSAFull.ebexp **)

let rec ssa_ebexp m = function
| Etrue -> SSAFull.etrue
| Eeq (e1, e2) -> SSAFull.eeq (ssa_eexp m e1) (ssa_eexp m e2)
| Eeqmod (e1, e2, ms) ->
  SSAFull.eeqmod (ssa_eexp m e1) (ssa_eexp m e2) (ssa_eexps m ms)
| Eand (e1, e2) -> SSAFull.eand (ssa_ebexp m e1) (ssa_ebexp m e2)

(** val ssa_rbexp : vmap -> DSLFull.DSLFull.rbexp -> SSAFull.rbexp **)

let rec ssa_rbexp m = function
| Rtrue -> SSAFull.rtrue
| Req (w, e1, e2) -> SSAFull.req w (ssa_rexp m e1) (ssa_rexp m e2)
| Rcmp (w, op, e1, e2) -> SSAFull.rcmp w op (ssa_rexp m e1) (ssa_rexp m e2)
| Rneg e0 -> SSAFull.rneg (ssa_rbexp m e0)
| Rand (e1, e2) -> SSAFull.rand (ssa_rbexp m e1) (ssa_rbexp m e2)
| Ror (e1, e2) -> SSAFull.ror (ssa_rbexp m e1) (ssa_rbexp m e2)

(** val ssa_bexp :
    vmap -> DSLFull.DSLFull.bexp -> SSAFull.ebexp * SSAFull.rbexp **)

let ssa_bexp m e =
  ((ssa_ebexp m (DSLFull.DSLFull.eqn_bexp e)),
    (ssa_rbexp m (DSLFull.DSLFull.rng_bexp e)))

(** val ssa_instr : vmap -> DSLFull.DSLFull.instr -> vmap * SSAFull.instr **)

let ssa_instr m = function
| DSLFull.DSLFull.Imov (v, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Imov ((ssa_var m0 (Obj.magic v)), a0)))
| DSLFull.DSLFull.Ishl (v, a, p) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Ishl ((ssa_var m0 (Obj.magic v)), a0, p)))
| DSLFull.DSLFull.Icshl (vh, vl, a1, a2, p) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSAFull.Icshl ((ssa_var mh (Obj.magic vh)),
  (ssa_var ml (Obj.magic vl)), a3, a4, p)))
| DSLFull.DSLFull.Inondet (v, ty) ->
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Inondet ((ssa_var m0 (Obj.magic v)), ty)))
| DSLFull.DSLFull.Icmov (v, c, a1, a2) ->
  let c0 = ssa_atom m c in
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Icmov ((ssa_var m0 (Obj.magic v)), c0, a3, a4)))
| DSLFull.DSLFull.Inop -> (m, SSAFull.Inop)
| DSLFull.DSLFull.Inot (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Inot ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSLFull.DSLFull.Iadd (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Iadd ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLFull.DSLFull.Iadds (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSAFull.Iadds ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4)))
| DSLFull.DSLFull.Iadc (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Iadc ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSLFull.DSLFull.Iadcs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSAFull.Iadcs ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4, y0)))
| DSLFull.DSLFull.Isub (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Isub ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLFull.DSLFull.Isubc (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSAFull.Isubc ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4)))
| DSLFull.DSLFull.Isubb (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSAFull.Isubb ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4)))
| DSLFull.DSLFull.Isbc (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Isbc ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSLFull.DSLFull.Isbcs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSAFull.Isbcs ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4, y0)))
| DSLFull.DSLFull.Isbb (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Isbb ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSLFull.DSLFull.Isbbs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSAFull.Isbbs ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4, y0)))
| DSLFull.DSLFull.Imul (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Imul ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLFull.DSLFull.Imull (vh, vl, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSAFull.Imull ((ssa_var mh (Obj.magic vh)),
  (ssa_var ml (Obj.magic vl)), a3, a4)))
| DSLFull.DSLFull.Imulj (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Imulj ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLFull.DSLFull.Isplit (vh, vl, a, n) ->
  let a0 = ssa_atom m a in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSAFull.Isplit ((ssa_var mh (Obj.magic vh)),
  (ssa_var ml (Obj.magic vl)), a0, n)))
| DSLFull.DSLFull.Iand (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Iand ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSLFull.DSLFull.Ior (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Ior ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSLFull.DSLFull.Ixor (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Ixor ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSLFull.DSLFull.Icast (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Icast ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSLFull.DSLFull.Ivpc (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Ivpc ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSLFull.DSLFull.Ijoin (v, ah, al) ->
  let ah0 = ssa_atom m ah in
  let al0 = ssa_atom m al in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSAFull.Ijoin ((ssa_var m0 (Obj.magic v)), ah0, al0)))
| DSLFull.DSLFull.Icut e -> (m, (SSAFull.Icut (ssa_bexp m e)))
| DSLFull.DSLFull.Iassert e -> (m, (SSAFull.Iassert (ssa_bexp m e)))
| DSLFull.DSLFull.Iassume e -> (m, (SSAFull.Iassume (ssa_bexp m e)))

(** val ssa_program :
    vmap -> DSLFull.DSLFull.program -> vmap * SSAFull.program **)

let rec ssa_program m = function
| [] -> (m, [])
| hd :: tl ->
  let (m0, hd0) = ssa_instr m hd in
  let (m1, tl0) = ssa_program m0 tl in (m1, (hd0 :: tl0))

(** val add_to_ste :
    vmap -> var -> typ -> TypEnv.SSATE.env -> typ TypEnv.SSATE.t **)

let add_to_ste m k v e =
  TypEnv.SSATE.add (ssa_var m k) v e

(** val ssa_typenv : vmap -> TypEnv.TE.env -> TypEnv.SSATE.env **)

let ssa_typenv m te =
  TypEnv.TE.fold (Obj.magic add_to_ste m) te TypEnv.SSATE.empty

(** val ssa_spec : DSLFull.DSLFull.spec -> SSAFull.spec **)

let ssa_spec s =
  let si = ssa_typenv empty_vmap (DSLFull.DSLFull.sinputs s) in
  let f = ssa_bexp empty_vmap (DSLFull.DSLFull.spre s) in
  let (m, p) = ssa_program empty_vmap (DSLFull.DSLFull.sprog s) in
  let g = ssa_bexp m (DSLFull.DSLFull.spost s) in
  { SSAFull.sinputs = si; SSAFull.spre = f; SSAFull.sprog = p;
  SSAFull.spost = g }
