open BinNat
open BinNums
open Bool
open DSLRaw
open EqVar
open NBitsDef
open Options0
open State
open Typ
open Eqtype
open Seq

type __ = Obj.t

module SSALite =
 DSLLite.MakeDSL(SSAVarOrder)(SSAVarOrderPrinter)(SSAVS)(SSAVM)(TypEnv.SSATE)(SSAStore)

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

(** val ssa_atom : vmap -> DSLLite.DSLLite.atom -> SSALite.atom **)

let ssa_atom m = function
| Avar v -> SSALite.avar (ssa_var m (Obj.magic v))
| Aconst (ty, n) -> SSALite.aconst ty n

(** val ssa_eexp : vmap -> DSLLite.DSLLite.eexp -> SSALite.eexp **)

let rec ssa_eexp m = function
| Evar v -> SSALite.evar (ssa_var m (Obj.magic v))
| Econst c -> SSALite.econst c
| Eunop (op, e0) -> SSALite.eunary op (ssa_eexp m e0)
| Ebinop (op, e1, e2) -> SSALite.ebinary op (ssa_eexp m e1) (ssa_eexp m e2)
| Epow (e0, n) -> SSALite.epow (ssa_eexp m e0) n

(** val ssa_eexps : vmap -> DSLLite.DSLLite.eexp list -> SSALite.eexp list **)

let ssa_eexps m es =
  map (ssa_eexp m) es

(** val ssa_rexp : vmap -> DSLLite.DSLLite.rexp -> SSALite.rexp **)

let rec ssa_rexp m = function
| Rvar v -> SSALite.rvar (ssa_var m (Obj.magic v))
| Rconst (w, n) -> SSALite.rconst w n
| Runop (w, op, e0) -> SSALite.runary w op (ssa_rexp m e0)
| Rbinop (w, op, e1, e2) ->
  SSALite.rbinary w op (ssa_rexp m e1) (ssa_rexp m e2)
| Ruext (w, e0, i) -> SSALite.ruext w (ssa_rexp m e0) i
| Rsext (w, e0, i) -> SSALite.rsext w (ssa_rexp m e0) i

(** val ssa_ebexp : vmap -> DSLLite.DSLLite.ebexp -> SSALite.ebexp **)

let rec ssa_ebexp m = function
| Etrue -> SSALite.etrue
| Eeq (e1, e2) -> SSALite.eeq (ssa_eexp m e1) (ssa_eexp m e2)
| Eeqmod (e1, e2, ms) ->
  SSALite.eeqmod (ssa_eexp m e1) (ssa_eexp m e2) (ssa_eexps m ms)
| Eand (e1, e2) -> SSALite.eand (ssa_ebexp m e1) (ssa_ebexp m e2)

(** val ssa_rbexp : vmap -> DSLLite.DSLLite.rbexp -> SSALite.rbexp **)

let rec ssa_rbexp m = function
| Rtrue -> SSALite.rtrue
| Req (w, e1, e2) -> SSALite.req w (ssa_rexp m e1) (ssa_rexp m e2)
| Rcmp (w, op, e1, e2) -> SSALite.rcmp w op (ssa_rexp m e1) (ssa_rexp m e2)
| Rneg e0 -> SSALite.rneg (ssa_rbexp m e0)
| Rand (e1, e2) -> SSALite.rand (ssa_rbexp m e1) (ssa_rbexp m e2)
| Ror (e1, e2) -> SSALite.ror (ssa_rbexp m e1) (ssa_rbexp m e2)

(** val ssa_bexp :
    vmap -> DSLLite.DSLLite.bexp -> SSALite.ebexp * SSALite.rbexp **)

let ssa_bexp m e =
  ((ssa_ebexp m (DSLLite.DSLLite.eqn_bexp e)),
    (ssa_rbexp m (DSLLite.DSLLite.rng_bexp e)))

(** val ssa_instr : vmap -> DSLLite.DSLLite.instr -> vmap * SSALite.instr **)

let ssa_instr m = function
| DSLLite.DSLLite.Imov (v, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Imov ((ssa_var m0 (Obj.magic v)), a0)))
| DSLLite.DSLLite.Ishl (v, a, p) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Ishl ((ssa_var m0 (Obj.magic v)), a0, p)))
| DSLLite.DSLLite.Icshl (vh, vl, a1, a2, p) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSALite.Icshl ((ssa_var mh (Obj.magic vh)),
  (ssa_var ml (Obj.magic vl)), a3, a4, p)))
| DSLLite.DSLLite.Inondet (v, ty) ->
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Inondet ((ssa_var m0 (Obj.magic v)), ty)))
| DSLLite.DSLLite.Icmov (v, c, a1, a2) ->
  let c0 = ssa_atom m c in
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Icmov ((ssa_var m0 (Obj.magic v)), c0, a3, a4)))
| DSLLite.DSLLite.Inop -> (m, SSALite.Inop)
| DSLLite.DSLLite.Inot (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Inot ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSLLite.DSLLite.Iadd (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Iadd ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLLite.DSLLite.Iadds (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSALite.Iadds ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4)))
| DSLLite.DSLLite.Iadc (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Iadc ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSLLite.DSLLite.Iadcs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSALite.Iadcs ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4, y0)))
| DSLLite.DSLLite.Isub (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Isub ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLLite.DSLLite.Isubc (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSALite.Isubc ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4)))
| DSLLite.DSLLite.Isubb (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSALite.Isubb ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4)))
| DSLLite.DSLLite.Isbc (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Isbc ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSLLite.DSLLite.Isbcs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSALite.Isbcs ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4, y0)))
| DSLLite.DSLLite.Isbb (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Isbb ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSLLite.DSLLite.Isbbs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSALite.Isbbs ((ssa_var mc (Obj.magic c)),
  (ssa_var mv (Obj.magic v)), a3, a4, y0)))
| DSLLite.DSLLite.Imul (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Imul ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLLite.DSLLite.Imull (vh, vl, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSALite.Imull ((ssa_var mh (Obj.magic vh)),
  (ssa_var ml (Obj.magic vl)), a3, a4)))
| DSLLite.DSLLite.Imulj (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Imulj ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSLLite.DSLLite.Isplit (vh, vl, a, n) ->
  let a0 = ssa_atom m a in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSALite.Isplit ((ssa_var mh (Obj.magic vh)),
  (ssa_var ml (Obj.magic vl)), a0, n)))
| DSLLite.DSLLite.Iand (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Iand ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSLLite.DSLLite.Ior (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Ior ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSLLite.DSLLite.Ixor (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Ixor ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSLLite.DSLLite.Icast (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Icast ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSLLite.DSLLite.Ivpc (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Ivpc ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSLLite.DSLLite.Ijoin (v, ah, al) ->
  let ah0 = ssa_atom m ah in
  let al0 = ssa_atom m al in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSALite.Ijoin ((ssa_var m0 (Obj.magic v)), ah0, al0)))
| DSLLite.DSLLite.Iassume e -> (m, (SSALite.Iassume (ssa_bexp m e)))

(** val ssa_program :
    vmap -> DSLLite.DSLLite.program -> vmap * SSALite.program **)

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

(** val ssa_spec : DSLLite.DSLLite.spec -> SSALite.spec **)

let ssa_spec s =
  let si = ssa_typenv empty_vmap (DSLLite.DSLLite.sinputs s) in
  let f = ssa_bexp empty_vmap (DSLLite.DSLLite.spre s) in
  let (m, p) = ssa_program empty_vmap (DSLLite.DSLLite.sprog s) in
  let g = ssa_bexp m (DSLLite.DSLLite.spost s) in
  { SSALite.sinputs = si; SSALite.spre = f; SSALite.sprog = p;
  SSALite.spost = g }
