open BinNat
open BinNums
open BinaryString
open Bool
open Datatypes
open NBitsDef
open State
open String0
open Typ
open Var
open Eqtype
open Seq

type __ = Obj.t

module SSA = DSL.MakeDSL(SSAVarOrder)(SSAVS)(SSAVM)(TypEnv.SSATE)(SSAStore)

(** val string_of_ssavar : ssavar -> char list **)

let string_of_ssavar v =
  append ('v'::[])
    (append (of_N (fst (Obj.magic v)))
      (append ('_'::[]) (of_N (snd (Obj.magic v)))))

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

(** val svar : ssavar -> Equality.sort **)

let svar x =
  fst (Obj.magic x)

(** val ssa_atom : vmap -> DSL.DSL.atom -> SSA.atom **)

let ssa_atom m = function
| DSL.DSL.Avar v -> SSA.Avar (ssa_var m (Obj.magic v))
| DSL.DSL.Aconst (ty, n) -> SSA.Aconst (ty, n)

(** val ssa_eexp : vmap -> DSL.DSL.eexp -> SSA.eexp **)

let rec ssa_eexp m = function
| DSL.Evar v -> SSA.evar (ssa_var m (Obj.magic v))
| DSL.Econst c -> SSA.econst c
| DSL.Eunop (op, e0) -> SSA.eunary op (ssa_eexp m e0)
| DSL.Ebinop (op, e1, e2) -> SSA.ebinary op (ssa_eexp m e1) (ssa_eexp m e2)
| DSL.Epow (e0, n) -> SSA.epow (ssa_eexp m e0) n

(** val ssa_eexps : vmap -> DSL.DSL.eexp list -> SSA.eexp list **)

let ssa_eexps m es =
  map (ssa_eexp m) es

(** val ssa_rexp : vmap -> DSL.DSL.rexp -> SSA.rexp **)

let rec ssa_rexp m = function
| DSL.Rvar v -> SSA.rvar (ssa_var m (Obj.magic v))
| DSL.Rconst (w, n) -> SSA.rconst w n
| DSL.Runop (w, op, e0) -> SSA.runary w op (ssa_rexp m e0)
| DSL.Rbinop (w, op, e1, e2) ->
  SSA.rbinary w op (ssa_rexp m e1) (ssa_rexp m e2)
| DSL.Ruext (w, e0, i) -> SSA.ruext w (ssa_rexp m e0) i
| DSL.Rsext (w, e0, i) -> SSA.rsext w (ssa_rexp m e0) i

(** val ssa_ebexp : vmap -> DSL.DSL.ebexp -> SSA.ebexp **)

let rec ssa_ebexp m = function
| DSL.Etrue -> SSA.etrue
| DSL.Eeq (e1, e2) -> SSA.eeq (ssa_eexp m e1) (ssa_eexp m e2)
| DSL.Eeqmod (e1, e2, ms) ->
  SSA.eeqmod (ssa_eexp m e1) (ssa_eexp m e2) (ssa_eexps m ms)
| DSL.Eand (e1, e2) -> SSA.eand (ssa_ebexp m e1) (ssa_ebexp m e2)

(** val ssa_rbexp : vmap -> DSL.DSL.rbexp -> SSA.rbexp **)

let rec ssa_rbexp m = function
| DSL.Rtrue -> SSA.rtrue
| DSL.Req (w, e1, e2) -> SSA.req w (ssa_rexp m e1) (ssa_rexp m e2)
| DSL.Rcmp (w, op, e1, e2) -> SSA.rcmp w op (ssa_rexp m e1) (ssa_rexp m e2)
| DSL.Rneg e0 -> SSA.rneg (ssa_rbexp m e0)
| DSL.Rand (e1, e2) -> SSA.rand (ssa_rbexp m e1) (ssa_rbexp m e2)
| DSL.Ror (e1, e2) -> SSA.ror (ssa_rbexp m e1) (ssa_rbexp m e2)

(** val ssa_bexp : vmap -> DSL.DSL.bexp -> SSA.ebexp * SSA.rbexp **)

let ssa_bexp m e =
  ((ssa_ebexp m (DSL.DSL.eqn_bexp e)), (ssa_rbexp m (DSL.DSL.rng_bexp e)))

(** val ssa_instr : vmap -> DSL.DSL.instr -> vmap * SSA.instr **)

let ssa_instr m = function
| DSL.DSL.Imov (v, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Imov ((ssa_var m0 (Obj.magic v)), a0)))
| DSL.DSL.Ishl (v, a, p) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Ishl ((ssa_var m0 (Obj.magic v)), a0, p)))
| DSL.DSL.Icshl (vh, vl, a1, a2, p) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSA.Icshl ((ssa_var mh (Obj.magic vh)), (ssa_var ml (Obj.magic vl)),
  a3, a4, p)))
| DSL.DSL.Inondet (v, ty) ->
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Inondet ((ssa_var m0 (Obj.magic v)), ty)))
| DSL.DSL.Icmov (v, c, a1, a2) ->
  let c0 = ssa_atom m c in
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Icmov ((ssa_var m0 (Obj.magic v)), c0, a3, a4)))
| DSL.DSL.Inop -> (m, SSA.Inop)
| DSL.DSL.Inot (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Inot ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSL.DSL.Iadd (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Iadd ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSL.DSL.Iadds (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSA.Iadds ((ssa_var mc (Obj.magic c)), (ssa_var mv (Obj.magic v)),
  a3, a4)))
| DSL.DSL.Iadc (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Iadc ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSL.DSL.Iadcs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSA.Iadcs ((ssa_var mc (Obj.magic c)), (ssa_var mv (Obj.magic v)),
  a3, a4, y0)))
| DSL.DSL.Isub (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Isub ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSL.DSL.Isubc (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSA.Isubc ((ssa_var mc (Obj.magic c)), (ssa_var mv (Obj.magic v)),
  a3, a4)))
| DSL.DSL.Isubb (c, v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSA.Isubb ((ssa_var mc (Obj.magic c)), (ssa_var mv (Obj.magic v)),
  a3, a4)))
| DSL.DSL.Isbc (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Isbc ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSL.DSL.Isbcs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSA.Isbcs ((ssa_var mc (Obj.magic c)), (ssa_var mv (Obj.magic v)),
  a3, a4, y0)))
| DSL.DSL.Isbb (v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Isbb ((ssa_var m0 (Obj.magic v)), a3, a4, y0)))
| DSL.DSL.Isbbs (c, v, a1, a2, y) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let y0 = ssa_atom m y in
  let mv = upd_index (Obj.magic v) m in
  let mc = upd_index (Obj.magic c) mv in
  (mc, (SSA.Isbbs ((ssa_var mc (Obj.magic c)), (ssa_var mv (Obj.magic v)),
  a3, a4, y0)))
| DSL.DSL.Imul (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Imul ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSL.DSL.Imull (vh, vl, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSA.Imull ((ssa_var mh (Obj.magic vh)), (ssa_var ml (Obj.magic vl)),
  a3, a4)))
| DSL.DSL.Imulj (v, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Imulj ((ssa_var m0 (Obj.magic v)), a3, a4)))
| DSL.DSL.Isplit (vh, vl, a, n) ->
  let a0 = ssa_atom m a in
  let ml = upd_index (Obj.magic vl) m in
  let mh = upd_index (Obj.magic vh) ml in
  (mh, (SSA.Isplit ((ssa_var mh (Obj.magic vh)), (ssa_var ml (Obj.magic vl)),
  a0, n)))
| DSL.DSL.Iand (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Iand ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSL.DSL.Ior (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Ior ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSL.DSL.Ixor (v, ty, a1, a2) ->
  let a3 = ssa_atom m a1 in
  let a4 = ssa_atom m a2 in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Ixor ((ssa_var m0 (Obj.magic v)), ty, a3, a4)))
| DSL.DSL.Icast (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Icast ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSL.DSL.Ivpc (v, ty, a) ->
  let a0 = ssa_atom m a in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Ivpc ((ssa_var m0 (Obj.magic v)), ty, a0)))
| DSL.DSL.Ijoin (v, ah, al) ->
  let ah0 = ssa_atom m ah in
  let al0 = ssa_atom m al in
  let m0 = upd_index (Obj.magic v) m in
  (m0, (SSA.Ijoin ((ssa_var m0 (Obj.magic v)), ah0, al0)))
| DSL.DSL.Iassume e -> (m, (SSA.Iassume (ssa_bexp m e)))

(** val ssa_program : vmap -> DSL.DSL.program -> vmap * SSA.program **)

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

(** val ssa_spec : DSL.DSL.spec -> SSA.spec **)

let ssa_spec s =
  let si = ssa_typenv empty_vmap (DSL.DSL.sinputs s) in
  let f = ssa_bexp empty_vmap (DSL.DSL.spre s) in
  let (m, p) = ssa_program empty_vmap (DSL.DSL.sprog s) in
  let g = ssa_bexp m (DSL.DSL.spost s) in
  { SSA.sinputs = si; SSA.spre = f; SSA.sprog = p; SSA.spost = g }
