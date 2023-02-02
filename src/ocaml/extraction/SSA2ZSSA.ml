open BinInt
open BinNat
open BinNums
open DSLRaw
open Options0
open Typ
open Var
open Eqtype
open Seq
open Ssrnat

(** val max_svar : SSAVS.t -> VarOrder.t **)

let max_svar vs =
  match SSAVS.max_elt vs with
  | Some v -> SSA.svar v
  | None -> Obj.magic N0

(** val new_svar : SSAVS.t -> VarOrder.t **)

let new_svar vs =
  Obj.magic N.succ (max_svar vs)

(** val algred_atom : SSA.SSA.atom -> SSA.SSA.eexp **)

let algred_atom = function
| Avar v -> SSA.SSA.evar v
| Aconst (ty, bs) -> SSA.SSA.econst (SSA.SSA.bv2z ty bs)

(** val algred_assign : ssavar -> SSA.SSA.eexp -> SSA.SSA.ebexp **)

let algred_assign v e =
  SSA.SSA.eeq (SSA.SSA.evar v) e

(** val algred_join :
    SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp -> int -> SSA.SSA.ebexp **)

let algred_join e h l p =
  SSA.SSA.eeq (SSA.SSA.eadd l (SSA.SSA.emul2p h (Z.of_nat p))) e

(** val algred_split :
    ssavar -> ssavar -> SSA.SSA.eexp -> int -> SSA.SSA.ebexp **)

let algred_split vh vl e p =
  algred_join e (SSA.SSA.evar vh) (SSA.SSA.evar vl) p

(** val algred_is_carry : ssavar -> SSA.SSA.ebexp **)

let algred_is_carry c =
  SSA.SSA.eeq
    (SSA.SSA.emul (SSA.SSA.evar c)
      (SSA.SSA.esub (SSA.SSA.evar c) (SSA.SSA.econst (Zpos Coq_xH))))
    (SSA.SSA.econst Z0)

(** val carry_constr : options -> ssavar -> SSA.SSA.ebexp list **)

let carry_constr o c =
  if o.add_carry_constraints then (algred_is_carry c) :: [] else []

(** val algred_cast :
    VarOrder.t -> coq_N -> SSAVarOrder.t -> typ -> SSA.SSA.atom -> typ ->
    coq_N * ebexp list **)

let algred_cast avn g v vtyp a atyp0 =
  match vtyp with
  | Tuint wv ->
    (match atyp0 with
     | Tuint wa ->
       if leq wa wv
       then (g, ((Eeq ((SSA.SSA.evar v), (algred_atom a))) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: []))
     | Tsint wa ->
       if leq wa wv
       then let a_sign = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_join (SSA.SSA.evar v) (SSA.SSA.evar (Obj.magic a_sign))
               (algred_atom a) wv) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: [])))
  | Tsint wv ->
    (match atyp0 with
     | Tuint wa ->
       if leq (Pervasives.succ wa) wv
       then (g, ((Eeq ((SSA.SSA.evar v), (algred_atom a))) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: []))
     | Tsint wa ->
       if leq wa wv
       then (g, ((Eeq ((SSA.SSA.evar v), (algred_atom a))) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: [])))

(** val algred_vpc :
    VarOrder.t -> coq_N -> ssavar -> SSA.SSA.atom -> coq_N * ebexp list **)

let algred_vpc _ g v a =
  (g, ((Eeq ((SSA.SSA.evar v), (algred_atom a))) :: []))

(** val algred_instr :
    options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N -> SSA.SSA.instr ->
    coq_N * SSA.SSA.ebexp list **)

let algred_instr o te avn g = function
| SSA.SSA.Imov (v, a) ->
  let za = algred_atom a in (g, ((algred_assign v za) :: []))
| SSA.SSA.Ishl (v, a, n) ->
  let za = algred_atom a in
  (g, ((algred_assign v (SSA.SSA.emul2p za (Z.of_nat n))) :: []))
| SSA.SSA.Icshl (vh, vl, a1, a2, n) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let a2size = SSA.SSA.asize a2 te in
  (g,
  ((algred_split vh vl
     (SSA.SSA.eadd (SSA.SSA.emul2p za1 (Z.of_nat a2size)) za2)
     (subn a2size n)) :: []))
| SSA.SSA.Inondet (v, t0) ->
  if eq_op typ_eqType (Obj.magic t0) (Obj.magic coq_Tbit)
  then (g, (carry_constr o v))
  else (g, [])
| SSA.SSA.Icmov (v, c, a1, a2) ->
  let zc = algred_atom c in
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g,
  ((algred_assign v
     (SSA.SSA.eadd (SSA.SSA.emul zc za1)
       (SSA.SSA.emul (SSA.SSA.esub (SSA.SSA.econst Z.one) zc) za2))) :: []))
| SSA.SSA.Inot (v, t0, a) ->
  let za = algred_atom a in
  let ta = SSA.SSA.atyp a te in
  (match t0 with
   | Tuint w ->
     (match ta with
      | Tuint _ ->
        (g,
          ((algred_assign v
             (SSA.SSA.esub
               (SSA.SSA.econst (Z.sub (SSA.SSA.z2expn (Z.of_nat w)) Z.one))
               za)) :: []))
      | Tsint _ -> (g, []))
   | Tsint _ ->
     (match ta with
      | Tuint _ -> (g, [])
      | Tsint _ ->
        (g,
          ((algred_assign v
             (SSA.SSA.esub (SSA.SSA.eneg za) (SSA.SSA.econst Z.one))) :: []))))
| SSA.SSA.Iadd (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSA.SSA.eadd za1 za2)) :: []))
| SSA.SSA.Iadds (c, v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (match SSA.SSA.atyp a1 te with
   | Tuint w ->
     (g,
       (cat ((algred_split c v (SSA.SSA.eadd za1 za2) w) :: [])
         (carry_constr o c)))
   | Tsint _ -> (g, ((algred_assign v (SSA.SSA.eadd za1 za2)) :: [])))
| SSA.SSA.Iadc (v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (g, ((algred_assign v (SSA.SSA.eadd (SSA.SSA.eadd za1 za2) zy)) :: []))
| SSA.SSA.Iadcs (c, v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (match SSA.SSA.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_split c v (SSA.SSA.eadd (SSA.SSA.eadd za1 za2) zy) w) :: [])
         (carry_constr o c)))
   | Tsint _ ->
     (g, ((algred_assign v (SSA.SSA.eadd (SSA.SSA.eadd za1 za2) zy)) :: [])))
| SSA.SSA.Isub (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSA.SSA.esub za1 za2)) :: []))
| SSA.SSA.Isubc (c, v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (match SSA.SSA.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join (SSA.SSA.evar v)
            (SSA.SSA.esub (SSA.SSA.econst Z.one) (SSA.SSA.evar c))
            (SSA.SSA.esub za1 za2) w) :: []) (carry_constr o c)))
   | Tsint _ -> (g, ((algred_assign v (SSA.SSA.esub za1 za2)) :: [])))
| SSA.SSA.Isubb (c, v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (match SSA.SSA.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join (SSA.SSA.evar v) (SSA.SSA.evar c)
            (SSA.SSA.esub za1 za2) w) :: []) (carry_constr o c)))
   | Tsint _ -> (g, ((algred_assign v (SSA.SSA.esub za1 za2)) :: [])))
| SSA.SSA.Isbc (v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (g,
  ((algred_assign v
     (SSA.SSA.esub (SSA.SSA.esub za1 za2)
       (SSA.SSA.esub (SSA.SSA.econst Z.one) zy))) :: []))
| SSA.SSA.Isbcs (c, v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (match SSA.SSA.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join (SSA.SSA.evar v)
            (SSA.SSA.esub (SSA.SSA.econst Z.one) (SSA.SSA.evar c))
            (SSA.SSA.esub (SSA.SSA.esub za1 za2)
              (SSA.SSA.esub (SSA.SSA.econst Z.one) zy)) w) :: [])
         (carry_constr o c)))
   | Tsint _ ->
     (g,
       ((algred_assign v
          (SSA.SSA.esub (SSA.SSA.esub za1 za2)
            (SSA.SSA.esub (SSA.SSA.econst Z.one) zy))) :: [])))
| SSA.SSA.Isbb (v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (g, ((algred_assign v (SSA.SSA.esub (SSA.SSA.esub za1 za2) zy)) :: []))
| SSA.SSA.Isbbs (c, v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (match SSA.SSA.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join (SSA.SSA.esub (SSA.SSA.esub za1 za2) zy)
            (SSA.SSA.eneg (SSA.SSA.evar c)) (SSA.SSA.evar v) w) :: [])
         (carry_constr o c)))
   | Tsint _ ->
     (g, ((algred_assign v (SSA.SSA.esub (SSA.SSA.esub za1 za2) zy)) :: [])))
| SSA.SSA.Imul (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSA.SSA.emul za1 za2)) :: []))
| SSA.SSA.Imull (vh, vl, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let a2size = SSA.SSA.asize a2 te in
  (g, ((algred_split vh vl (SSA.SSA.emul za1 za2) a2size) :: []))
| SSA.SSA.Imulj (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSA.SSA.emul za1 za2)) :: []))
| SSA.SSA.Isplit (vh, vl, a, n) ->
  let za = algred_atom a in (g, ((algred_split vh vl za n) :: []))
| SSA.SSA.Icast (v, t0, a) -> algred_cast avn g v t0 a (SSA.SSA.atyp a te)
| SSA.SSA.Ivpc (v, _, a) -> algred_vpc avn g v a
| SSA.SSA.Ijoin (v, ah, al) ->
  let zah = algred_atom ah in
  let zal = algred_atom al in
  let alsize = SSA.SSA.asize al te in
  (g, ((algred_join (SSA.SSA.evar v) zah zal alsize) :: []))
| SSA.SSA.Iassume e -> (g, (SSA.SSA.split_eand (SSA.SSA.eqn_bexp e)))
| _ -> (g, [])

(** val algred_program :
    options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N -> SSA.SSA.program ->
    coq_N * SSA.SSA.ebexp list **)

let rec algred_program o te avn g = function
| [] -> (g, [])
| hd :: tl ->
  let (g_hd, zhd) = algred_instr o te avn g hd in
  let (g_tl, ztl) =
    algred_program o (SSA.SSA.instr_succ_typenv hd te) avn g_hd tl
  in
  (g_tl, (cat zhd ztl))

(** val new_svar_spec : SSA.SSA.spec -> VarOrder.t **)

let new_svar_spec s =
  new_svar
    (SSAVS.union (SSA.SSA.vars_env (SSA.SSA.sinputs s))
      (SSAVS.union (SSA.SSA.vars_bexp (SSA.SSA.spre s))
        (SSAVS.union (SSA.SSA.vars_program (SSA.SSA.sprog s))
          (SSA.SSA.vars_bexp (SSA.SSA.spost s)))))

(** val algred_espec :
    options -> VarOrder.t -> SSA.SSA.espec -> ZSSA.ZSSA.rep **)

let algred_espec o avn s =
  let (_, eprogs) =
    algred_program o (SSA.SSA.esinputs s) avn SSA.initial_index
      (SSA.SSA.esprog s)
  in
  { ZSSA.ZSSA.premise =
  (SSA.SSA.eand (SSA.SSA.eqn_bexp (SSA.SSA.espre s)) (SSA.SSA.eands eprogs));
  ZSSA.ZSSA.conseq = (SSA.SSA.espost s) }
