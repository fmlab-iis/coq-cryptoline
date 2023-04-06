open BinInt
open BinNat
open BinNums
open DSLRaw
open EqVar
open Options0
open Typ
open Eqtype
open Seq
open Ssrnat

(** val max_svar : SSAVS.t -> VarOrder.t **)

let max_svar vs =
  match SSAVS.max_elt vs with
  | Some v -> SSALite.svar v
  | None -> Obj.magic N0

(** val new_svar : SSAVS.t -> VarOrder.t **)

let new_svar vs =
  Obj.magic N.succ (max_svar vs)

(** val algred_atom : SSALite.SSALite.atom -> SSALite.SSALite.eexp **)

let algred_atom = function
| Avar v -> SSALite.SSALite.evar v
| Aconst (ty, bs) -> SSALite.SSALite.econst (SSALite.SSALite.bv2z ty bs)

(** val algred_assign :
    ssavar -> SSALite.SSALite.eexp -> SSALite.SSALite.ebexp **)

let algred_assign v e =
  SSALite.SSALite.eeq (SSALite.SSALite.evar v) e

(** val algred_join :
    SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp ->
    int -> SSALite.SSALite.ebexp **)

let algred_join e h l p =
  SSALite.SSALite.eeq
    (SSALite.SSALite.eadd l (SSALite.SSALite.emul2p h (Z.of_nat p))) e

(** val algred_split :
    ssavar -> ssavar -> SSALite.SSALite.eexp -> int -> SSALite.SSALite.ebexp **)

let algred_split vh vl e p =
  algred_join e (SSALite.SSALite.evar vh) (SSALite.SSALite.evar vl) p

(** val algred_is_carry : ssavar -> SSALite.SSALite.ebexp **)

let algred_is_carry c =
  SSALite.SSALite.eeq
    (SSALite.SSALite.emul (SSALite.SSALite.evar c)
      (SSALite.SSALite.esub (SSALite.SSALite.evar c)
        (SSALite.SSALite.econst (Zpos Coq_xH)))) (SSALite.SSALite.econst Z0)

(** val carry_constr : options -> ssavar -> SSALite.SSALite.ebexp list **)

let carry_constr o c =
  if o.add_carry_constraints then (algred_is_carry c) :: [] else []

(** val algred_cast :
    VarOrder.t -> coq_N -> SSAVarOrder.t -> typ -> SSALite.SSALite.atom ->
    typ -> coq_N * ebexp list **)

let algred_cast avn g v vtyp a atyp0 =
  match vtyp with
  | Tuint wv ->
    (match atyp0 with
     | Tuint wa ->
       if leq wa wv
       then (g, ((Eeq ((SSALite.SSALite.evar v), (algred_atom a))) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: []))
     | Tsint wa ->
       if leq wa wv
       then let a_sign = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_join (SSALite.SSALite.evar v)
               (SSALite.SSALite.evar (Obj.magic a_sign)) (algred_atom a) wv) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: [])))
  | Tsint wv ->
    (match atyp0 with
     | Tuint wa ->
       if leq (Pervasives.succ wa) wv
       then (g, ((Eeq ((SSALite.SSALite.evar v), (algred_atom a))) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: []))
     | Tsint wa ->
       if leq wa wv
       then (g, ((Eeq ((SSALite.SSALite.evar v), (algred_atom a))) :: []))
       else let discarded = (avn, g) in
            let g' = N.succ g in
            (g',
            ((algred_split (Obj.magic discarded) v (algred_atom a) wv) :: [])))

(** val algred_vpc :
    VarOrder.t -> coq_N -> ssavar -> SSALite.SSALite.atom -> coq_N * ebexp
    list **)

let algred_vpc _ g v a =
  (g, ((Eeq ((SSALite.SSALite.evar v), (algred_atom a))) :: []))

(** val algred_instr :
    options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N ->
    SSALite.SSALite.instr -> coq_N * SSALite.SSALite.ebexp list **)

let algred_instr o te avn g = function
| SSALite.SSALite.Imov (v, a) ->
  let za = algred_atom a in (g, ((algred_assign v za) :: []))
| SSALite.SSALite.Ishl (v, a, n) ->
  let za = algred_atom a in
  (g, ((algred_assign v (SSALite.SSALite.emul2p za (Z.of_nat n))) :: []))
| SSALite.SSALite.Icshl (vh, vl, a1, a2, n) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let a2size = SSALite.SSALite.asize a2 te in
  (g,
  ((algred_split vh vl
     (SSALite.SSALite.eadd (SSALite.SSALite.emul2p za1 (Z.of_nat a2size)) za2)
     (subn a2size n)) :: []))
| SSALite.SSALite.Inondet (v, t0) ->
  if eq_op typ_eqType (Obj.magic t0) (Obj.magic coq_Tbit)
  then (g, (carry_constr o v))
  else (g, [])
| SSALite.SSALite.Icmov (v, c, a1, a2) ->
  let zc = algred_atom c in
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g,
  ((algred_assign v
     (SSALite.SSALite.eadd (SSALite.SSALite.emul zc za1)
       (SSALite.SSALite.emul
         (SSALite.SSALite.esub (SSALite.SSALite.econst Z.one) zc) za2))) :: []))
| SSALite.SSALite.Inot (v, t0, a) ->
  let za = algred_atom a in
  let ta = SSALite.SSALite.atyp a te in
  (match t0 with
   | Tuint w ->
     (match ta with
      | Tuint _ ->
        (g,
          ((algred_assign v
             (SSALite.SSALite.esub
               (SSALite.SSALite.econst
                 (Z.sub (SSALite.SSALite.z2expn (Z.of_nat w)) Z.one)) za)) :: []))
      | Tsint _ -> (g, []))
   | Tsint _ ->
     (match ta with
      | Tuint _ -> (g, [])
      | Tsint _ ->
        (g,
          ((algred_assign v
             (SSALite.SSALite.esub (SSALite.SSALite.eneg za)
               (SSALite.SSALite.econst Z.one))) :: []))))
| SSALite.SSALite.Iadd (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSALite.SSALite.eadd za1 za2)) :: []))
| SSALite.SSALite.Iadds (c, v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (match SSALite.SSALite.atyp a1 te with
   | Tuint w ->
     (g,
       (cat ((algred_split c v (SSALite.SSALite.eadd za1 za2) w) :: [])
         (carry_constr o c)))
   | Tsint _ -> (g, ((algred_assign v (SSALite.SSALite.eadd za1 za2)) :: [])))
| SSALite.SSALite.Iadc (v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (g,
  ((algred_assign v (SSALite.SSALite.eadd (SSALite.SSALite.eadd za1 za2) zy)) :: []))
| SSALite.SSALite.Iadcs (c, v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (match SSALite.SSALite.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_split c v
            (SSALite.SSALite.eadd (SSALite.SSALite.eadd za1 za2) zy) w) :: [])
         (carry_constr o c)))
   | Tsint _ ->
     (g,
       ((algred_assign v
          (SSALite.SSALite.eadd (SSALite.SSALite.eadd za1 za2) zy)) :: [])))
| SSALite.SSALite.Isub (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSALite.SSALite.esub za1 za2)) :: []))
| SSALite.SSALite.Isubc (c, v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (match SSALite.SSALite.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join (SSALite.SSALite.evar v)
            (SSALite.SSALite.esub (SSALite.SSALite.econst Z.one)
              (SSALite.SSALite.evar c)) (SSALite.SSALite.esub za1 za2) w) :: [])
         (carry_constr o c)))
   | Tsint _ -> (g, ((algred_assign v (SSALite.SSALite.esub za1 za2)) :: [])))
| SSALite.SSALite.Isubb (c, v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (match SSALite.SSALite.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join (SSALite.SSALite.evar v) (SSALite.SSALite.evar c)
            (SSALite.SSALite.esub za1 za2) w) :: []) (carry_constr o c)))
   | Tsint _ -> (g, ((algred_assign v (SSALite.SSALite.esub za1 za2)) :: [])))
| SSALite.SSALite.Isbc (v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (g,
  ((algred_assign v
     (SSALite.SSALite.esub (SSALite.SSALite.esub za1 za2)
       (SSALite.SSALite.esub (SSALite.SSALite.econst Z.one) zy))) :: []))
| SSALite.SSALite.Isbcs (c, v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (match SSALite.SSALite.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join (SSALite.SSALite.evar v)
            (SSALite.SSALite.esub (SSALite.SSALite.econst Z.one)
              (SSALite.SSALite.evar c))
            (SSALite.SSALite.esub (SSALite.SSALite.esub za1 za2)
              (SSALite.SSALite.esub (SSALite.SSALite.econst Z.one) zy)) w) :: [])
         (carry_constr o c)))
   | Tsint _ ->
     (g,
       ((algred_assign v
          (SSALite.SSALite.esub (SSALite.SSALite.esub za1 za2)
            (SSALite.SSALite.esub (SSALite.SSALite.econst Z.one) zy))) :: [])))
| SSALite.SSALite.Isbb (v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (g,
  ((algred_assign v (SSALite.SSALite.esub (SSALite.SSALite.esub za1 za2) zy)) :: []))
| SSALite.SSALite.Isbbs (c, v, a1, a2, y) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let zy = algred_atom y in
  (match SSALite.SSALite.atyp a1 te with
   | Tuint w ->
     (g,
       (cat
         ((algred_join
            (SSALite.SSALite.esub (SSALite.SSALite.esub za1 za2) zy)
            (SSALite.SSALite.eneg (SSALite.SSALite.evar c))
            (SSALite.SSALite.evar v) w) :: []) (carry_constr o c)))
   | Tsint _ ->
     (g,
       ((algred_assign v
          (SSALite.SSALite.esub (SSALite.SSALite.esub za1 za2) zy)) :: [])))
| SSALite.SSALite.Imul (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSALite.SSALite.emul za1 za2)) :: []))
| SSALite.SSALite.Imull (vh, vl, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  let a2size = SSALite.SSALite.asize a2 te in
  (g, ((algred_split vh vl (SSALite.SSALite.emul za1 za2) a2size) :: []))
| SSALite.SSALite.Imulj (v, a1, a2) ->
  let za1 = algred_atom a1 in
  let za2 = algred_atom a2 in
  (g, ((algred_assign v (SSALite.SSALite.emul za1 za2)) :: []))
| SSALite.SSALite.Isplit (vh, vl, a, n) ->
  let za = algred_atom a in (g, ((algred_split vh vl za n) :: []))
| SSALite.SSALite.Icast (v, t0, a) ->
  algred_cast avn g v t0 a (SSALite.SSALite.atyp a te)
| SSALite.SSALite.Ivpc (v, _, a) -> algred_vpc avn g v a
| SSALite.SSALite.Ijoin (v, ah, al) ->
  let zah = algred_atom ah in
  let zal = algred_atom al in
  let alsize = SSALite.SSALite.asize al te in
  (g, ((algred_join (SSALite.SSALite.evar v) zah zal alsize) :: []))
| SSALite.SSALite.Iassume e ->
  (g, (SSALite.SSALite.split_eand (SSALite.SSALite.eqn_bexp e)))
| _ -> (g, [])

(** val algred_program :
    options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N ->
    SSALite.SSALite.program -> coq_N * SSALite.SSALite.ebexp list **)

let rec algred_program o te avn g = function
| [] -> (g, [])
| hd :: tl ->
  let (g_hd, zhd) = algred_instr o te avn g hd in
  let (g_tl, ztl) =
    algred_program o (SSALite.SSALite.instr_succ_typenv hd te) avn g_hd tl
  in
  (g_tl, (cat zhd ztl))

(** val new_svar_spec : SSALite.SSALite.spec -> VarOrder.t **)

let new_svar_spec s =
  new_svar
    (SSAVS.union (SSALite.SSALite.vars_env (SSALite.SSALite.sinputs s))
      (SSAVS.union (SSALite.SSALite.vars_bexp (SSALite.SSALite.spre s))
        (SSAVS.union (SSALite.SSALite.vars_program (SSALite.SSALite.sprog s))
          (SSALite.SSALite.vars_bexp (SSALite.SSALite.spost s)))))

(** val algred_espec :
    options -> VarOrder.t -> SSALite.SSALite.espec -> ZSSA.ZSSA.rep **)

let algred_espec o avn s =
  let (_, eprogs) =
    algred_program o (SSALite.SSALite.esinputs s) avn SSALite.initial_index
      (SSALite.SSALite.esprog s)
  in
  { ZSSA.ZSSA.premise =
  (SSALite.SSALite.eand (SSALite.SSALite.eqn_bexp (SSALite.SSALite.espre s))
    (SSALite.SSALite.eands eprogs)); ZSSA.ZSSA.conseq =
  (SSALite.SSALite.espost s) }
