open NBitsDef
open Typ
open Var
open Eqtype
open Seq
open Ssrnat

(** val qfbv_true : QFBV.QFBV.bexp **)

let qfbv_true =
  QFBV.QFBV.Btrue

(** val qfbv_var : SSAVarOrder.t -> QFBV.QFBV.exp **)

let qfbv_var v =
  QFBV.QFBV.Evar v

(** val qfbv_const : int -> int -> QFBV.QFBV.exp **)

let qfbv_const w n =
  QFBV.QFBV.Econst (from_nat w n)

(** val qfbv_zero : int -> QFBV.QFBV.exp **)

let qfbv_zero w =
  QFBV.QFBV.Econst (from_nat w 0)

(** val qfbv_one : int -> QFBV.QFBV.exp **)

let qfbv_one w =
  QFBV.QFBV.Econst (from_nat w (Pervasives.succ 0))

(** val qfbv_not : QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_not qe =
  QFBV.QFBV.Eunop (QFBV.QFBV.Unot, qe)

(** val qfbv_neg : QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_neg qe =
  QFBV.QFBV.Eunop (QFBV.QFBV.Uneg, qe)

(** val qfbv_high : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_high n qe =
  QFBV.QFBV.Eunop ((QFBV.QFBV.Uhigh n), qe)

(** val qfbv_low : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_low n qe =
  QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow n), qe)

(** val qfbv_zext : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_zext n qe =
  QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext n), qe)

(** val qfbv_sext : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_sext n qe =
  QFBV.QFBV.Eunop ((QFBV.QFBV.Usext n), qe)

(** val qfbv_and : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_and qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Band, qe0, qe1)

(** val qfbv_or : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_or qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bor, qe0, qe1)

(** val qfbv_xor : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_xor qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bxor, qe0, qe1)

(** val qfbv_add : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_add qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, qe0, qe1)

(** val qfbv_sub : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_sub qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, qe0, qe1)

(** val qfbv_mul : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_mul qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bmul, qe0, qe1)

(** val qfbv_mod : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_mod qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bmod, qe0, qe1)

(** val qfbv_srem : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_srem qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bsrem, qe0, qe1)

(** val qfbv_smod : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_smod qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bsmod, qe0, qe1)

(** val qfbv_shl : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_shl qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, qe0, qe1)

(** val qfbv_lshr : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_lshr qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Blshr, qe0, qe1)

(** val qfbv_ashr : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_ashr qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bashr, qe0, qe1)

(** val qfbv_concat : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let qfbv_concat qe0 qe1 =
  QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, qe0, qe1)

(** val qfbv_eq : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_eq qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, qe0, qe1)

(** val qfbv_ult : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_ult qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bult, qe0, qe1)

(** val qfbv_ule : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_ule qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bule, qe0, qe1)

(** val qfbv_ugt : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_ugt qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bugt, qe0, qe1)

(** val qfbv_uge : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_uge qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Buge, qe0, qe1)

(** val qfbv_slt : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_slt qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bslt, qe0, qe1)

(** val qfbv_sle : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_sle qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle, qe0, qe1)

(** val qfbv_sgt : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_sgt qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bsgt, qe0, qe1)

(** val qfbv_sge : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_sge qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bsge, qe0, qe1)

(** val qfbv_uaddo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_uaddo qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Buaddo, qe0, qe1)

(** val qfbv_usubo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_usubo qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Busubo, qe0, qe1)

(** val qfbv_umulo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_umulo qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bumulo, qe0, qe1)

(** val qfbv_saddo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_saddo qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bsaddo, qe0, qe1)

(** val qfbv_ssubo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_ssubo qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bssubo, qe0, qe1)

(** val qfbv_smulo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let qfbv_smulo qe0 qe1 =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bsmulo, qe0, qe1)

(** val qfbv_lneg : QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let qfbv_lneg qb =
  QFBV.QFBV.Blneg qb

(** val qfbv_conj : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let qfbv_conj qb0 qb1 =
  QFBV.QFBV.Bconj (qb0, qb1)

(** val qfbv_disj : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let qfbv_disj qb0 qb1 =
  QFBV.QFBV.Bdisj (qb0, qb1)

(** val qfbv_imp : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let qfbv_imp f g =
  qfbv_disj (qfbv_lneg f) g

(** val exp_rexp : SSA.SSA.rexp -> QFBV.QFBV.exp **)

let rec exp_rexp = function
| DSL.Rvar v -> qfbv_var v
| DSL.Rconst (_, n) -> QFBV.QFBV.Econst n
| DSL.Runop (_, op, e0) ->
  (match op with
   | DSL.Rnegb -> qfbv_neg (exp_rexp e0)
   | DSL.Rnotb -> qfbv_not (exp_rexp e0))
| DSL.Rbinop (_, op, e1, e2) ->
  (match op with
   | DSL.Radd -> qfbv_add (exp_rexp e1) (exp_rexp e2)
   | DSL.Rsub -> qfbv_sub (exp_rexp e1) (exp_rexp e2)
   | DSL.Rmul -> qfbv_mul (exp_rexp e1) (exp_rexp e2)
   | DSL.Rumod -> qfbv_mod (exp_rexp e1) (exp_rexp e2)
   | DSL.Rsrem -> qfbv_srem (exp_rexp e1) (exp_rexp e2)
   | DSL.Rsmod -> qfbv_smod (exp_rexp e1) (exp_rexp e2)
   | DSL.Randb -> qfbv_and (exp_rexp e1) (exp_rexp e2)
   | DSL.Rorb -> qfbv_or (exp_rexp e1) (exp_rexp e2)
   | DSL.Rxorb -> qfbv_xor (exp_rexp e1) (exp_rexp e2))
| DSL.Ruext (_, e0, n) -> qfbv_zext n (exp_rexp e0)
| DSL.Rsext (_, e0, n) -> qfbv_sext n (exp_rexp e0)

(** val bexp_rbexp : SSA.SSA.rbexp -> QFBV.QFBV.bexp **)

let rec bexp_rbexp = function
| DSL.Rtrue -> QFBV.QFBV.Btrue
| DSL.Req (_, e1, e2) -> qfbv_eq (exp_rexp e1) (exp_rexp e2)
| DSL.Rcmp (_, op, e1, e2) ->
  (match op with
   | DSL.Rult -> qfbv_ult (exp_rexp e1) (exp_rexp e2)
   | DSL.Rule -> qfbv_ule (exp_rexp e1) (exp_rexp e2)
   | DSL.Rugt -> qfbv_ugt (exp_rexp e1) (exp_rexp e2)
   | DSL.Ruge -> qfbv_uge (exp_rexp e1) (exp_rexp e2)
   | DSL.Rslt -> qfbv_slt (exp_rexp e1) (exp_rexp e2)
   | DSL.Rsle -> qfbv_sle (exp_rexp e1) (exp_rexp e2)
   | DSL.Rsgt -> qfbv_sgt (exp_rexp e1) (exp_rexp e2)
   | DSL.Rsge -> qfbv_sge (exp_rexp e1) (exp_rexp e2))
| DSL.Rneg e0 -> qfbv_lneg (bexp_rbexp e0)
| DSL.Rand (e1, e2) -> qfbv_conj (bexp_rbexp e1) (bexp_rbexp e2)
| DSL.Ror (e1, e2) -> qfbv_disj (bexp_rbexp e1) (bexp_rbexp e2)

(** val qfbv_conjs_rec :
    QFBV.QFBV.bexp -> QFBV.QFBV.bexp list -> QFBV.QFBV.bexp **)

let rec qfbv_conjs_rec pre_es = function
| [] -> pre_es
| hd :: tl -> qfbv_conjs_rec (qfbv_conj pre_es hd) tl

(** val qfbv_conjs_la : QFBV.QFBV.bexp list -> QFBV.QFBV.bexp **)

let qfbv_conjs_la = function
| [] -> QFBV.QFBV.Btrue
| e :: es0 -> qfbv_conjs_rec (qfbv_conj QFBV.QFBV.Btrue e) es0

(** val qfbv_atom : SSA.SSA.atom -> QFBV.QFBV.exp **)

let qfbv_atom = function
| SSA.SSA.Avar v -> QFBV.QFBV.Evar v
| SSA.SSA.Aconst (_, n) -> QFBV.QFBV.Econst n

(** val bexp_instr : TypEnv.SSATE.env -> SSA.SSA.instr -> QFBV.QFBV.bexp **)

let bexp_instr e = function
| SSA.SSA.Imov (v, a) -> qfbv_eq (qfbv_var v) (qfbv_atom a)
| SSA.SSA.Ishl (v, a, n) ->
  let a_size = SSA.SSA.asize a e in
  qfbv_eq (qfbv_var v) (qfbv_shl (qfbv_atom a) (qfbv_const a_size n))
| SSA.SSA.Icshl (vh, vl, a1, a2, n) ->
  qfbv_conj
    (qfbv_eq (qfbv_var vh)
      (qfbv_high (SSA.SSA.asize a1 e)
        (qfbv_shl (qfbv_concat (qfbv_atom a1) (qfbv_atom a2))
          (qfbv_const (addn (SSA.SSA.asize a1 e) (SSA.SSA.asize a2 e)) n))))
    (qfbv_eq (qfbv_var vl)
      (qfbv_lshr
        (qfbv_low (SSA.SSA.asize a2 e)
          (qfbv_shl (qfbv_concat (qfbv_atom a1) (qfbv_atom a2))
            (qfbv_const (addn (SSA.SSA.asize a1 e) (SSA.SSA.asize a2 e)) n)))
        (qfbv_const (SSA.SSA.asize a2 e) n)))
| SSA.SSA.Icmov (v, c, a1, a2) ->
  qfbv_eq (qfbv_var v) (QFBV.QFBV.Eite
    ((qfbv_eq (qfbv_const (Pervasives.succ 0) (Pervasives.succ 0))
       (qfbv_atom c)), (qfbv_atom a1), (qfbv_atom a2)))
| SSA.SSA.Inot (v, _, a) -> qfbv_eq (qfbv_var v) (qfbv_not (qfbv_atom a))
| SSA.SSA.Iadd (v, a1, a2) ->
  qfbv_eq (qfbv_var v) (qfbv_add (qfbv_atom a1) (qfbv_atom a2))
| SSA.SSA.Iadds (c, v, a1, a2) ->
  qfbv_conj
    (qfbv_eq (qfbv_var c)
      (qfbv_high (Pervasives.succ 0)
        (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
    (qfbv_eq (qfbv_var v)
      (qfbv_low (SSA.SSA.asize a1 e)
        (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
| SSA.SSA.Iadc (v, a1, a2, y) ->
  qfbv_eq (qfbv_var v)
    (qfbv_low (SSA.SSA.asize a1 e)
      (qfbv_add
        (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
        (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y))))
| SSA.SSA.Iadcs (c, v, a1, a2, y) ->
  qfbv_conj
    (qfbv_eq (qfbv_var c)
      (qfbv_high (Pervasives.succ 0)
        (qfbv_add
          (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y)))))
    (qfbv_eq (qfbv_var v)
      (qfbv_low (SSA.SSA.asize a1 e)
        (qfbv_add
          (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y)))))
| SSA.SSA.Isub (v, a1, a2) ->
  qfbv_eq (qfbv_var v) (qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
| SSA.SSA.Isubc (c, v, a1, a2) ->
  qfbv_conj
    (qfbv_eq (qfbv_var c)
      (qfbv_high (Pervasives.succ 0)
        (qfbv_add
          (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_not (qfbv_atom a2))))
          (qfbv_zext (SSA.SSA.asize a1 e)
            (qfbv_const (Pervasives.succ 0) (Pervasives.succ 0))))))
    (qfbv_eq (qfbv_var v)
      (qfbv_low (SSA.SSA.asize a1 e)
        (qfbv_add
          (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_not (qfbv_atom a2))))
          (qfbv_zext (SSA.SSA.asize a1 e)
            (qfbv_const (Pervasives.succ 0) (Pervasives.succ 0))))))
| SSA.SSA.Isubb (b, v, a1, a2) ->
  qfbv_conj
    (qfbv_eq (qfbv_var b)
      (qfbv_high (Pervasives.succ 0)
        (qfbv_sub (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
    (qfbv_eq (qfbv_var v)
      (qfbv_low (SSA.SSA.asize a1 e)
        (qfbv_sub (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
| SSA.SSA.Isbc (v, a1, a2, y) ->
  qfbv_eq (qfbv_var v)
    (qfbv_low (SSA.SSA.asize a1 e)
      (qfbv_add
        (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (qfbv_zext (Pervasives.succ 0) (qfbv_not (qfbv_atom a2))))
        (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y))))
| SSA.SSA.Isbcs (c, v, a1, a2, y) ->
  qfbv_conj
    (qfbv_eq (qfbv_var c)
      (qfbv_high (Pervasives.succ 0)
        (qfbv_add
          (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_not (qfbv_atom a2))))
          (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y)))))
    (qfbv_eq (qfbv_var v)
      (qfbv_low (SSA.SSA.asize a1 e)
        (qfbv_add
          (qfbv_add (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_not (qfbv_atom a2))))
          (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y)))))
| SSA.SSA.Isbb (v, a1, a2, y) ->
  qfbv_eq (qfbv_var v)
    (qfbv_low (SSA.SSA.asize a1 e)
      (qfbv_sub
        (qfbv_sub (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
        (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y))))
| SSA.SSA.Isbbs (b, v, a1, a2, y) ->
  qfbv_conj
    (qfbv_eq (qfbv_var b)
      (qfbv_high (Pervasives.succ 0)
        (qfbv_sub
          (qfbv_sub (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y)))))
    (qfbv_eq (qfbv_var v)
      (qfbv_low (SSA.SSA.asize a1 e)
        (qfbv_sub
          (qfbv_sub (qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom y)))))
| SSA.SSA.Imul (v, a1, a2) ->
  qfbv_eq (qfbv_var v) (qfbv_mul (qfbv_atom a1) (qfbv_atom a2))
| SSA.SSA.Imull (vh, vl, a1, a2) ->
  qfbv_conj
    (qfbv_eq (qfbv_var vh)
      (qfbv_high (SSA.SSA.asize a1 e)
        (qfbv_mul
          (if is_unsigned (SSA.SSA.atyp a1 e)
           then qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom a1)
           else qfbv_sext (SSA.SSA.asize a1 e) (qfbv_atom a1))
          (if is_unsigned (SSA.SSA.atyp a1 e)
           then qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom a2)
           else qfbv_sext (SSA.SSA.asize a1 e) (qfbv_atom a2)))))
    (qfbv_eq (qfbv_var vl)
      (qfbv_low (SSA.SSA.asize a2 e)
        (qfbv_mul
          (if is_unsigned (SSA.SSA.atyp a1 e)
           then qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom a1)
           else qfbv_sext (SSA.SSA.asize a1 e) (qfbv_atom a1))
          (if is_unsigned (SSA.SSA.atyp a1 e)
           then qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom a2)
           else qfbv_sext (SSA.SSA.asize a1 e) (qfbv_atom a2)))))
| SSA.SSA.Imulj (v, a1, a2) ->
  qfbv_eq (qfbv_var v)
    (qfbv_mul
      (if is_unsigned (SSA.SSA.atyp a1 e)
       then qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom a1)
       else qfbv_sext (SSA.SSA.asize a1 e) (qfbv_atom a1))
      (if is_unsigned (SSA.SSA.atyp a1 e)
       then qfbv_zext (SSA.SSA.asize a1 e) (qfbv_atom a2)
       else qfbv_sext (SSA.SSA.asize a1 e) (qfbv_atom a2)))
| SSA.SSA.Isplit (vh, vl, a, n) ->
  if is_unsigned (SSA.SSA.atyp a e)
  then qfbv_conj
         (qfbv_eq (qfbv_var vh)
           (qfbv_lshr (qfbv_atom a) (qfbv_const (SSA.SSA.asize a e) n)))
         (qfbv_eq (qfbv_var vl)
           (qfbv_lshr
             (qfbv_shl (qfbv_atom a)
               (qfbv_const (SSA.SSA.asize a e) (subn (SSA.SSA.asize a e) n)))
             (qfbv_const (SSA.SSA.asize a e) (subn (SSA.SSA.asize a e) n))))
  else qfbv_conj
         (qfbv_eq (qfbv_var vh)
           (qfbv_ashr (qfbv_atom a) (qfbv_const (SSA.SSA.asize a e) n)))
         (qfbv_eq (qfbv_var vl)
           (qfbv_lshr
             (qfbv_shl (qfbv_atom a)
               (qfbv_const (SSA.SSA.asize a e) (subn (SSA.SSA.asize a e) n)))
             (qfbv_const (SSA.SSA.asize a e) (subn (SSA.SSA.asize a e) n))))
| SSA.SSA.Iand (v, _, a1, a2) ->
  qfbv_eq (qfbv_var v) (qfbv_and (qfbv_atom a1) (qfbv_atom a2))
| SSA.SSA.Ior (v, _, a1, a2) ->
  qfbv_eq (qfbv_var v) (qfbv_or (qfbv_atom a1) (qfbv_atom a2))
| SSA.SSA.Ixor (v, _, a1, a2) ->
  qfbv_eq (qfbv_var v) (qfbv_xor (qfbv_atom a1) (qfbv_atom a2))
| SSA.SSA.Icast (v, t0, a) ->
  qfbv_eq (qfbv_var v)
    (if is_unsigned (SSA.SSA.atyp a e)
     then if eq_op nat_eqType (Obj.magic sizeof_typ t0)
               (Obj.magic sizeof_typ (SSA.SSA.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t0))
                    (sizeof_typ (SSA.SSA.atyp a e))
               then qfbv_low (sizeof_typ t0) (qfbv_atom a)
               else qfbv_zext
                      (subn (sizeof_typ t0) (sizeof_typ (SSA.SSA.atyp a e)))
                      (qfbv_atom a)
     else if eq_op nat_eqType (Obj.magic sizeof_typ t0)
               (Obj.magic sizeof_typ (SSA.SSA.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t0))
                    (sizeof_typ (SSA.SSA.atyp a e))
               then qfbv_low (sizeof_typ t0) (qfbv_atom a)
               else qfbv_sext
                      (subn (sizeof_typ t0) (sizeof_typ (SSA.SSA.atyp a e)))
                      (qfbv_atom a))
| SSA.SSA.Ivpc (v, t0, a) ->
  qfbv_eq (qfbv_var v)
    (if is_unsigned (SSA.SSA.atyp a e)
     then if eq_op nat_eqType (Obj.magic sizeof_typ t0)
               (Obj.magic sizeof_typ (SSA.SSA.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t0))
                    (sizeof_typ (SSA.SSA.atyp a e))
               then qfbv_low (sizeof_typ t0) (qfbv_atom a)
               else qfbv_zext
                      (subn (sizeof_typ t0) (sizeof_typ (SSA.SSA.atyp a e)))
                      (qfbv_atom a)
     else if eq_op nat_eqType (Obj.magic sizeof_typ t0)
               (Obj.magic sizeof_typ (SSA.SSA.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t0))
                    (sizeof_typ (SSA.SSA.atyp a e))
               then qfbv_low (sizeof_typ t0) (qfbv_atom a)
               else qfbv_sext
                      (subn (sizeof_typ t0) (sizeof_typ (SSA.SSA.atyp a e)))
                      (qfbv_atom a))
| SSA.SSA.Ijoin (v, ah, al) ->
  qfbv_eq (qfbv_var v) (qfbv_concat (qfbv_atom ah) (qfbv_atom al))
| SSA.SSA.Iassume b -> let (_, rbexp0) = b in bexp_rbexp rbexp0
| _ -> QFBV.QFBV.Btrue

(** val bexp_program :
    TypEnv.SSATE.env -> SSA.SSA.program -> QFBV.QFBV.bexp list **)

let rec bexp_program e = function
| [] -> []
| hd :: tl ->
  (bexp_instr e hd) :: (bexp_program (SSA.SSA.instr_succ_typenv hd e) tl)

type bexp_spec = { binputs : TypEnv.SSATE.env; bpre : QFBV.QFBV.bexp;
                   bprog : QFBV.QFBV.bexp list; bpost : QFBV.QFBV.bexp }

(** val bexp_of_rspec : TypEnv.SSATE.env -> SSA.SSA.rspec -> bexp_spec **)

let bexp_of_rspec e s =
  { binputs = (SSA.SSA.program_succ_typenv (SSA.SSA.rsprog s) e); bpre =
    (bexp_rbexp (SSA.SSA.rspre s)); bprog =
    (bexp_program e (SSA.SSA.rsprog s)); bpost =
    (bexp_rbexp (SSA.SSA.rspost s)) }

(** val rngred_rspec_split_la : SSA.SSA.spec -> QFBV.QFBV.bexp list **)

let rngred_rspec_split_la s =
  let bs = bexp_of_rspec (SSA.SSA.sinputs s) (SSA.SSA.rspec_of_spec s) in
  map (fun post ->
    qfbv_imp (qfbv_conj bs.bpre (qfbv_conjs_la bs.bprog)) post)
    (QFBV.QFBV.split_conj bs.bpost)

(** val bexp_atom_uaddB_algsnd :
    SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_uaddB_algsnd a1 a2 =
  qfbv_lneg (qfbv_uaddo (qfbv_atom a1) (qfbv_atom a2))

(** val bexp_atom_saddB_algsnd :
    SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_saddB_algsnd a1 a2 =
  qfbv_lneg (qfbv_saddo (qfbv_atom a1) (qfbv_atom a2))

(** val bexp_atom_addB_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_addB_algsnd e a1 a2 =
  if is_unsigned (SSA.SSA.atyp a1 e)
  then bexp_atom_uaddB_algsnd a1 a2
  else bexp_atom_saddB_algsnd a1 a2

(** val bexp_atom_adds_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_adds_algsnd e a1 a2 =
  if is_unsigned (SSA.SSA.atyp a1 e)
  then QFBV.QFBV.Btrue
  else bexp_atom_saddB_algsnd a1 a2

(** val bexp_atom_uadcB_algsnd :
    int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_uadcB_algsnd a_size a1 a2 ac =
  qfbv_conj (qfbv_lneg (qfbv_uaddo (qfbv_atom a1) (qfbv_atom a2)))
    (qfbv_lneg
      (qfbv_uaddo (qfbv_add (qfbv_atom a1) (qfbv_atom a2))
        (qfbv_zext (subn a_size (Pervasives.succ 0)) (qfbv_atom ac))))

(** val bexp_atom_sadcB_algsnd :
    int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_sadcB_algsnd a_size a1 a2 ac =
  qfbv_conj (qfbv_lneg (qfbv_saddo (qfbv_atom a1) (qfbv_atom a2)))
    (qfbv_lneg
      (qfbv_saddo (qfbv_add (qfbv_atom a1) (qfbv_atom a2))
        (qfbv_zext (subn a_size (Pervasives.succ 0)) (qfbv_atom ac))))

(** val bexp_atom_adcB_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
    QFBV.QFBV.bexp **)

let bexp_atom_adcB_algsnd e a1 a2 ac =
  let a_typ = SSA.SSA.atyp a1 e in
  let a_size = SSA.SSA.asize a1 e in
  if is_unsigned a_typ
  then bexp_atom_uadcB_algsnd a_size a1 a2 ac
  else bexp_atom_sadcB_algsnd a_size a1 a2 ac

(** val bexp_atom_adcs_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
    QFBV.QFBV.bexp **)

let bexp_atom_adcs_algsnd e a1 a2 ac =
  let a_typ = SSA.SSA.atyp a1 e in
  let a_size = SSA.SSA.asize a1 e in
  if is_unsigned a_typ
  then QFBV.QFBV.Btrue
  else bexp_atom_sadcB_algsnd a_size a1 a2 ac

(** val bexp_atom_usubB_algsnd :
    SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_usubB_algsnd a1 a2 =
  qfbv_lneg (qfbv_usubo (qfbv_atom a1) (qfbv_atom a2))

(** val bexp_atom_ssubB_algsnd :
    SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_ssubB_algsnd a1 a2 =
  qfbv_lneg (qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2))

(** val bexp_atom_subB_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_subB_algsnd e a1 a2 =
  if is_unsigned (SSA.SSA.atyp a1 e)
  then bexp_atom_usubB_algsnd a1 a2
  else bexp_atom_ssubB_algsnd a1 a2

(** val bexp_atom_subc_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_subc_algsnd e a1 a2 =
  if is_unsigned (SSA.SSA.atyp a1 e)
  then QFBV.QFBV.Btrue
  else bexp_atom_ssubB_algsnd a1 a2

(** val bexp_atom_subb_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_subb_algsnd e a1 a2 =
  if is_unsigned (SSA.SSA.atyp a1 e)
  then QFBV.QFBV.Btrue
  else bexp_atom_ssubB_algsnd a1 a2

(** val bexp_atom_usbbB_algsnd :
    int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_usbbB_algsnd a_size a1 a2 ab =
  qfbv_conj (qfbv_lneg (qfbv_usubo (qfbv_atom a1) (qfbv_atom a2)))
    (qfbv_lneg
      (qfbv_usubo (qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (qfbv_zext (subn a_size (Pervasives.succ 0)) (qfbv_atom ab))))

(** val bexp_atom_ssbbB_algsnd :
    int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_ssbbB_algsnd a_size a1 a2 ab =
  qfbv_conj (qfbv_lneg (qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2)))
    (qfbv_lneg
      (qfbv_ssubo (qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (qfbv_zext (subn a_size (Pervasives.succ 0)) (qfbv_atom ab))))

(** val bexp_atom_sbbB_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
    QFBV.QFBV.bexp **)

let bexp_atom_sbbB_algsnd e a1 a2 ab =
  let a_typ = SSA.SSA.atyp a1 e in
  let a_size = SSA.SSA.asize a1 e in
  if is_unsigned a_typ
  then bexp_atom_usbbB_algsnd a_size a1 a2 ab
  else bexp_atom_ssbbB_algsnd a_size a1 a2 ab

(** val bexp_atom_sbbs_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
    QFBV.QFBV.bexp **)

let bexp_atom_sbbs_algsnd e a1 a2 ab =
  let a_typ = SSA.SSA.atyp a1 e in
  let a_size = SSA.SSA.asize a1 e in
  if is_unsigned a_typ
  then QFBV.QFBV.Btrue
  else bexp_atom_ssbbB_algsnd a_size a1 a2 ab

(** val bexp_atom_usbcB_algsnd :
    int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_usbcB_algsnd a_size a1 a2 ac =
  qfbv_conj (qfbv_lneg (qfbv_usubo (qfbv_atom a1) (qfbv_atom a2)))
    (qfbv_lneg
      (qfbv_usubo (qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (qfbv_zext (subn a_size (Pervasives.succ 0))
          (qfbv_sub (qfbv_one (Pervasives.succ 0)) (qfbv_atom ac)))))

(** val bexp_atom_ssbcB_algsnd :
    int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_ssbcB_algsnd a_size a1 a2 ac =
  qfbv_conj (qfbv_lneg (qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2)))
    (qfbv_lneg
      (qfbv_ssubo (qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (qfbv_zext (subn a_size (Pervasives.succ 0))
          (qfbv_sub (qfbv_one (Pervasives.succ 0)) (qfbv_atom ac)))))

(** val bexp_atom_sbcB_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
    QFBV.QFBV.bexp **)

let bexp_atom_sbcB_algsnd e a1 a2 ac =
  let a_typ = SSA.SSA.atyp a1 e in
  let a_size = SSA.SSA.asize a1 e in
  if is_unsigned a_typ
  then bexp_atom_usbcB_algsnd a_size a1 a2 ac
  else bexp_atom_ssbcB_algsnd a_size a1 a2 ac

(** val bexp_atom_sbcs_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
    QFBV.QFBV.bexp **)

let bexp_atom_sbcs_algsnd e a1 a2 ac =
  let a_typ = SSA.SSA.atyp a1 e in
  let a_size = SSA.SSA.asize a1 e in
  if is_unsigned a_typ
  then QFBV.QFBV.Btrue
  else bexp_atom_ssbcB_algsnd a_size a1 a2 ac

(** val bexp_atom_mulB_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_mulB_algsnd e a1 a2 =
  if is_unsigned (SSA.SSA.atyp a1 e)
  then qfbv_lneg (qfbv_umulo (qfbv_atom a1) (qfbv_atom a2))
  else qfbv_lneg (qfbv_smulo (qfbv_atom a1) (qfbv_atom a2))

(** val bexp_atom_shl_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> int -> QFBV.QFBV.bexp **)

let bexp_atom_shl_algsnd e a n =
  if is_unsigned (SSA.SSA.atyp a e)
  then qfbv_eq (qfbv_high n (qfbv_atom a)) (qfbv_zero n)
  else qfbv_disj
         (qfbv_eq (qfbv_high (addn n (Pervasives.succ 0)) (qfbv_atom a))
           (qfbv_zero (addn n (Pervasives.succ 0))))
         (qfbv_eq (qfbv_high (addn n (Pervasives.succ 0)) (qfbv_atom a))
           (qfbv_not (qfbv_zero (addn n (Pervasives.succ 0)))))

(** val bexp_atom_cshl_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> int -> QFBV.QFBV.bexp **)

let bexp_atom_cshl_algsnd e a1 a2 n =
  if is_unsigned (SSA.SSA.atyp a1 e)
  then qfbv_eq (qfbv_high n (qfbv_concat (qfbv_atom a1) (qfbv_atom a2)))
         (qfbv_zero n)
  else qfbv_disj
         (qfbv_eq
           (qfbv_high (addn n (Pervasives.succ 0))
             (qfbv_concat (qfbv_atom a1) (qfbv_atom a2)))
           (qfbv_zero (addn n (Pervasives.succ 0))))
         (qfbv_eq
           (qfbv_high (addn n (Pervasives.succ 0))
             (qfbv_concat (qfbv_atom a1) (qfbv_atom a2)))
           (qfbv_not (qfbv_zero (addn n (Pervasives.succ 0)))))

(** val bexp_atom_vpc_algsnd :
    TypEnv.SSATE.env -> typ -> SSA.SSA.atom -> QFBV.QFBV.bexp **)

let bexp_atom_vpc_algsnd e t0 a =
  if is_unsigned (SSA.SSA.atyp a e)
  then if is_unsigned t0
       then if leq (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0)
            then qfbv_true
            else qfbv_eq
                   (qfbv_high
                     (subn (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0))
                     (qfbv_atom a))
                   (qfbv_zero
                     (subn (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0)))
       else if leq (Pervasives.succ (sizeof_typ (SSA.SSA.atyp a e)))
                 (sizeof_typ t0)
            then qfbv_true
            else qfbv_eq
                   (qfbv_high
                     (addn
                       (subn (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0))
                       (Pervasives.succ 0)) (qfbv_atom a))
                   (qfbv_zero
                     (addn
                       (subn (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0))
                       (Pervasives.succ 0)))
  else if is_unsigned t0
       then if leq (subn (sizeof_typ (SSA.SSA.atyp a e)) (Pervasives.succ 0))
                 (sizeof_typ t0)
            then qfbv_eq (qfbv_high (Pervasives.succ 0) (qfbv_atom a))
                   (qfbv_zero (Pervasives.succ 0))
            else qfbv_eq
                   (qfbv_high
                     (subn (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0))
                     (qfbv_atom a))
                   (qfbv_zero
                     (subn (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0)))
       else if leq (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0)
            then qfbv_true
            else qfbv_eq
                   (qfbv_sext
                     (subn (sizeof_typ (SSA.SSA.atyp a e)) (sizeof_typ t0))
                     (qfbv_low (sizeof_typ t0) (qfbv_atom a))) (qfbv_atom a)

(** val bexp_instr_algsnd :
    TypEnv.SSATE.env -> SSA.SSA.instr -> QFBV.QFBV.bexp **)

let bexp_instr_algsnd e = function
| SSA.SSA.Ishl (_, a, n) -> bexp_atom_shl_algsnd e a n
| SSA.SSA.Icshl (_, _, a1, a2, n) -> bexp_atom_cshl_algsnd e a1 a2 n
| SSA.SSA.Iadd (_, a1, a2) -> bexp_atom_addB_algsnd e a1 a2
| SSA.SSA.Iadds (_, _, a1, a2) -> bexp_atom_adds_algsnd e a1 a2
| SSA.SSA.Iadc (_, a1, a2, ac) -> bexp_atom_adcB_algsnd e a1 a2 ac
| SSA.SSA.Iadcs (_, _, a1, a2, ac) -> bexp_atom_adcs_algsnd e a1 a2 ac
| SSA.SSA.Isub (_, a1, a2) -> bexp_atom_subB_algsnd e a1 a2
| SSA.SSA.Isubc (_, _, a1, a2) -> bexp_atom_subc_algsnd e a1 a2
| SSA.SSA.Isubb (_, _, a1, a2) -> bexp_atom_subb_algsnd e a1 a2
| SSA.SSA.Isbc (_, a1, a2, ac) -> bexp_atom_sbcB_algsnd e a1 a2 ac
| SSA.SSA.Isbcs (_, _, a1, a2, ac) -> bexp_atom_sbcs_algsnd e a1 a2 ac
| SSA.SSA.Isbb (_, a1, a2, ab) -> bexp_atom_sbbB_algsnd e a1 a2 ab
| SSA.SSA.Isbbs (_, _, a1, a2, ab) -> bexp_atom_sbbs_algsnd e a1 a2 ab
| SSA.SSA.Imul (_, a1, a2) -> bexp_atom_mulB_algsnd e a1 a2
| SSA.SSA.Ivpc (_, t0, a) -> bexp_atom_vpc_algsnd e t0 a
| _ -> qfbv_true

(** val bexp_program_algsnd_split_fixed_final_rec :
    TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> SSA.SSA.instr list ->
    (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list **)

let rec bexp_program_algsnd_split_fixed_final_rec e pre_es = function
| [] -> []
| hd :: tl ->
  (pre_es,
    (bexp_instr_algsnd e hd)) :: (bexp_program_algsnd_split_fixed_final_rec e
                                   (rcons pre_es
                                     (bexp_instr e (SSA.SSA.rng_instr hd)))
                                   tl)

(** val bexp_program_algsnd_split_fixed_final :
    TypEnv.SSATE.env -> SSA.SSA.instr list -> (QFBV.QFBV.bexp
    list * QFBV.QFBV.bexp) list **)

let bexp_program_algsnd_split_fixed_final e p =
  bexp_program_algsnd_split_fixed_final_rec e [] p
