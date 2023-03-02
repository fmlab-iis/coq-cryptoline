open DSLRaw
open NBitsDef
open NBitsOp
open Options0
open Seqs
open Typ
open Eqtype
open Seq
open Ssrnat

type bexp_spec = { binputs : TypEnv.SSATE.env; bpre : QFBV.QFBV.bexp;
                   bprog : QFBV.QFBV.bexp list; bpost : QFBV.QFBV.bexp }

(** val exp_rexp : SSALite.SSALite.rexp -> QFBV.QFBV.exp **)

let rec exp_rexp = function
| Rvar v -> QFBV.QFBV.qfbv_var v
| Rconst (_, n) -> QFBV.QFBV.Econst n
| Runop (_, op, e0) ->
  (match op with
   | Rnegb -> QFBV.QFBV.qfbv_neg (exp_rexp e0)
   | Rnotb -> QFBV.QFBV.qfbv_not (exp_rexp e0))
| Rbinop (_, op, e1, e2) ->
  (match op with
   | Radd -> QFBV.QFBV.qfbv_add (exp_rexp e1) (exp_rexp e2)
   | Rsub -> QFBV.QFBV.qfbv_sub (exp_rexp e1) (exp_rexp e2)
   | Rmul -> QFBV.QFBV.qfbv_mul (exp_rexp e1) (exp_rexp e2)
   | Rumod -> QFBV.QFBV.qfbv_mod (exp_rexp e1) (exp_rexp e2)
   | Rsrem -> QFBV.QFBV.qfbv_srem (exp_rexp e1) (exp_rexp e2)
   | Rsmod -> QFBV.QFBV.qfbv_smod (exp_rexp e1) (exp_rexp e2)
   | Randb -> QFBV.QFBV.qfbv_and (exp_rexp e1) (exp_rexp e2)
   | Rorb -> QFBV.QFBV.qfbv_or (exp_rexp e1) (exp_rexp e2)
   | Rxorb -> QFBV.QFBV.qfbv_xor (exp_rexp e1) (exp_rexp e2))
| Ruext (_, e0, n) -> QFBV.QFBV.qfbv_zext n (exp_rexp e0)
| Rsext (_, e0, n) -> QFBV.QFBV.qfbv_sext n (exp_rexp e0)

(** val bexp_rbexp : SSALite.SSALite.rbexp -> QFBV.QFBV.bexp **)

let rec bexp_rbexp = function
| Rtrue -> QFBV.QFBV.qfbv_true
| Req (_, e1, e2) -> QFBV.QFBV.qfbv_eq (exp_rexp e1) (exp_rexp e2)
| Rcmp (_, op, e1, e2) ->
  (match op with
   | Rult -> QFBV.QFBV.qfbv_ult (exp_rexp e1) (exp_rexp e2)
   | Rule -> QFBV.QFBV.qfbv_ule (exp_rexp e1) (exp_rexp e2)
   | Rugt -> QFBV.QFBV.qfbv_ugt (exp_rexp e1) (exp_rexp e2)
   | Ruge -> QFBV.QFBV.qfbv_uge (exp_rexp e1) (exp_rexp e2)
   | Rslt -> QFBV.QFBV.qfbv_slt (exp_rexp e1) (exp_rexp e2)
   | Rsle -> QFBV.QFBV.qfbv_sle (exp_rexp e1) (exp_rexp e2)
   | Rsgt -> QFBV.QFBV.qfbv_sgt (exp_rexp e1) (exp_rexp e2)
   | Rsge -> QFBV.QFBV.qfbv_sge (exp_rexp e1) (exp_rexp e2))
| Rneg e0 -> QFBV.QFBV.qfbv_lneg (bexp_rbexp e0)
| Rand (e1, e2) -> QFBV.QFBV.qfbv_conj (bexp_rbexp e1) (bexp_rbexp e2)
| Ror (e1, e2) -> QFBV.QFBV.qfbv_disj (bexp_rbexp e1) (bexp_rbexp e2)

(** val qfbv_atom : atom -> QFBV.QFBV.exp **)

let qfbv_atom = function
| Avar v -> QFBV.QFBV.Evar v
| Aconst (_, n) -> QFBV.QFBV.Econst n

(** val bexp_instr :
    TypEnv.SSATE.env -> SSALite.SSALite.instr -> QFBV.QFBV.bexp **)

let bexp_instr e = function
| SSALite.SSALite.Imov (v, a) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v) (qfbv_atom a)
| SSALite.SSALite.Ishl (v, a, n) ->
  let a_size = SSALite.SSALite.asize a e in
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_shl (qfbv_atom a) (QFBV.QFBV.qfbv_const a_size n))
| SSALite.SSALite.Icshl (vh, vl, a1, a2, n) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vh)
      (QFBV.QFBV.qfbv_high (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_shl
          (QFBV.QFBV.qfbv_concat (qfbv_atom a1) (qfbv_atom a2))
          (QFBV.QFBV.qfbv_const
            (addn (SSALite.SSALite.asize a1 e) (SSALite.SSALite.asize a2 e))
            n))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vl)
      (QFBV.QFBV.qfbv_lshr
        (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a2 e)
          (QFBV.QFBV.qfbv_shl
            (QFBV.QFBV.qfbv_concat (qfbv_atom a1) (qfbv_atom a2))
            (QFBV.QFBV.qfbv_const
              (addn (SSALite.SSALite.asize a1 e) (SSALite.SSALite.asize a2 e))
              n))) (QFBV.QFBV.qfbv_const (SSALite.SSALite.asize a2 e) n)))
| SSALite.SSALite.Icmov (v, c, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v) (QFBV.QFBV.Eite
    ((QFBV.QFBV.qfbv_eq
       (QFBV.QFBV.qfbv_const (Pervasives.succ 0) (Pervasives.succ 0))
       (qfbv_atom c)), (qfbv_atom a1), (qfbv_atom a2)))
| SSALite.SSALite.Inot (v, _, a) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v) (QFBV.QFBV.qfbv_not (qfbv_atom a))
| SSALite.SSALite.Iadd (v, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_add (qfbv_atom a1) (qfbv_atom a2))
| SSALite.SSALite.Iadds (c, v, a1, a2) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var c)
      (QFBV.QFBV.qfbv_high (Pervasives.succ 0)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
      (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
| SSALite.SSALite.Iadc (v, a1, a2, y) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
      (QFBV.QFBV.qfbv_add
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
        (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y))))
| SSALite.SSALite.Iadcs (c, v, a1, a2, y) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var c)
      (QFBV.QFBV.qfbv_high (Pervasives.succ 0)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_add
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y)))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
      (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_add
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y)))))
| SSALite.SSALite.Isub (v, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
| SSALite.SSALite.Isubc (c, v, a1, a2) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var c)
      (QFBV.QFBV.qfbv_high (Pervasives.succ 0)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_add
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0)
              (QFBV.QFBV.qfbv_not (qfbv_atom a2))))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e)
            (QFBV.QFBV.qfbv_const (Pervasives.succ 0) (Pervasives.succ 0))))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
      (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_add
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0)
              (QFBV.QFBV.qfbv_not (qfbv_atom a2))))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e)
            (QFBV.QFBV.qfbv_const (Pervasives.succ 0) (Pervasives.succ 0))))))
| SSALite.SSALite.Isubb (b, v, a1, a2) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var b)
      (QFBV.QFBV.qfbv_high (Pervasives.succ 0)
        (QFBV.QFBV.qfbv_sub
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
      (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_sub
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))))
| SSALite.SSALite.Isbc (v, a1, a2, y) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
      (QFBV.QFBV.qfbv_add
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0)
            (QFBV.QFBV.qfbv_not (qfbv_atom a2))))
        (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y))))
| SSALite.SSALite.Isbcs (c, v, a1, a2, y) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var c)
      (QFBV.QFBV.qfbv_high (Pervasives.succ 0)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_add
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0)
              (QFBV.QFBV.qfbv_not (qfbv_atom a2))))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y)))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
      (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_add
          (QFBV.QFBV.qfbv_add
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0)
              (QFBV.QFBV.qfbv_not (qfbv_atom a2))))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y)))))
| SSALite.SSALite.Isbb (v, a1, a2, y) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
      (QFBV.QFBV.qfbv_sub
        (QFBV.QFBV.qfbv_sub
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
          (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
        (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y))))
| SSALite.SSALite.Isbbs (b, v, a1, a2, y) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var b)
      (QFBV.QFBV.qfbv_high (Pervasives.succ 0)
        (QFBV.QFBV.qfbv_sub
          (QFBV.QFBV.qfbv_sub
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y)))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
      (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_sub
          (QFBV.QFBV.qfbv_sub
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a1))
            (QFBV.QFBV.qfbv_zext (Pervasives.succ 0) (qfbv_atom a2)))
          (QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom y)))))
| SSALite.SSALite.Imul (v, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_mul (qfbv_atom a1) (qfbv_atom a2))
| SSALite.SSALite.Imull (vh, vl, a1, a2) ->
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vh)
      (QFBV.QFBV.qfbv_high (SSALite.SSALite.asize a1 e)
        (QFBV.QFBV.qfbv_mul
          (if is_unsigned (SSALite.SSALite.atyp a1 e)
           then QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a1)
           else QFBV.QFBV.qfbv_sext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a1))
          (if is_unsigned (SSALite.SSALite.atyp a1 e)
           then QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a2)
           else QFBV.QFBV.qfbv_sext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a2)))))
    (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vl)
      (QFBV.QFBV.qfbv_low (SSALite.SSALite.asize a2 e)
        (QFBV.QFBV.qfbv_mul
          (if is_unsigned (SSALite.SSALite.atyp a1 e)
           then QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a1)
           else QFBV.QFBV.qfbv_sext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a1))
          (if is_unsigned (SSALite.SSALite.atyp a1 e)
           then QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a2)
           else QFBV.QFBV.qfbv_sext (SSALite.SSALite.asize a1 e)
                  (qfbv_atom a2)))))
| SSALite.SSALite.Imulj (v, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_mul
      (if is_unsigned (SSALite.SSALite.atyp a1 e)
       then QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom a1)
       else QFBV.QFBV.qfbv_sext (SSALite.SSALite.asize a1 e) (qfbv_atom a1))
      (if is_unsigned (SSALite.SSALite.atyp a1 e)
       then QFBV.QFBV.qfbv_zext (SSALite.SSALite.asize a1 e) (qfbv_atom a2)
       else QFBV.QFBV.qfbv_sext (SSALite.SSALite.asize a1 e) (qfbv_atom a2)))
| SSALite.SSALite.Isplit (vh, vl, a, n) ->
  if is_unsigned (SSALite.SSALite.atyp a e)
  then QFBV.QFBV.qfbv_conj
         (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vh)
           (QFBV.QFBV.qfbv_lshr (qfbv_atom a)
             (QFBV.QFBV.qfbv_const (SSALite.SSALite.asize a e) n)))
         (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vl)
           (QFBV.QFBV.qfbv_lshr
             (QFBV.QFBV.qfbv_shl (qfbv_atom a)
               (QFBV.QFBV.qfbv_const (SSALite.SSALite.asize a e)
                 (subn (SSALite.SSALite.asize a e) n)))
             (QFBV.QFBV.qfbv_const (SSALite.SSALite.asize a e)
               (subn (SSALite.SSALite.asize a e) n))))
  else QFBV.QFBV.qfbv_conj
         (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vh)
           (QFBV.QFBV.qfbv_ashr (qfbv_atom a)
             (QFBV.QFBV.qfbv_const (SSALite.SSALite.asize a e) n)))
         (QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var vl)
           (QFBV.QFBV.qfbv_lshr
             (QFBV.QFBV.qfbv_shl (qfbv_atom a)
               (QFBV.QFBV.qfbv_const (SSALite.SSALite.asize a e)
                 (subn (SSALite.SSALite.asize a e) n)))
             (QFBV.QFBV.qfbv_const (SSALite.SSALite.asize a e)
               (subn (SSALite.SSALite.asize a e) n))))
| SSALite.SSALite.Iand (v, _, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_and (qfbv_atom a1) (qfbv_atom a2))
| SSALite.SSALite.Ior (v, _, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_or (qfbv_atom a1) (qfbv_atom a2))
| SSALite.SSALite.Ixor (v, _, a1, a2) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_xor (qfbv_atom a1) (qfbv_atom a2))
| SSALite.SSALite.Icast (v, t, a) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (if is_unsigned (SSALite.SSALite.atyp a e)
     then if eq_op nat_eqType (Obj.magic sizeof_typ t)
               (Obj.magic sizeof_typ (SSALite.SSALite.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t))
                    (sizeof_typ (SSALite.SSALite.atyp a e))
               then QFBV.QFBV.qfbv_low (sizeof_typ t) (qfbv_atom a)
               else QFBV.QFBV.qfbv_zext
                      (subn (sizeof_typ t)
                        (sizeof_typ (SSALite.SSALite.atyp a e))) (qfbv_atom a)
     else if eq_op nat_eqType (Obj.magic sizeof_typ t)
               (Obj.magic sizeof_typ (SSALite.SSALite.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t))
                    (sizeof_typ (SSALite.SSALite.atyp a e))
               then QFBV.QFBV.qfbv_low (sizeof_typ t) (qfbv_atom a)
               else QFBV.QFBV.qfbv_sext
                      (subn (sizeof_typ t)
                        (sizeof_typ (SSALite.SSALite.atyp a e))) (qfbv_atom a))
| SSALite.SSALite.Ivpc (v, t, a) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (if is_unsigned (SSALite.SSALite.atyp a e)
     then if eq_op nat_eqType (Obj.magic sizeof_typ t)
               (Obj.magic sizeof_typ (SSALite.SSALite.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t))
                    (sizeof_typ (SSALite.SSALite.atyp a e))
               then QFBV.QFBV.qfbv_low (sizeof_typ t) (qfbv_atom a)
               else QFBV.QFBV.qfbv_zext
                      (subn (sizeof_typ t)
                        (sizeof_typ (SSALite.SSALite.atyp a e))) (qfbv_atom a)
     else if eq_op nat_eqType (Obj.magic sizeof_typ t)
               (Obj.magic sizeof_typ (SSALite.SSALite.atyp a e))
          then qfbv_atom a
          else if leq (Pervasives.succ (sizeof_typ t))
                    (sizeof_typ (SSALite.SSALite.atyp a e))
               then QFBV.QFBV.qfbv_low (sizeof_typ t) (qfbv_atom a)
               else QFBV.QFBV.qfbv_sext
                      (subn (sizeof_typ t)
                        (sizeof_typ (SSALite.SSALite.atyp a e))) (qfbv_atom a))
| SSALite.SSALite.Ijoin (v, ah, al) ->
  QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_var v)
    (QFBV.QFBV.qfbv_concat (qfbv_atom ah) (qfbv_atom al))
| SSALite.SSALite.Iassume b -> let (_, rbexp0) = b in bexp_rbexp rbexp0
| _ -> QFBV.QFBV.Btrue

(** val bexp_program :
    TypEnv.SSATE.env -> SSALite.SSALite.program -> QFBV.QFBV.bexp list **)

let rec bexp_program e = function
| [] -> []
| hd :: tl ->
  (bexp_instr e hd) :: (bexp_program (SSALite.SSALite.instr_succ_typenv hd e)
                         tl)

(** val bexp_of_rspec :
    TypEnv.SSATE.env -> SSALite.SSALite.rspec -> bexp_spec **)

let bexp_of_rspec e s =
  { binputs =
    (SSALite.SSALite.program_succ_typenv (SSALite.SSALite.rsprog s) e);
    bpre = (bexp_rbexp (SSALite.SSALite.rspre s)); bprog =
    (bexp_program e (SSALite.SSALite.rsprog s)); bpost =
    (bexp_rbexp (SSALite.SSALite.rspost s)) }

(** val rngred_rspec_split_la :
    SSALite.SSALite.rspec -> QFBV.QFBV.bexp list **)

let rngred_rspec_split_la s =
  let bs = bexp_of_rspec (SSALite.SSALite.rsinputs s) s in
  map (fun post ->
    QFBV.QFBV.qfbv_imp
      (QFBV.QFBV.qfbv_conj bs.bpre (QFBV.QFBV.qfbv_conjs_la bs.bprog)) post)
    (QFBV.QFBV.split_conj bs.bpost)

(** val rngred_rspec_split_las :
    SSALite.SSALite.rspec list -> QFBV.QFBV.bexp list **)

let rngred_rspec_split_las rs =
  tflatten (tmap rngred_rspec_split_la rs)

(** val rngred_rspec_slice_split_la :
    options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list **)

let rngred_rspec_slice_split_la o s =
  rngred_rspec_split_las
    (tmap (SSALite.SSALite.slice_rspec o) (SSALite.SSALite.split_rspec s))

(** val bexp_atom_uaddB_algsnd : atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_uaddB_algsnd a1 a2 =
  match a1 with
  | Avar _ ->
    QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_uaddo (qfbv_atom a1) (qfbv_atom a2))
  | Aconst (_, bs1) ->
    (match a2 with
     | Avar _ ->
       QFBV.QFBV.qfbv_lneg
         (QFBV.QFBV.qfbv_uaddo (qfbv_atom a1) (qfbv_atom a2))
     | Aconst (_, bs2) ->
       if coq_Uaddo bs1 bs2 then QFBV.QFBV.qfbv_false else QFBV.QFBV.qfbv_true)

(** val bexp_atom_saddB_algsnd : atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_saddB_algsnd a1 a2 =
  match a1 with
  | Avar _ ->
    QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_saddo (qfbv_atom a1) (qfbv_atom a2))
  | Aconst (_, bs1) ->
    (match a2 with
     | Avar _ ->
       QFBV.QFBV.qfbv_lneg
         (QFBV.QFBV.qfbv_saddo (qfbv_atom a1) (qfbv_atom a2))
     | Aconst (_, bs2) ->
       if coq_Saddo bs1 bs2 then QFBV.QFBV.qfbv_false else QFBV.QFBV.qfbv_true)

(** val bexp_atom_addB_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_addB_algsnd e a1 a2 =
  if is_unsigned (SSALite.SSALite.atyp a1 e)
  then bexp_atom_uaddB_algsnd a1 a2
  else bexp_atom_saddB_algsnd a1 a2

(** val bexp_atom_adds_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_adds_algsnd e a1 a2 =
  if is_unsigned (SSALite.SSALite.atyp a1 e)
  then QFBV.QFBV.Btrue
  else bexp_atom_saddB_algsnd a1 a2

(** val bexp_atom_uadcB_algsnd :
    int -> atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_uadcB_algsnd a_size a1 a2 ac =
  match a1 with
  | Avar _ ->
    QFBV.QFBV.qfbv_conj
      (QFBV.QFBV.qfbv_lneg
        (QFBV.QFBV.qfbv_uaddo (qfbv_atom a1) (qfbv_atom a2)))
      (QFBV.QFBV.qfbv_lneg
        (QFBV.QFBV.qfbv_uaddo
          (QFBV.QFBV.qfbv_add (qfbv_atom a1) (qfbv_atom a2))
          (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0))
            (qfbv_atom ac))))
  | Aconst (_, bs1) ->
    (match a2 with
     | Avar _ ->
       QFBV.QFBV.qfbv_conj
         (QFBV.QFBV.qfbv_lneg
           (QFBV.QFBV.qfbv_uaddo (qfbv_atom a1) (qfbv_atom a2)))
         (QFBV.QFBV.qfbv_lneg
           (QFBV.QFBV.qfbv_uaddo
             (QFBV.QFBV.qfbv_add (qfbv_atom a1) (qfbv_atom a2))
             (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0))
               (qfbv_atom ac))))
     | Aconst (_, bs2) ->
       (match ac with
        | Avar _ ->
          if coq_Uaddo bs1 bs2
          then QFBV.QFBV.qfbv_false
          else if coq_Uaddo (addB bs1 bs2)
                    (zext (subn a_size (Pervasives.succ 0)) (b1 :: []))
               then QFBV.QFBV.qfbv_lneg
                      (QFBV.QFBV.qfbv_uaddo (QFBV.QFBV.Econst (addB bs1 bs2))
                        (QFBV.QFBV.qfbv_zext
                          (subn a_size (Pervasives.succ 0)) (qfbv_atom ac)))
               else QFBV.QFBV.qfbv_true
        | Aconst (_, c) ->
          if (||) (coq_Uaddo bs1 bs2)
               (coq_Uaddo (addB bs1 bs2)
                 (zext (subn a_size (Pervasives.succ 0)) c))
          then QFBV.QFBV.qfbv_false
          else QFBV.QFBV.qfbv_true))

(** val bexp_atom_sadcB_algsnd :
    int -> atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_sadcB_algsnd a_size a1 a2 ac =
  match a1 with
  | Avar _ ->
    QFBV.QFBV.qfbv_conj
      (QFBV.QFBV.qfbv_lneg
        (QFBV.QFBV.qfbv_saddo (qfbv_atom a1) (qfbv_atom a2)))
      (QFBV.QFBV.qfbv_lneg
        (QFBV.QFBV.qfbv_saddo
          (QFBV.QFBV.qfbv_add (qfbv_atom a1) (qfbv_atom a2))
          (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0))
            (qfbv_atom ac))))
  | Aconst (_, bs1) ->
    (match a2 with
     | Avar _ ->
       QFBV.QFBV.qfbv_conj
         (QFBV.QFBV.qfbv_lneg
           (QFBV.QFBV.qfbv_saddo (qfbv_atom a1) (qfbv_atom a2)))
         (QFBV.QFBV.qfbv_lneg
           (QFBV.QFBV.qfbv_saddo
             (QFBV.QFBV.qfbv_add (qfbv_atom a1) (qfbv_atom a2))
             (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0))
               (qfbv_atom ac))))
     | Aconst (_, bs2) ->
       (match ac with
        | Avar _ ->
          if coq_Saddo bs1 bs2
          then QFBV.QFBV.qfbv_false
          else if coq_Saddo (addB bs1 bs2)
                    (zext (subn a_size (Pervasives.succ 0)) (b1 :: []))
               then QFBV.QFBV.qfbv_lneg
                      (QFBV.QFBV.qfbv_saddo (QFBV.QFBV.Econst (addB bs1 bs2))
                        (QFBV.QFBV.qfbv_zext
                          (subn a_size (Pervasives.succ 0)) (qfbv_atom ac)))
               else QFBV.QFBV.qfbv_true
        | Aconst (_, c) ->
          if (||) (coq_Saddo bs1 bs2)
               (coq_Saddo (addB bs1 bs2)
                 (zext (subn a_size (Pervasives.succ 0)) c))
          then QFBV.QFBV.qfbv_false
          else QFBV.QFBV.qfbv_true))

(** val bexp_atom_adcB_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_adcB_algsnd e a1 a2 ac =
  let a_typ = SSALite.SSALite.atyp a1 e in
  let a_size = SSALite.SSALite.asize a1 e in
  if is_unsigned a_typ
  then bexp_atom_uadcB_algsnd a_size a1 a2 ac
  else bexp_atom_sadcB_algsnd a_size a1 a2 ac

(** val bexp_atom_adcs_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_adcs_algsnd e a1 a2 ac =
  let a_typ = SSALite.SSALite.atyp a1 e in
  let a_size = SSALite.SSALite.asize a1 e in
  if is_unsigned a_typ
  then QFBV.QFBV.Btrue
  else bexp_atom_sadcB_algsnd a_size a1 a2 ac

(** val bexp_atom_usubB_algsnd : atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_usubB_algsnd a1 a2 =
  match a1 with
  | Avar _ ->
    QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_usubo (qfbv_atom a1) (qfbv_atom a2))
  | Aconst (_, bs1) ->
    (match a2 with
     | Avar _ ->
       QFBV.QFBV.qfbv_lneg
         (QFBV.QFBV.qfbv_usubo (qfbv_atom a1) (qfbv_atom a2))
     | Aconst (_, bs2) ->
       if borrow_subB bs1 bs2
       then QFBV.QFBV.qfbv_false
       else QFBV.QFBV.qfbv_true)

(** val bexp_atom_ssubB_algsnd : atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_ssubB_algsnd a1 a2 =
  match a1 with
  | Avar _ ->
    QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2))
  | Aconst (_, bs1) ->
    (match a2 with
     | Avar _ ->
       QFBV.QFBV.qfbv_lneg
         (QFBV.QFBV.qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2))
     | Aconst (_, bs2) ->
       if coq_Ssubo bs1 bs2 then QFBV.QFBV.qfbv_false else QFBV.QFBV.qfbv_true)

(** val bexp_atom_subB_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_subB_algsnd e a1 a2 =
  if is_unsigned (SSALite.SSALite.atyp a1 e)
  then bexp_atom_usubB_algsnd a1 a2
  else bexp_atom_ssubB_algsnd a1 a2

(** val bexp_atom_subc_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_subc_algsnd e a1 a2 =
  if is_unsigned (SSALite.SSALite.atyp a1 e)
  then QFBV.QFBV.Btrue
  else bexp_atom_ssubB_algsnd a1 a2

(** val bexp_atom_subb_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_subb_algsnd e a1 a2 =
  if is_unsigned (SSALite.SSALite.atyp a1 e)
  then QFBV.QFBV.Btrue
  else bexp_atom_ssubB_algsnd a1 a2

(** val bexp_atom_usbbB_algsnd :
    int -> atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_usbbB_algsnd a_size a1 a2 ab =
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_usubo (qfbv_atom a1) (qfbv_atom a2)))
    (QFBV.QFBV.qfbv_lneg
      (QFBV.QFBV.qfbv_usubo
        (QFBV.QFBV.qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0)) (qfbv_atom ab))))

(** val bexp_atom_ssbbB_algsnd :
    int -> atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_ssbbB_algsnd a_size a1 a2 ab =
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2)))
    (QFBV.QFBV.qfbv_lneg
      (QFBV.QFBV.qfbv_ssubo
        (QFBV.QFBV.qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0)) (qfbv_atom ab))))

(** val bexp_atom_sbbB_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_sbbB_algsnd e a1 a2 ab =
  let a_typ = SSALite.SSALite.atyp a1 e in
  let a_size = SSALite.SSALite.asize a1 e in
  if is_unsigned a_typ
  then bexp_atom_usbbB_algsnd a_size a1 a2 ab
  else bexp_atom_ssbbB_algsnd a_size a1 a2 ab

(** val bexp_atom_sbbs_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_sbbs_algsnd e a1 a2 ab =
  let a_typ = SSALite.SSALite.atyp a1 e in
  let a_size = SSALite.SSALite.asize a1 e in
  if is_unsigned a_typ
  then QFBV.QFBV.Btrue
  else bexp_atom_ssbbB_algsnd a_size a1 a2 ab

(** val bexp_atom_usbcB_algsnd :
    int -> atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_usbcB_algsnd a_size a1 a2 ac =
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_usubo (qfbv_atom a1) (qfbv_atom a2)))
    (QFBV.QFBV.qfbv_lneg
      (QFBV.QFBV.qfbv_usubo
        (QFBV.QFBV.qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0))
          (QFBV.QFBV.qfbv_sub (QFBV.QFBV.qfbv_one (Pervasives.succ 0))
            (qfbv_atom ac)))))

(** val bexp_atom_ssbcB_algsnd :
    int -> atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_ssbcB_algsnd a_size a1 a2 ac =
  QFBV.QFBV.qfbv_conj
    (QFBV.QFBV.qfbv_lneg (QFBV.QFBV.qfbv_ssubo (qfbv_atom a1) (qfbv_atom a2)))
    (QFBV.QFBV.qfbv_lneg
      (QFBV.QFBV.qfbv_ssubo
        (QFBV.QFBV.qfbv_sub (qfbv_atom a1) (qfbv_atom a2))
        (QFBV.QFBV.qfbv_zext (subn a_size (Pervasives.succ 0))
          (QFBV.QFBV.qfbv_sub (QFBV.QFBV.qfbv_one (Pervasives.succ 0))
            (qfbv_atom ac)))))

(** val bexp_atom_sbcB_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_sbcB_algsnd e a1 a2 ac =
  let a_typ = SSALite.SSALite.atyp a1 e in
  let a_size = SSALite.SSALite.asize a1 e in
  if is_unsigned a_typ
  then bexp_atom_usbcB_algsnd a_size a1 a2 ac
  else bexp_atom_ssbcB_algsnd a_size a1 a2 ac

(** val bexp_atom_sbcs_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_sbcs_algsnd e a1 a2 ac =
  let a_typ = SSALite.SSALite.atyp a1 e in
  let a_size = SSALite.SSALite.asize a1 e in
  if is_unsigned a_typ
  then QFBV.QFBV.Btrue
  else bexp_atom_ssbcB_algsnd a_size a1 a2 ac

(** val bexp_atom_mulB_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp **)

let bexp_atom_mulB_algsnd e a1 a2 =
  if is_unsigned (SSALite.SSALite.atyp a1 e)
  then QFBV.QFBV.qfbv_lneg
         (QFBV.QFBV.qfbv_umulo (qfbv_atom a1) (qfbv_atom a2))
  else QFBV.QFBV.qfbv_lneg
         (QFBV.QFBV.qfbv_smulo (qfbv_atom a1) (qfbv_atom a2))

(** val bexp_atom_shl_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> int -> QFBV.QFBV.bexp **)

let bexp_atom_shl_algsnd e a n =
  if is_unsigned (SSALite.SSALite.atyp a e)
  then QFBV.QFBV.qfbv_eq (QFBV.QFBV.qfbv_high n (qfbv_atom a))
         (QFBV.QFBV.qfbv_zero n)
  else QFBV.QFBV.qfbv_disj
         (QFBV.QFBV.qfbv_eq
           (QFBV.QFBV.qfbv_high (addn n (Pervasives.succ 0)) (qfbv_atom a))
           (QFBV.QFBV.qfbv_zero (addn n (Pervasives.succ 0))))
         (QFBV.QFBV.qfbv_eq
           (QFBV.QFBV.qfbv_high (addn n (Pervasives.succ 0)) (qfbv_atom a))
           (QFBV.QFBV.qfbv_not
             (QFBV.QFBV.qfbv_zero (addn n (Pervasives.succ 0)))))

(** val bexp_atom_cshl_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> int -> QFBV.QFBV.bexp **)

let bexp_atom_cshl_algsnd e a1 a2 n =
  if is_unsigned (SSALite.SSALite.atyp a1 e)
  then QFBV.QFBV.qfbv_eq
         (QFBV.QFBV.qfbv_high n
           (QFBV.QFBV.qfbv_concat (qfbv_atom a1) (qfbv_atom a2)))
         (QFBV.QFBV.qfbv_zero n)
  else QFBV.QFBV.qfbv_disj
         (QFBV.QFBV.qfbv_eq
           (QFBV.QFBV.qfbv_high (addn n (Pervasives.succ 0))
             (QFBV.QFBV.qfbv_concat (qfbv_atom a1) (qfbv_atom a2)))
           (QFBV.QFBV.qfbv_zero (addn n (Pervasives.succ 0))))
         (QFBV.QFBV.qfbv_eq
           (QFBV.QFBV.qfbv_high (addn n (Pervasives.succ 0))
             (QFBV.QFBV.qfbv_concat (qfbv_atom a1) (qfbv_atom a2)))
           (QFBV.QFBV.qfbv_not
             (QFBV.QFBV.qfbv_zero (addn n (Pervasives.succ 0)))))

(** val bexp_atom_vpc_algsnd :
    TypEnv.SSATE.env -> typ -> SSALite.SSALite.atom -> QFBV.QFBV.bexp **)

let bexp_atom_vpc_algsnd e t a =
  if is_unsigned (SSALite.SSALite.atyp a e)
  then if is_unsigned t
       then if leq (sizeof_typ (SSALite.SSALite.atyp a e)) (sizeof_typ t)
            then QFBV.QFBV.qfbv_true
            else QFBV.QFBV.qfbv_eq
                   (QFBV.QFBV.qfbv_high
                     (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                       (sizeof_typ t)) (qfbv_atom a))
                   (QFBV.QFBV.qfbv_zero
                     (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                       (sizeof_typ t)))
       else if leq (Pervasives.succ (sizeof_typ (SSALite.SSALite.atyp a e)))
                 (sizeof_typ t)
            then QFBV.QFBV.qfbv_true
            else QFBV.QFBV.qfbv_eq
                   (QFBV.QFBV.qfbv_high
                     (addn
                       (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                         (sizeof_typ t)) (Pervasives.succ 0)) (qfbv_atom a))
                   (QFBV.QFBV.qfbv_zero
                     (addn
                       (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                         (sizeof_typ t)) (Pervasives.succ 0)))
  else if is_unsigned t
       then if leq
                 (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                   (Pervasives.succ 0)) (sizeof_typ t)
            then QFBV.QFBV.qfbv_eq
                   (QFBV.QFBV.qfbv_high (Pervasives.succ 0) (qfbv_atom a))
                   (QFBV.QFBV.qfbv_zero (Pervasives.succ 0))
            else QFBV.QFBV.qfbv_eq
                   (QFBV.QFBV.qfbv_high
                     (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                       (sizeof_typ t)) (qfbv_atom a))
                   (QFBV.QFBV.qfbv_zero
                     (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                       (sizeof_typ t)))
       else if leq (sizeof_typ (SSALite.SSALite.atyp a e)) (sizeof_typ t)
            then QFBV.QFBV.qfbv_true
            else QFBV.QFBV.qfbv_eq
                   (QFBV.QFBV.qfbv_sext
                     (subn (sizeof_typ (SSALite.SSALite.atyp a e))
                       (sizeof_typ t))
                     (QFBV.QFBV.qfbv_low (sizeof_typ t) (qfbv_atom a)))
                   (qfbv_atom a)

(** val bexp_instr_algsnd :
    TypEnv.SSATE.env -> SSALite.SSALite.instr -> QFBV.QFBV.bexp **)

let bexp_instr_algsnd e = function
| SSALite.SSALite.Ishl (_, a, n) -> bexp_atom_shl_algsnd e a n
| SSALite.SSALite.Icshl (_, _, a1, a2, n) -> bexp_atom_cshl_algsnd e a1 a2 n
| SSALite.SSALite.Iadd (_, a1, a2) -> bexp_atom_addB_algsnd e a1 a2
| SSALite.SSALite.Iadds (_, _, a1, a2) -> bexp_atom_adds_algsnd e a1 a2
| SSALite.SSALite.Iadc (_, a1, a2, ac) -> bexp_atom_adcB_algsnd e a1 a2 ac
| SSALite.SSALite.Iadcs (_, _, a1, a2, ac) -> bexp_atom_adcs_algsnd e a1 a2 ac
| SSALite.SSALite.Isub (_, a1, a2) -> bexp_atom_subB_algsnd e a1 a2
| SSALite.SSALite.Isubc (_, _, a1, a2) -> bexp_atom_subc_algsnd e a1 a2
| SSALite.SSALite.Isubb (_, _, a1, a2) -> bexp_atom_subb_algsnd e a1 a2
| SSALite.SSALite.Isbc (_, a1, a2, ac) -> bexp_atom_sbcB_algsnd e a1 a2 ac
| SSALite.SSALite.Isbcs (_, _, a1, a2, ac) -> bexp_atom_sbcs_algsnd e a1 a2 ac
| SSALite.SSALite.Isbb (_, a1, a2, ab) -> bexp_atom_sbbB_algsnd e a1 a2 ab
| SSALite.SSALite.Isbbs (_, _, a1, a2, ab) -> bexp_atom_sbbs_algsnd e a1 a2 ab
| SSALite.SSALite.Imul (_, a1, a2) -> bexp_atom_mulB_algsnd e a1 a2
| SSALite.SSALite.Ivpc (_, t, a) -> bexp_atom_vpc_algsnd e t a
| _ -> QFBV.QFBV.qfbv_true

(** val bexp_program_algsnd_split_fixed_final_rec :
    TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> SSALite.SSALite.instr list ->
    (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list **)

let rec bexp_program_algsnd_split_fixed_final_rec e pre_es = function
| [] -> []
| hd :: tl ->
  (pre_es,
    (bexp_instr_algsnd e hd)) :: (bexp_program_algsnd_split_fixed_final_rec e
                                   (rcons pre_es (bexp_instr e hd)) tl)

(** val bexp_program_algsnd_split_fixed_final :
    TypEnv.SSATE.env -> SSALite.SSALite.instr list -> (QFBV.QFBV.bexp
    list * QFBV.QFBV.bexp) list **)

let bexp_program_algsnd_split_fixed_final e p =
  bexp_program_algsnd_split_fixed_final_rec e [] p

(** val qfbv_spec_algsnd_la_rec :
    QFBV.QFBV.bexp -> (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list ->
    QFBV.QFBV.bexp list **)

let rec qfbv_spec_algsnd_la_rec f = function
| [] -> []
| p :: tl ->
  let (pre_es, safe) = p in
  (QFBV.QFBV.qfbv_imp
    (QFBV.QFBV.qfbv_conj f (QFBV.QFBV.qfbv_conjs_la pre_es)) safe) :: 
  (qfbv_spec_algsnd_la_rec f tl)

(** val qfbv_spec_algsnd_la : SSALite.SSALite.rspec -> QFBV.QFBV.bexp list **)

let qfbv_spec_algsnd_la s =
  let fE =
    SSALite.SSALite.program_succ_typenv (SSALite.SSALite.rsprog s)
      (SSALite.SSALite.rsinputs s)
  in
  qfbv_spec_algsnd_la_rec (bexp_rbexp (SSALite.SSALite.rspre s))
    (bexp_program_algsnd_split_fixed_final fE (SSALite.SSALite.rsprog s))

(** val make_sndcond :
    options -> TypEnv.SSATE.env -> SSALite.SSALite.rbexp ->
    SSALite.SSALite.instr list -> SSALite.SSALite.instr -> QFBV.QFBV.bexp **)

let make_sndcond o fE f p i =
  let es = bexp_instr_algsnd fE i in
  if eq_op QFBV.bexp_eqType (Obj.magic es) (Obj.magic QFBV.QFBV.qfbv_true)
  then QFBV.QFBV.qfbv_true
  else let ef = bexp_rbexp f in
       let vs =
         SSALite.SSALite.depvars_rpre_rprogram o
           (SSALite.SSALite.rvs_instr i) f p
       in
       let ep = bexp_program fE (SSALite.SSALite.slice_rprogram vs p) in
       QFBV.QFBV.qfbv_imp
         (QFBV.QFBV.qfbv_conj ef (QFBV.QFBV.qfbv_conjs_la ep)) es

(** val algsnd_slice_la_rec :
    options -> TypEnv.SSATE.env -> SSALite.SSALite.program ->
    SSALite.SSALite.rbexp -> SSALite.SSALite.program -> QFBV.QFBV.bexp list **)

let rec algsnd_slice_la_rec o fE pre f = function
| [] -> []
| hd :: tl ->
  (make_sndcond o fE f pre hd) :: (algsnd_slice_la_rec o fE (rcons pre hd) f
                                    tl)

(** val algsnd_slice_la :
    options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list **)

let algsnd_slice_la o s =
  let fE =
    SSALite.SSALite.program_succ_typenv (SSALite.SSALite.rsprog s)
      (SSALite.SSALite.rsinputs s)
  in
  algsnd_slice_la_rec o fE [] (SSALite.SSALite.rspre s)
    (SSALite.SSALite.rsprog s)

(** val rngred_algsnd_split_la :
    SSALite.SSALite.rspec -> QFBV.QFBV.bexp list **)

let rngred_algsnd_split_la s =
  cat (rngred_rspec_split_la s) (qfbv_spec_algsnd_la s)

(** val rngred_algsnd_slice_split_la :
    options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list **)

let rngred_algsnd_slice_split_la o s =
  cat (rngred_rspec_slice_split_la o s) (algsnd_slice_la o s)
