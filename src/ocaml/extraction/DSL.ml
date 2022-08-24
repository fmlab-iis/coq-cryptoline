open BinInt
open BinNums
open Bool
open Datatypes
open FMaps
open FSets
open NBitsDef
open NBitsOp
open State
open Typ
open Var
open ZAriths
open Eqtype
open Seq
open Ssrnat

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type eunop =
| Eneg

type ebinop =
| Eadd
| Esub
| Emul

type runop =
| Rnegb
| Rnotb

type rbinop =
| Radd
| Rsub
| Rmul
| Rumod
| Rsrem
| Rsmod
| Randb
| Rorb
| Rxorb

type rcmpop =
| Rult
| Rule
| Rugt
| Ruge
| Rslt
| Rsle
| Rsgt
| Rsge

(** val eunop_eqn : eunop -> eunop -> bool **)

let eunop_eqn _ _ =
  true

(** val eunop_eqP : eunop -> eunop -> reflect **)

let eunop_eqP o1 o2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if eunop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

(** val eunop_eqMixin : eunop Equality.mixin_of **)

let eunop_eqMixin =
  { Equality.op = eunop_eqn; Equality.mixin_of__1 = eunop_eqP }

(** val eunop_eqType : Equality.coq_type **)

let eunop_eqType =
  Obj.magic eunop_eqMixin

(** val ebinop_eqn : ebinop -> ebinop -> bool **)

let ebinop_eqn o1 o2 =
  match o1 with
  | Eadd -> (match o2 with
             | Eadd -> true
             | _ -> false)
  | Esub -> (match o2 with
             | Esub -> true
             | _ -> false)
  | Emul -> (match o2 with
             | Emul -> true
             | _ -> false)

(** val ebinop_eqP : ebinop -> ebinop -> reflect **)

let ebinop_eqP o1 o2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if ebinop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

(** val ebinop_eqMixin : ebinop Equality.mixin_of **)

let ebinop_eqMixin =
  { Equality.op = ebinop_eqn; Equality.mixin_of__1 = ebinop_eqP }

(** val ebinop_eqType : Equality.coq_type **)

let ebinop_eqType =
  Obj.magic ebinop_eqMixin

(** val runop_eqn : runop -> runop -> bool **)

let runop_eqn o1 o2 =
  match o1 with
  | Rnegb -> (match o2 with
              | Rnegb -> true
              | Rnotb -> false)
  | Rnotb -> (match o2 with
              | Rnegb -> false
              | Rnotb -> true)

(** val runop_eqP : runop -> runop -> reflect **)

let runop_eqP o1 o2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if runop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

(** val runop_eqMixin : runop Equality.mixin_of **)

let runop_eqMixin =
  { Equality.op = runop_eqn; Equality.mixin_of__1 = runop_eqP }

(** val runop_eqType : Equality.coq_type **)

let runop_eqType =
  Obj.magic runop_eqMixin

(** val rbinop_eqn : rbinop -> rbinop -> bool **)

let rbinop_eqn o1 o2 =
  match o1 with
  | Radd -> (match o2 with
             | Radd -> true
             | _ -> false)
  | Rsub -> (match o2 with
             | Rsub -> true
             | _ -> false)
  | Rmul -> (match o2 with
             | Rmul -> true
             | _ -> false)
  | Rumod -> (match o2 with
              | Rumod -> true
              | _ -> false)
  | Rsrem -> (match o2 with
              | Rsrem -> true
              | _ -> false)
  | Rsmod -> (match o2 with
              | Rsmod -> true
              | _ -> false)
  | Randb -> (match o2 with
              | Randb -> true
              | _ -> false)
  | Rorb -> (match o2 with
             | Rorb -> true
             | _ -> false)
  | Rxorb -> (match o2 with
              | Rxorb -> true
              | _ -> false)

(** val rbinop_eqP : rbinop -> rbinop -> reflect **)

let rbinop_eqP o1 o2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if rbinop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

(** val rbinop_eqMixin : rbinop Equality.mixin_of **)

let rbinop_eqMixin =
  { Equality.op = rbinop_eqn; Equality.mixin_of__1 = rbinop_eqP }

(** val rbinop_eqType : Equality.coq_type **)

let rbinop_eqType =
  Obj.magic rbinop_eqMixin

(** val rcmpop_eqn : rcmpop -> rcmpop -> bool **)

let rcmpop_eqn o1 o2 =
  match o1 with
  | Rult -> (match o2 with
             | Rult -> true
             | _ -> false)
  | Rule -> (match o2 with
             | Rule -> true
             | _ -> false)
  | Rugt -> (match o2 with
             | Rugt -> true
             | _ -> false)
  | Ruge -> (match o2 with
             | Ruge -> true
             | _ -> false)
  | Rslt -> (match o2 with
             | Rslt -> true
             | _ -> false)
  | Rsle -> (match o2 with
             | Rsle -> true
             | _ -> false)
  | Rsgt -> (match o2 with
             | Rsgt -> true
             | _ -> false)
  | Rsge -> (match o2 with
             | Rsge -> true
             | _ -> false)

(** val rcmpop_eqP : rcmpop -> rcmpop -> reflect **)

let rcmpop_eqP o1 o2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if rcmpop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

(** val rcmpop_eqMixin : rcmpop Equality.mixin_of **)

let rcmpop_eqMixin =
  { Equality.op = rcmpop_eqn; Equality.mixin_of__1 = rcmpop_eqP }

(** val rcmpop_eqType : Equality.coq_type **)

let rcmpop_eqType =
  Obj.magic rcmpop_eqMixin

module Coq__1 = struct
 type eexp =
 | Evar of Equality.sort
 | Econst of coq_Z
 | Eunop of eunop * eexp
 | Ebinop of ebinop * eexp * eexp
 | Epow of eexp * coq_N
end
include Coq__1

(** val econst : Equality.coq_type -> coq_Z -> eexp **)

let econst _ n =
  Econst n

(** val eadd : Equality.coq_type -> eexp -> eexp -> eexp **)

let eadd _ e1 e2 =
  Ebinop (Eadd, e1, e2)

(** val emul : Equality.coq_type -> eexp -> eexp -> eexp **)

let emul _ e1 e2 =
  Ebinop (Emul, e1, e2)

(** val eadds : Equality.coq_type -> eexp list -> eexp **)

let eadds var = function
| [] -> econst var Z.zero
| e :: es0 ->
  (match es0 with
   | [] -> e
   | _ :: _ -> foldl (fun res e0 -> eadd var res e0) e es0)

(** val emuls : Equality.coq_type -> eexp list -> eexp **)

let emuls var = function
| [] -> econst var Z.one
| e :: es0 ->
  (match es0 with
   | [] -> e
   | _ :: _ -> foldl (fun res e0 -> emul var res e0) e es0)

(** val z2expn : coq_Z -> coq_Z **)

let z2expn n =
  Z.pow (Zpos (Coq_xO Coq_xH)) n

(** val e2expn : Equality.coq_type -> coq_Z -> eexp **)

let e2expn var n =
  econst var (z2expn n)

(** val emul2p : Equality.coq_type -> eexp -> coq_Z -> eexp **)

let emul2p var x n =
  emul var x (e2expn var n)

(** val eexp_eqn : Equality.coq_type -> eexp -> eexp -> bool **)

let rec eexp_eqn var e1 e2 =
  match e1 with
  | Evar v1 -> (match e2 with
                | Evar v2 -> eq_op var v1 v2
                | _ -> false)
  | Econst n1 ->
    (match e2 with
     | Econst n2 -> eq_op coq_Z_eqType (Obj.magic n1) (Obj.magic n2)
     | _ -> false)
  | Eunop (op1, e3) ->
    (match e2 with
     | Eunop (op2, e4) ->
       (&&) (eq_op eunop_eqType (Obj.magic op1) (Obj.magic op2))
         (eexp_eqn var e3 e4)
     | _ -> false)
  | Ebinop (op1, e3, e4) ->
    (match e2 with
     | Ebinop (op2, e5, e6) ->
       (&&)
         ((&&) (eq_op ebinop_eqType (Obj.magic op1) (Obj.magic op2))
           (eexp_eqn var e3 e5)) (eexp_eqn var e4 e6)
     | _ -> false)
  | Epow (e3, n1) ->
    (match e2 with
     | Epow (e4, n2) ->
       (&&) (eexp_eqn var e3 e4)
         (eq_op bin_nat_eqType (Obj.magic n1) (Obj.magic n2))
     | _ -> false)

(** val eexp_eqP : Equality.coq_type -> eexp -> eexp -> reflect **)

let eexp_eqP var e1 e2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if eexp_eqn var e1 e2 then _evar_0_ __ else _evar_0_0 __

(** val eexp_eqMixin : Equality.coq_type -> eexp Equality.mixin_of **)

let eexp_eqMixin var =
  { Equality.op = (eexp_eqn var); Equality.mixin_of__1 = (eexp_eqP var) }

(** val eexp_eqType : Equality.coq_type -> Equality.coq_type **)

let eexp_eqType var =
  Obj.magic eexp_eqMixin var

(** val limbsi : Equality.coq_type -> int -> coq_Z -> eexp list -> eexp **)

let rec limbsi var i r = function
| [] -> econst var Z.zero
| e :: es0 ->
  (match es0 with
   | [] -> e
   | _ :: _ ->
     eadd var (emul var e (e2expn var (Z.mul (Z.of_nat i) r)))
       (limbsi var (addn i (Pervasives.succ 0)) r es0))

module Coq__2 = struct
 type rexp =
 | Rvar of Equality.sort
 | Rconst of int * bits
 | Runop of int * runop * rexp
 | Rbinop of int * rbinop * rexp * rexp
 | Ruext of int * rexp * int
 | Rsext of int * rexp * int
end
include Coq__2

(** val rbits : Equality.coq_type -> bool list -> rexp **)

let rbits _ n =
  Rconst ((size n), n)

(** val radd : Equality.coq_type -> int -> rexp -> rexp -> rexp **)

let radd _ w e1 e2 =
  Rbinop (w, Radd, e1, e2)

(** val rmul : Equality.coq_type -> int -> rexp -> rexp -> rexp **)

let rmul _ w e1 e2 =
  Rbinop (w, Rmul, e1, e2)

(** val radds : Equality.coq_type -> int -> rexp list -> rexp **)

let radds var w = function
| [] -> rbits var (from_nat w 0)
| e :: es0 ->
  (match es0 with
   | [] -> e
   | _ :: _ -> foldl (fun res e0 -> radd var w res e0) e es0)

(** val rmuls : Equality.coq_type -> int -> rexp list -> rexp **)

let rmuls var w = function
| [] -> rbits var (from_nat w (Pervasives.succ 0))
| e :: es0 ->
  (match es0 with
   | [] -> e
   | _ :: _ -> foldl (fun res e0 -> rmul var w res e0) e es0)

(** val rexp_eqn : Equality.coq_type -> rexp -> rexp -> bool **)

let rec rexp_eqn var e1 e2 =
  match e1 with
  | Rvar v1 -> (match e2 with
                | Rvar v2 -> eq_op var v1 v2
                | _ -> false)
  | Rconst (w1, n1) ->
    (match e2 with
     | Rconst (w2, n2) ->
       (&&) (eq_op nat_eqType (Obj.magic w1) (Obj.magic w2))
         (eq_op bitseq_eqType (Obj.magic n1) (Obj.magic n2))
     | _ -> false)
  | Runop (w1, op1, e3) ->
    (match e2 with
     | Runop (w2, op2, e4) ->
       (&&)
         ((&&) (eq_op nat_eqType (Obj.magic w1) (Obj.magic w2))
           (eq_op runop_eqType (Obj.magic op1) (Obj.magic op2)))
         (rexp_eqn var e3 e4)
     | _ -> false)
  | Rbinop (w1, op1, e3, e4) ->
    (match e2 with
     | Rbinop (w2, op2, e5, e6) ->
       (&&)
         ((&&)
           ((&&) (eq_op nat_eqType (Obj.magic w1) (Obj.magic w2))
             (eq_op rbinop_eqType (Obj.magic op1) (Obj.magic op2)))
           (rexp_eqn var e3 e5)) (rexp_eqn var e4 e6)
     | _ -> false)
  | Ruext (w1, e3, n1) ->
    (match e2 with
     | Ruext (w2, e4, n2) ->
       (&&)
         ((&&) (eq_op nat_eqType (Obj.magic w1) (Obj.magic w2))
           (rexp_eqn var e3 e4))
         (eq_op nat_eqType (Obj.magic n1) (Obj.magic n2))
     | _ -> false)
  | Rsext (w1, e3, n1) ->
    (match e2 with
     | Rsext (w2, e4, n2) ->
       (&&)
         ((&&) (eq_op nat_eqType (Obj.magic w1) (Obj.magic w2))
           (rexp_eqn var e3 e4))
         (eq_op nat_eqType (Obj.magic n1) (Obj.magic n2))
     | _ -> false)

(** val rexp_eqP : Equality.coq_type -> rexp -> rexp -> reflect **)

let rexp_eqP var e1 e2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if rexp_eqn var e1 e2 then _evar_0_ __ else _evar_0_0 __

(** val rexp_eqMixin : Equality.coq_type -> rexp Equality.mixin_of **)

let rexp_eqMixin var =
  { Equality.op = (rexp_eqn var); Equality.mixin_of__1 = (rexp_eqP var) }

(** val rexp_eqType : Equality.coq_type -> Equality.coq_type **)

let rexp_eqType var =
  Obj.magic rexp_eqMixin var

module Coq__3 = struct
 type ebexp =
 | Etrue
 | Eeq of eexp * eexp
 | Eeqmod of eexp * eexp * eexp list
 | Eand of ebexp * ebexp
end
include Coq__3

(** val eand : Equality.coq_type -> ebexp -> ebexp -> ebexp **)

let eand _ b1 b2 =
  Eand (b1, b2)

(** val eands : Equality.coq_type -> ebexp list -> ebexp **)

let eands var es =
  foldr (fun res e -> eand var res e) Etrue es

(** val split_eand : Equality.coq_type -> ebexp -> ebexp list **)

let rec split_eand var e = match e with
| Eand (e1, e2) -> cat (split_eand var e1) (split_eand var e2)
| _ -> e :: []

(** val ebexp_eqn : Equality.coq_type -> ebexp -> ebexp -> bool **)

let rec ebexp_eqn var e1 e2 =
  match e1 with
  | Etrue -> (match e2 with
              | Etrue -> true
              | _ -> false)
  | Eeq (e3, e4) ->
    (match e2 with
     | Eeq (e5, e6) ->
       (&&) (eq_op (eexp_eqType var) (Obj.magic e3) (Obj.magic e5))
         (eq_op (eexp_eqType var) (Obj.magic e4) (Obj.magic e6))
     | _ -> false)
  | Eeqmod (e3, e4, ms1) ->
    (match e2 with
     | Eeqmod (e5, e6, ms2) ->
       (&&)
         ((&&) (eq_op (eexp_eqType var) (Obj.magic e3) (Obj.magic e5))
           (eq_op (eexp_eqType var) (Obj.magic e4) (Obj.magic e6)))
         (eq_op (seq_eqType (eexp_eqType var)) (Obj.magic ms1)
           (Obj.magic ms2))
     | _ -> false)
  | Eand (e3, e4) ->
    (match e2 with
     | Eand (e5, e6) -> (&&) (ebexp_eqn var e3 e5) (ebexp_eqn var e4 e6)
     | _ -> false)

(** val ebexp_eqP : Equality.coq_type -> ebexp -> ebexp -> reflect **)

let ebexp_eqP var e1 e2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if ebexp_eqn var e1 e2 then _evar_0_ __ else _evar_0_0 __

(** val ebexp_eqMixin : Equality.coq_type -> ebexp Equality.mixin_of **)

let ebexp_eqMixin var =
  { Equality.op = (ebexp_eqn var); Equality.mixin_of__1 = (ebexp_eqP var) }

(** val ebexp_eqType : Equality.coq_type -> Equality.coq_type **)

let ebexp_eqType var =
  Obj.magic ebexp_eqMixin var

module Coq__4 = struct
 type rbexp =
 | Rtrue
 | Req of int * rexp * rexp
 | Rcmp of int * rcmpop * rexp * rexp
 | Rneg of rbexp
 | Rand of rbexp * rbexp
 | Ror of rbexp * rbexp
end
include Coq__4

(** val rand : Equality.coq_type -> rbexp -> rbexp -> rbexp **)

let rand _ e1 e2 =
  match e1 with
  | Rtrue -> e2
  | Rcmp (_, _, _, _) ->
    (match e2 with
     | Rtrue -> e1
     | Rneg r2 -> (match r2 with
                   | Rtrue -> Rneg Rtrue
                   | _ -> Rand (e1, e2))
     | _ -> Rand (e1, e2))
  | Rneg r ->
    (match r with
     | Rtrue -> (match e2 with
                 | Rtrue -> e1
                 | _ -> Rneg Rtrue)
     | Rcmp (_, _, _, _) ->
       (match e2 with
        | Rtrue -> e1
        | Rneg r3 -> (match r3 with
                      | Rtrue -> Rneg Rtrue
                      | _ -> Rand (e1, e2))
        | _ -> Rand (e1, e2))
     | Rneg _ ->
       (match e2 with
        | Rtrue -> e1
        | Rneg r1 -> (match r1 with
                      | Rtrue -> Rneg Rtrue
                      | _ -> Rand (e1, e2))
        | _ -> Rand (e1, e2))
     | _ ->
       (match e2 with
        | Rtrue -> e1
        | Rneg r2 -> (match r2 with
                      | Rtrue -> Rneg Rtrue
                      | _ -> Rand (e1, e2))
        | _ -> Rand (e1, e2)))
  | _ ->
    (match e2 with
     | Rtrue -> e1
     | Rneg r1 -> (match r1 with
                   | Rtrue -> Rneg Rtrue
                   | _ -> Rand (e1, e2))
     | _ -> Rand (e1, e2))

(** val ror : Equality.coq_type -> rbexp -> rbexp -> rbexp **)

let ror _ e1 e2 =
  match e1 with
  | Rtrue -> Rtrue
  | Rcmp (_, _, _, _) ->
    (match e2 with
     | Rtrue -> Rtrue
     | Rneg r2 -> (match r2 with
                   | Rtrue -> e1
                   | _ -> Ror (e1, e2))
     | _ -> Ror (e1, e2))
  | Rneg r ->
    (match r with
     | Rtrue -> (match e2 with
                 | Rtrue -> Rtrue
                 | _ -> e2)
     | Rcmp (_, _, _, _) ->
       (match e2 with
        | Rtrue -> Rtrue
        | Rneg r3 -> (match r3 with
                      | Rtrue -> e1
                      | _ -> Ror (e1, e2))
        | _ -> Ror (e1, e2))
     | Rneg _ ->
       (match e2 with
        | Rtrue -> Rtrue
        | Rneg r1 -> (match r1 with
                      | Rtrue -> e1
                      | _ -> Ror (e1, e2))
        | _ -> Ror (e1, e2))
     | _ ->
       (match e2 with
        | Rtrue -> Rtrue
        | Rneg r2 -> (match r2 with
                      | Rtrue -> e1
                      | _ -> Ror (e1, e2))
        | _ -> Ror (e1, e2)))
  | _ ->
    (match e2 with
     | Rtrue -> Rtrue
     | Rneg r1 -> (match r1 with
                   | Rtrue -> e1
                   | _ -> Ror (e1, e2))
     | _ -> Ror (e1, e2))

(** val rands : Equality.coq_type -> rbexp list -> rbexp **)

let rands var es =
  foldl (fun res e -> rand var res e) Rtrue es

(** val rors : Equality.coq_type -> rbexp list -> rbexp **)

let rors var es =
  foldl (fun res e -> ror var res e) (Rneg Rtrue) es

(** val rbexp_eqn : Equality.coq_type -> rbexp -> rbexp -> bool **)

let rec rbexp_eqn var e1 e2 =
  match e1 with
  | Rtrue -> (match e2 with
              | Rtrue -> true
              | _ -> false)
  | Req (n1, e3, e4) ->
    (match e2 with
     | Req (n2, e5, e6) ->
       (&&)
         ((&&) (eq_op nat_eqType (Obj.magic n1) (Obj.magic n2))
           (eq_op (rexp_eqType var) (Obj.magic e3) (Obj.magic e5)))
         (eq_op (rexp_eqType var) (Obj.magic e4) (Obj.magic e6))
     | _ -> false)
  | Rcmp (n1, op1, e3, e4) ->
    (match e2 with
     | Rcmp (n2, op2, e5, e6) ->
       (&&)
         ((&&)
           ((&&) (eq_op nat_eqType (Obj.magic n1) (Obj.magic n2))
             (eq_op rcmpop_eqType (Obj.magic op1) (Obj.magic op2)))
           (eq_op (rexp_eqType var) (Obj.magic e3) (Obj.magic e5)))
         (eq_op (rexp_eqType var) (Obj.magic e4) (Obj.magic e6))
     | _ -> false)
  | Rneg e3 -> (match e2 with
                | Rneg e4 -> rbexp_eqn var e3 e4
                | _ -> false)
  | Rand (e3, e4) ->
    (match e2 with
     | Rand (e5, e6) -> (&&) (rbexp_eqn var e3 e5) (rbexp_eqn var e4 e6)
     | _ -> false)
  | Ror (e3, e4) ->
    (match e2 with
     | Ror (e5, e6) -> (&&) (rbexp_eqn var e3 e5) (rbexp_eqn var e4 e6)
     | _ -> false)

(** val rbexp_eqP : Equality.coq_type -> rbexp -> rbexp -> reflect **)

let rbexp_eqP var e1 e2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if rbexp_eqn var e1 e2 then _evar_0_ __ else _evar_0_0 __

module MakeDSL =
 functor (V:SsrOrder.SsrOrder) ->
 functor (VS:SsrFSet with module SE = V) ->
 functor (VM:SsrFMap with module SE = V) ->
 functor (TE:TypEnv.TypEnv with module SE = V) ->
 functor (S:sig
  module Lemmas :
   sig
    module F :
     sig
      val eqb : TE.SE.t -> TE.SE.t -> bool

      val coq_In_dec : 'a1 TE.t -> TE.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TE.SE.t -> TE.SE.t -> bool

          val lt_dec : TE.SE.t -> TE.SE.t -> bool

          val eqb : TE.SE.t -> TE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TE.SE.t -> TE.SE.t -> bool

          val coq_In_dec : 'a1 TE.t -> TE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TE.key * 'a1) list -> 'a1 TE.t

        val to_list : 'a1 TE.t -> (TE.key * 'a1) list

        val fold_rec :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
          -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ ->
          __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t ->
          'a1 TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 ->
          'a2 -> 'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key
          -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t ->
          'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1
          TE.t -> __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

        val fold_rel :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) ->
          'a2 -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __
          -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val map_induction_bis :
          ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
          -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

        val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

        val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

        val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val partition :
          (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val coq_Partition_In :
          'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

        val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

        val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val partition_dom :
          (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
       end

      val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

      val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val map_induction_max :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_min :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2
     end

    val eqb : TE.SE.t -> TE.SE.t -> bool

    val coq_In_dec : 'a1 TE.t -> TE.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : TE.SE.t -> TE.SE.t -> bool

        val coq_In_dec : 'a1 TE.t -> TE.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TE.key * 'a1) list -> 'a1 TE.t

      val to_list : 'a1 TE.t -> (TE.key * 'a1) list

      val fold_rec :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
        -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ -> __
        -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> 'a1
        TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 ->
        'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t -> 'a2
        -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t ->
        __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

      val fold_rel :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __ ->
        'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_bis :
        ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
        -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

      val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

      val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

      val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val partition :
        (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val coq_Partition_In :
        'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

      val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

      val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val partition_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
     end

    val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

    val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val map_induction_max :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val map_induction_min :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val memP : TE.key -> 'a1 TE.t -> reflect

    val split : ('a1 * 'a2) TE.t -> 'a1 TE.t * 'a2 TE.t

    module EFacts :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    val max_opt : TE.key -> TE.key option -> TE.key

    val max_key_elements : (TE.key * 'a1) list -> TE.key option

    val max_key : 'a1 TE.t -> TE.key option

    val min_opt : TE.key -> TE.key option -> TE.key

    val min_key_elements : (TE.key * 'a1) list -> TE.key option

    val min_key : 'a1 TE.t -> TE.key option
   end

  type t

  val acc : V.t -> t -> bits

  val upd : V.t -> bits -> t -> t

  val upd2 : V.t -> bits -> V.t -> bits -> t -> t
 end) ->
 struct
  module VSLemmas = SsrFSetLemmas(VS)

  module TELemmas = FMapLemmas(TE)

  type eexp = Coq__1.eexp

  (** val evar : V.t -> eexp **)

  let evar v =
    Evar v

  (** val econst : coq_Z -> eexp **)

  let econst n =
    Econst n

  (** val eunary : eunop -> eexp -> eexp **)

  let eunary op0 e =
    Eunop (op0, e)

  (** val ebinary : ebinop -> eexp -> eexp -> eexp **)

  let ebinary op0 e1 e2 =
    Ebinop (op0, e1, e2)

  (** val eneg : eexp -> eexp **)

  let eneg e =
    Eunop (Eneg, e)

  (** val eadd : eexp -> eexp -> eexp **)

  let eadd e1 e2 =
    Ebinop (Eadd, e1, e2)

  (** val esub : eexp -> eexp -> eexp **)

  let esub e1 e2 =
    Ebinop (Esub, e1, e2)

  (** val emul : eexp -> eexp -> eexp **)

  let emul e1 e2 =
    Ebinop (Emul, e1, e2)

  (** val esq : eexp -> eexp **)

  let esq e =
    Ebinop (Emul, e, e)

  (** val epow : eexp -> coq_N -> Coq__1.eexp **)

  let epow e n =
    Epow (e, n)

  (** val eadds : eexp list -> eexp **)

  let eadds es =
    eadds V.coq_T es

  (** val emuls : eexp list -> eexp **)

  let emuls es =
    emuls V.coq_T es

  (** val z2expn : coq_Z -> coq_Z **)

  let z2expn =
    z2expn

  (** val e2expn : coq_Z -> Coq__1.eexp **)

  let e2expn n =
    e2expn V.coq_T n

  (** val emul2p : Coq__1.eexp -> coq_Z -> Coq__1.eexp **)

  let emul2p x n =
    emul2p V.coq_T x n

  (** val vars_eexp : eexp -> VS.t **)

  let rec vars_eexp = function
  | Evar v -> VS.singleton v
  | Econst _ -> VS.empty
  | Eunop (_, e0) -> vars_eexp e0
  | Ebinop (_, e1, e2) -> VS.union (vars_eexp e1) (vars_eexp e2)
  | Epow (e0, _) -> vars_eexp e0

  (** val vars_eexps : eexp list -> VS.t **)

  let rec vars_eexps = function
  | [] -> VS.empty
  | e :: es0 -> VS.union (vars_eexp e) (vars_eexps es0)

  (** val eexp_eqP : eexp -> eexp -> reflect **)

  let eexp_eqP e1 e2 =
    eexp_eqP V.coq_T e1 e2

  (** val eexp_eqMixin : eexp Equality.mixin_of **)

  let eexp_eqMixin =
    { Equality.op = (eexp_eqn V.coq_T); Equality.mixin_of__1 = eexp_eqP }

  (** val eexp_eqType : Equality.coq_type **)

  let eexp_eqType =
    Obj.magic eexp_eqMixin

  (** val limbsi : int -> coq_Z -> eexp list -> eexp **)

  let limbsi i r es =
    limbsi V.coq_T i r es

  (** val limbs : coq_Z -> eexp list -> eexp **)

  let limbs r es =
    limbsi 0 r es

  type rexp = Coq__2.rexp

  (** val size_of_rexp : rexp -> TE.env -> int **)

  let rec size_of_rexp e te =
    match e with
    | Rvar v -> TE.vsize v te
    | Rconst (w, _) -> w
    | Runop (w, _, _) -> w
    | Rbinop (w, _, _, _) -> w
    | Ruext (w, _, i) -> addn w i
    | Rsext (w, _, i) -> addn w i

  (** val rvar : Equality.sort -> rexp **)

  let rvar v =
    Rvar v

  (** val rconst : int -> bits -> rexp **)

  let rconst w n =
    Rconst (w, n)

  (** val rbits : bits -> rexp **)

  let rbits n =
    rbits V.coq_T n

  (** val runary : int -> runop -> rexp -> rexp **)

  let runary w op0 e =
    Runop (w, op0, e)

  (** val rbinary : int -> rbinop -> rexp -> rexp -> rexp **)

  let rbinary w op0 e1 e2 =
    Rbinop (w, op0, e1, e2)

  (** val rnegb : int -> rexp -> rexp **)

  let rnegb w e =
    Runop (w, Rnegb, e)

  (** val rnotb : int -> rexp -> rexp **)

  let rnotb w e =
    Runop (w, Rnotb, e)

  (** val radd : int -> rexp -> rexp -> rexp **)

  let radd w e1 e2 =
    Rbinop (w, Radd, e1, e2)

  (** val rsub : int -> rexp -> rexp -> rexp **)

  let rsub w e1 e2 =
    Rbinop (w, Rsub, e1, e2)

  (** val rmul : int -> rexp -> rexp -> rexp **)

  let rmul w e1 e2 =
    Rbinop (w, Rmul, e1, e2)

  (** val rumod : int -> rexp -> rexp -> rexp **)

  let rumod w e1 e2 =
    Rbinop (w, Rumod, e1, e2)

  (** val rsrem : int -> rexp -> rexp -> rexp **)

  let rsrem w e1 e2 =
    Rbinop (w, Rsrem, e1, e2)

  (** val rsmod : int -> rexp -> rexp -> rexp **)

  let rsmod w e1 e2 =
    Rbinop (w, Rsmod, e1, e2)

  (** val randb : int -> rexp -> rexp -> rexp **)

  let randb w e1 e2 =
    Rbinop (w, Randb, e1, e2)

  (** val rorb : int -> rexp -> rexp -> rexp **)

  let rorb w e1 e2 =
    Rbinop (w, Rorb, e1, e2)

  (** val rxorb : int -> rexp -> rexp -> rexp **)

  let rxorb w e1 e2 =
    Rbinop (w, Rxorb, e1, e2)

  (** val rsq : int -> rexp -> rexp **)

  let rsq w e =
    Rbinop (w, Rmul, e, e)

  (** val ruext : int -> rexp -> int -> rexp **)

  let ruext w e i =
    Ruext (w, e, i)

  (** val rsext : int -> rexp -> int -> rexp **)

  let rsext w e i =
    Rsext (w, e, i)

  (** val radds : int -> rexp list -> rexp **)

  let radds w es =
    radds V.coq_T w es

  (** val rmuls : int -> rexp list -> rexp **)

  let rmuls w es =
    rmuls V.coq_T w es

  (** val vars_rexp : rexp -> VS.t **)

  let rec vars_rexp = function
  | Rvar v -> VS.singleton v
  | Rconst (_, _) -> VS.empty
  | Runop (_, _, e0) -> vars_rexp e0
  | Rbinop (_, _, e1, e2) -> VS.union (vars_rexp e1) (vars_rexp e2)
  | Ruext (_, e0, _) -> vars_rexp e0
  | Rsext (_, e0, _) -> vars_rexp e0

  (** val rexp_eqP : rexp -> rexp -> reflect **)

  let rexp_eqP e1 e2 =
    rexp_eqP V.coq_T e1 e2

  (** val rexp_eqMixin : rexp Equality.mixin_of **)

  let rexp_eqMixin =
    { Equality.op = (rexp_eqn V.coq_T); Equality.mixin_of__1 = rexp_eqP }

  (** val rexp_eqType : Equality.coq_type **)

  let rexp_eqType =
    Obj.magic rexp_eqMixin

  type ebexp = Coq__3.ebexp

  (** val etrue : ebexp **)

  let etrue =
    Etrue

  (** val eeq : eexp -> eexp -> ebexp **)

  let eeq e1 e2 =
    Eeq (e1, e2)

  (** val eeqmod : eexp -> eexp -> eexp list -> ebexp **)

  let eeqmod e1 e2 ms =
    Eeqmod (e1, e2, ms)

  (** val eand : ebexp -> ebexp -> ebexp **)

  let eand b1 b2 =
    Eand (b1, b2)

  (** val eands : ebexp list -> ebexp **)

  let eands es =
    eands V.coq_T es

  (** val split_eand : ebexp -> ebexp list **)

  let split_eand e =
    split_eand V.coq_T e

  (** val vars_ebexp : ebexp -> VS.t **)

  let rec vars_ebexp = function
  | Etrue -> VS.empty
  | Eeq (e1, e2) -> VS.union (vars_eexp e1) (vars_eexp e2)
  | Eeqmod (e1, e2, ms) ->
    VS.union (vars_eexp e1) (VS.union (vars_eexp e2) (vars_eexps ms))
  | Eand (e1, e2) -> VS.union (vars_ebexp e1) (vars_ebexp e2)

  (** val ebexp_eqP : ebexp -> ebexp -> reflect **)

  let ebexp_eqP e1 e2 =
    ebexp_eqP V.coq_T e1 e2

  (** val ebexp_eqMixin : ebexp Equality.mixin_of **)

  let ebexp_eqMixin =
    { Equality.op = (ebexp_eqn V.coq_T); Equality.mixin_of__1 = ebexp_eqP }

  (** val ebexp_eqType : Equality.coq_type **)

  let ebexp_eqType =
    Obj.magic ebexp_eqMixin

  type rbexp = Coq__4.rbexp

  (** val rtrue : rbexp **)

  let rtrue =
    Rtrue

  (** val rfalse : rbexp **)

  let rfalse =
    Rneg rtrue

  (** val req : int -> rexp -> rexp -> rbexp **)

  let req w e1 e2 =
    Req (w, e1, e2)

  (** val rcmp : int -> rcmpop -> rexp -> rexp -> rbexp **)

  let rcmp w op0 e1 e2 =
    Rcmp (w, op0, e1, e2)

  (** val rult : int -> rexp -> rexp -> rbexp **)

  let rult w e1 e2 =
    Rcmp (w, Rult, e1, e2)

  (** val rule : int -> rexp -> rexp -> rbexp **)

  let rule w e1 e2 =
    Rcmp (w, Rule, e1, e2)

  (** val rugt : int -> rexp -> rexp -> rbexp **)

  let rugt w e1 e2 =
    Rcmp (w, Rugt, e1, e2)

  (** val ruge : int -> rexp -> rexp -> rbexp **)

  let ruge w e1 e2 =
    Rcmp (w, Ruge, e1, e2)

  (** val rslt : int -> rexp -> rexp -> rbexp **)

  let rslt w e1 e2 =
    Rcmp (w, Rslt, e1, e2)

  (** val rsle : int -> rexp -> rexp -> rbexp **)

  let rsle w e1 e2 =
    Rcmp (w, Rsle, e1, e2)

  (** val rsgt : int -> rexp -> rexp -> rbexp **)

  let rsgt w e1 e2 =
    Rcmp (w, Rsgt, e1, e2)

  (** val rsge : int -> rexp -> rexp -> rbexp **)

  let rsge w e1 e2 =
    Rcmp (w, Rsge, e1, e2)

  (** val reqmod : int -> rexp -> rexp -> rexp -> rbexp **)

  let reqmod w e1 e2 m =
    req w (rsrem w (rsub w e1 e2) m) (rbits (from_nat w 0))

  (** val rneg : rbexp -> rbexp **)

  let rneg e =
    Rneg e

  (** val rand : rbexp -> rbexp -> rbexp **)

  let rand e1 e2 =
    Rand (e1, e2)

  (** val ror : rbexp -> rbexp -> rbexp **)

  let ror e1 e2 =
    Ror (e1, e2)

  (** val rands : rbexp list -> rbexp **)

  let rands es =
    rands V.coq_T es

  (** val rors : rbexp list -> rbexp **)

  let rors es =
    rors V.coq_T es

  (** val vars_rbexp : rbexp -> VS.t **)

  let rec vars_rbexp = function
  | Rtrue -> VS.empty
  | Req (_, e1, e2) -> VS.union (vars_rexp e1) (vars_rexp e2)
  | Rcmp (_, _, e1, e2) -> VS.union (vars_rexp e1) (vars_rexp e2)
  | Rneg e0 -> vars_rbexp e0
  | Rand (e1, e2) -> VS.union (vars_rbexp e1) (vars_rbexp e2)
  | Ror (e1, e2) -> VS.union (vars_rbexp e1) (vars_rbexp e2)

  (** val rbexp_eqP : rbexp -> rbexp -> reflect **)

  let rbexp_eqP e1 e2 =
    rbexp_eqP V.coq_T e1 e2

  (** val rbexp_eqMixin : rbexp Equality.mixin_of **)

  let rbexp_eqMixin =
    { Equality.op = (rbexp_eqn V.coq_T); Equality.mixin_of__1 = rbexp_eqP }

  (** val rbexp_eqType : Equality.coq_type **)

  let rbexp_eqType =
    Obj.magic rbexp_eqMixin

  type bexp = ebexp * rbexp

  (** val btrue : bexp **)

  let btrue =
    (etrue, rtrue)

  (** val eqn_bexp : bexp -> ebexp **)

  let eqn_bexp =
    fst

  (** val rng_bexp : bexp -> rbexp **)

  let rng_bexp =
    snd

  (** val band : bexp -> bexp -> bexp **)

  let band e1 e2 =
    let (ee1, re1) = e1 in
    (match ee1 with
     | Etrue ->
       (match re1 with
        | Rtrue -> e2
        | _ ->
          let (ee2, re2) = e2 in
          (match ee2 with
           | Etrue ->
             (match re2 with
              | Rtrue -> (ee1, re1)
              | _ -> ((eand ee1 ee2), (rand re1 re2)))
           | _ ->
             (match re2 with
              | Rtrue -> (ee2, re1)
              | _ -> ((eand ee1 ee2), (rand re1 re2)))))
     | _ ->
       (match re1 with
        | Rtrue ->
          let (ee2, re2) = e2 in
          (match ee2 with
           | Etrue -> (match re2 with
                       | Rtrue -> (ee1, re1)
                       | _ -> (ee1, re2))
           | _ -> ((eand ee1 ee2), (rand re1 re2)))
        | _ ->
          let (ee2, re2) = e2 in
          (match ee2 with
           | Etrue ->
             (match re2 with
              | Rtrue -> (ee1, re1)
              | _ -> ((eand ee1 ee2), (rand re1 re2)))
           | _ -> ((eand ee1 ee2), (rand re1 re2)))))

  (** val bands : bexp list -> bexp **)

  let bands es =
    foldl band btrue es

  (** val bands2 : ebexp list -> rbexp list -> ebexp * rbexp **)

  let bands2 es rs =
    ((eands es), (rands rs))

  (** val vars_bexp : bexp -> VS.t **)

  let vars_bexp e =
    VS.union (vars_ebexp (eqn_bexp e)) (vars_rbexp (rng_bexp e))

  type atom =
  | Avar of V.t
  | Aconst of typ * bits

  (** val atom_rect : (V.t -> 'a1) -> (typ -> bits -> 'a1) -> atom -> 'a1 **)

  let atom_rect f f0 = function
  | Avar t0 -> f t0
  | Aconst (t0, b) -> f0 t0 b

  (** val atom_rec : (V.t -> 'a1) -> (typ -> bits -> 'a1) -> atom -> 'a1 **)

  let atom_rec f f0 = function
  | Avar t0 -> f t0
  | Aconst (t0, b) -> f0 t0 b

  (** val atyp : atom -> TE.env -> typ **)

  let atyp a te =
    match a with
    | Avar v -> TE.vtyp v te
    | Aconst (ty, _) -> ty

  (** val asize : atom -> TE.env -> int **)

  let asize a te =
    sizeof_typ (atyp a te)

  type instr =
  | Imov of V.t * atom
  | Ishl of V.t * atom * int
  | Icshl of V.t * V.t * atom * atom * int
  | Inondet of V.t * typ
  | Icmov of V.t * atom * atom * atom
  | Inop
  | Inot of V.t * typ * atom
  | Iadd of V.t * atom * atom
  | Iadds of V.t * V.t * atom * atom
  | Iadc of V.t * atom * atom * atom
  | Iadcs of V.t * V.t * atom * atom * atom
  | Isub of V.t * atom * atom
  | Isubc of V.t * V.t * atom * atom
  | Isubb of V.t * V.t * atom * atom
  | Isbc of V.t * atom * atom * atom
  | Isbcs of V.t * V.t * atom * atom * atom
  | Isbb of V.t * atom * atom * atom
  | Isbbs of V.t * V.t * atom * atom * atom
  | Imul of V.t * atom * atom
  | Imull of V.t * V.t * atom * atom
  | Imulj of V.t * atom * atom
  | Isplit of V.t * V.t * atom * int
  | Iand of V.t * typ * atom * atom
  | Ior of V.t * typ * atom * atom
  | Ixor of V.t * typ * atom * atom
  | Icast of V.t * typ * atom
  | Ivpc of V.t * typ * atom
  | Ijoin of V.t * atom * atom
  | Iassume of bexp

  (** val instr_rect :
      (V.t -> atom -> 'a1) -> (V.t -> atom -> int -> 'a1) -> (V.t -> V.t ->
      atom -> atom -> int -> 'a1) -> (V.t -> typ -> 'a1) -> (V.t -> atom ->
      atom -> atom -> 'a1) -> 'a1 -> (V.t -> typ -> atom -> 'a1) -> (V.t ->
      atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> 'a1) -> (V.t ->
      atom -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> atom ->
      'a1) -> (V.t -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom ->
      'a1) -> (V.t -> V.t -> atom -> atom -> 'a1) -> (V.t -> atom -> atom ->
      atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> atom -> 'a1) -> (V.t ->
      atom -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> atom ->
      'a1) -> (V.t -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom ->
      'a1) -> (V.t -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> int ->
      'a1) -> (V.t -> typ -> atom -> atom -> 'a1) -> (V.t -> typ -> atom ->
      atom -> 'a1) -> (V.t -> typ -> atom -> atom -> 'a1) -> (V.t -> typ ->
      atom -> 'a1) -> (V.t -> typ -> atom -> 'a1) -> (V.t -> atom -> atom ->
      'a1) -> (bexp -> 'a1) -> instr -> 'a1 **)

  let instr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 = function
  | Imov (t0, a) -> f t0 a
  | Ishl (t0, a, n) -> f0 t0 a n
  | Icshl (t0, t1, a, a0, n) -> f1 t0 t1 a a0 n
  | Inondet (t0, t1) -> f2 t0 t1
  | Icmov (t0, a, a0, a1) -> f3 t0 a a0 a1
  | Inop -> f4
  | Inot (t0, t1, a) -> f5 t0 t1 a
  | Iadd (t0, a, a0) -> f6 t0 a a0
  | Iadds (t0, t1, a, a0) -> f7 t0 t1 a a0
  | Iadc (t0, a, a0, a1) -> f8 t0 a a0 a1
  | Iadcs (t0, t1, a, a0, a1) -> f9 t0 t1 a a0 a1
  | Isub (t0, a, a0) -> f10 t0 a a0
  | Isubc (t0, t1, a, a0) -> f11 t0 t1 a a0
  | Isubb (t0, t1, a, a0) -> f12 t0 t1 a a0
  | Isbc (t0, a, a0, a1) -> f13 t0 a a0 a1
  | Isbcs (t0, t1, a, a0, a1) -> f14 t0 t1 a a0 a1
  | Isbb (t0, a, a0, a1) -> f15 t0 a a0 a1
  | Isbbs (t0, t1, a, a0, a1) -> f16 t0 t1 a a0 a1
  | Imul (t0, a, a0) -> f17 t0 a a0
  | Imull (t0, t1, a, a0) -> f18 t0 t1 a a0
  | Imulj (t0, a, a0) -> f19 t0 a a0
  | Isplit (t0, t1, a, n) -> f20 t0 t1 a n
  | Iand (t0, t1, a, a0) -> f21 t0 t1 a a0
  | Ior (t0, t1, a, a0) -> f22 t0 t1 a a0
  | Ixor (t0, t1, a, a0) -> f23 t0 t1 a a0
  | Icast (t0, t1, a) -> f24 t0 t1 a
  | Ivpc (t0, t1, a) -> f25 t0 t1 a
  | Ijoin (t0, a, a0) -> f26 t0 a a0
  | Iassume b -> f27 b

  (** val instr_rec :
      (V.t -> atom -> 'a1) -> (V.t -> atom -> int -> 'a1) -> (V.t -> V.t ->
      atom -> atom -> int -> 'a1) -> (V.t -> typ -> 'a1) -> (V.t -> atom ->
      atom -> atom -> 'a1) -> 'a1 -> (V.t -> typ -> atom -> 'a1) -> (V.t ->
      atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> 'a1) -> (V.t ->
      atom -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> atom ->
      'a1) -> (V.t -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom ->
      'a1) -> (V.t -> V.t -> atom -> atom -> 'a1) -> (V.t -> atom -> atom ->
      atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> atom -> 'a1) -> (V.t ->
      atom -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom -> atom ->
      'a1) -> (V.t -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> atom ->
      'a1) -> (V.t -> atom -> atom -> 'a1) -> (V.t -> V.t -> atom -> int ->
      'a1) -> (V.t -> typ -> atom -> atom -> 'a1) -> (V.t -> typ -> atom ->
      atom -> 'a1) -> (V.t -> typ -> atom -> atom -> 'a1) -> (V.t -> typ ->
      atom -> 'a1) -> (V.t -> typ -> atom -> 'a1) -> (V.t -> atom -> atom ->
      'a1) -> (bexp -> 'a1) -> instr -> 'a1 **)

  let instr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 = function
  | Imov (t0, a) -> f t0 a
  | Ishl (t0, a, n) -> f0 t0 a n
  | Icshl (t0, t1, a, a0, n) -> f1 t0 t1 a a0 n
  | Inondet (t0, t1) -> f2 t0 t1
  | Icmov (t0, a, a0, a1) -> f3 t0 a a0 a1
  | Inop -> f4
  | Inot (t0, t1, a) -> f5 t0 t1 a
  | Iadd (t0, a, a0) -> f6 t0 a a0
  | Iadds (t0, t1, a, a0) -> f7 t0 t1 a a0
  | Iadc (t0, a, a0, a1) -> f8 t0 a a0 a1
  | Iadcs (t0, t1, a, a0, a1) -> f9 t0 t1 a a0 a1
  | Isub (t0, a, a0) -> f10 t0 a a0
  | Isubc (t0, t1, a, a0) -> f11 t0 t1 a a0
  | Isubb (t0, t1, a, a0) -> f12 t0 t1 a a0
  | Isbc (t0, a, a0, a1) -> f13 t0 a a0 a1
  | Isbcs (t0, t1, a, a0, a1) -> f14 t0 t1 a a0 a1
  | Isbb (t0, a, a0, a1) -> f15 t0 a a0 a1
  | Isbbs (t0, t1, a, a0, a1) -> f16 t0 t1 a a0 a1
  | Imul (t0, a, a0) -> f17 t0 a a0
  | Imull (t0, t1, a, a0) -> f18 t0 t1 a a0
  | Imulj (t0, a, a0) -> f19 t0 a a0
  | Isplit (t0, t1, a, n) -> f20 t0 t1 a n
  | Iand (t0, t1, a, a0) -> f21 t0 t1 a a0
  | Ior (t0, t1, a, a0) -> f22 t0 t1 a a0
  | Ixor (t0, t1, a, a0) -> f23 t0 t1 a a0
  | Icast (t0, t1, a) -> f24 t0 t1 a
  | Ivpc (t0, t1, a) -> f25 t0 t1 a
  | Ijoin (t0, a, a0) -> f26 t0 a a0
  | Iassume b -> f27 b

  type program = instr list

  (** val vars_atom : atom -> VS.t **)

  let vars_atom = function
  | Avar v -> VS.singleton v
  | Aconst (_, _) -> VS.empty

  (** val vars_instr : instr -> VS.t **)

  let vars_instr = function
  | Imov (v, a) -> VS.add v (vars_atom a)
  | Ishl (v, a, _) -> VS.add v (vars_atom a)
  | Icshl (vh, vl, a1, a2, _) ->
    VS.add vh (VS.add vl (VS.union (vars_atom a1) (vars_atom a2)))
  | Inondet (v, _) -> VS.singleton v
  | Icmov (v, c, a1, a2) ->
    VS.add v (VS.union (vars_atom c) (VS.union (vars_atom a1) (vars_atom a2)))
  | Inop -> VS.empty
  | Inot (v, _, a) -> VS.add v (vars_atom a)
  | Iadd (v, a1, a2) -> VS.add v (VS.union (vars_atom a1) (vars_atom a2))
  | Iadds (c, v, a1, a2) ->
    VS.add c (VS.add v (VS.union (vars_atom a1) (vars_atom a2)))
  | Iadc (v, a1, a2, y) ->
    VS.add v (VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y)))
  | Iadcs (c, v, a1, a2, y) ->
    VS.add c
      (VS.add v
        (VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))))
  | Isub (v, a1, a2) -> VS.add v (VS.union (vars_atom a1) (vars_atom a2))
  | Isubc (c, v, a1, a2) ->
    VS.add c (VS.add v (VS.union (vars_atom a1) (vars_atom a2)))
  | Isubb (c, v, a1, a2) ->
    VS.add c (VS.add v (VS.union (vars_atom a1) (vars_atom a2)))
  | Isbc (v, a1, a2, y) ->
    VS.add v (VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y)))
  | Isbcs (c, v, a1, a2, y) ->
    VS.add c
      (VS.add v
        (VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))))
  | Isbb (v, a1, a2, y) ->
    VS.add v (VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y)))
  | Isbbs (c, v, a1, a2, y) ->
    VS.add c
      (VS.add v
        (VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))))
  | Imul (v, a1, a2) -> VS.add v (VS.union (vars_atom a1) (vars_atom a2))
  | Imull (vh, vl, a1, a2) ->
    VS.add vh (VS.add vl (VS.union (vars_atom a1) (vars_atom a2)))
  | Imulj (v, a1, a2) -> VS.add v (VS.union (vars_atom a1) (vars_atom a2))
  | Isplit (vh, vl, a, _) -> VS.add vh (VS.add vl (vars_atom a))
  | Iand (v, _, a1, a2) -> VS.add v (VS.union (vars_atom a1) (vars_atom a2))
  | Ior (v, _, a1, a2) -> VS.add v (VS.union (vars_atom a1) (vars_atom a2))
  | Ixor (v, _, a1, a2) -> VS.add v (VS.union (vars_atom a1) (vars_atom a2))
  | Icast (v, _, a) -> VS.add v (vars_atom a)
  | Ivpc (v, _, a) -> VS.add v (vars_atom a)
  | Ijoin (v, ah, al) -> VS.add v (VS.union (vars_atom ah) (vars_atom al))
  | Iassume e -> vars_bexp e

  (** val lvs_instr : instr -> VS.t **)

  let lvs_instr = function
  | Imov (v, _) -> VS.singleton v
  | Ishl (v, _, _) -> VS.singleton v
  | Icshl (vh, vl, _, _, _) -> VS.add vh (VS.singleton vl)
  | Inondet (v, _) -> VS.singleton v
  | Icmov (v, _, _, _) -> VS.singleton v
  | Inot (v, _, _) -> VS.singleton v
  | Iadd (v, _, _) -> VS.singleton v
  | Iadds (c, v, _, _) -> VS.add c (VS.singleton v)
  | Iadc (v, _, _, _) -> VS.singleton v
  | Iadcs (c, v, _, _, _) -> VS.add c (VS.singleton v)
  | Isub (v, _, _) -> VS.singleton v
  | Isubc (c, v, _, _) -> VS.add c (VS.singleton v)
  | Isubb (c, v, _, _) -> VS.add c (VS.singleton v)
  | Isbc (v, _, _, _) -> VS.singleton v
  | Isbcs (c, v, _, _, _) -> VS.add c (VS.singleton v)
  | Isbb (v, _, _, _) -> VS.singleton v
  | Isbbs (c, v, _, _, _) -> VS.add c (VS.singleton v)
  | Imul (v, _, _) -> VS.singleton v
  | Imull (vh, vl, _, _) -> VS.add vh (VS.singleton vl)
  | Imulj (v, _, _) -> VS.singleton v
  | Isplit (vh, vl, _, _) -> VS.add vh (VS.singleton vl)
  | Iand (v, _, _, _) -> VS.singleton v
  | Ior (v, _, _, _) -> VS.singleton v
  | Ixor (v, _, _, _) -> VS.singleton v
  | Icast (v, _, _) -> VS.singleton v
  | Ivpc (v, _, _) -> VS.singleton v
  | Ijoin (v, _, _) -> VS.singleton v
  | _ -> VS.empty

  (** val rvs_instr : instr -> VS.t **)

  let rvs_instr = function
  | Imov (_, a) -> vars_atom a
  | Ishl (_, a, _) -> vars_atom a
  | Icshl (_, _, a1, a2, _) -> VS.union (vars_atom a1) (vars_atom a2)
  | Icmov (_, c, a1, a2) ->
    VS.union (vars_atom c) (VS.union (vars_atom a1) (vars_atom a2))
  | Inot (_, _, a) -> vars_atom a
  | Iadd (_, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Iadds (_, _, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Iadc (_, a1, a2, y) ->
    VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))
  | Iadcs (_, _, a1, a2, y) ->
    VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))
  | Isub (_, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Isubc (_, _, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Isubb (_, _, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Isbc (_, a1, a2, y) ->
    VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))
  | Isbcs (_, _, a1, a2, y) ->
    VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))
  | Isbb (_, a1, a2, y) ->
    VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))
  | Isbbs (_, _, a1, a2, y) ->
    VS.union (vars_atom a1) (VS.union (vars_atom a2) (vars_atom y))
  | Imul (_, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Imull (_, _, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Imulj (_, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Isplit (_, _, a, _) -> vars_atom a
  | Iand (_, _, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Ior (_, _, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Ixor (_, _, a1, a2) -> VS.union (vars_atom a1) (vars_atom a2)
  | Icast (_, _, a) -> vars_atom a
  | Ivpc (_, _, a) -> vars_atom a
  | Ijoin (_, ah, al) -> VS.union (vars_atom ah) (vars_atom al)
  | Iassume e -> vars_bexp e
  | _ -> VS.empty

  (** val vars_program : program -> VS.t **)

  let rec vars_program = function
  | [] -> VS.empty
  | hd :: tl -> VS.union (vars_instr hd) (vars_program tl)

  (** val lvs_program : program -> VS.t **)

  let rec lvs_program = function
  | [] -> VS.empty
  | hd :: tl -> VS.union (lvs_instr hd) (lvs_program tl)

  (** val rvs_program : program -> VS.t **)

  let rec rvs_program = function
  | [] -> VS.empty
  | hd :: tl -> VS.union (rvs_instr hd) (rvs_program tl)

  (** val eqn_instr : instr -> instr **)

  let eqn_instr i = match i with
  | Iassume b -> let (ee, _) = b in Iassume (ee, rtrue)
  | _ -> i

  (** val rng_instr : instr -> instr **)

  let rng_instr i = match i with
  | Iassume b -> let (_, re) = b in Iassume (etrue, re)
  | _ -> i

  (** val eqn_program : program -> program **)

  let rec eqn_program = function
  | [] -> []
  | hd :: tl -> (eqn_instr hd) :: (eqn_program tl)

  (** val rng_program : program -> program **)

  let rec rng_program = function
  | [] -> []
  | hd :: tl -> (rng_instr hd) :: (rng_program tl)

  type spec = { sinputs : TE.env; spre : bexp; sprog : program; spost : bexp }

  (** val sinputs : spec -> TE.env **)

  let sinputs s =
    s.sinputs

  (** val spre : spec -> bexp **)

  let spre s =
    s.spre

  (** val sprog : spec -> program **)

  let sprog s =
    s.sprog

  (** val spost : spec -> bexp **)

  let spost s =
    s.spost

  type espec = { esinputs : TE.env; espre : bexp; esprog : program;
                 espost : ebexp }

  (** val esinputs : espec -> TE.env **)

  let esinputs e =
    e.esinputs

  (** val espre : espec -> bexp **)

  let espre e =
    e.espre

  (** val esprog : espec -> program **)

  let esprog e =
    e.esprog

  (** val espost : espec -> ebexp **)

  let espost e =
    e.espost

  type rspec = { rsinputs : TE.env; rspre : rbexp; rsprog : program;
                 rspost : rbexp }

  (** val rsinputs : rspec -> TE.env **)

  let rsinputs r =
    r.rsinputs

  (** val rspre : rspec -> rbexp **)

  let rspre r =
    r.rspre

  (** val rsprog : rspec -> program **)

  let rsprog r =
    r.rsprog

  (** val rspost : rspec -> rbexp **)

  let rspost r =
    r.rspost

  (** val espec_of_spec : spec -> espec **)

  let espec_of_spec s =
    { esinputs = (sinputs s); espre = (spre s); esprog = (sprog s); espost =
      (eqn_bexp (spost s)) }

  (** val rspec_of_spec : spec -> rspec **)

  let rspec_of_spec s =
    { rsinputs = (sinputs s); rspre = (rng_bexp (spre s)); rsprog =
      (rng_program (sprog s)); rspost = (rng_bexp (spost s)) }

  (** val bv2z : typ -> bits -> coq_Z **)

  let bv2z t0 bs =
    match t0 with
    | Tuint _ -> to_Zpos bs
    | Tsint _ -> to_Z bs

  (** val acc2z : TE.env -> V.t -> S.t -> coq_Z **)

  let acc2z e v s =
    bv2z (TE.vtyp v e) (S.acc v s)

  (** val eval_eunop : eunop -> coq_Z -> coq_Z **)

  let eval_eunop _ =
    Z.opp

  (** val eval_ebinop : ebinop -> coq_Z -> coq_Z -> coq_Z **)

  let eval_ebinop op0 v1 v2 =
    match op0 with
    | Eadd -> Z.add v1 v2
    | Esub -> Z.sub v1 v2
    | Emul -> Z.mul v1 v2

  (** val eval_runop : runop -> bits -> bits **)

  let eval_runop op0 v =
    match op0 with
    | Rnegb -> negB v
    | Rnotb -> invB v

  (** val eval_rbinop : rbinop -> bits -> bits -> bits **)

  let eval_rbinop op0 v1 v2 =
    match op0 with
    | Radd -> addB v1 v2
    | Rsub -> subB v1 v2
    | Rmul -> mulB v1 v2
    | Rumod -> uremB v1 v2
    | Rsrem -> sremB v1 v2
    | Rsmod -> smodB v1 v2
    | Randb -> andB v1 v2
    | Rorb -> orB v1 v2
    | Rxorb -> xorB v1 v2

  (** val eval_rcmpop : rcmpop -> bits -> bits -> bool **)

  let eval_rcmpop op0 v1 v2 =
    match op0 with
    | Rult -> ltB_lsb v1 v2
    | Rule -> leB v1 v2
    | Rugt -> gtB v1 v2
    | Ruge -> geB v1 v2
    | Rslt -> sltB v1 v2
    | Rsle -> sleB v1 v2
    | Rsgt -> sgtB v1 v2
    | Rsge -> sgeB v1 v2

  (** val eval_eexp : eexp -> TE.env -> S.t -> coq_Z **)

  let rec eval_eexp e te s =
    match e with
    | Evar v -> acc2z te v s
    | Econst n -> n
    | Eunop (op0, e0) -> eval_eunop op0 (eval_eexp e0 te s)
    | Ebinop (op0, e1, e2) ->
      eval_ebinop op0 (eval_eexp e1 te s) (eval_eexp e2 te s)
    | Epow (e0, n) -> Z.pow (eval_eexp e0 te s) (Z.of_N n)

  (** val eval_eexps : eexp list -> TE.env -> S.t -> coq_Z list **)

  let eval_eexps es te s =
    map (fun e -> eval_eexp e te s) es

  (** val eval_rexp : rexp -> S.t -> bits **)

  let rec eval_rexp e s =
    match e with
    | Rvar v -> S.acc v s
    | Rconst (_, n) -> n
    | Runop (_, op0, e0) -> eval_runop op0 (eval_rexp e0 s)
    | Rbinop (_, op0, e1, e2) ->
      eval_rbinop op0 (eval_rexp e1 s) (eval_rexp e2 s)
    | Ruext (_, e0, i) -> zext i (eval_rexp e0 s)
    | Rsext (_, e0, i) -> sext i (eval_rexp e0 s)

  (** val eval_rbexp : rbexp -> S.t -> bool **)

  let rec eval_rbexp e s =
    match e with
    | Rtrue -> true
    | Req (_, e1, e2) ->
      eq_op bitseq_eqType (Obj.magic eval_rexp e1 s)
        (Obj.magic eval_rexp e2 s)
    | Rcmp (_, op0, e1, e2) ->
      eval_rcmpop op0 (eval_rexp e1 s) (eval_rexp e2 s)
    | Rneg e0 -> negb (eval_rbexp e0 s)
    | Rand (e1, e2) -> (&&) (eval_rbexp e1 s) (eval_rbexp e2 s)
    | Ror (e1, e2) -> (||) (eval_rbexp e1 s) (eval_rbexp e2 s)

  (** val eval_atom : atom -> S.t -> bits **)

  let eval_atom a s =
    match a with
    | Avar v -> S.acc v s
    | Aconst (_, n) -> n

  (** val instr_succ_typenv : instr -> TE.env -> TE.env **)

  let instr_succ_typenv i te =
    match i with
    | Imov (v, a) -> TE.add v (atyp a te) te
    | Ishl (v, a, _) -> TE.add v (atyp a te) te
    | Icshl (v1, v2, a1, a2, _) ->
      TE.add v1 (atyp a1 te) (TE.add v2 (atyp a2 te) te)
    | Inondet (v, t0) -> TE.add v t0 te
    | Icmov (v, _, a1, _) -> TE.add v (atyp a1 te) te
    | Inot (v, t0, _) -> TE.add v t0 te
    | Iadd (v, a1, _) -> TE.add v (atyp a1 te) te
    | Iadds (c, v, a1, _) -> TE.add c coq_Tbit (TE.add v (atyp a1 te) te)
    | Iadc (v, a1, _, _) -> TE.add v (atyp a1 te) te
    | Iadcs (c, v, a1, _, _) -> TE.add c coq_Tbit (TE.add v (atyp a1 te) te)
    | Isub (v, a1, _) -> TE.add v (atyp a1 te) te
    | Isubc (c, v, a1, _) -> TE.add c coq_Tbit (TE.add v (atyp a1 te) te)
    | Isubb (c, v, a1, _) -> TE.add c coq_Tbit (TE.add v (atyp a1 te) te)
    | Isbc (v, a1, _, _) -> TE.add v (atyp a1 te) te
    | Isbcs (c, v, a1, _, _) -> TE.add c coq_Tbit (TE.add v (atyp a1 te) te)
    | Isbb (v, a1, _, _) -> TE.add v (atyp a1 te) te
    | Isbbs (c, v, a1, _, _) -> TE.add c coq_Tbit (TE.add v (atyp a1 te) te)
    | Imul (v, a1, _) -> TE.add v (atyp a1 te) te
    | Imull (vh, vl, a1, a2) ->
      TE.add vh (atyp a1 te) (TE.add vl (unsigned_typ (atyp a2 te)) te)
    | Imulj (v, a1, _) -> TE.add v (double_typ (atyp a1 te)) te
    | Isplit (vh, vl, a, _) ->
      TE.add vh (atyp a te) (TE.add vl (unsigned_typ (atyp a te)) te)
    | Iand (v, t0, _, _) -> TE.add v t0 te
    | Ior (v, t0, _, _) -> TE.add v t0 te
    | Ixor (v, t0, _, _) -> TE.add v t0 te
    | Icast (v, t0, _) -> TE.add v t0 te
    | Ivpc (v, t0, _) -> TE.add v t0 te
    | Ijoin (v, ah, _) -> TE.add v (double_typ (atyp ah te)) te
    | _ -> te

  (** val program_succ_typenv : program -> TE.env -> TE.env **)

  let program_succ_typenv p te =
    foldl (fun te0 i -> instr_succ_typenv i te0) te p

  (** val well_typed_eexp : TE.env -> eexp -> bool **)

  let rec well_typed_eexp te = function
  | Eunop (_, e0) -> well_typed_eexp te e0
  | Ebinop (_, e1, e2) -> (&&) (well_typed_eexp te e1) (well_typed_eexp te e2)
  | Epow (e0, _) -> well_typed_eexp te e0
  | _ -> true

  (** val well_typed_eexps : TE.env -> eexp list -> bool **)

  let rec well_typed_eexps te = function
  | [] -> true
  | e :: es0 -> (&&) (well_typed_eexp te e) (well_typed_eexps te es0)

  (** val well_typed_rexp : TE.env -> rexp -> bool **)

  let rec well_typed_rexp te = function
  | Rvar v -> leq (Pervasives.succ 0) (TE.vsize v te)
  | Rconst (w, n) ->
    (&&) (leq (Pervasives.succ 0) w)
      (eq_op nat_eqType (Obj.magic size n) (Obj.magic w))
  | Runop (w, _, e0) ->
    (&&) ((&&) (leq (Pervasives.succ 0) w) (well_typed_rexp te e0))
      (eq_op nat_eqType (Obj.magic size_of_rexp e0 te) (Obj.magic w))
  | Rbinop (w, _, e1, e2) ->
    (&&)
      ((&&)
        ((&&) ((&&) (leq (Pervasives.succ 0) w) (well_typed_rexp te e1))
          (eq_op nat_eqType (Obj.magic size_of_rexp e1 te) (Obj.magic w)))
        (well_typed_rexp te e2))
      (eq_op nat_eqType (Obj.magic size_of_rexp e2 te) (Obj.magic w))
  | Ruext (w, e0, _) ->
    (&&) ((&&) (leq (Pervasives.succ 0) w) (well_typed_rexp te e0))
      (eq_op nat_eqType (Obj.magic size_of_rexp e0 te) (Obj.magic w))
  | Rsext (w, e0, _) ->
    (&&) ((&&) (leq (Pervasives.succ 0) w) (well_typed_rexp te e0))
      (eq_op nat_eqType (Obj.magic size_of_rexp e0 te) (Obj.magic w))

  (** val well_typed_ebexp : TE.env -> ebexp -> bool **)

  let rec well_typed_ebexp te = function
  | Etrue -> true
  | Eeq (e1, e2) -> (&&) (well_typed_eexp te e1) (well_typed_eexp te e2)
  | Eeqmod (e1, e2, ms) ->
    (&&) ((&&) (well_typed_eexp te e1) (well_typed_eexp te e2))
      (well_typed_eexps te ms)
  | Eand (e1, e2) -> (&&) (well_typed_ebexp te e1) (well_typed_ebexp te e2)

  (** val well_typed_rbexp : TE.env -> rbexp -> bool **)

  let rec well_typed_rbexp te = function
  | Rtrue -> true
  | Req (w, e1, e2) ->
    (&&)
      ((&&)
        ((&&) ((&&) (leq (Pervasives.succ 0) w) (well_typed_rexp te e1))
          (eq_op nat_eqType (Obj.magic size_of_rexp e1 te) (Obj.magic w)))
        (well_typed_rexp te e2))
      (eq_op nat_eqType (Obj.magic size_of_rexp e2 te) (Obj.magic w))
  | Rcmp (w, _, e1, e2) ->
    (&&)
      ((&&)
        ((&&) ((&&) (leq (Pervasives.succ 0) w) (well_typed_rexp te e1))
          (eq_op nat_eqType (Obj.magic size_of_rexp e1 te) (Obj.magic w)))
        (well_typed_rexp te e2))
      (eq_op nat_eqType (Obj.magic size_of_rexp e2 te) (Obj.magic w))
  | Rneg e0 -> well_typed_rbexp te e0
  | Rand (e1, e2) -> (&&) (well_typed_rbexp te e1) (well_typed_rbexp te e2)
  | Ror (e1, e2) -> (&&) (well_typed_rbexp te e1) (well_typed_rbexp te e2)

  (** val well_typed_bexp : TE.env -> bexp -> bool **)

  let well_typed_bexp te e =
    (&&) (well_typed_ebexp te (eqn_bexp e)) (well_typed_rbexp te (rng_bexp e))

  (** val well_sized_atom : TE.env -> atom -> bool **)

  let well_sized_atom e a =
    if is_unsigned (atyp a e)
    then leq (Pervasives.succ 0) (asize a e)
    else leq (Pervasives.succ (Pervasives.succ 0)) (asize a e)

  (** val size_matched_atom : atom -> bool **)

  let size_matched_atom = function
  | Avar _ -> true
  | Aconst (t0, n) ->
    eq_op nat_eqType (Obj.magic size n) (Obj.magic sizeof_typ t0)

  (** val well_typed_atom : TE.env -> atom -> bool **)

  let well_typed_atom e a =
    (&&) (well_sized_atom e a) (size_matched_atom a)

  (** val well_typed_instr : TE.env -> instr -> bool **)

  let well_typed_instr e = function
  | Imov (_, a) -> well_typed_atom e a
  | Ishl (_, a, n) ->
    (&&) (well_typed_atom e a) (leq (Pervasives.succ n) (asize a e))
  | Icshl (_, _, a1, a2, n) ->
    (&&)
      ((&&)
        ((&&)
          ((&&) (is_unsigned (atyp a2 e))
            (compatible (atyp a1 e) (atyp a2 e))) (well_typed_atom e a1))
        (well_typed_atom e a2)) (leq n (asize a2 e))
  | Icmov (_, c, a1, a2) ->
    (&&)
      ((&&)
        ((&&)
          ((&&) (eq_op typ_eqType (Obj.magic atyp c e) (Obj.magic coq_Tbit))
            (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e)))
          (well_typed_atom e a1)) (well_typed_atom e a2))
      (well_typed_atom e c)
  | Inot (_, t0, a) -> (&&) (compatible t0 (atyp a e)) (well_typed_atom e a)
  | Iadd (_, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Iadds (_, _, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Iadc (_, a1, a2, y) ->
    (&&)
      ((&&)
        ((&&)
          ((&&)
            (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
            (eq_op typ_eqType (Obj.magic atyp y e) (Obj.magic coq_Tbit)))
          (well_typed_atom e a1)) (well_typed_atom e a2))
      (well_typed_atom e y)
  | Iadcs (_, _, a1, a2, y) ->
    (&&)
      ((&&)
        ((&&)
          ((&&)
            (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
            (eq_op typ_eqType (Obj.magic atyp y e) (Obj.magic coq_Tbit)))
          (well_typed_atom e a1)) (well_typed_atom e a2))
      (well_typed_atom e y)
  | Isub (_, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Isubc (_, _, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Isubb (_, _, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Isbc (_, a1, a2, y) ->
    (&&)
      ((&&)
        ((&&)
          ((&&)
            (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
            (eq_op typ_eqType (Obj.magic atyp y e) (Obj.magic coq_Tbit)))
          (well_typed_atom e a1)) (well_typed_atom e a2))
      (well_typed_atom e y)
  | Isbcs (_, _, a1, a2, y) ->
    (&&)
      ((&&)
        ((&&)
          ((&&)
            (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
            (eq_op typ_eqType (Obj.magic atyp y e) (Obj.magic coq_Tbit)))
          (well_typed_atom e a1)) (well_typed_atom e a2))
      (well_typed_atom e y)
  | Isbb (_, a1, a2, y) ->
    (&&)
      ((&&)
        ((&&)
          ((&&)
            (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
            (eq_op typ_eqType (Obj.magic atyp y e) (Obj.magic coq_Tbit)))
          (well_typed_atom e a1)) (well_typed_atom e a2))
      (well_typed_atom e y)
  | Isbbs (_, _, a1, a2, y) ->
    (&&)
      ((&&)
        ((&&)
          ((&&)
            (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
            (eq_op typ_eqType (Obj.magic atyp y e) (Obj.magic coq_Tbit)))
          (well_typed_atom e a1)) (well_typed_atom e a2))
      (well_typed_atom e y)
  | Imul (_, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Imull (_, _, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Imulj (_, a1, a2) ->
    (&&)
      ((&&) (eq_op typ_eqType (Obj.magic atyp a1 e) (Obj.magic atyp a2 e))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Isplit (_, _, a, n) ->
    (&&) (well_typed_atom e a) (leq (Pervasives.succ n) (asize a e))
  | Iand (_, t0, a1, a2) ->
    (&&)
      ((&&) ((&&) (compatible t0 (atyp a1 e)) (compatible t0 (atyp a2 e)))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Ior (_, t0, a1, a2) ->
    (&&)
      ((&&) ((&&) (compatible t0 (atyp a1 e)) (compatible t0 (atyp a2 e)))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Ixor (_, t0, a1, a2) ->
    (&&)
      ((&&) ((&&) (compatible t0 (atyp a1 e)) (compatible t0 (atyp a2 e)))
        (well_typed_atom e a1)) (well_typed_atom e a2)
  | Icast (_, _, a) -> well_typed_atom e a
  | Ivpc (_, _, a) -> well_typed_atom e a
  | Ijoin (_, ah, al) ->
    (&&)
      ((&&)
        ((&&) (is_unsigned (atyp al e)) (compatible (atyp ah e) (atyp al e)))
        (well_typed_atom e ah)) (well_typed_atom e al)
  | Iassume e0 -> well_typed_bexp e e0
  | _ -> true

  module TEKS = MapKeySet(V)(TE)(VS)

  (** val vars_env : TE.env -> VS.t **)

  let vars_env =
    TEKS.key_set

  (** val is_defined : V.t -> TE.env -> bool **)

  let is_defined =
    TE.mem

  (** val are_defined : VS.t -> TE.env -> bool **)

  let are_defined vs te =
    VS.for_all (fun x -> is_defined x te) vs

  (** val memenvP : TE.key -> typ TE.t -> reflect **)

  let memenvP v e =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if VS.mem v (vars_env e) then _evar_0_ __ else _evar_0_0 __

  (** val well_defined_instr : TE.env -> instr -> bool **)

  let well_defined_instr te = function
  | Imov (_, a) -> are_defined (vars_atom a) te
  | Ishl (_, a, _) -> are_defined (vars_atom a) te
  | Icshl (v1, v2, a1, a2, _) ->
    (&&) ((&&) (negb (eq_op V.coq_T v1 v2)) (are_defined (vars_atom a1) te))
      (are_defined (vars_atom a2) te)
  | Icmov (_, c, a1, a2) ->
    (&&)
      ((&&) (are_defined (vars_atom c) te) (are_defined (vars_atom a1) te))
      (are_defined (vars_atom a2) te)
  | Inot (_, _, a) -> are_defined (vars_atom a) te
  | Iadd (_, a1, a2) ->
    (&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te)
  | Iadds (c, v, a1, a2) ->
    (&&) ((&&) (negb (eq_op V.coq_T c v)) (are_defined (vars_atom a1) te))
      (are_defined (vars_atom a2) te)
  | Iadc (_, a1, a2, y) ->
    (&&)
      ((&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te))
      (are_defined (vars_atom y) te)
  | Iadcs (c, v, a1, a2, y) ->
    (&&)
      ((&&) ((&&) (negb (eq_op V.coq_T c v)) (are_defined (vars_atom a1) te))
        (are_defined (vars_atom a2) te)) (are_defined (vars_atom y) te)
  | Isub (_, a1, a2) ->
    (&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te)
  | Isubc (c, v, a1, a2) ->
    (&&) ((&&) (negb (eq_op V.coq_T c v)) (are_defined (vars_atom a1) te))
      (are_defined (vars_atom a2) te)
  | Isubb (c, v, a1, a2) ->
    (&&) ((&&) (negb (eq_op V.coq_T c v)) (are_defined (vars_atom a1) te))
      (are_defined (vars_atom a2) te)
  | Isbc (_, a1, a2, y) ->
    (&&)
      ((&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te))
      (are_defined (vars_atom y) te)
  | Isbcs (c, v, a1, a2, y) ->
    (&&)
      ((&&) ((&&) (negb (eq_op V.coq_T c v)) (are_defined (vars_atom a1) te))
        (are_defined (vars_atom a2) te)) (are_defined (vars_atom y) te)
  | Isbb (_, a1, a2, y) ->
    (&&)
      ((&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te))
      (are_defined (vars_atom y) te)
  | Isbbs (c, v, a1, a2, y) ->
    (&&)
      ((&&) ((&&) (negb (eq_op V.coq_T c v)) (are_defined (vars_atom a1) te))
        (are_defined (vars_atom a2) te)) (are_defined (vars_atom y) te)
  | Imul (_, a1, a2) ->
    (&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te)
  | Imull (vh, vl, a1, a2) ->
    (&&) ((&&) (negb (eq_op V.coq_T vh vl)) (are_defined (vars_atom a1) te))
      (are_defined (vars_atom a2) te)
  | Imulj (_, a1, a2) ->
    (&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te)
  | Isplit (vh, vl, a, _) ->
    (&&) (negb (eq_op V.coq_T vh vl)) (are_defined (vars_atom a) te)
  | Iand (_, _, a1, a2) ->
    (&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te)
  | Ior (_, _, a1, a2) ->
    (&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te)
  | Ixor (_, _, a1, a2) ->
    (&&) (are_defined (vars_atom a1) te) (are_defined (vars_atom a2) te)
  | Icast (_, _, a) -> are_defined (vars_atom a) te
  | Ivpc (_, _, a) -> are_defined (vars_atom a) te
  | Ijoin (_, ah, al) ->
    (&&) (are_defined (vars_atom ah) te) (are_defined (vars_atom al) te)
  | Iassume e -> are_defined (vars_bexp e) te
  | _ -> true

  (** val well_formed_instr : TE.env -> instr -> bool **)

  let well_formed_instr te i =
    (&&) (well_defined_instr te i) (well_typed_instr te i)

  (** val well_formed_program : TE.env -> program -> bool **)

  let rec well_formed_program te = function
  | [] -> true
  | hd :: tl ->
    (&&) (well_formed_instr te hd)
      (well_formed_program (instr_succ_typenv hd te) tl)

  (** val find_non_well_formed_instr : TE.env -> program -> instr option **)

  let rec find_non_well_formed_instr te = function
  | [] -> None
  | hd :: tl ->
    if well_formed_instr te hd
    then find_non_well_formed_instr (instr_succ_typenv hd te) tl
    else Some hd

  (** val well_formed_eexp : TE.env -> eexp -> bool **)

  let well_formed_eexp te e =
    (&&) (are_defined (vars_eexp e) te) (well_typed_eexp te e)

  (** val well_formed_eexps : TE.env -> eexp list -> bool **)

  let rec well_formed_eexps te = function
  | [] -> true
  | e :: es0 -> (&&) (well_formed_eexp te e) (well_formed_eexps te es0)

  (** val well_formed_rexp : TE.env -> rexp -> bool **)

  let well_formed_rexp te e =
    (&&) (are_defined (vars_rexp e) te) (well_typed_rexp te e)

  (** val well_formed_ebexp : TE.env -> ebexp -> bool **)

  let well_formed_ebexp te e =
    (&&) (are_defined (vars_ebexp e) te) (well_typed_ebexp te e)

  (** val well_formed_rbexp : TE.env -> rbexp -> bool **)

  let well_formed_rbexp te e =
    (&&) (are_defined (vars_rbexp e) te) (well_typed_rbexp te e)

  (** val well_formed_bexp : TE.env -> bexp -> bool **)

  let well_formed_bexp te e =
    (&&) (are_defined (vars_bexp e) te) (well_typed_bexp te e)

  (** val well_formed_spec : spec -> bool **)

  let well_formed_spec s =
    (&&)
      ((&&) (well_formed_bexp (sinputs s) (spre s))
        (well_formed_program (sinputs s) (sprog s)))
      (well_formed_bexp (program_succ_typenv (sprog s) (sinputs s)) (spost s))

  (** val defmemP : V.t -> TE.env -> reflect **)

  let defmemP v e =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if TE.mem v e then _evar_0_ __ else _evar_0_0 __

  (** val memdefP : TE.key -> typ TE.t -> reflect **)

  let memdefP v e =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if is_defined v e then _evar_0_ __ else _evar_0_0 __

  (** val defsubP : VS.t -> TE.env -> reflect **)

  let defsubP vs e =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if VS.subset vs (vars_env e) then _evar_0_ __ else _evar_0_0 __

  (** val is_assume : instr -> bool **)

  let is_assume = function
  | Iassume _ -> true
  | _ -> false

  (** val force_conform_vars : TE.env -> V.t list -> S.t -> S.t **)

  let rec force_conform_vars e vs s =
    match vs with
    | [] -> s
    | v :: vs0 -> S.upd v (zeros (TE.vsize v e)) (force_conform_vars e vs0 s)

  (** val force_conform : TE.env -> TE.env -> S.t -> S.t **)

  let force_conform e1 e2 s =
    force_conform_vars e2 (VS.elements (VS.diff (vars_env e2) (vars_env e1)))
      s
 end

module DSL = MakeDSL(VarOrder)(VS)(VM)(TypEnv.TE)(Store)
