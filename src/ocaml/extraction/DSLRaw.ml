open BinInt
open BinNums
open Bool
open NBitsDef
open String0
open Strings
open Typ
open ZAriths
open Eqtype
open Seq
open Ssrnat

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

(** val string_of_eunop : eunop -> char list **)

let string_of_eunop _ =
  '-'::[]

(** val string_of_ebinop : ebinop -> char list **)

let string_of_ebinop = function
| Eadd -> '+'::[]
| Esub -> '-'::[]
| Emul -> '*'::[]

(** val string_of_runop : runop -> char list **)

let string_of_runop = function
| Rnegb -> '-'::[]
| Rnotb -> '!'::[]

(** val string_of_rbinop : rbinop -> char list **)

let string_of_rbinop = function
| Radd -> '+'::[]
| Rsub -> '-'::[]
| Rmul -> '*'::[]
| Rumod -> 'u'::('m'::('o'::('d'::[])))
| Rsrem -> 's'::('r'::('e'::('m'::[])))
| Rsmod -> 's'::('m'::('o'::('d'::[])))
| Randb -> '&'::[]
| Rorb -> '|'::[]
| Rxorb -> 'x'::('o'::('r'::[]))

(** val string_of_rcmpop : rcmpop -> char list **)

let string_of_rcmpop = function
| Rult -> '<'::('u'::[])
| Rule -> '<'::('='::('u'::[]))
| Rugt -> '>'::('u'::[])
| Ruge -> '>'::('='::('u'::[]))
| Rslt -> '<'::('s'::[])
| Rsle -> '<'::('='::('s'::[]))
| Rsgt -> '>'::('s'::[])
| Rsge -> '>'::('='::('s'::[]))

type eexp =
| Evar of Equality.sort
| Econst of coq_Z
| Eunop of eunop * eexp
| Ebinop of ebinop * eexp * eexp
| Epow of eexp * coq_N

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

type rexp =
| Rvar of Equality.sort
| Rconst of int * bits
| Runop of int * runop * rexp
| Rbinop of int * rbinop * rexp * rexp
| Ruext of int * rexp * int
| Rsext of int * rexp * int

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

type ebexp =
| Etrue
| Eeq of eexp * eexp
| Eeqmod of eexp * eexp * eexp list
| Eand of ebexp * ebexp

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

type rbexp =
| Rtrue
| Req of int * rexp * rexp
| Rcmp of int * rcmpop * rexp * rexp
| Rneg of rbexp
| Rand of rbexp * rbexp
| Ror of rbexp * rbexp

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

(** val split_rand : Equality.coq_type -> rbexp -> rbexp list **)

let rec split_rand var e = match e with
| Rand (e1, e2) -> cat (split_rand var e1) (split_rand var e2)
| _ -> e :: []

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

type atom =
| Avar of Equality.sort
| Aconst of typ * bits

(** val atom_eqn : Equality.coq_type -> atom -> atom -> bool **)

let atom_eqn var a1 a2 =
  match a1 with
  | Avar v1 ->
    (match a2 with
     | Avar v2 -> eq_op var v1 v2
     | Aconst (_, _) -> false)
  | Aconst (ty1, n1) ->
    (match a2 with
     | Avar _ -> false
     | Aconst (ty2, n2) ->
       (&&) (eq_op typ_eqType (Obj.magic ty1) (Obj.magic ty2))
         (eq_op bitseq_eqType (Obj.magic n1) (Obj.magic n2)))

(** val atom_eqP : Equality.coq_type -> atom -> atom -> reflect **)

let atom_eqP var a1 a2 =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if atom_eqn var a1 a2 then _evar_0_ __ else _evar_0_0 __

(** val atom_eqMixin : Equality.coq_type -> atom Equality.mixin_of **)

let atom_eqMixin var =
  { Equality.op = (atom_eqn var); Equality.mixin_of__1 = (atom_eqP var) }

(** val atom_eqType : Equality.coq_type -> Equality.coq_type **)

let atom_eqType var =
  Obj.magic atom_eqMixin var

(** val string_of_eexp :
    Equality.coq_type -> (Equality.sort -> char list) -> eexp -> char list **)

let string_of_eexp _ string_of_var =
  let rec string_of_eexp0 = function
  | Evar v -> string_of_var v
  | Econst n -> string_of_Z n
  | Eunop (op0, e0) ->
    append (string_of_eunop op0) (append (' '::[]) (string_of_eexp' e0))
  | Ebinop (op0, e1, e2) ->
    append (string_of_eexp' e1)
      (append (' '::[])
        (append (string_of_ebinop op0)
          (append (' '::[]) (string_of_eexp' e2))))
  | Epow (e0, n) ->
    append (string_of_eexp' e0)
      (append (' '::('^'::(' '::[]))) (string_of_N n))
  and string_of_eexp' = function
  | Evar v -> string_of_var v
  | Econst n -> string_of_Z n
  | Eunop (op0, e0) ->
    append ('('::[])
      (append (string_of_eunop op0)
        (append (' '::[]) (append (string_of_eexp0 e0) (')'::[]))))
  | Ebinop (op0, e1, e2) ->
    append ('('::[])
      (append (string_of_eexp0 e1)
        (append (' '::[])
          (append (string_of_ebinop op0)
            (append (' '::[]) (append (string_of_eexp0 e2) (')'::[]))))))
  | Epow (e0, n) ->
    append ('('::[])
      (append (string_of_eexp0 e0)
        (append (' '::('^'::(' '::[]))) (append (string_of_N n) (')'::[]))))
  in string_of_eexp0

(** val string_of_eexps :
    Equality.coq_type -> (Equality.sort -> char list) -> char list -> eexp
    list -> char list **)

let rec string_of_eexps var string_of_var glue = function
| [] -> []
| hd :: tl ->
  append (string_of_eexp var string_of_var hd)
    (append glue (string_of_eexps var string_of_var glue tl))

(** val string_of_ebexp :
    Equality.coq_type -> (Equality.sort -> char list) -> ebexp -> char list **)

let rec string_of_ebexp var string_of_var = function
| Etrue -> 't'::('r'::('u'::('e'::[])))
| Eeq (e1, e2) ->
  append (string_of_eexp var string_of_var e1)
    (append (' '::('='::(' '::[]))) (string_of_eexp var string_of_var e2))
| Eeqmod (e1, e2, ms) ->
  append (string_of_eexp var string_of_var e1)
    (append (' '::('='::(' '::[])))
      (append (string_of_eexp var string_of_var e2)
        (append ('('::('m'::('o'::('d'::(' '::('['::[]))))))
          (append (string_of_eexps var string_of_var (','::(' '::[])) ms)
            (']'::(')'::[]))))))
| Eand (e1, e2) ->
  append (string_of_ebexp var string_of_var e1)
    (append (' '::('/'::('\\'::(' '::[]))))
      (string_of_ebexp var string_of_var e2))

(** val string_of_rexp :
    Equality.coq_type -> (Equality.sort -> char list) -> rexp -> char list **)

let string_of_rexp _ string_of_var =
  let rec string_of_rexp0 = function
  | Rvar v -> string_of_var v
  | Rconst (w, bs) -> append (to_hex bs) (append ('@'::[]) (string_of_nat w))
  | Runop (_, op0, e0) ->
    append (string_of_runop op0) (append (' '::[]) (string_of_rexp' e0))
  | Rbinop (_, op0, e1, e2) ->
    append (string_of_rexp' e1)
      (append (' '::[])
        (append (string_of_rbinop op0)
          (append (' '::[]) (string_of_rexp' e2))))
  | Ruext (_, e0, i) ->
    append ('u'::('e'::('x'::('t'::(' '::[])))))
      (append (string_of_rexp' e0) (append (' '::[]) (string_of_nat i)))
  | Rsext (_, e0, i) ->
    append ('s'::('e'::('x'::('t'::(' '::[])))))
      (append (string_of_rexp' e0) (append (' '::[]) (string_of_nat i)))
  and string_of_rexp' = function
  | Rvar v -> string_of_var v
  | Rconst (_, bs) -> to_hex bs
  | Runop (_, op0, e0) ->
    append ('('::[])
      (append (string_of_runop op0)
        (append (' '::[]) (append (string_of_rexp0 e0) (')'::[]))))
  | Rbinop (_, op0, e1, e2) ->
    append ('('::[])
      (append (string_of_rexp0 e1)
        (append (' '::[])
          (append (string_of_rbinop op0)
            (append (' '::[]) (append (string_of_rexp' e2) (')'::[]))))))
  | Ruext (_, e0, i) ->
    append ('('::('u'::('e'::('x'::('t'::(' '::[]))))))
      (append (string_of_rexp0 e0)
        (append (' '::[]) (append (string_of_nat i) (')'::[]))))
  | Rsext (_, e0, i) ->
    append ('('::('s'::('e'::('x'::('t'::(' '::[]))))))
      (append (string_of_rexp0 e0)
        (append (' '::[]) (append (string_of_nat i) (')'::[]))))
  in string_of_rexp0

(** val is_rbexp_or : Equality.coq_type -> rbexp -> bool **)

let is_rbexp_or _ = function
| Ror (_, _) -> true
| _ -> false

(** val string_of_rbexp :
    Equality.coq_type -> (Equality.sort -> char list) -> rbexp -> char list **)

let rec string_of_rbexp var string_of_var = function
| Rtrue -> 't'::('r'::('u'::('e'::[])))
| Req (_, e1, e2) ->
  append (string_of_rexp var string_of_var e1)
    (append (' '::('='::(' '::[]))) (string_of_rexp var string_of_var e2))
| Rcmp (_, op0, e1, e2) ->
  append (string_of_rexp var string_of_var e1)
    (append (' '::[])
      (append (string_of_rcmpop op0)
        (append (' '::[]) (string_of_rexp var string_of_var e2))))
| Rneg e0 -> append ('~'::(' '::[])) (string_of_rbexp var string_of_var e0)
| Rand (e1, e2) ->
  append
    (if is_rbexp_or var e1
     then append ('('::[])
            (append (string_of_rbexp var string_of_var e1) (')'::[]))
     else string_of_rbexp var string_of_var e1)
    (append (' '::('/'::('\\'::(' '::[]))))
      (if is_rbexp_or var e2
       then append ('('::[])
              (append (string_of_rbexp var string_of_var e2) (')'::[]))
       else string_of_rbexp var string_of_var e2))
| Ror (e1, e2) ->
  append (string_of_rbexp var string_of_var e1)
    (append (' '::('\\'::('/'::(' '::[]))))
      (string_of_rbexp var string_of_var e2))

(** val string_of_typ : typ -> char list **)

let string_of_typ = function
| Tuint n -> append ('u'::('i'::('n'::('t'::[])))) (string_of_nat n)
| Tsint n -> append ('s'::('i'::('n'::('t'::[])))) (string_of_nat n)
