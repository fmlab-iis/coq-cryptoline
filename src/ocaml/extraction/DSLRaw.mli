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

val eunop_eqn : eunop -> eunop -> bool

val eunop_eqP : eunop -> eunop -> reflect

val eunop_eqMixin : eunop Equality.mixin_of

val eunop_eqType : Equality.coq_type

val ebinop_eqn : ebinop -> ebinop -> bool

val ebinop_eqP : ebinop -> ebinop -> reflect

val ebinop_eqMixin : ebinop Equality.mixin_of

val ebinop_eqType : Equality.coq_type

val runop_eqn : runop -> runop -> bool

val runop_eqP : runop -> runop -> reflect

val runop_eqMixin : runop Equality.mixin_of

val runop_eqType : Equality.coq_type

val rbinop_eqn : rbinop -> rbinop -> bool

val rbinop_eqP : rbinop -> rbinop -> reflect

val rbinop_eqMixin : rbinop Equality.mixin_of

val rbinop_eqType : Equality.coq_type

val rcmpop_eqn : rcmpop -> rcmpop -> bool

val rcmpop_eqP : rcmpop -> rcmpop -> reflect

val rcmpop_eqMixin : rcmpop Equality.mixin_of

val rcmpop_eqType : Equality.coq_type

val string_of_eunop : eunop -> char list

val string_of_ebinop : ebinop -> char list

val string_of_runop : runop -> char list

val string_of_rbinop : rbinop -> char list

val string_of_rcmpop : rcmpop -> char list

type eexp =
| Evar of Equality.sort
| Econst of coq_Z
| Eunop of eunop * eexp
| Ebinop of ebinop * eexp * eexp
| Epow of eexp * coq_N

val econst : Equality.coq_type -> coq_Z -> eexp

val eadd : Equality.coq_type -> eexp -> eexp -> eexp

val emul : Equality.coq_type -> eexp -> eexp -> eexp

val eadds : Equality.coq_type -> eexp list -> eexp

val emuls : Equality.coq_type -> eexp list -> eexp

val z2expn : coq_Z -> coq_Z

val e2expn : Equality.coq_type -> coq_Z -> eexp

val emul2p : Equality.coq_type -> eexp -> coq_Z -> eexp

val eexp_eqn : Equality.coq_type -> eexp -> eexp -> bool

val eexp_eqP : Equality.coq_type -> eexp -> eexp -> reflect

val eexp_eqMixin : Equality.coq_type -> eexp Equality.mixin_of

val eexp_eqType : Equality.coq_type -> Equality.coq_type

val limbsi : Equality.coq_type -> int -> coq_Z -> eexp list -> eexp

type rexp =
| Rvar of Equality.sort
| Rconst of int * bits
| Runop of int * runop * rexp
| Rbinop of int * rbinop * rexp * rexp
| Ruext of int * rexp * int
| Rsext of int * rexp * int

val rbits : Equality.coq_type -> bool list -> rexp

val radd : Equality.coq_type -> int -> rexp -> rexp -> rexp

val rmul : Equality.coq_type -> int -> rexp -> rexp -> rexp

val radds : Equality.coq_type -> int -> rexp list -> rexp

val rmuls : Equality.coq_type -> int -> rexp list -> rexp

val rexp_eqn : Equality.coq_type -> rexp -> rexp -> bool

val rexp_eqP : Equality.coq_type -> rexp -> rexp -> reflect

val rexp_eqMixin : Equality.coq_type -> rexp Equality.mixin_of

val rexp_eqType : Equality.coq_type -> Equality.coq_type

type ebexp =
| Etrue
| Eeq of eexp * eexp
| Eeqmod of eexp * eexp * eexp list
| Eand of ebexp * ebexp

val eand : Equality.coq_type -> ebexp -> ebexp -> ebexp

val eands : Equality.coq_type -> ebexp list -> ebexp

val split_eand : Equality.coq_type -> ebexp -> ebexp list

val ebexp_eqn : Equality.coq_type -> ebexp -> ebexp -> bool

val ebexp_eqP : Equality.coq_type -> ebexp -> ebexp -> reflect

val ebexp_eqMixin : Equality.coq_type -> ebexp Equality.mixin_of

val ebexp_eqType : Equality.coq_type -> Equality.coq_type

type rbexp =
| Rtrue
| Req of int * rexp * rexp
| Rcmp of int * rcmpop * rexp * rexp
| Rneg of rbexp
| Rand of rbexp * rbexp
| Ror of rbexp * rbexp

val rand : Equality.coq_type -> rbexp -> rbexp -> rbexp

val ror : Equality.coq_type -> rbexp -> rbexp -> rbexp

val rands : Equality.coq_type -> rbexp list -> rbexp

val rors : Equality.coq_type -> rbexp list -> rbexp

val split_rand : Equality.coq_type -> rbexp -> rbexp list

val rbexp_eqn : Equality.coq_type -> rbexp -> rbexp -> bool

val rbexp_eqP : Equality.coq_type -> rbexp -> rbexp -> reflect

type atom =
| Avar of Equality.sort
| Aconst of typ * bits

val atom_eqn : Equality.coq_type -> atom -> atom -> bool

val atom_eqP : Equality.coq_type -> atom -> atom -> reflect

val atom_eqMixin : Equality.coq_type -> atom Equality.mixin_of

val atom_eqType : Equality.coq_type -> Equality.coq_type

val string_of_eexp :
  Equality.coq_type -> (Equality.sort -> char list) -> eexp -> char list

val string_of_eexps :
  Equality.coq_type -> (Equality.sort -> char list) -> char list -> eexp list
  -> char list

val string_of_ebexp :
  Equality.coq_type -> (Equality.sort -> char list) -> ebexp -> char list

val string_of_rexp :
  Equality.coq_type -> (Equality.sort -> char list) -> rexp -> char list

val is_rbexp_or : Equality.coq_type -> rbexp -> bool

val string_of_rbexp :
  Equality.coq_type -> (Equality.sort -> char list) -> rbexp -> char list

val string_of_typ : typ -> char list
