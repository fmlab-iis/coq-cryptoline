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

module Coq__1 : sig
 type eexp =
 | Evar of Equality.sort
 | Econst of coq_Z
 | Eunop of eunop * eexp
 | Ebinop of ebinop * eexp * eexp
end
include module type of struct include Coq__1 end

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

module Coq__2 : sig
 type rexp =
 | Rvar of Equality.sort
 | Rconst of int * bits
 | Runop of int * runop * rexp
 | Rbinop of int * rbinop * rexp * rexp
 | Ruext of int * rexp * int
 | Rsext of int * rexp * int
end
include module type of struct include Coq__2 end

val rbits : Equality.coq_type -> bool list -> rexp

val radd : Equality.coq_type -> int -> rexp -> rexp -> rexp

val rmul : Equality.coq_type -> int -> rexp -> rexp -> rexp

val radds : Equality.coq_type -> int -> rexp list -> rexp

val rmuls : Equality.coq_type -> int -> rexp list -> rexp

val rexp_eqn : Equality.coq_type -> rexp -> rexp -> bool

val rexp_eqP : Equality.coq_type -> rexp -> rexp -> reflect

val rexp_eqMixin : Equality.coq_type -> rexp Equality.mixin_of

val rexp_eqType : Equality.coq_type -> Equality.coq_type

module Coq__3 : sig
 type ebexp =
 | Etrue
 | Eeq of eexp * eexp
 | Eeqmod of eexp * eexp * eexp
 | Eand of ebexp * ebexp
end
include module type of struct include Coq__3 end

val eand : Equality.coq_type -> ebexp -> ebexp -> ebexp

val eands : Equality.coq_type -> ebexp list -> ebexp

val split_eand : Equality.coq_type -> ebexp -> ebexp list

val ebexp_eqn : Equality.coq_type -> ebexp -> ebexp -> bool

val ebexp_eqP : Equality.coq_type -> ebexp -> ebexp -> reflect

module Coq__4 : sig
 type rbexp =
 | Rtrue
 | Req of int * rexp * rexp
 | Rcmp of int * rcmpop * rexp * rexp
 | Rneg of rbexp
 | Rand of rbexp * rbexp
 | Ror of rbexp * rbexp
end
include module type of struct include Coq__4 end

val rand : Equality.coq_type -> rbexp -> rbexp -> rbexp

val ror : Equality.coq_type -> rbexp -> rbexp -> rbexp

val rands : Equality.coq_type -> rbexp list -> rbexp

val rors : Equality.coq_type -> rbexp list -> rbexp

val rbexp_eqn : Equality.coq_type -> rbexp -> rbexp -> bool

val rbexp_eqP : Equality.coq_type -> rbexp -> rbexp -> reflect

module MakeDSL :
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
 sig
  module VSLemmas :
   sig
    module F :
     sig
      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = VS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VS.SE.t -> VS.SE.t -> bool

        val lt_dec : VS.SE.t -> VS.SE.t -> bool

        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        val coq_In_dec : VS.elt -> VS.t -> bool

        val of_list : VS.elt list -> VS.t

        val to_list : VS.t -> VS.elt list

        val fold_rec :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
          (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) ->
          VS.t -> 'a2

        val fold_rel :
          (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_bis :
          (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __
          -> 'a1 -> 'a1) -> VS.t -> 'a1

        val cardinal_inv_2 : VS.t -> int -> VS.elt

        val cardinal_inv_2b : VS.t -> VS.elt
       end

      val gtb : VS.SE.t -> VS.SE.t -> bool

      val leb : VS.SE.t -> VS.SE.t -> bool

      val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

      val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1
     end

    val eqb : VS.SE.t -> VS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = VS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VS.SE.t -> VS.SE.t -> bool

      val lt_dec : VS.SE.t -> VS.SE.t -> bool

      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        module FSetLogicalFacts :
         sig
         end

        module FSetDecideAuxiliary :
         sig
         end

        module FSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      val coq_In_dec : VS.elt -> VS.t -> bool

      val of_list : VS.elt list -> VS.t

      val to_list : VS.t -> VS.elt list

      val fold_rec :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
        (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) -> VS.t ->
        'a2

      val fold_rel :
        (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_bis :
        (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __ ->
        'a1 -> 'a1) -> VS.t -> 'a1

      val cardinal_inv_2 : VS.t -> int -> VS.elt

      val cardinal_inv_2b : VS.t -> VS.elt
     end

    val gtb : VS.SE.t -> VS.SE.t -> bool

    val leb : VS.SE.t -> VS.SE.t -> bool

    val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

    val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

    val set_induction_max :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val set_induction_min :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val memP : VS.elt -> VS.t -> reflect

    val disjoint : VS.t -> VS.t -> bool
   end

  module TELemmas :
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

  type eexp = Coq__1.eexp

  val evar : V.t -> eexp

  val econst : coq_Z -> eexp

  val eunary : eunop -> eexp -> eexp

  val ebinary : ebinop -> eexp -> eexp -> eexp

  val eneg : eexp -> eexp

  val eadd : eexp -> eexp -> eexp

  val esub : eexp -> eexp -> eexp

  val emul : eexp -> eexp -> eexp

  val esq : eexp -> eexp

  val eadds : eexp list -> eexp

  val emuls : eexp list -> eexp

  val z2expn : coq_Z -> coq_Z

  val e2expn : coq_Z -> Coq__1.eexp

  val emul2p : Coq__1.eexp -> coq_Z -> Coq__1.eexp

  val vars_eexp : eexp -> VS.t

  val eexp_eqP : eexp -> eexp -> reflect

  val eexp_eqMixin : eexp Equality.mixin_of

  val eexp_eqType : Equality.coq_type

  val limbsi : int -> coq_Z -> eexp list -> eexp

  val limbs : coq_Z -> eexp list -> eexp

  type rexp = Coq__2.rexp

  val size_of_rexp : rexp -> TE.env -> int

  val rvar : Equality.sort -> rexp

  val rconst : int -> bits -> rexp

  val rbits : bits -> rexp

  val runary : int -> runop -> rexp -> rexp

  val rbinary : int -> rbinop -> rexp -> rexp -> rexp

  val rnegb : int -> rexp -> rexp

  val rnotb : int -> rexp -> rexp

  val radd : int -> rexp -> rexp -> rexp

  val rsub : int -> rexp -> rexp -> rexp

  val rmul : int -> rexp -> rexp -> rexp

  val rumod : int -> rexp -> rexp -> rexp

  val rsrem : int -> rexp -> rexp -> rexp

  val rsmod : int -> rexp -> rexp -> rexp

  val randb : int -> rexp -> rexp -> rexp

  val rorb : int -> rexp -> rexp -> rexp

  val rxorb : int -> rexp -> rexp -> rexp

  val rsq : int -> rexp -> rexp

  val ruext : int -> rexp -> int -> rexp

  val rsext : int -> rexp -> int -> rexp

  val radds : int -> rexp list -> rexp

  val rmuls : int -> rexp list -> rexp

  val vars_rexp : rexp -> VS.t

  val rexp_eqP : rexp -> rexp -> reflect

  val rexp_eqMixin : rexp Equality.mixin_of

  val rexp_eqType : Equality.coq_type

  type ebexp = Coq__3.ebexp

  val etrue : ebexp

  val eeq : eexp -> eexp -> ebexp

  val eeqmod : eexp -> eexp -> eexp -> ebexp

  val eand : ebexp -> ebexp -> ebexp

  val eands : ebexp list -> ebexp

  val split_eand : ebexp -> ebexp list

  val vars_ebexp : ebexp -> VS.t

  val ebexp_eqP : ebexp -> ebexp -> reflect

  val ebexp_eqMixin : ebexp Equality.mixin_of

  val ebexp_eqType : Equality.coq_type

  type rbexp = Coq__4.rbexp

  val rtrue : rbexp

  val rfalse : rbexp

  val req : int -> rexp -> rexp -> rbexp

  val rcmp : int -> rcmpop -> rexp -> rexp -> rbexp

  val rult : int -> rexp -> rexp -> rbexp

  val rule : int -> rexp -> rexp -> rbexp

  val rugt : int -> rexp -> rexp -> rbexp

  val ruge : int -> rexp -> rexp -> rbexp

  val rslt : int -> rexp -> rexp -> rbexp

  val rsle : int -> rexp -> rexp -> rbexp

  val rsgt : int -> rexp -> rexp -> rbexp

  val rsge : int -> rexp -> rexp -> rbexp

  val reqmod : int -> rexp -> rexp -> rexp -> rbexp

  val rneg : rbexp -> rbexp

  val rand : rbexp -> rbexp -> rbexp

  val ror : rbexp -> rbexp -> rbexp

  val rands : rbexp list -> rbexp

  val rors : rbexp list -> rbexp

  val vars_rbexp : rbexp -> VS.t

  val rbexp_eqP : rbexp -> rbexp -> reflect

  val rbexp_eqMixin : rbexp Equality.mixin_of

  val rbexp_eqType : Equality.coq_type

  type bexp = ebexp * rbexp

  val btrue : bexp

  val eqn_bexp : bexp -> ebexp

  val rng_bexp : bexp -> rbexp

  val band : bexp -> bexp -> bexp

  val bands : bexp list -> bexp

  val bands2 : ebexp list -> rbexp list -> ebexp * rbexp

  val vars_bexp : bexp -> VS.t

  type atomic =
  | Avar of V.t
  | Aconst of typ * bits

  val atomic_rect : (V.t -> 'a1) -> (typ -> bits -> 'a1) -> atomic -> 'a1

  val atomic_rec : (V.t -> 'a1) -> (typ -> bits -> 'a1) -> atomic -> 'a1

  val atyp : atomic -> TE.env -> typ

  val asize : atomic -> TE.env -> int

  type instr =
  | Imov of V.t * atomic
  | Ishl of V.t * atomic * int
  | Icshl of V.t * V.t * atomic * atomic * int
  | Inondet of V.t * typ
  | Icmov of V.t * atomic * atomic * atomic
  | Inop
  | Inot of V.t * typ * atomic
  | Iadd of V.t * atomic * atomic
  | Iadds of V.t * V.t * atomic * atomic
  | Iadc of V.t * atomic * atomic * atomic
  | Iadcs of V.t * V.t * atomic * atomic * atomic
  | Isub of V.t * atomic * atomic
  | Isubc of V.t * V.t * atomic * atomic
  | Isubb of V.t * V.t * atomic * atomic
  | Isbc of V.t * atomic * atomic * atomic
  | Isbcs of V.t * V.t * atomic * atomic * atomic
  | Isbb of V.t * atomic * atomic * atomic
  | Isbbs of V.t * V.t * atomic * atomic * atomic
  | Imul of V.t * atomic * atomic
  | Imull of V.t * V.t * atomic * atomic
  | Imulj of V.t * atomic * atomic
  | Isplit of V.t * V.t * atomic * int
  | Iand of V.t * typ * atomic * atomic
  | Ior of V.t * typ * atomic * atomic
  | Ixor of V.t * typ * atomic * atomic
  | Icast of V.t * typ * atomic
  | Ivpc of V.t * typ * atomic
  | Ijoin of V.t * atomic * atomic
  | Iassume of bexp

  val instr_rect :
    (V.t -> atomic -> 'a1) -> (V.t -> atomic -> int -> 'a1) -> (V.t -> V.t ->
    atomic -> atomic -> int -> 'a1) -> (V.t -> typ -> 'a1) -> (V.t -> atomic
    -> atomic -> atomic -> 'a1) -> 'a1 -> (V.t -> typ -> atomic -> 'a1) ->
    (V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic -> atomic ->
    'a1) -> (V.t -> atomic -> atomic -> atomic -> 'a1) -> (V.t -> V.t ->
    atomic -> atomic -> atomic -> 'a1) -> (V.t -> atomic -> atomic -> 'a1) ->
    (V.t -> V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic ->
    atomic -> 'a1) -> (V.t -> atomic -> atomic -> atomic -> 'a1) -> (V.t ->
    V.t -> atomic -> atomic -> atomic -> 'a1) -> (V.t -> atomic -> atomic ->
    atomic -> 'a1) -> (V.t -> V.t -> atomic -> atomic -> atomic -> 'a1) ->
    (V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic -> atomic ->
    'a1) -> (V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic -> int
    -> 'a1) -> (V.t -> typ -> atomic -> atomic -> 'a1) -> (V.t -> typ ->
    atomic -> atomic -> 'a1) -> (V.t -> typ -> atomic -> atomic -> 'a1) ->
    (V.t -> typ -> atomic -> 'a1) -> (V.t -> typ -> atomic -> 'a1) -> (V.t ->
    atomic -> atomic -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  val instr_rec :
    (V.t -> atomic -> 'a1) -> (V.t -> atomic -> int -> 'a1) -> (V.t -> V.t ->
    atomic -> atomic -> int -> 'a1) -> (V.t -> typ -> 'a1) -> (V.t -> atomic
    -> atomic -> atomic -> 'a1) -> 'a1 -> (V.t -> typ -> atomic -> 'a1) ->
    (V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic -> atomic ->
    'a1) -> (V.t -> atomic -> atomic -> atomic -> 'a1) -> (V.t -> V.t ->
    atomic -> atomic -> atomic -> 'a1) -> (V.t -> atomic -> atomic -> 'a1) ->
    (V.t -> V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic ->
    atomic -> 'a1) -> (V.t -> atomic -> atomic -> atomic -> 'a1) -> (V.t ->
    V.t -> atomic -> atomic -> atomic -> 'a1) -> (V.t -> atomic -> atomic ->
    atomic -> 'a1) -> (V.t -> V.t -> atomic -> atomic -> atomic -> 'a1) ->
    (V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic -> atomic ->
    'a1) -> (V.t -> atomic -> atomic -> 'a1) -> (V.t -> V.t -> atomic -> int
    -> 'a1) -> (V.t -> typ -> atomic -> atomic -> 'a1) -> (V.t -> typ ->
    atomic -> atomic -> 'a1) -> (V.t -> typ -> atomic -> atomic -> 'a1) ->
    (V.t -> typ -> atomic -> 'a1) -> (V.t -> typ -> atomic -> 'a1) -> (V.t ->
    atomic -> atomic -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  type program = instr list

  val vars_atomic : atomic -> VS.t

  val vars_instr : instr -> VS.t

  val lvs_instr : instr -> VS.t

  val rvs_instr : instr -> VS.t

  val vars_program : program -> VS.t

  val lvs_program : program -> VS.t

  val rvs_program : program -> VS.t

  val eqn_instr : instr -> instr

  val rng_instr : instr -> instr

  val eqn_program : program -> program

  val rng_program : program -> program

  type spec = { sinputs : TE.env; spre : bexp; sprog : program; spost : bexp }

  val sinputs : spec -> TE.env

  val spre : spec -> bexp

  val sprog : spec -> program

  val spost : spec -> bexp

  type espec = { esinputs : TE.env; espre : bexp; esprog : program;
                 espost : ebexp }

  val esinputs : espec -> TE.env

  val espre : espec -> bexp

  val esprog : espec -> program

  val espost : espec -> ebexp

  type rspec = { rsinputs : TE.env; rspre : rbexp; rsprog : program;
                 rspost : rbexp }

  val rsinputs : rspec -> TE.env

  val rspre : rspec -> rbexp

  val rsprog : rspec -> program

  val rspost : rspec -> rbexp

  val espec_of_spec : spec -> espec

  val rspec_of_spec : spec -> rspec

  val bv2z : typ -> bits -> coq_Z

  val acc2z : TE.env -> V.t -> S.t -> coq_Z

  val eval_eunop : eunop -> coq_Z -> coq_Z

  val eval_ebinop : ebinop -> coq_Z -> coq_Z -> coq_Z

  val eval_runop : runop -> bits -> bits

  val eval_rbinop : rbinop -> bits -> bits -> bits

  val eval_rcmpop : rcmpop -> bits -> bits -> bool

  val eval_eexp : eexp -> TE.env -> S.t -> coq_Z

  val eval_rexp : rexp -> S.t -> bits

  val eval_atomic : atomic -> S.t -> bits

  val instr_succ_typenv : instr -> TE.env -> TE.env

  val program_succ_typenv : program -> TE.env -> TE.env

  val well_typed_eexp : TE.env -> eexp -> bool

  val well_typed_rexp : TE.env -> rexp -> bool

  val well_typed_ebexp : TE.env -> ebexp -> bool

  val well_typed_rbexp : TE.env -> rbexp -> bool

  val well_typed_bexp : TE.env -> bexp -> bool

  val well_sized_atomic : TE.env -> atomic -> bool

  val size_matched_atomic : atomic -> bool

  val well_typed_atomic : TE.env -> atomic -> bool

  val well_typed_instr : TE.env -> instr -> bool

  module TEKS :
   sig
    module MLemmas :
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
            (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t ->
            __ -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __
            -> __ -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_bis :
            (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t ->
            'a1 TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 ->
            'a2 -> 'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_nodep :
            (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 ->
            (TE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_weak :
            (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t ->
            'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1
            TE.t -> __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

          val fold_rel :
            (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) ->
            'a2 -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 ->
            __ -> 'a4 -> 'a4) -> 'a4

          val map_induction :
            ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key
            -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

          val map_induction_bis :
            ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key ->
            'a1 -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

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

          val partition_range :
            ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
         end

        val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

        val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

        val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

        val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

        val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

        val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

        val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

        val map_induction_max :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val map_induction_min :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2
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

    module SLemmas :
     sig
      module F :
       sig
        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = VS.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : VS.SE.t -> VS.SE.t -> bool

          val lt_dec : VS.SE.t -> VS.SE.t -> bool

          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        module P :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : VS.SE.t -> VS.SE.t -> bool
             end

            module FSetLogicalFacts :
             sig
             end

            module FSetDecideAuxiliary :
             sig
             end

            module FSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          val coq_In_dec : VS.elt -> VS.t -> bool

          val of_list : VS.elt list -> VS.t

          val to_list : VS.t -> VS.elt list

          val fold_rec :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
            (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a2

          val fold_rec_bis :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 ->
            __ -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ ->
            'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ ->
            'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2)
            -> VS.t -> 'a2

          val fold_rel :
            (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
            VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val set_induction :
            (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
            -> 'a1) -> VS.t -> 'a1

          val set_induction_bis :
            (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t ->
            __ -> 'a1 -> 'a1) -> VS.t -> 'a1

          val cardinal_inv_2 : VS.t -> int -> VS.elt

          val cardinal_inv_2b : VS.t -> VS.elt
         end

        val gtb : VS.SE.t -> VS.SE.t -> bool

        val leb : VS.SE.t -> VS.SE.t -> bool

        val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

        val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

        val set_induction_max :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_min :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __
          -> 'a1) -> VS.t -> 'a1
       end

      val eqb : VS.SE.t -> VS.SE.t -> bool

      module ME :
       sig
        module TO :
         sig
          type t = VS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VS.SE.t -> VS.SE.t -> bool

        val lt_dec : VS.SE.t -> VS.SE.t -> bool

        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        val coq_In_dec : VS.elt -> VS.t -> bool

        val of_list : VS.elt list -> VS.t

        val to_list : VS.t -> VS.elt list

        val fold_rec :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
          (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) ->
          VS.t -> 'a2

        val fold_rel :
          (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_bis :
          (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __
          -> 'a1 -> 'a1) -> VS.t -> 'a1

        val cardinal_inv_2 : VS.t -> int -> VS.elt

        val cardinal_inv_2b : VS.t -> VS.elt
       end

      val gtb : VS.SE.t -> VS.SE.t -> bool

      val leb : VS.SE.t -> VS.SE.t -> bool

      val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

      val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val memP : VS.elt -> VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool
     end

    val add_to_set : VS.elt -> 'a1 -> VS.t -> VS.t

    val key_set : 'a1 TE.t -> VS.t
   end

  val vars_env : TE.env -> VS.t

  val is_defined : V.t -> TE.env -> bool

  val are_defined : VS.t -> TE.env -> bool

  val memenvP : TE.key -> typ TE.t -> reflect

  val well_defined_instr : TE.env -> instr -> bool

  val well_formed_instr : TE.env -> instr -> bool

  val well_formed_program : TE.env -> program -> bool

  val find_non_well_formed_instr : TE.env -> program -> instr option

  val well_formed_eexp : TE.env -> eexp -> bool

  val well_formed_rexp : TE.env -> rexp -> bool

  val well_formed_ebexp : TE.env -> ebexp -> bool

  val well_formed_rbexp : TE.env -> rbexp -> bool

  val well_formed_bexp : TE.env -> bexp -> bool

  val well_formed_spec : spec -> bool

  val defmemP : V.t -> TE.env -> reflect

  val memdefP : TE.key -> typ TE.t -> reflect

  val defsubP : VS.t -> TE.env -> reflect

  val is_assume : instr -> bool

  val force_conform_vars : TE.env -> V.t list -> S.t -> S.t

  val force_conform : TE.env -> TE.env -> S.t -> S.t
 end

module DSL :
 sig
  module VSLemmas :
   sig
    module F :
     sig
      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = VS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VS.SE.t -> VS.SE.t -> bool

        val lt_dec : VS.SE.t -> VS.SE.t -> bool

        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        val coq_In_dec : VS.elt -> VS.t -> bool

        val of_list : VS.elt list -> VS.t

        val to_list : VS.t -> VS.elt list

        val fold_rec :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
          (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) ->
          VS.t -> 'a2

        val fold_rel :
          (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_bis :
          (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __
          -> 'a1 -> 'a1) -> VS.t -> 'a1

        val cardinal_inv_2 : VS.t -> int -> VS.elt

        val cardinal_inv_2b : VS.t -> VS.elt
       end

      val gtb : VS.SE.t -> VS.SE.t -> bool

      val leb : VS.SE.t -> VS.SE.t -> bool

      val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

      val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1
     end

    val eqb : VS.SE.t -> VS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = VS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VS.SE.t -> VS.SE.t -> bool

      val lt_dec : VS.SE.t -> VS.SE.t -> bool

      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        module FSetLogicalFacts :
         sig
         end

        module FSetDecideAuxiliary :
         sig
         end

        module FSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      val coq_In_dec : VS.elt -> VS.t -> bool

      val of_list : VS.elt list -> VS.t

      val to_list : VS.t -> VS.elt list

      val fold_rec :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
        (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) -> VS.t ->
        'a2

      val fold_rel :
        (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_bis :
        (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __ ->
        'a1 -> 'a1) -> VS.t -> 'a1

      val cardinal_inv_2 : VS.t -> int -> VS.elt

      val cardinal_inv_2b : VS.t -> VS.elt
     end

    val gtb : VS.SE.t -> VS.SE.t -> bool

    val leb : VS.SE.t -> VS.SE.t -> bool

    val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

    val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

    val set_induction_max :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val set_induction_min :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val memP : VS.elt -> VS.t -> reflect

    val disjoint : VS.t -> VS.t -> bool
   end

  module TELemmas :
   sig
    module F :
     sig
      val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

      val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TypEnv.TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TypEnv.TE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TypEnv.TE.key * 'a1) list -> 'a1 TypEnv.TE.t

        val to_list : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

        val fold_rec :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
          ('a1 TypEnv.TE.t -> __ -> 'a3) -> (TypEnv.TE.key -> 'a1 -> 'a2 ->
          'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> __ -> __ -> 'a3 -> 'a3)
          -> 'a3

        val fold_rec_bis :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
          ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) ->
          'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> __
          -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
          'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TypEnv.TE.t ->
          'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> 'a3 ->
          'a3) -> 'a1 TypEnv.TE.t -> 'a3

        val fold_rel :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.TE.key -> 'a1 ->
          'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.TE.t -> 'a4 ->
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t -> 'a2 -> TypEnv.TE.key -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val map_induction_bis :
          ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (TypEnv.TE.key -> 'a1 -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val cardinal_inv_2 : 'a1 TypEnv.TE.t -> int -> (TypEnv.TE.key * 'a1)

        val cardinal_inv_2b : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1)

        val filter :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val for_all :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val exists_ :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val partition :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t * 'a1 TypEnv.TE.t

        val update : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val restrict : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val diff : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val coq_Partition_In :
          'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t ->
          TypEnv.TE.key -> bool

        val update_dec :
          'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> TypEnv.TE.key -> 'a1 -> bool

        val filter_dom :
          (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val filter_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val for_all_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val exists_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val partition_dom :
          (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a1
          TypEnv.TE.t

        val partition_range :
          ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a1
          TypEnv.TE.t
       end

      val gtb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

      val leb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

      val elements_lt :
        (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

      val elements_ge :
        (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

      val max_elt_aux :
        (TypEnv.TE.key * 'a1) list -> (TypEnv.TE.key * 'a1) option

      val max_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

      val min_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

      val map_induction_max :
        ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
        -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1
        TypEnv.TE.t -> 'a2

      val map_induction_min :
        ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
        -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1
        TypEnv.TE.t -> 'a2
     end

    val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

    val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TypEnv.TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

      val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

      val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = TypEnv.TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TypEnv.TE.key * 'a1) list -> 'a1 TypEnv.TE.t

      val to_list : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

      val fold_rec :
        (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
        ('a1 TypEnv.TE.t -> __ -> 'a3) -> (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1
        TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
        ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) ->
        'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> __ ->
        'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t -> 'a3
        -> (TypEnv.TE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TypEnv.TE.t ->
        'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TypEnv.TE.key
        -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> 'a3 -> 'a3) -> 'a1
        TypEnv.TE.t -> 'a3

      val fold_rel :
        (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.TE.key -> 'a1 -> 'a3
        -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.TE.t -> 'a4 -> (TypEnv.TE.key ->
        'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
        -> 'a2 -> TypEnv.TE.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TypEnv.TE.t
        -> 'a2

      val map_induction_bis :
        ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
        (TypEnv.TE.key -> 'a1 -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) -> 'a1
        TypEnv.TE.t -> 'a2

      val cardinal_inv_2 : 'a1 TypEnv.TE.t -> int -> (TypEnv.TE.key * 'a1)

      val cardinal_inv_2b : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1)

      val filter :
        (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

      val for_all : (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

      val exists_ : (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

      val partition :
        (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1
        TypEnv.TE.t * 'a1 TypEnv.TE.t

      val update : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

      val restrict : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

      val diff : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

      val coq_Partition_In :
        'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t ->
        TypEnv.TE.key -> bool

      val update_dec :
        'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> TypEnv.TE.key -> 'a1 -> bool

      val filter_dom :
        (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

      val filter_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

      val for_all_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

      val exists_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

      val partition_dom :
        (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a1
        TypEnv.TE.t

      val partition_range :
        ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a1 TypEnv.TE.t
     end

    val gtb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

    val leb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

    val elements_lt :
      (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

    val elements_ge :
      (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

    val max_elt_aux :
      (TypEnv.TE.key * 'a1) list -> (TypEnv.TE.key * 'a1) option

    val max_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

    val min_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

    val map_induction_max :
      ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
      -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TypEnv.TE.t
      -> 'a2

    val map_induction_min :
      ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
      -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TypEnv.TE.t
      -> 'a2

    val memP : TypEnv.TE.key -> 'a1 TypEnv.TE.t -> reflect

    val split : ('a1 * 'a2) TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a2 TypEnv.TE.t

    module EFacts :
     sig
      module TO :
       sig
        type t = TypEnv.TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

      val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

      val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
     end

    val max_opt : TypEnv.TE.key -> TypEnv.TE.key option -> TypEnv.TE.key

    val max_key_elements : (TypEnv.TE.key * 'a1) list -> TypEnv.TE.key option

    val max_key : 'a1 TypEnv.TE.t -> TypEnv.TE.key option

    val min_opt : TypEnv.TE.key -> TypEnv.TE.key option -> TypEnv.TE.key

    val min_key_elements : (TypEnv.TE.key * 'a1) list -> TypEnv.TE.key option

    val min_key : 'a1 TypEnv.TE.t -> TypEnv.TE.key option
   end

  type eexp = Coq__1.eexp

  val evar : VarOrder.t -> eexp

  val econst : coq_Z -> eexp

  val eunary : eunop -> eexp -> eexp

  val ebinary : ebinop -> eexp -> eexp -> eexp

  val eneg : eexp -> eexp

  val eadd : eexp -> eexp -> eexp

  val esub : eexp -> eexp -> eexp

  val emul : eexp -> eexp -> eexp

  val esq : eexp -> eexp

  val eadds : eexp list -> eexp

  val emuls : eexp list -> eexp

  val z2expn : coq_Z -> coq_Z

  val e2expn : coq_Z -> Coq__1.eexp

  val emul2p : Coq__1.eexp -> coq_Z -> Coq__1.eexp

  val vars_eexp : eexp -> VS.t

  val eexp_eqP : eexp -> eexp -> reflect

  val eexp_eqMixin : eexp Equality.mixin_of

  val eexp_eqType : Equality.coq_type

  val limbsi : int -> coq_Z -> eexp list -> eexp

  val limbs : coq_Z -> eexp list -> eexp

  type rexp = Coq__2.rexp

  val size_of_rexp : rexp -> TypEnv.TE.env -> int

  val rvar : Equality.sort -> rexp

  val rconst : int -> bits -> rexp

  val rbits : bits -> rexp

  val runary : int -> runop -> rexp -> rexp

  val rbinary : int -> rbinop -> rexp -> rexp -> rexp

  val rnegb : int -> rexp -> rexp

  val rnotb : int -> rexp -> rexp

  val radd : int -> rexp -> rexp -> rexp

  val rsub : int -> rexp -> rexp -> rexp

  val rmul : int -> rexp -> rexp -> rexp

  val rumod : int -> rexp -> rexp -> rexp

  val rsrem : int -> rexp -> rexp -> rexp

  val rsmod : int -> rexp -> rexp -> rexp

  val randb : int -> rexp -> rexp -> rexp

  val rorb : int -> rexp -> rexp -> rexp

  val rxorb : int -> rexp -> rexp -> rexp

  val rsq : int -> rexp -> rexp

  val ruext : int -> rexp -> int -> rexp

  val rsext : int -> rexp -> int -> rexp

  val radds : int -> rexp list -> rexp

  val rmuls : int -> rexp list -> rexp

  val vars_rexp : rexp -> VS.t

  val rexp_eqP : rexp -> rexp -> reflect

  val rexp_eqMixin : rexp Equality.mixin_of

  val rexp_eqType : Equality.coq_type

  type ebexp = Coq__3.ebexp

  val etrue : ebexp

  val eeq : eexp -> eexp -> ebexp

  val eeqmod : eexp -> eexp -> eexp -> ebexp

  val eand : ebexp -> ebexp -> ebexp

  val eands : ebexp list -> ebexp

  val split_eand : ebexp -> ebexp list

  val vars_ebexp : ebexp -> VS.t

  val ebexp_eqP : ebexp -> ebexp -> reflect

  val ebexp_eqMixin : ebexp Equality.mixin_of

  val ebexp_eqType : Equality.coq_type

  type rbexp = Coq__4.rbexp

  val rtrue : rbexp

  val rfalse : rbexp

  val req : int -> rexp -> rexp -> rbexp

  val rcmp : int -> rcmpop -> rexp -> rexp -> rbexp

  val rult : int -> rexp -> rexp -> rbexp

  val rule : int -> rexp -> rexp -> rbexp

  val rugt : int -> rexp -> rexp -> rbexp

  val ruge : int -> rexp -> rexp -> rbexp

  val rslt : int -> rexp -> rexp -> rbexp

  val rsle : int -> rexp -> rexp -> rbexp

  val rsgt : int -> rexp -> rexp -> rbexp

  val rsge : int -> rexp -> rexp -> rbexp

  val reqmod : int -> rexp -> rexp -> rexp -> rbexp

  val rneg : rbexp -> rbexp

  val rand : rbexp -> rbexp -> rbexp

  val ror : rbexp -> rbexp -> rbexp

  val rands : rbexp list -> rbexp

  val rors : rbexp list -> rbexp

  val vars_rbexp : rbexp -> VS.t

  val rbexp_eqP : rbexp -> rbexp -> reflect

  val rbexp_eqMixin : rbexp Equality.mixin_of

  val rbexp_eqType : Equality.coq_type

  type bexp = ebexp * rbexp

  val btrue : bexp

  val eqn_bexp : bexp -> ebexp

  val rng_bexp : bexp -> rbexp

  val band : bexp -> bexp -> bexp

  val bands : bexp list -> bexp

  val bands2 : ebexp list -> rbexp list -> ebexp * rbexp

  val vars_bexp : bexp -> VS.t

  type atomic =
  | Avar of VarOrder.t
  | Aconst of typ * bits

  val atomic_rect :
    (VarOrder.t -> 'a1) -> (typ -> bits -> 'a1) -> atomic -> 'a1

  val atomic_rec :
    (VarOrder.t -> 'a1) -> (typ -> bits -> 'a1) -> atomic -> 'a1

  val atyp : atomic -> TypEnv.TE.env -> typ

  val asize : atomic -> TypEnv.TE.env -> int

  type instr =
  | Imov of VarOrder.t * atomic
  | Ishl of VarOrder.t * atomic * int
  | Icshl of VarOrder.t * VarOrder.t * atomic * atomic * int
  | Inondet of VarOrder.t * typ
  | Icmov of VarOrder.t * atomic * atomic * atomic
  | Inop
  | Inot of VarOrder.t * typ * atomic
  | Iadd of VarOrder.t * atomic * atomic
  | Iadds of VarOrder.t * VarOrder.t * atomic * atomic
  | Iadc of VarOrder.t * atomic * atomic * atomic
  | Iadcs of VarOrder.t * VarOrder.t * atomic * atomic * atomic
  | Isub of VarOrder.t * atomic * atomic
  | Isubc of VarOrder.t * VarOrder.t * atomic * atomic
  | Isubb of VarOrder.t * VarOrder.t * atomic * atomic
  | Isbc of VarOrder.t * atomic * atomic * atomic
  | Isbcs of VarOrder.t * VarOrder.t * atomic * atomic * atomic
  | Isbb of VarOrder.t * atomic * atomic * atomic
  | Isbbs of VarOrder.t * VarOrder.t * atomic * atomic * atomic
  | Imul of VarOrder.t * atomic * atomic
  | Imull of VarOrder.t * VarOrder.t * atomic * atomic
  | Imulj of VarOrder.t * atomic * atomic
  | Isplit of VarOrder.t * VarOrder.t * atomic * int
  | Iand of VarOrder.t * typ * atomic * atomic
  | Ior of VarOrder.t * typ * atomic * atomic
  | Ixor of VarOrder.t * typ * atomic * atomic
  | Icast of VarOrder.t * typ * atomic
  | Ivpc of VarOrder.t * typ * atomic
  | Ijoin of VarOrder.t * atomic * atomic
  | Iassume of bexp

  val instr_rect :
    (VarOrder.t -> atomic -> 'a1) -> (VarOrder.t -> atomic -> int -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atomic -> atomic -> int -> 'a1) ->
    (VarOrder.t -> typ -> 'a1) -> (VarOrder.t -> atomic -> atomic -> atomic
    -> 'a1) -> 'a1 -> (VarOrder.t -> typ -> atomic -> 'a1) -> (VarOrder.t ->
    atomic -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t -> atomic -> atomic
    -> 'a1) -> (VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> atomic -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t ->
    atomic -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t -> atomic -> atomic
    -> 'a1) -> (VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> atomic -> atomic -> atomic -> 'a1) -> (VarOrder.t ->
    VarOrder.t -> atomic -> atomic -> atomic -> 'a1) -> (VarOrder.t -> atomic
    -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t -> atomic -> atomic ->
    'a1) -> (VarOrder.t -> atomic -> atomic -> 'a1) -> (VarOrder.t ->
    VarOrder.t -> atomic -> int -> 'a1) -> (VarOrder.t -> typ -> atomic ->
    atomic -> 'a1) -> (VarOrder.t -> typ -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> typ -> atomic -> atomic -> 'a1) -> (VarOrder.t -> typ ->
    atomic -> 'a1) -> (VarOrder.t -> typ -> atomic -> 'a1) -> (VarOrder.t ->
    atomic -> atomic -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  val instr_rec :
    (VarOrder.t -> atomic -> 'a1) -> (VarOrder.t -> atomic -> int -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atomic -> atomic -> int -> 'a1) ->
    (VarOrder.t -> typ -> 'a1) -> (VarOrder.t -> atomic -> atomic -> atomic
    -> 'a1) -> 'a1 -> (VarOrder.t -> typ -> atomic -> 'a1) -> (VarOrder.t ->
    atomic -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t -> atomic -> atomic
    -> 'a1) -> (VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> atomic -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t ->
    atomic -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t -> atomic -> atomic
    -> 'a1) -> (VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atomic -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> atomic -> atomic -> atomic -> 'a1) -> (VarOrder.t ->
    VarOrder.t -> atomic -> atomic -> atomic -> 'a1) -> (VarOrder.t -> atomic
    -> atomic -> 'a1) -> (VarOrder.t -> VarOrder.t -> atomic -> atomic ->
    'a1) -> (VarOrder.t -> atomic -> atomic -> 'a1) -> (VarOrder.t ->
    VarOrder.t -> atomic -> int -> 'a1) -> (VarOrder.t -> typ -> atomic ->
    atomic -> 'a1) -> (VarOrder.t -> typ -> atomic -> atomic -> 'a1) ->
    (VarOrder.t -> typ -> atomic -> atomic -> 'a1) -> (VarOrder.t -> typ ->
    atomic -> 'a1) -> (VarOrder.t -> typ -> atomic -> 'a1) -> (VarOrder.t ->
    atomic -> atomic -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  type program = instr list

  val vars_atomic : atomic -> VS.t

  val vars_instr : instr -> VS.t

  val lvs_instr : instr -> VS.t

  val rvs_instr : instr -> VS.t

  val vars_program : program -> VS.t

  val lvs_program : program -> VS.t

  val rvs_program : program -> VS.t

  val eqn_instr : instr -> instr

  val rng_instr : instr -> instr

  val eqn_program : program -> program

  val rng_program : program -> program

  type spec = { sinputs : TypEnv.TE.env; spre : bexp; sprog : program;
                spost : bexp }

  val sinputs : spec -> TypEnv.TE.env

  val spre : spec -> bexp

  val sprog : spec -> program

  val spost : spec -> bexp

  type espec = { esinputs : TypEnv.TE.env; espre : bexp; esprog : program;
                 espost : ebexp }

  val esinputs : espec -> TypEnv.TE.env

  val espre : espec -> bexp

  val esprog : espec -> program

  val espost : espec -> ebexp

  type rspec = { rsinputs : TypEnv.TE.env; rspre : rbexp; rsprog : program;
                 rspost : rbexp }

  val rsinputs : rspec -> TypEnv.TE.env

  val rspre : rspec -> rbexp

  val rsprog : rspec -> program

  val rspost : rspec -> rbexp

  val espec_of_spec : spec -> espec

  val rspec_of_spec : spec -> rspec

  val bv2z : typ -> bits -> coq_Z

  val acc2z : TypEnv.TE.env -> VarOrder.t -> Store.t -> coq_Z

  val eval_eunop : eunop -> coq_Z -> coq_Z

  val eval_ebinop : ebinop -> coq_Z -> coq_Z -> coq_Z

  val eval_runop : runop -> bits -> bits

  val eval_rbinop : rbinop -> bits -> bits -> bits

  val eval_rcmpop : rcmpop -> bits -> bits -> bool

  val eval_eexp : eexp -> TypEnv.TE.env -> Store.t -> coq_Z

  val eval_rexp : rexp -> Store.t -> bits

  val eval_atomic : atomic -> Store.t -> bits

  val instr_succ_typenv : instr -> TypEnv.TE.env -> TypEnv.TE.env

  val program_succ_typenv : program -> TypEnv.TE.env -> TypEnv.TE.env

  val well_typed_eexp : TypEnv.TE.env -> eexp -> bool

  val well_typed_rexp : TypEnv.TE.env -> rexp -> bool

  val well_typed_ebexp : TypEnv.TE.env -> ebexp -> bool

  val well_typed_rbexp : TypEnv.TE.env -> rbexp -> bool

  val well_typed_bexp : TypEnv.TE.env -> bexp -> bool

  val well_sized_atomic : TypEnv.TE.env -> atomic -> bool

  val size_matched_atomic : atomic -> bool

  val well_typed_atomic : TypEnv.TE.env -> atomic -> bool

  val well_typed_instr : TypEnv.TE.env -> instr -> bool

  module TEKS :
   sig
    module MLemmas :
     sig
      module F :
       sig
        val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = TypEnv.TE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
         end

        module O :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = TypEnv.TE.SE.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

            val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

            val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
           end
         end

        module P :
         sig
          module F :
           sig
            val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

            val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
           end

          val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

          val of_list : (TypEnv.TE.key * 'a1) list -> 'a1 TypEnv.TE.t

          val to_list : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

          val fold_rec :
            (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
            ('a1 TypEnv.TE.t -> __ -> 'a3) -> (TypEnv.TE.key -> 'a1 -> 'a2 ->
            'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> __ -> __ -> 'a3 ->
            'a3) -> 'a3

          val fold_rec_bis :
            (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
            ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3)
            -> 'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __
            -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_nodep :
            (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
            'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_weak :
            (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TypEnv.TE.t
            -> 'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
            (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> 'a3 ->
            'a3) -> 'a1 TypEnv.TE.t -> 'a3

          val fold_rel :
            (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.TE.key -> 'a1 ->
            'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.TE.t -> 'a4 ->
            (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

          val map_induction :
            ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
            TypEnv.TE.t -> 'a2 -> TypEnv.TE.key -> 'a1 -> __ -> __ -> 'a2) ->
            'a1 TypEnv.TE.t -> 'a2

          val map_induction_bis :
            ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) -> 'a2
            -> (TypEnv.TE.key -> 'a1 -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2)
            -> 'a1 TypEnv.TE.t -> 'a2

          val cardinal_inv_2 : 'a1 TypEnv.TE.t -> int -> (TypEnv.TE.key * 'a1)

          val cardinal_inv_2b : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1)

          val filter :
            (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1
            TypEnv.TE.t

          val for_all :
            (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

          val exists_ :
            (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

          val partition :
            (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1
            TypEnv.TE.t * 'a1 TypEnv.TE.t

          val update : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

          val restrict : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

          val diff : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

          val coq_Partition_In :
            'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t ->
            TypEnv.TE.key -> bool

          val update_dec :
            'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> TypEnv.TE.key -> 'a1 -> bool

          val filter_dom :
            (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

          val filter_range :
            ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

          val for_all_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

          val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

          val exists_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

          val exists_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

          val partition_dom :
            (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1
            TypEnv.TE.t * 'a1 TypEnv.TE.t

          val partition_range :
            ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a1
            TypEnv.TE.t
         end

        val gtb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

        val leb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

        val elements_lt :
          (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1)
          list

        val elements_ge :
          (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1)
          list

        val max_elt_aux :
          (TypEnv.TE.key * 'a1) list -> (TypEnv.TE.key * 'a1) option

        val max_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

        val min_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

        val map_induction_max :
          ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val map_induction_min :
          ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2
       end

      val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

      val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool

      module ME :
       sig
        module TO :
         sig
          type t = TypEnv.TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TypEnv.TE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

          val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TypEnv.TE.key * 'a1) list -> 'a1 TypEnv.TE.t

        val to_list : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

        val fold_rec :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
          ('a1 TypEnv.TE.t -> __ -> 'a3) -> (TypEnv.TE.key -> 'a1 -> 'a2 ->
          'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> __ -> __ -> 'a3 -> 'a3)
          -> 'a3

        val fold_rec_bis :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
          ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) ->
          'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> __
          -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t ->
          'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TypEnv.TE.t ->
          'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> 'a3 ->
          'a3) -> 'a1 TypEnv.TE.t -> 'a3

        val fold_rel :
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.TE.key -> 'a1 ->
          'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.TE.t -> 'a4 ->
          (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t -> 'a2 -> TypEnv.TE.key -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val map_induction_bis :
          ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (TypEnv.TE.key -> 'a1 -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val cardinal_inv_2 : 'a1 TypEnv.TE.t -> int -> (TypEnv.TE.key * 'a1)

        val cardinal_inv_2b : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1)

        val filter :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val for_all :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val exists_ :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val partition :
          (TypEnv.TE.key -> 'a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t * 'a1 TypEnv.TE.t

        val update : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val restrict : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val diff : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val coq_Partition_In :
          'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t ->
          TypEnv.TE.key -> bool

        val update_dec :
          'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> TypEnv.TE.key -> 'a1 -> bool

        val filter_dom :
          (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val filter_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

        val for_all_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val exists_dom : (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

        val partition_dom :
          (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a1
          TypEnv.TE.t

        val partition_range :
          ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a1
          TypEnv.TE.t
       end

      val gtb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

      val leb : (TypEnv.TE.key * 'a1) -> (TypEnv.TE.key * 'a1) -> bool

      val elements_lt :
        (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

      val elements_ge :
        (TypEnv.TE.key * 'a1) -> 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

      val max_elt_aux :
        (TypEnv.TE.key * 'a1) list -> (TypEnv.TE.key * 'a1) option

      val max_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

      val min_elt : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) option

      val map_induction_max :
        ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
        -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1
        TypEnv.TE.t -> 'a2

      val map_induction_min :
        ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
        -> 'a2 -> TypEnv.TE.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1
        TypEnv.TE.t -> 'a2

      val memP : TypEnv.TE.key -> 'a1 TypEnv.TE.t -> reflect

      val split : ('a1 * 'a2) TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a2 TypEnv.TE.t

      module EFacts :
       sig
        module TO :
         sig
          type t = TypEnv.TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val lt_dec : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool

        val eqb : TypEnv.TE.SE.t -> TypEnv.TE.SE.t -> bool
       end

      val max_opt : TypEnv.TE.key -> TypEnv.TE.key option -> TypEnv.TE.key

      val max_key_elements :
        (TypEnv.TE.key * 'a1) list -> TypEnv.TE.key option

      val max_key : 'a1 TypEnv.TE.t -> TypEnv.TE.key option

      val min_opt : TypEnv.TE.key -> TypEnv.TE.key option -> TypEnv.TE.key

      val min_key_elements :
        (TypEnv.TE.key * 'a1) list -> TypEnv.TE.key option

      val min_key : 'a1 TypEnv.TE.t -> TypEnv.TE.key option
     end

    module SLemmas :
     sig
      module F :
       sig
        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = VS.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : VS.SE.t -> VS.SE.t -> bool

          val lt_dec : VS.SE.t -> VS.SE.t -> bool

          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        module P :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : VS.SE.t -> VS.SE.t -> bool
             end

            module FSetLogicalFacts :
             sig
             end

            module FSetDecideAuxiliary :
             sig
             end

            module FSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          val coq_In_dec : VS.elt -> VS.t -> bool

          val of_list : VS.elt list -> VS.t

          val to_list : VS.t -> VS.elt list

          val fold_rec :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
            (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a2

          val fold_rec_bis :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 ->
            __ -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ ->
            'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ ->
            'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2)
            -> VS.t -> 'a2

          val fold_rel :
            (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
            VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val set_induction :
            (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
            -> 'a1) -> VS.t -> 'a1

          val set_induction_bis :
            (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t ->
            __ -> 'a1 -> 'a1) -> VS.t -> 'a1

          val cardinal_inv_2 : VS.t -> int -> VS.elt

          val cardinal_inv_2b : VS.t -> VS.elt
         end

        val gtb : VS.SE.t -> VS.SE.t -> bool

        val leb : VS.SE.t -> VS.SE.t -> bool

        val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

        val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

        val set_induction_max :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_min :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __
          -> 'a1) -> VS.t -> 'a1
       end

      val eqb : VS.SE.t -> VS.SE.t -> bool

      module ME :
       sig
        module TO :
         sig
          type t = VS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VS.SE.t -> VS.SE.t -> bool

        val lt_dec : VS.SE.t -> VS.SE.t -> bool

        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        val coq_In_dec : VS.elt -> VS.t -> bool

        val of_list : VS.elt list -> VS.t

        val to_list : VS.t -> VS.elt list

        val fold_rec :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
          (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) ->
          VS.t -> 'a2

        val fold_rel :
          (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_bis :
          (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __
          -> 'a1 -> 'a1) -> VS.t -> 'a1

        val cardinal_inv_2 : VS.t -> int -> VS.elt

        val cardinal_inv_2b : VS.t -> VS.elt
       end

      val gtb : VS.SE.t -> VS.SE.t -> bool

      val leb : VS.SE.t -> VS.SE.t -> bool

      val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

      val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val memP : VS.elt -> VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool
     end

    val add_to_set : VS.elt -> 'a1 -> VS.t -> VS.t

    val key_set : 'a1 TypEnv.TE.t -> VS.t
   end

  val vars_env : TypEnv.TE.env -> VS.t

  val is_defined : VarOrder.t -> TypEnv.TE.env -> bool

  val are_defined : VS.t -> TypEnv.TE.env -> bool

  val memenvP : TypEnv.TE.key -> typ TypEnv.TE.t -> reflect

  val well_defined_instr : TypEnv.TE.env -> instr -> bool

  val well_formed_instr : TypEnv.TE.env -> instr -> bool

  val well_formed_program : TypEnv.TE.env -> program -> bool

  val find_non_well_formed_instr : TypEnv.TE.env -> program -> instr option

  val well_formed_eexp : TypEnv.TE.env -> eexp -> bool

  val well_formed_rexp : TypEnv.TE.env -> rexp -> bool

  val well_formed_ebexp : TypEnv.TE.env -> ebexp -> bool

  val well_formed_rbexp : TypEnv.TE.env -> rbexp -> bool

  val well_formed_bexp : TypEnv.TE.env -> bexp -> bool

  val well_formed_spec : spec -> bool

  val defmemP : VarOrder.t -> TypEnv.TE.env -> reflect

  val memdefP : TypEnv.TE.key -> typ TypEnv.TE.t -> reflect

  val defsubP : VS.t -> TypEnv.TE.env -> reflect

  val is_assume : instr -> bool

  val force_conform_vars :
    TypEnv.TE.env -> VarOrder.t list -> Store.t -> Store.t

  val force_conform : TypEnv.TE.env -> TypEnv.TE.env -> Store.t -> Store.t
 end
