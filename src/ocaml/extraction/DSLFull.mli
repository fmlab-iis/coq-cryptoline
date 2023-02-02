open BinInt
open BinNums
open Bool
open DSLRaw
open Datatypes
open FMaps
open FSets
open NBitsDef
open NBitsOp
open Seqs
open Store
open String0
open Strings
open Typ
open Var
open Eqtype
open Seq
open Ssrnat

type __ = Obj.t

module MakeDSL :
 functor (V:SsrOrder.SsrOrder) ->
 functor (VP:Printer with type t = V.t) ->
 functor (VS:SsrFSet with module SE = V) ->
 functor (VM:SsrFMap with module SE = V) ->
 functor (TE:TypEnv.TypEnv with module SE = V with type 'x t = 'x VM.t) ->
 functor (S:sig
  type t

  val acc : V.t -> t -> bits

  val upd : V.t -> bits -> t -> t

  val upd2 : V.t -> bits -> V.t -> bits -> t -> t

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

    val equalP : typ TE.t -> typ TE.t -> reflect

    val eequalP : typ TE.t -> typ TE.t -> reflect
   end
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

    val equalP : VS.t -> VS.t -> reflect

    val subsetP : VS.t -> VS.t -> reflect

    val emptyP : VS.t -> reflect

    val disjoint : VS.t -> VS.t -> bool

    val proper_subset : VS.t -> VS.t -> bool
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

    val equalP : typ TE.t -> typ TE.t -> reflect

    val eequalP : typ TE.t -> typ TE.t -> reflect
   end

  type eexp = DSLRaw.eexp

  val evar : V.t -> eexp

  val econst : coq_Z -> eexp

  val eunary : eunop -> eexp -> eexp

  val ebinary : ebinop -> eexp -> eexp -> eexp

  val eneg : eexp -> eexp

  val eadd : eexp -> eexp -> eexp

  val esub : eexp -> eexp -> eexp

  val emul : eexp -> eexp -> eexp

  val esq : eexp -> eexp

  val epow : eexp -> coq_N -> DSLRaw.eexp

  val eadds : eexp list -> eexp

  val emuls : eexp list -> eexp

  val z2expn : coq_Z -> coq_Z

  val e2expn : coq_Z -> DSLRaw.eexp

  val emul2p : DSLRaw.eexp -> coq_Z -> DSLRaw.eexp

  val vars_eexp : eexp -> VS.t

  val vars_eexps : eexp list -> VS.t

  val eexp_eqP : eexp -> eexp -> reflect

  val eexp_eqMixin : eexp Equality.mixin_of

  val eexp_eqType : Equality.coq_type

  val eexp_eqn : DSLRaw.eexp -> DSLRaw.eexp -> bool

  val limbsi : int -> coq_Z -> eexp list -> eexp

  val limbs : coq_Z -> eexp list -> eexp

  type rexp = DSLRaw.rexp

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

  val rexp_eqn : DSLRaw.rexp -> DSLRaw.rexp -> bool

  type ebexp = DSLRaw.ebexp

  val etrue : ebexp

  val eeq : eexp -> eexp -> ebexp

  val eeqmod : eexp -> eexp -> eexp list -> ebexp

  val eand : ebexp -> ebexp -> ebexp

  val eands : ebexp list -> ebexp

  val split_eand : ebexp -> ebexp list

  val vars_ebexp : ebexp -> VS.t

  val ebexp_eqP : ebexp -> ebexp -> reflect

  val ebexp_eqMixin : ebexp Equality.mixin_of

  val ebexp_eqType : Equality.coq_type

  val ebexp_eqn : DSLRaw.ebexp -> DSLRaw.ebexp -> bool

  type rbexp = DSLRaw.rbexp

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

  val rbexp_eqn : DSLRaw.rbexp -> DSLRaw.rbexp -> bool

  type bexp = ebexp * rbexp

  val btrue : bexp

  val eqn_bexp : bexp -> ebexp

  val rng_bexp : bexp -> rbexp

  val band : bexp -> bexp -> bexp

  val bands : bexp list -> bexp

  val bands2 : ebexp list -> rbexp list -> ebexp * rbexp

  val vars_bexp : bexp -> VS.t

  val avar : Equality.sort -> atom

  val aconst : typ -> bits -> atom

  type atom = DSLRaw.atom

  val atyp : atom -> TE.env -> typ

  val asize : atom -> TE.env -> int

  val atom_eqn : atom -> atom -> bool

  val atom_eqP : atom -> atom -> reflect

  val atom_eqMixin : atom Equality.mixin_of

  val atom_eqType : Equality.coq_type

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
  | Icut of bexp
  | Iassert of bexp
  | Iassume of bexp

  val instr_rect :
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
    'a1) -> (bexp -> 'a1) -> (bexp -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  val instr_rec :
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
    'a1) -> (bexp -> 'a1) -> (bexp -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  type program = instr list

  val instr_eqn : instr -> instr -> bool

  val instr_eqP : instr -> instr -> reflect

  val instr_eqMixin : instr Equality.mixin_of

  val instr_eqType : Equality.coq_type

  val vars_atom : atom -> VS.t

  val vars_instr : instr -> VS.t

  val lvs_instr : instr -> VS.t

  val rvs_instr : instr -> VS.t

  val vars_program : program -> VS.t

  val lvs_program : program -> VS.t

  val rvs_program : program -> VS.t

  type spec = { sinputs : TE.env; spre : bexp; sprog : program; spost : bexp }

  val sinputs : spec -> TE.env

  val spre : spec -> bexp

  val sprog : spec -> program

  val spost : spec -> bexp

  val vars_spec : spec -> VS.t

  val string_of_eunop : eunop -> char list

  val string_of_ebinop : ebinop -> char list

  val string_of_runop : runop -> char list

  val string_of_rbinop : rbinop -> char list

  val string_of_rcmpop : rcmpop -> char list

  val string_of_eexp : DSLRaw.eexp -> char list

  val string_of_eexps : char list -> DSLRaw.eexp list -> char list

  val string_of_ebexp : DSLRaw.ebexp -> char list

  val string_of_rexp : DSLRaw.rexp -> char list

  val string_of_rbexp : DSLRaw.rbexp -> char list

  val string_of_bexp : bexp -> char list

  val string_of_typ : typ -> char list

  val string_of_var_with_typ : (V.t * typ) -> char list

  val string_of_vars : VS.t -> char list

  val string_of_atom : atom -> char list

  val string_of_instr : instr -> char list

  val string_of_instr' : instr -> char list

  val string_of_program : program -> char list

  val string_of_typenv : TE.env -> char list

  val string_of_spec : spec -> char list

  val bv2z : typ -> bits -> coq_Z

  val acc2z : TE.env -> V.t -> S.t -> coq_Z

  val instr_succ_typenv : instr -> TE.env -> TE.env

  val program_succ_typenv : program -> TE.env -> TE.env

  val eval_eunop : eunop -> coq_Z -> coq_Z

  val eval_ebinop : ebinop -> coq_Z -> coq_Z -> coq_Z

  val eval_runop : runop -> bits -> bits

  val eval_rbinop : rbinop -> bits -> bits -> bits

  val eval_rcmpop : rcmpop -> bits -> bits -> bool

  val eval_eexp : eexp -> TE.env -> S.t -> coq_Z

  val eval_eexps : eexp list -> TE.env -> S.t -> coq_Z list

  val eval_rexp : rexp -> S.t -> bits

  val eval_rbexp : rbexp -> S.t -> bool

  val eval_atom : atom -> S.t -> bits

  val well_typed_eexp : TE.env -> eexp -> bool

  val well_typed_eexps : TE.env -> eexp list -> bool

  val well_typed_rexp : TE.env -> rexp -> bool

  val well_typed_ebexp : TE.env -> ebexp -> bool

  val well_typed_rbexp : TE.env -> rbexp -> bool

  val well_typed_bexp : TE.env -> bexp -> bool

  val well_sized_atom : TE.env -> atom -> bool

  val size_matched_atom : atom -> bool

  val well_typed_atom : TE.env -> atom -> bool

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

      val equalP : VS.t -> VS.t -> reflect

      val subsetP : VS.t -> VS.t -> reflect

      val emptyP : VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool

      val proper_subset : VS.t -> VS.t -> bool
     end

    val add_to_set : VS.elt -> 'a1 -> VS.t -> VS.t

    val key_set : 'a1 TE.t -> VS.t
   end

  val vars_env : TE.env -> VS.t

  val is_defined : V.t -> TE.env -> bool

  val are_defined : VS.t -> TE.env -> bool

  val memenvP : TE.key -> typ TE.t -> reflect

  val well_defined_instr : TE.env -> instr -> bool

  val well_formed_eexp : TE.env -> eexp -> bool

  val well_formed_eexps : TE.env -> eexp list -> bool

  val well_formed_rexp : TE.env -> rexp -> bool

  val well_formed_ebexp : TE.env -> ebexp -> bool

  val well_formed_rbexp : TE.env -> rbexp -> bool

  val well_formed_bexp : TE.env -> bexp -> bool

  val well_formed_instr : TE.env -> instr -> bool

  val well_formed_program : TE.env -> program -> bool

  val find_non_well_formed_instr : TE.env -> program -> instr option

  val well_formed_spec : spec -> bool

  val defmemP : V.t -> TE.env -> reflect

  val memdefP : TE.key -> typ TE.t -> reflect

  val defsubP : VS.t -> TE.env -> reflect

  val inputs_program_rec : VS.t -> program -> VS.t

  val inputs_program : program -> VS.t

  val is_nondet : instr -> bool

  val is_cut : instr -> bool

  val is_assert : instr -> bool

  val is_assume : instr -> bool

  val force_conform_vars : TE.env -> V.t list -> S.t -> S.t

  val force_conform : TE.env -> TE.env -> S.t -> S.t

  module TSEQM :
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

      val equalP : VS.t -> VS.t -> reflect

      val subsetP : VS.t -> VS.t -> reflect

      val emptyP : VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool

      val proper_subset : VS.t -> VS.t -> bool
     end
   end

  module MA :
   sig
    module MA :
     sig
      module VSLemmas :
       sig
        module F :
         sig
          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module OP :
         sig
          module ME :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end

          module P :
           sig
            module Dec :
             sig
              module F :
               sig
                val eqb : Equality.sort -> Equality.sort -> bool
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
              val eqb : Equality.sort -> Equality.sort -> bool
             end

            val coq_In_dec : VS.elt -> VS.t -> bool

            val of_list : VS.elt list -> VS.t

            val to_list : VS.t -> VS.elt list

            val fold_rec :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
              (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a2

            val fold_rec_bis :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1
              -> __ -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ ->
              __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_nodep :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1
              -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_weak :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ ->
              'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 ->
              'a2) -> VS.t -> 'a2

            val fold_rel :
              (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
              -> VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
              'a3

            val set_induction :
              (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ ->
              __ -> 'a1) -> VS.t -> 'a1

            val set_induction_bis :
              (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t ->
              __ -> 'a1 -> 'a1) -> VS.t -> 'a1

            val cardinal_inv_2 : VS.t -> int -> VS.elt

            val cardinal_inv_2b : VS.t -> VS.elt
           end

          val gtb : Equality.sort -> Equality.sort -> bool

          val leb : Equality.sort -> Equality.sort -> bool

          val elements_lt : Equality.sort -> VS.t -> Equality.sort list

          val elements_ge : Equality.sort -> VS.t -> Equality.sort list

          val set_induction_max :
            (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort ->
            __ -> __ -> 'a1) -> VS.t -> 'a1

          val set_induction_min :
            (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort ->
            __ -> __ -> 'a1) -> VS.t -> 'a1
         end

        val eqb : Equality.sort -> Equality.sort -> bool

        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module P :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : Equality.sort -> Equality.sort -> bool
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
            val eqb : Equality.sort -> Equality.sort -> bool
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

        val gtb : Equality.sort -> Equality.sort -> bool

        val leb : Equality.sort -> Equality.sort -> bool

        val elements_lt : Equality.sort -> VS.t -> Equality.sort list

        val elements_ge : Equality.sort -> VS.t -> Equality.sort list

        val set_induction_max :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1

        val set_induction_min :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1

        val memP : VS.elt -> VS.t -> reflect

        val equalP : VS.t -> VS.t -> reflect

        val subsetP : VS.t -> VS.t -> reflect

        val emptyP : VS.t -> reflect

        val disjoint : VS.t -> VS.t -> bool

        val proper_subset : VS.t -> VS.t -> bool
       end

      module VMLemmas :
       sig
        module F :
         sig
          val eqb : Equality.sort -> Equality.sort -> bool

          val coq_In_dec : 'a1 TE.t -> TE.key -> bool
         end

        module OP :
         sig
          module ME :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end

          module O :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = Equality.sort
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Equality.sort -> Equality.sort -> bool

              val lt_dec : Equality.sort -> Equality.sort -> bool

              val eqb : Equality.sort -> Equality.sort -> bool
             end
           end

          module P :
           sig
            module F :
             sig
              val eqb : Equality.sort -> Equality.sort -> bool

              val coq_In_dec : 'a1 TE.t -> TE.key -> bool
             end

            val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

            val of_list : (TE.key * 'a1) list -> 'a1 TE.t

            val to_list : 'a1 TE.t -> (TE.key * 'a1) list

            val fold_rec :
              (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t
              -> __ -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t
              -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

            val fold_rec_bis :
              (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t
              -> 'a1 TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key ->
              'a1 -> 'a2 -> 'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

            val fold_rec_nodep :
              (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 ->
              (TE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

            val fold_rec_weak :
              (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t
              -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 ->
              'a1 TE.t -> __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

            val fold_rel :
              (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3)
              -> 'a2 -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 ->
              'a3 -> __ -> 'a4 -> 'a4) -> 'a4

            val map_induction :
              ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
              TE.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

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
            ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
            Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

          val map_induction_min :
            ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
            Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2
         end

        val eqb : Equality.sort -> Equality.sort -> bool

        val coq_In_dec : 'a1 TE.t -> TE.key -> bool

        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module O :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end
         end

        module P :
         sig
          module F :
           sig
            val eqb : Equality.sort -> Equality.sort -> bool

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
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
          Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val map_induction_min :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
          Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val memP : TE.key -> 'a1 TE.t -> reflect

        val split : ('a1 * 'a2) TE.t -> 'a1 TE.t * 'a2 TE.t

        module EFacts :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        val max_opt : TE.key -> TE.key option -> TE.key

        val max_key_elements : (TE.key * 'a1) list -> TE.key option

        val max_key : 'a1 TE.t -> TE.key option

        val min_opt : TE.key -> TE.key option -> TE.key

        val min_key_elements : (TE.key * 'a1) list -> TE.key option

        val min_key : 'a1 TE.t -> TE.key option
       end
     end

    module VSLemmas :
     sig
      module F :
       sig
        val eqb : Equality.sort -> Equality.sort -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module P :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : Equality.sort -> Equality.sort -> bool
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
            val eqb : Equality.sort -> Equality.sort -> bool
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

        val gtb : Equality.sort -> Equality.sort -> bool

        val leb : Equality.sort -> Equality.sort -> bool

        val elements_lt : Equality.sort -> VS.t -> Equality.sort list

        val elements_ge : Equality.sort -> VS.t -> Equality.sort list

        val set_induction_max :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1

        val set_induction_min :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1
       end

      val eqb : Equality.sort -> Equality.sort -> bool

      module ME :
       sig
        module TO :
         sig
          type t = Equality.sort
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : Equality.sort -> Equality.sort -> bool
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
          val eqb : Equality.sort -> Equality.sort -> bool
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

      val gtb : Equality.sort -> Equality.sort -> bool

      val leb : Equality.sort -> Equality.sort -> bool

      val elements_lt : Equality.sort -> VS.t -> Equality.sort list

      val elements_ge : Equality.sort -> VS.t -> Equality.sort list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __ ->
        __ -> 'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __ ->
        __ -> 'a1) -> VS.t -> 'a1

      val memP : VS.elt -> VS.t -> reflect

      val equalP : VS.t -> VS.t -> reflect

      val subsetP : VS.t -> VS.t -> reflect

      val emptyP : VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool

      val proper_subset : VS.t -> VS.t -> bool
     end

    module VMLemmas :
     sig
      module F :
       sig
        val eqb : Equality.sort -> Equality.sort -> bool

        val coq_In_dec : 'a1 TE.t -> TE.key -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module O :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end
         end

        module P :
         sig
          module F :
           sig
            val eqb : Equality.sort -> Equality.sort -> bool

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
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
          Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val map_induction_min :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
          Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2
       end

      val eqb : Equality.sort -> Equality.sort -> bool

      val coq_In_dec : 'a1 TE.t -> TE.key -> bool

      module ME :
       sig
        module TO :
         sig
          type t = Equality.sort
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : Equality.sort -> Equality.sort -> bool

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
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
        Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_min :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
        Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val memP : TE.key -> 'a1 TE.t -> reflect

      val split : ('a1 * 'a2) TE.t -> 'a1 TE.t * 'a2 TE.t

      module EFacts :
       sig
        module TO :
         sig
          type t = Equality.sort
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end

      val max_opt : TE.key -> TE.key option -> TE.key

      val max_key_elements : (TE.key * 'a1) list -> TE.key option

      val max_key : 'a1 TE.t -> TE.key option

      val min_opt : TE.key -> TE.key option -> TE.key

      val min_key_elements : (TE.key * 'a1) list -> TE.key option

      val min_key : 'a1 TE.t -> TE.key option
     end
   end

  val cut_spec_rec :
    instr list -> TE.env -> bexp -> instr list -> bexp -> spec list

  val cut_spec : spec -> spec list

  val compose_spec : spec -> spec -> spec

  val program_has_no_cut : program -> bool

  val spec_has_no_cut : spec -> bool

  val cut_asserts_rec :
    instr list -> TE.env -> bexp -> instr list -> bexp -> spec list

  val cut_asserts : spec -> spec list

  val program_has_no_assert : program -> bool

  val spec_has_no_assert : spec -> bool

  val extract_asserts_rec :
    instr list -> TE.env -> bexp -> instr list -> spec list

  val extract_asserts : spec -> spec list

  val remove_asserts_program : program -> program

  val remove_asserts : spec -> spec
 end

module DSLFull :
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

    val equalP : VS.t -> VS.t -> reflect

    val subsetP : VS.t -> VS.t -> reflect

    val emptyP : VS.t -> reflect

    val disjoint : VS.t -> VS.t -> bool

    val proper_subset : VS.t -> VS.t -> bool
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

    val equalP : typ TypEnv.TE.t -> typ TypEnv.TE.t -> reflect

    val eequalP : typ TypEnv.TE.t -> typ TypEnv.TE.t -> reflect
   end

  type eexp = DSLRaw.eexp

  val evar : VarOrder.t -> eexp

  val econst : coq_Z -> eexp

  val eunary : eunop -> eexp -> eexp

  val ebinary : ebinop -> eexp -> eexp -> eexp

  val eneg : eexp -> eexp

  val eadd : eexp -> eexp -> eexp

  val esub : eexp -> eexp -> eexp

  val emul : eexp -> eexp -> eexp

  val esq : eexp -> eexp

  val epow : eexp -> coq_N -> DSLRaw.eexp

  val eadds : eexp list -> eexp

  val emuls : eexp list -> eexp

  val z2expn : coq_Z -> coq_Z

  val e2expn : coq_Z -> DSLRaw.eexp

  val emul2p : DSLRaw.eexp -> coq_Z -> DSLRaw.eexp

  val vars_eexp : eexp -> VS.t

  val vars_eexps : eexp list -> VS.t

  val eexp_eqP : eexp -> eexp -> reflect

  val eexp_eqMixin : eexp Equality.mixin_of

  val eexp_eqType : Equality.coq_type

  val eexp_eqn : DSLRaw.eexp -> DSLRaw.eexp -> bool

  val limbsi : int -> coq_Z -> eexp list -> eexp

  val limbs : coq_Z -> eexp list -> eexp

  type rexp = DSLRaw.rexp

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

  val rexp_eqn : DSLRaw.rexp -> DSLRaw.rexp -> bool

  type ebexp = DSLRaw.ebexp

  val etrue : ebexp

  val eeq : eexp -> eexp -> ebexp

  val eeqmod : eexp -> eexp -> eexp list -> ebexp

  val eand : ebexp -> ebexp -> ebexp

  val eands : ebexp list -> ebexp

  val split_eand : ebexp -> ebexp list

  val vars_ebexp : ebexp -> VS.t

  val ebexp_eqP : ebexp -> ebexp -> reflect

  val ebexp_eqMixin : ebexp Equality.mixin_of

  val ebexp_eqType : Equality.coq_type

  val ebexp_eqn : DSLRaw.ebexp -> DSLRaw.ebexp -> bool

  type rbexp = DSLRaw.rbexp

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

  val rbexp_eqn : DSLRaw.rbexp -> DSLRaw.rbexp -> bool

  type bexp = ebexp * rbexp

  val btrue : bexp

  val eqn_bexp : bexp -> ebexp

  val rng_bexp : bexp -> rbexp

  val band : bexp -> bexp -> bexp

  val bands : bexp list -> bexp

  val bands2 : ebexp list -> rbexp list -> ebexp * rbexp

  val vars_bexp : bexp -> VS.t

  val avar : Equality.sort -> atom

  val aconst : typ -> bits -> atom

  type atom = DSLRaw.atom

  val atyp : atom -> TypEnv.TE.env -> typ

  val asize : atom -> TypEnv.TE.env -> int

  val atom_eqn : atom -> atom -> bool

  val atom_eqP : atom -> atom -> reflect

  val atom_eqMixin : atom Equality.mixin_of

  val atom_eqType : Equality.coq_type

  type instr =
  | Imov of VarOrder.t * atom
  | Ishl of VarOrder.t * atom * int
  | Icshl of VarOrder.t * VarOrder.t * atom * atom * int
  | Inondet of VarOrder.t * typ
  | Icmov of VarOrder.t * atom * atom * atom
  | Inop
  | Inot of VarOrder.t * typ * atom
  | Iadd of VarOrder.t * atom * atom
  | Iadds of VarOrder.t * VarOrder.t * atom * atom
  | Iadc of VarOrder.t * atom * atom * atom
  | Iadcs of VarOrder.t * VarOrder.t * atom * atom * atom
  | Isub of VarOrder.t * atom * atom
  | Isubc of VarOrder.t * VarOrder.t * atom * atom
  | Isubb of VarOrder.t * VarOrder.t * atom * atom
  | Isbc of VarOrder.t * atom * atom * atom
  | Isbcs of VarOrder.t * VarOrder.t * atom * atom * atom
  | Isbb of VarOrder.t * atom * atom * atom
  | Isbbs of VarOrder.t * VarOrder.t * atom * atom * atom
  | Imul of VarOrder.t * atom * atom
  | Imull of VarOrder.t * VarOrder.t * atom * atom
  | Imulj of VarOrder.t * atom * atom
  | Isplit of VarOrder.t * VarOrder.t * atom * int
  | Iand of VarOrder.t * typ * atom * atom
  | Ior of VarOrder.t * typ * atom * atom
  | Ixor of VarOrder.t * typ * atom * atom
  | Icast of VarOrder.t * typ * atom
  | Ivpc of VarOrder.t * typ * atom
  | Ijoin of VarOrder.t * atom * atom
  | Icut of bexp
  | Iassert of bexp
  | Iassume of bexp

  val instr_rect :
    (VarOrder.t -> atom -> 'a1) -> (VarOrder.t -> atom -> int -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atom -> atom -> int -> 'a1) -> (VarOrder.t
    -> typ -> 'a1) -> (VarOrder.t -> atom -> atom -> atom -> 'a1) -> 'a1 ->
    (VarOrder.t -> typ -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> 'a1)
    -> (VarOrder.t -> VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t ->
    atom -> atom -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom -> atom
    -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t ->
    VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom
    -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atom -> atom -> atom -> 'a1) -> (VarOrder.t
    -> atom -> atom -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom ->
    atom -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t -> atom
    -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom -> int -> 'a1) ->
    (VarOrder.t -> typ -> atom -> atom -> 'a1) -> (VarOrder.t -> typ -> atom
    -> atom -> 'a1) -> (VarOrder.t -> typ -> atom -> atom -> 'a1) ->
    (VarOrder.t -> typ -> atom -> 'a1) -> (VarOrder.t -> typ -> atom -> 'a1)
    -> (VarOrder.t -> atom -> atom -> 'a1) -> (bexp -> 'a1) -> (bexp -> 'a1)
    -> (bexp -> 'a1) -> instr -> 'a1

  val instr_rec :
    (VarOrder.t -> atom -> 'a1) -> (VarOrder.t -> atom -> int -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atom -> atom -> int -> 'a1) -> (VarOrder.t
    -> typ -> 'a1) -> (VarOrder.t -> atom -> atom -> atom -> 'a1) -> 'a1 ->
    (VarOrder.t -> typ -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> 'a1)
    -> (VarOrder.t -> VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t ->
    atom -> atom -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom -> atom
    -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t ->
    VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom
    -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atom -> atom -> atom -> 'a1) -> (VarOrder.t
    -> atom -> atom -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom ->
    atom -> atom -> 'a1) -> (VarOrder.t -> atom -> atom -> 'a1) ->
    (VarOrder.t -> VarOrder.t -> atom -> atom -> 'a1) -> (VarOrder.t -> atom
    -> atom -> 'a1) -> (VarOrder.t -> VarOrder.t -> atom -> int -> 'a1) ->
    (VarOrder.t -> typ -> atom -> atom -> 'a1) -> (VarOrder.t -> typ -> atom
    -> atom -> 'a1) -> (VarOrder.t -> typ -> atom -> atom -> 'a1) ->
    (VarOrder.t -> typ -> atom -> 'a1) -> (VarOrder.t -> typ -> atom -> 'a1)
    -> (VarOrder.t -> atom -> atom -> 'a1) -> (bexp -> 'a1) -> (bexp -> 'a1)
    -> (bexp -> 'a1) -> instr -> 'a1

  type program = instr list

  val instr_eqn : instr -> instr -> bool

  val instr_eqP : instr -> instr -> reflect

  val instr_eqMixin : instr Equality.mixin_of

  val instr_eqType : Equality.coq_type

  val vars_atom : atom -> VS.t

  val vars_instr : instr -> VS.t

  val lvs_instr : instr -> VS.t

  val rvs_instr : instr -> VS.t

  val vars_program : program -> VS.t

  val lvs_program : program -> VS.t

  val rvs_program : program -> VS.t

  type spec = { sinputs : TypEnv.TE.env; spre : bexp; sprog : program;
                spost : bexp }

  val sinputs : spec -> TypEnv.TE.env

  val spre : spec -> bexp

  val sprog : spec -> program

  val spost : spec -> bexp

  val vars_spec : spec -> VS.t

  val string_of_eunop : eunop -> char list

  val string_of_ebinop : ebinop -> char list

  val string_of_runop : runop -> char list

  val string_of_rbinop : rbinop -> char list

  val string_of_rcmpop : rcmpop -> char list

  val string_of_eexp : DSLRaw.eexp -> char list

  val string_of_eexps : char list -> DSLRaw.eexp list -> char list

  val string_of_ebexp : DSLRaw.ebexp -> char list

  val string_of_rexp : DSLRaw.rexp -> char list

  val string_of_rbexp : DSLRaw.rbexp -> char list

  val string_of_bexp : bexp -> char list

  val string_of_typ : typ -> char list

  val string_of_var_with_typ : (VarOrder.t * typ) -> char list

  val string_of_vars : VS.t -> char list

  val string_of_atom : atom -> char list

  val string_of_instr : instr -> char list

  val string_of_instr' : instr -> char list

  val string_of_program : program -> char list

  val string_of_typenv : TypEnv.TE.env -> char list

  val string_of_spec : spec -> char list

  val bv2z : typ -> bits -> coq_Z

  val acc2z : TypEnv.TE.env -> VarOrder.t -> State.Store.t -> coq_Z

  val instr_succ_typenv : instr -> TypEnv.TE.env -> TypEnv.TE.env

  val program_succ_typenv : program -> TypEnv.TE.env -> TypEnv.TE.env

  val eval_eunop : eunop -> coq_Z -> coq_Z

  val eval_ebinop : ebinop -> coq_Z -> coq_Z -> coq_Z

  val eval_runop : runop -> bits -> bits

  val eval_rbinop : rbinop -> bits -> bits -> bits

  val eval_rcmpop : rcmpop -> bits -> bits -> bool

  val eval_eexp : eexp -> TypEnv.TE.env -> State.Store.t -> coq_Z

  val eval_eexps : eexp list -> TypEnv.TE.env -> State.Store.t -> coq_Z list

  val eval_rexp : rexp -> State.Store.t -> bits

  val eval_rbexp : rbexp -> State.Store.t -> bool

  val eval_atom : atom -> State.Store.t -> bits

  val well_typed_eexp : TypEnv.TE.env -> eexp -> bool

  val well_typed_eexps : TypEnv.TE.env -> eexp list -> bool

  val well_typed_rexp : TypEnv.TE.env -> rexp -> bool

  val well_typed_ebexp : TypEnv.TE.env -> ebexp -> bool

  val well_typed_rbexp : TypEnv.TE.env -> rbexp -> bool

  val well_typed_bexp : TypEnv.TE.env -> bexp -> bool

  val well_sized_atom : TypEnv.TE.env -> atom -> bool

  val size_matched_atom : atom -> bool

  val well_typed_atom : TypEnv.TE.env -> atom -> bool

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

      val equalP : VS.t -> VS.t -> reflect

      val subsetP : VS.t -> VS.t -> reflect

      val emptyP : VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool

      val proper_subset : VS.t -> VS.t -> bool
     end

    val add_to_set : VS.elt -> 'a1 -> VS.t -> VS.t

    val key_set : 'a1 TypEnv.TE.t -> VS.t
   end

  val vars_env : TypEnv.TE.env -> VS.t

  val is_defined : VarOrder.t -> TypEnv.TE.env -> bool

  val are_defined : VS.t -> TypEnv.TE.env -> bool

  val memenvP : TypEnv.TE.key -> typ TypEnv.TE.t -> reflect

  val well_defined_instr : TypEnv.TE.env -> instr -> bool

  val well_formed_eexp : TypEnv.TE.env -> eexp -> bool

  val well_formed_eexps : TypEnv.TE.env -> eexp list -> bool

  val well_formed_rexp : TypEnv.TE.env -> rexp -> bool

  val well_formed_ebexp : TypEnv.TE.env -> ebexp -> bool

  val well_formed_rbexp : TypEnv.TE.env -> rbexp -> bool

  val well_formed_bexp : TypEnv.TE.env -> bexp -> bool

  val well_formed_instr : TypEnv.TE.env -> instr -> bool

  val well_formed_program : TypEnv.TE.env -> program -> bool

  val find_non_well_formed_instr : TypEnv.TE.env -> program -> instr option

  val well_formed_spec : spec -> bool

  val defmemP : VarOrder.t -> TypEnv.TE.env -> reflect

  val memdefP : TypEnv.TE.key -> typ TypEnv.TE.t -> reflect

  val defsubP : VS.t -> TypEnv.TE.env -> reflect

  val inputs_program_rec : VS.t -> program -> VS.t

  val inputs_program : program -> VS.t

  val is_nondet : instr -> bool

  val is_cut : instr -> bool

  val is_assert : instr -> bool

  val is_assume : instr -> bool

  val force_conform_vars :
    TypEnv.TE.env -> VarOrder.t list -> State.Store.t -> State.Store.t

  val force_conform :
    TypEnv.TE.env -> TypEnv.TE.env -> State.Store.t -> State.Store.t

  module TSEQM :
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

      val equalP : VS.t -> VS.t -> reflect

      val subsetP : VS.t -> VS.t -> reflect

      val emptyP : VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool

      val proper_subset : VS.t -> VS.t -> bool
     end
   end

  module MA :
   sig
    module MA :
     sig
      module VSLemmas :
       sig
        module F :
         sig
          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module OP :
         sig
          module ME :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end

          module P :
           sig
            module Dec :
             sig
              module F :
               sig
                val eqb : Equality.sort -> Equality.sort -> bool
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
              val eqb : Equality.sort -> Equality.sort -> bool
             end

            val coq_In_dec : VS.elt -> VS.t -> bool

            val of_list : VS.elt list -> VS.t

            val to_list : VS.t -> VS.elt list

            val fold_rec :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
              (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2)
              -> 'a2

            val fold_rec_bis :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1
              -> __ -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ ->
              __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_nodep :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1
              -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_weak :
              (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ ->
              'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 ->
              'a2) -> VS.t -> 'a2

            val fold_rel :
              (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
              -> VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
              'a3

            val set_induction :
              (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ ->
              __ -> 'a1) -> VS.t -> 'a1

            val set_induction_bis :
              (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t ->
              __ -> 'a1 -> 'a1) -> VS.t -> 'a1

            val cardinal_inv_2 : VS.t -> int -> VS.elt

            val cardinal_inv_2b : VS.t -> VS.elt
           end

          val gtb : Equality.sort -> Equality.sort -> bool

          val leb : Equality.sort -> Equality.sort -> bool

          val elements_lt : Equality.sort -> VS.t -> Equality.sort list

          val elements_ge : Equality.sort -> VS.t -> Equality.sort list

          val set_induction_max :
            (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort ->
            __ -> __ -> 'a1) -> VS.t -> 'a1

          val set_induction_min :
            (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort ->
            __ -> __ -> 'a1) -> VS.t -> 'a1
         end

        val eqb : Equality.sort -> Equality.sort -> bool

        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module P :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : Equality.sort -> Equality.sort -> bool
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
            val eqb : Equality.sort -> Equality.sort -> bool
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

        val gtb : Equality.sort -> Equality.sort -> bool

        val leb : Equality.sort -> Equality.sort -> bool

        val elements_lt : Equality.sort -> VS.t -> Equality.sort list

        val elements_ge : Equality.sort -> VS.t -> Equality.sort list

        val set_induction_max :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1

        val set_induction_min :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1

        val memP : VS.elt -> VS.t -> reflect

        val equalP : VS.t -> VS.t -> reflect

        val subsetP : VS.t -> VS.t -> reflect

        val emptyP : VS.t -> reflect

        val disjoint : VS.t -> VS.t -> bool

        val proper_subset : VS.t -> VS.t -> bool
       end

      module VMLemmas :
       sig
        module F :
         sig
          val eqb : Equality.sort -> Equality.sort -> bool

          val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
         end

        module OP :
         sig
          module ME :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end

          module O :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = Equality.sort
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Equality.sort -> Equality.sort -> bool

              val lt_dec : Equality.sort -> Equality.sort -> bool

              val eqb : Equality.sort -> Equality.sort -> bool
             end
           end

          module P :
           sig
            module F :
             sig
              val eqb : Equality.sort -> Equality.sort -> bool

              val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
             end

            val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

            val of_list : (TypEnv.TE.key * 'a1) list -> 'a1 TypEnv.TE.t

            val to_list : 'a1 TypEnv.TE.t -> (TypEnv.TE.key * 'a1) list

            val fold_rec :
              (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t
              -> ('a1 TypEnv.TE.t -> __ -> 'a3) -> (TypEnv.TE.key -> 'a1 ->
              'a2 -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> __ -> __ ->
              'a3 -> 'a3) -> 'a3

            val fold_rec_bis :
              (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t
              -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 ->
              'a3) -> 'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t
              -> __ -> __ -> 'a3 -> 'a3) -> 'a3

            val fold_rec_nodep :
              (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.TE.t
              -> 'a3 -> (TypEnv.TE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
              'a3

            val fold_rec_weak :
              (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TypEnv.TE.t
              -> 'a1 TypEnv.TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
              (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.TE.t -> __ -> 'a3 ->
              'a3) -> 'a1 TypEnv.TE.t -> 'a3

            val fold_rel :
              (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.TE.key -> 'a1
              -> 'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.TE.t -> 'a4 ->
              (TypEnv.TE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

            val map_induction :
              ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
              TypEnv.TE.t -> 'a2 -> TypEnv.TE.key -> 'a1 -> __ -> __ -> 'a2)
              -> 'a1 TypEnv.TE.t -> 'a2

            val map_induction_bis :
              ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> __ -> 'a2 -> 'a2) -> 'a2
              -> (TypEnv.TE.key -> 'a1 -> 'a1 TypEnv.TE.t -> __ -> 'a2 ->
              'a2) -> 'a1 TypEnv.TE.t -> 'a2

            val cardinal_inv_2 :
              'a1 TypEnv.TE.t -> int -> (TypEnv.TE.key * 'a1)

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

            val restrict :
              'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

            val diff : 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

            val coq_Partition_In :
              'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t ->
              TypEnv.TE.key -> bool

            val update_dec :
              'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t -> TypEnv.TE.key -> 'a1 ->
              bool

            val filter_dom :
              (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

            val filter_range :
              ('a1 -> bool) -> 'a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t

            val for_all_dom :
              (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

            val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.TE.t -> bool

            val exists_dom :
              (TypEnv.TE.key -> bool) -> 'a1 TypEnv.TE.t -> bool

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
            TypEnv.TE.t -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) ->
            'a1 TypEnv.TE.t -> 'a2

          val map_induction_min :
            ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
            TypEnv.TE.t -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) ->
            'a1 TypEnv.TE.t -> 'a2
         end

        val eqb : Equality.sort -> Equality.sort -> bool

        val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool

        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module O :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end
         end

        module P :
         sig
          module F :
           sig
            val eqb : Equality.sort -> Equality.sort -> bool

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
          TypEnv.TE.t -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val map_induction_min :
          ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val memP : TypEnv.TE.key -> 'a1 TypEnv.TE.t -> reflect

        val split :
          ('a1 * 'a2) TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a2 TypEnv.TE.t

        module EFacts :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
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
     end

    module VSLemmas :
     sig
      module F :
       sig
        val eqb : Equality.sort -> Equality.sort -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module P :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : Equality.sort -> Equality.sort -> bool
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
            val eqb : Equality.sort -> Equality.sort -> bool
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

        val gtb : Equality.sort -> Equality.sort -> bool

        val leb : Equality.sort -> Equality.sort -> bool

        val elements_lt : Equality.sort -> VS.t -> Equality.sort list

        val elements_ge : Equality.sort -> VS.t -> Equality.sort list

        val set_induction_max :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1

        val set_induction_min :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __
          -> __ -> 'a1) -> VS.t -> 'a1
       end

      val eqb : Equality.sort -> Equality.sort -> bool

      module ME :
       sig
        module TO :
         sig
          type t = Equality.sort
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : Equality.sort -> Equality.sort -> bool
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
          val eqb : Equality.sort -> Equality.sort -> bool
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

      val gtb : Equality.sort -> Equality.sort -> bool

      val leb : Equality.sort -> Equality.sort -> bool

      val elements_lt : Equality.sort -> VS.t -> Equality.sort list

      val elements_ge : Equality.sort -> VS.t -> Equality.sort list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __ ->
        __ -> 'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> Equality.sort -> __ ->
        __ -> 'a1) -> VS.t -> 'a1

      val memP : VS.elt -> VS.t -> reflect

      val equalP : VS.t -> VS.t -> reflect

      val subsetP : VS.t -> VS.t -> reflect

      val emptyP : VS.t -> reflect

      val disjoint : VS.t -> VS.t -> bool

      val proper_subset : VS.t -> VS.t -> bool
     end

    module VMLemmas :
     sig
      module F :
       sig
        val eqb : Equality.sort -> Equality.sort -> bool

        val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module O :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end
         end

        module P :
         sig
          module F :
           sig
            val eqb : Equality.sort -> Equality.sort -> bool

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
          TypEnv.TE.t -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2

        val map_induction_min :
          ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1
          TypEnv.TE.t -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) ->
          'a1 TypEnv.TE.t -> 'a2
       end

      val eqb : Equality.sort -> Equality.sort -> bool

      val coq_In_dec : 'a1 TypEnv.TE.t -> TypEnv.TE.key -> bool

      module ME :
       sig
        module TO :
         sig
          type t = Equality.sort
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : Equality.sort -> Equality.sort -> bool

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
        -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TypEnv.TE.t
        -> 'a2

      val map_induction_min :
        ('a1 TypEnv.TE.t -> __ -> 'a2) -> ('a1 TypEnv.TE.t -> 'a1 TypEnv.TE.t
        -> 'a2 -> Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TypEnv.TE.t
        -> 'a2

      val memP : TypEnv.TE.key -> 'a1 TypEnv.TE.t -> reflect

      val split : ('a1 * 'a2) TypEnv.TE.t -> 'a1 TypEnv.TE.t * 'a2 TypEnv.TE.t

      module EFacts :
       sig
        module TO :
         sig
          type t = Equality.sort
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
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
   end

  val cut_spec_rec :
    instr list -> TypEnv.TE.env -> bexp -> instr list -> bexp -> spec list

  val cut_spec : spec -> spec list

  val compose_spec : spec -> spec -> spec

  val program_has_no_cut : program -> bool

  val spec_has_no_cut : spec -> bool

  val cut_asserts_rec :
    instr list -> TypEnv.TE.env -> bexp -> instr list -> bexp -> spec list

  val cut_asserts : spec -> spec list

  val program_has_no_assert : program -> bool

  val spec_has_no_assert : spec -> bool

  val extract_asserts_rec :
    instr list -> TypEnv.TE.env -> bexp -> instr list -> spec list

  val extract_asserts : spec -> spec list

  val remove_asserts_program : program -> program

  val remove_asserts : spec -> spec
 end
