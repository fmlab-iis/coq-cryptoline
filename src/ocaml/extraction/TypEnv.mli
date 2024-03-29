open Bool
open Datatypes
open EqFMaps
open EqFSets
open EqVar
open List0
open Typ
open Eqtype
open Ssreflect

type __ = Obj.t

module type TypEnv =
 sig
  module SE :
   EqOrder.EqOrder

  module E :
   OrderedType.OrderedType with type t = SE.t

  type key = SE.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  type env = typ t

  val deftyp : typ

  val vtyp : SE.t -> env -> typ

  val vsize : SE.t -> env -> int

  val eequal : env -> env -> bool
 end

module TypEnvLemmas :
 functor (TE:TypEnv) ->
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
      (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __ ->
      'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ -> __ -> __
      -> 'a3 -> 'a3) -> 'a3

    val fold_rec_bis :
      (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> 'a1
      TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1
      TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_nodep :
      (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key ->
      'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_weak :
      (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t -> 'a2 ->
      __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> __ ->
      'a3 -> 'a3) -> 'a1 TE.t -> 'a3

    val fold_rel :
      (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
      -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4
      -> 'a4) -> 'a4

    val map_induction :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val map_induction_bis :
      ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1 ->
      'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

    val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

    val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

    val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

    val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

    val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

    val partition : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

    val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

    val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

    val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

    val coq_Partition_In : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

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
    ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t -> 'a1
    -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

  val map_induction_min :
    ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t -> 'a1
    -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

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

module MakeTypEnv :
 functor (V:EqOrder.EqOrder) ->
 functor (VM:EqFMap with module SE = V) ->
 sig
  module SE :
   EqOrder.EqOrder

  module E :
   OrderedType.OrderedType with type t = VM.SE.t

  type key = SE.t

  type 'x t = 'x VM.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  module Lemmas :
   sig
    module F :
     sig
      val eqb : VM.SE.t -> VM.SE.t -> bool

      val coq_In_dec : 'a1 VM.t -> VM.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = VM.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VM.SE.t -> VM.SE.t -> bool

        val lt_dec : VM.SE.t -> VM.SE.t -> bool

        val eqb : VM.SE.t -> VM.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = VM.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : VM.SE.t -> VM.SE.t -> bool

          val lt_dec : VM.SE.t -> VM.SE.t -> bool

          val eqb : VM.SE.t -> VM.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : VM.SE.t -> VM.SE.t -> bool

          val coq_In_dec : 'a1 VM.t -> VM.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (VM.key * 'a1) list -> 'a1 VM.t

        val to_list : 'a1 VM.t -> (VM.key * 'a1) list

        val fold_rec :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t -> __
          -> 'a3) -> (VM.key -> 'a1 -> 'a2 -> 'a1 VM.t -> 'a1 VM.t -> __ ->
          __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t ->
          'a1 VM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 ->
          'a2 -> 'a1 VM.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> 'a3 -> (VM.key
          -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 VM.t -> 'a1 VM.t ->
          'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 -> 'a2 -> 'a1
          VM.t -> __ -> 'a3 -> 'a3) -> 'a1 VM.t -> 'a3

        val fold_rel :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> (VM.key -> 'a1 -> 'a3 -> 'a3) ->
          'a2 -> 'a3 -> 'a1 VM.t -> 'a4 -> (VM.key -> 'a1 -> 'a2 -> 'a3 -> __
          -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.key
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

        val map_induction_bis :
          ('a1 VM.t -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (VM.key -> 'a1
          -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a1 VM.t -> 'a2

        val cardinal_inv_2 : 'a1 VM.t -> int -> (VM.key * 'a1)

        val cardinal_inv_2b : 'a1 VM.t -> (VM.key * 'a1)

        val filter : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

        val for_all : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

        val exists_ : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

        val partition :
          (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

        val update : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

        val restrict : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

        val diff : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

        val coq_Partition_In :
          'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t -> VM.key -> bool

        val update_dec : 'a1 VM.t -> 'a1 VM.t -> VM.key -> 'a1 -> bool

        val filter_dom : (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t

        val filter_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

        val for_all_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 VM.t -> bool

        val exists_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 VM.t -> bool

        val partition_dom :
          (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

        val partition_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t
       end

      val gtb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

      val leb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

      val elements_lt : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

      val elements_ge : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

      val max_elt_aux : (VM.key * 'a1) list -> (VM.key * 'a1) option

      val max_elt : 'a1 VM.t -> (VM.key * 'a1) option

      val min_elt : 'a1 VM.t -> (VM.key * 'a1) option

      val map_induction_max :
        ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

      val map_induction_min :
        ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2
     end

    val eqb : VM.SE.t -> VM.SE.t -> bool

    val coq_In_dec : 'a1 VM.t -> VM.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = VM.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VM.SE.t -> VM.SE.t -> bool

      val lt_dec : VM.SE.t -> VM.SE.t -> bool

      val eqb : VM.SE.t -> VM.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = VM.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VM.SE.t -> VM.SE.t -> bool

        val lt_dec : VM.SE.t -> VM.SE.t -> bool

        val eqb : VM.SE.t -> VM.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : VM.SE.t -> VM.SE.t -> bool

        val coq_In_dec : 'a1 VM.t -> VM.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (VM.key * 'a1) list -> 'a1 VM.t

      val to_list : 'a1 VM.t -> (VM.key * 'a1) list

      val fold_rec :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t -> __
        -> 'a3) -> (VM.key -> 'a1 -> 'a2 -> 'a1 VM.t -> 'a1 VM.t -> __ -> __
        -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t -> 'a1
        VM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 -> 'a2 ->
        'a1 VM.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> 'a3 -> (VM.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 VM.t -> 'a1 VM.t -> 'a2
        -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 -> 'a2 -> 'a1 VM.t ->
        __ -> 'a3 -> 'a3) -> 'a1 VM.t -> 'a3

      val fold_rel :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> (VM.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 VM.t -> 'a4 -> (VM.key -> 'a1 -> 'a2 -> 'a3 -> __ ->
        'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.key ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

      val map_induction_bis :
        ('a1 VM.t -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (VM.key -> 'a1
        -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a1 VM.t -> 'a2

      val cardinal_inv_2 : 'a1 VM.t -> int -> (VM.key * 'a1)

      val cardinal_inv_2b : 'a1 VM.t -> (VM.key * 'a1)

      val filter : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

      val for_all : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

      val exists_ : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

      val partition :
        (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

      val update : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

      val restrict : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

      val diff : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

      val coq_Partition_In :
        'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t -> VM.key -> bool

      val update_dec : 'a1 VM.t -> 'a1 VM.t -> VM.key -> 'a1 -> bool

      val filter_dom : (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t

      val filter_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

      val for_all_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 VM.t -> bool

      val exists_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 VM.t -> bool

      val partition_dom : (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

      val partition_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t
     end

    val gtb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

    val leb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

    val elements_lt : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

    val elements_ge : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

    val max_elt_aux : (VM.key * 'a1) list -> (VM.key * 'a1) option

    val max_elt : 'a1 VM.t -> (VM.key * 'a1) option

    val min_elt : 'a1 VM.t -> (VM.key * 'a1) option

    val map_induction_max :
      ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

    val map_induction_min :
      ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

    val memP : VM.key -> 'a1 VM.t -> reflect

    val split : ('a1 * 'a2) VM.t -> 'a1 VM.t * 'a2 VM.t

    module EFacts :
     sig
      module TO :
       sig
        type t = VM.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VM.SE.t -> VM.SE.t -> bool

      val lt_dec : VM.SE.t -> VM.SE.t -> bool

      val eqb : VM.SE.t -> VM.SE.t -> bool
     end

    val max_opt : VM.key -> VM.key option -> VM.key

    val max_key_elements : (VM.key * 'a1) list -> VM.key option

    val max_key : 'a1 VM.t -> VM.key option

    val min_opt : VM.key -> VM.key option -> VM.key

    val min_key_elements : (VM.key * 'a1) list -> VM.key option

    val min_key : 'a1 VM.t -> VM.key option
   end

  type env = typ t

  val deftyp : typ

  val vtyp : V.t -> env -> typ

  val vsize : V.t -> env -> int

  val eequal : typ t -> typ t -> bool
 end

module TE :
 sig
  module SE :
   EqOrder.EqOrder

  module E :
   OrderedType.OrderedType with type t = VM.SE.t

  type key = SE.t

  type 'x t = 'x VM.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  module Lemmas :
   sig
    module F :
     sig
      val eqb : VM.SE.t -> VM.SE.t -> bool

      val coq_In_dec : 'a1 VM.t -> VM.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = VM.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VM.SE.t -> VM.SE.t -> bool

        val lt_dec : VM.SE.t -> VM.SE.t -> bool

        val eqb : VM.SE.t -> VM.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = VM.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : VM.SE.t -> VM.SE.t -> bool

          val lt_dec : VM.SE.t -> VM.SE.t -> bool

          val eqb : VM.SE.t -> VM.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : VM.SE.t -> VM.SE.t -> bool

          val coq_In_dec : 'a1 VM.t -> VM.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (VM.key * 'a1) list -> 'a1 VM.t

        val to_list : 'a1 VM.t -> (VM.key * 'a1) list

        val fold_rec :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t -> __
          -> 'a3) -> (VM.key -> 'a1 -> 'a2 -> 'a1 VM.t -> 'a1 VM.t -> __ ->
          __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t ->
          'a1 VM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 ->
          'a2 -> 'a1 VM.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> 'a3 -> (VM.key
          -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 VM.t -> 'a1 VM.t ->
          'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 -> 'a2 -> 'a1
          VM.t -> __ -> 'a3 -> 'a3) -> 'a1 VM.t -> 'a3

        val fold_rel :
          (VM.key -> 'a1 -> 'a2 -> 'a2) -> (VM.key -> 'a1 -> 'a3 -> 'a3) ->
          'a2 -> 'a3 -> 'a1 VM.t -> 'a4 -> (VM.key -> 'a1 -> 'a2 -> 'a3 -> __
          -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.key
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

        val map_induction_bis :
          ('a1 VM.t -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (VM.key -> 'a1
          -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a1 VM.t -> 'a2

        val cardinal_inv_2 : 'a1 VM.t -> int -> (VM.key * 'a1)

        val cardinal_inv_2b : 'a1 VM.t -> (VM.key * 'a1)

        val filter : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

        val for_all : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

        val exists_ : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

        val partition :
          (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

        val update : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

        val restrict : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

        val diff : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

        val coq_Partition_In :
          'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t -> VM.key -> bool

        val update_dec : 'a1 VM.t -> 'a1 VM.t -> VM.key -> 'a1 -> bool

        val filter_dom : (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t

        val filter_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

        val for_all_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 VM.t -> bool

        val exists_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 VM.t -> bool

        val partition_dom :
          (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

        val partition_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t
       end

      val gtb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

      val leb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

      val elements_lt : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

      val elements_ge : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

      val max_elt_aux : (VM.key * 'a1) list -> (VM.key * 'a1) option

      val max_elt : 'a1 VM.t -> (VM.key * 'a1) option

      val min_elt : 'a1 VM.t -> (VM.key * 'a1) option

      val map_induction_max :
        ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

      val map_induction_min :
        ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2
     end

    val eqb : VM.SE.t -> VM.SE.t -> bool

    val coq_In_dec : 'a1 VM.t -> VM.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = VM.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VM.SE.t -> VM.SE.t -> bool

      val lt_dec : VM.SE.t -> VM.SE.t -> bool

      val eqb : VM.SE.t -> VM.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = VM.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VM.SE.t -> VM.SE.t -> bool

        val lt_dec : VM.SE.t -> VM.SE.t -> bool

        val eqb : VM.SE.t -> VM.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : VM.SE.t -> VM.SE.t -> bool

        val coq_In_dec : 'a1 VM.t -> VM.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (VM.key * 'a1) list -> 'a1 VM.t

      val to_list : 'a1 VM.t -> (VM.key * 'a1) list

      val fold_rec :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t -> __
        -> 'a3) -> (VM.key -> 'a1 -> 'a2 -> 'a1 VM.t -> 'a1 VM.t -> __ -> __
        -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> ('a1 VM.t -> 'a1
        VM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 -> 'a2 ->
        'a1 VM.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 VM.t -> 'a3 -> (VM.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 VM.t -> 'a1 VM.t -> 'a2
        -> __ -> 'a3 -> 'a3) -> 'a3 -> (VM.key -> 'a1 -> 'a2 -> 'a1 VM.t ->
        __ -> 'a3 -> 'a3) -> 'a1 VM.t -> 'a3

      val fold_rel :
        (VM.key -> 'a1 -> 'a2 -> 'a2) -> (VM.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 VM.t -> 'a4 -> (VM.key -> 'a1 -> 'a2 -> 'a3 -> __ ->
        'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.key ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

      val map_induction_bis :
        ('a1 VM.t -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (VM.key -> 'a1
        -> 'a1 VM.t -> __ -> 'a2 -> 'a2) -> 'a1 VM.t -> 'a2

      val cardinal_inv_2 : 'a1 VM.t -> int -> (VM.key * 'a1)

      val cardinal_inv_2b : 'a1 VM.t -> (VM.key * 'a1)

      val filter : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

      val for_all : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

      val exists_ : (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> bool

      val partition :
        (VM.key -> 'a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

      val update : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

      val restrict : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

      val diff : 'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t

      val coq_Partition_In :
        'a1 VM.t -> 'a1 VM.t -> 'a1 VM.t -> VM.key -> bool

      val update_dec : 'a1 VM.t -> 'a1 VM.t -> VM.key -> 'a1 -> bool

      val filter_dom : (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t

      val filter_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t

      val for_all_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 VM.t -> bool

      val exists_dom : (VM.key -> bool) -> 'a1 VM.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 VM.t -> bool

      val partition_dom : (VM.key -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t

      val partition_range : ('a1 -> bool) -> 'a1 VM.t -> 'a1 VM.t * 'a1 VM.t
     end

    val gtb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

    val leb : (VM.key * 'a1) -> (VM.key * 'a1) -> bool

    val elements_lt : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

    val elements_ge : (VM.key * 'a1) -> 'a1 VM.t -> (VM.key * 'a1) list

    val max_elt_aux : (VM.key * 'a1) list -> (VM.key * 'a1) option

    val max_elt : 'a1 VM.t -> (VM.key * 'a1) option

    val min_elt : 'a1 VM.t -> (VM.key * 'a1) option

    val map_induction_max :
      ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

    val map_induction_min :
      ('a1 VM.t -> __ -> 'a2) -> ('a1 VM.t -> 'a1 VM.t -> 'a2 -> VM.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 VM.t -> 'a2

    val memP : VM.key -> 'a1 VM.t -> reflect

    val split : ('a1 * 'a2) VM.t -> 'a1 VM.t * 'a2 VM.t

    module EFacts :
     sig
      module TO :
       sig
        type t = VM.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VM.SE.t -> VM.SE.t -> bool

      val lt_dec : VM.SE.t -> VM.SE.t -> bool

      val eqb : VM.SE.t -> VM.SE.t -> bool
     end

    val max_opt : VM.key -> VM.key option -> VM.key

    val max_key_elements : (VM.key * 'a1) list -> VM.key option

    val max_key : 'a1 VM.t -> VM.key option

    val min_opt : VM.key -> VM.key option -> VM.key

    val min_key_elements : (VM.key * 'a1) list -> VM.key option

    val min_key : 'a1 VM.t -> VM.key option
   end

  type env = typ t

  val deftyp : typ

  val vtyp : VarOrder.t -> env -> typ

  val vsize : VarOrder.t -> env -> int

  val eequal : typ t -> typ t -> bool
 end

module SSATE :
 sig
  module SE :
   EqOrder.EqOrder

  module E :
   OrderedType.OrderedType with type t = SSAVM.SE.t

  type key = SE.t

  type 'x t = 'x SSAVM.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  module Lemmas :
   sig
    module F :
     sig
      val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool

      val coq_In_dec : 'a1 SSAVM.t -> SSAVM.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = SSAVM.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

        val lt_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

        val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = SSAVM.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

          val lt_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

          val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool

          val coq_In_dec : 'a1 SSAVM.t -> SSAVM.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (SSAVM.key * 'a1) list -> 'a1 SSAVM.t

        val to_list : 'a1 SSAVM.t -> (SSAVM.key * 'a1) list

        val fold_rec :
          (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 SSAVM.t -> ('a1
          SSAVM.t -> __ -> 'a3) -> (SSAVM.key -> 'a1 -> 'a2 -> 'a1 SSAVM.t ->
          'a1 SSAVM.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 SSAVM.t -> ('a1
          SSAVM.t -> 'a1 SSAVM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
          (SSAVM.key -> 'a1 -> 'a2 -> 'a1 SSAVM.t -> __ -> __ -> 'a3 -> 'a3)
          -> 'a3

        val fold_rec_nodep :
          (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 SSAVM.t -> 'a3 ->
          (SSAVM.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 SSAVM.t -> 'a1
          SSAVM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (SSAVM.key -> 'a1 ->
          'a2 -> 'a1 SSAVM.t -> __ -> 'a3 -> 'a3) -> 'a1 SSAVM.t -> 'a3

        val fold_rel :
          (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> (SSAVM.key -> 'a1 -> 'a3 ->
          'a3) -> 'a2 -> 'a3 -> 'a1 SSAVM.t -> 'a4 -> (SSAVM.key -> 'a1 ->
          'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 SSAVM.t -> __ -> 'a2) -> ('a1 SSAVM.t -> 'a1 SSAVM.t -> 'a2 ->
          SSAVM.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 SSAVM.t -> 'a2

        val map_induction_bis :
          ('a1 SSAVM.t -> 'a1 SSAVM.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (SSAVM.key -> 'a1 -> 'a1 SSAVM.t -> __ -> 'a2 -> 'a2) -> 'a1
          SSAVM.t -> 'a2

        val cardinal_inv_2 : 'a1 SSAVM.t -> int -> (SSAVM.key * 'a1)

        val cardinal_inv_2b : 'a1 SSAVM.t -> (SSAVM.key * 'a1)

        val filter : (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t

        val for_all : (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> bool

        val exists_ : (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> bool

        val partition :
          (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t * 'a1
          SSAVM.t

        val update : 'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t

        val restrict : 'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t

        val diff : 'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t

        val coq_Partition_In :
          'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t -> SSAVM.key -> bool

        val update_dec :
          'a1 SSAVM.t -> 'a1 SSAVM.t -> SSAVM.key -> 'a1 -> bool

        val filter_dom : (SSAVM.key -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t

        val filter_range : ('a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t

        val for_all_dom : (SSAVM.key -> bool) -> 'a1 SSAVM.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 SSAVM.t -> bool

        val exists_dom : (SSAVM.key -> bool) -> 'a1 SSAVM.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 SSAVM.t -> bool

        val partition_dom :
          (SSAVM.key -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t * 'a1 SSAVM.t

        val partition_range :
          ('a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t * 'a1 SSAVM.t
       end

      val gtb : (SSAVM.key * 'a1) -> (SSAVM.key * 'a1) -> bool

      val leb : (SSAVM.key * 'a1) -> (SSAVM.key * 'a1) -> bool

      val elements_lt :
        (SSAVM.key * 'a1) -> 'a1 SSAVM.t -> (SSAVM.key * 'a1) list

      val elements_ge :
        (SSAVM.key * 'a1) -> 'a1 SSAVM.t -> (SSAVM.key * 'a1) list

      val max_elt_aux : (SSAVM.key * 'a1) list -> (SSAVM.key * 'a1) option

      val max_elt : 'a1 SSAVM.t -> (SSAVM.key * 'a1) option

      val min_elt : 'a1 SSAVM.t -> (SSAVM.key * 'a1) option

      val map_induction_max :
        ('a1 SSAVM.t -> __ -> 'a2) -> ('a1 SSAVM.t -> 'a1 SSAVM.t -> 'a2 ->
        SSAVM.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1 SSAVM.t -> 'a2

      val map_induction_min :
        ('a1 SSAVM.t -> __ -> 'a2) -> ('a1 SSAVM.t -> 'a1 SSAVM.t -> 'a2 ->
        SSAVM.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1 SSAVM.t -> 'a2
     end

    val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool

    val coq_In_dec : 'a1 SSAVM.t -> SSAVM.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = SSAVM.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

      val lt_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

      val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = SSAVM.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

        val lt_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

        val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool

        val coq_In_dec : 'a1 SSAVM.t -> SSAVM.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (SSAVM.key * 'a1) list -> 'a1 SSAVM.t

      val to_list : 'a1 SSAVM.t -> (SSAVM.key * 'a1) list

      val fold_rec :
        (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 SSAVM.t -> ('a1
        SSAVM.t -> __ -> 'a3) -> (SSAVM.key -> 'a1 -> 'a2 -> 'a1 SSAVM.t ->
        'a1 SSAVM.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 SSAVM.t -> ('a1
        SSAVM.t -> 'a1 SSAVM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
        (SSAVM.key -> 'a1 -> 'a2 -> 'a1 SSAVM.t -> __ -> __ -> 'a3 -> 'a3) ->
        'a3

      val fold_rec_nodep :
        (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 SSAVM.t -> 'a3 ->
        (SSAVM.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 SSAVM.t -> 'a1
        SSAVM.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (SSAVM.key -> 'a1 ->
        'a2 -> 'a1 SSAVM.t -> __ -> 'a3 -> 'a3) -> 'a1 SSAVM.t -> 'a3

      val fold_rel :
        (SSAVM.key -> 'a1 -> 'a2 -> 'a2) -> (SSAVM.key -> 'a1 -> 'a3 -> 'a3)
        -> 'a2 -> 'a3 -> 'a1 SSAVM.t -> 'a4 -> (SSAVM.key -> 'a1 -> 'a2 ->
        'a3 -> __ -> 'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 SSAVM.t -> __ -> 'a2) -> ('a1 SSAVM.t -> 'a1 SSAVM.t -> 'a2 ->
        SSAVM.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 SSAVM.t -> 'a2

      val map_induction_bis :
        ('a1 SSAVM.t -> 'a1 SSAVM.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVM.key
        -> 'a1 -> 'a1 SSAVM.t -> __ -> 'a2 -> 'a2) -> 'a1 SSAVM.t -> 'a2

      val cardinal_inv_2 : 'a1 SSAVM.t -> int -> (SSAVM.key * 'a1)

      val cardinal_inv_2b : 'a1 SSAVM.t -> (SSAVM.key * 'a1)

      val filter : (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t

      val for_all : (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> bool

      val exists_ : (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> bool

      val partition :
        (SSAVM.key -> 'a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t * 'a1 SSAVM.t

      val update : 'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t

      val restrict : 'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t

      val diff : 'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t

      val coq_Partition_In :
        'a1 SSAVM.t -> 'a1 SSAVM.t -> 'a1 SSAVM.t -> SSAVM.key -> bool

      val update_dec : 'a1 SSAVM.t -> 'a1 SSAVM.t -> SSAVM.key -> 'a1 -> bool

      val filter_dom : (SSAVM.key -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t

      val filter_range : ('a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t

      val for_all_dom : (SSAVM.key -> bool) -> 'a1 SSAVM.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 SSAVM.t -> bool

      val exists_dom : (SSAVM.key -> bool) -> 'a1 SSAVM.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 SSAVM.t -> bool

      val partition_dom :
        (SSAVM.key -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t * 'a1 SSAVM.t

      val partition_range :
        ('a1 -> bool) -> 'a1 SSAVM.t -> 'a1 SSAVM.t * 'a1 SSAVM.t
     end

    val gtb : (SSAVM.key * 'a1) -> (SSAVM.key * 'a1) -> bool

    val leb : (SSAVM.key * 'a1) -> (SSAVM.key * 'a1) -> bool

    val elements_lt :
      (SSAVM.key * 'a1) -> 'a1 SSAVM.t -> (SSAVM.key * 'a1) list

    val elements_ge :
      (SSAVM.key * 'a1) -> 'a1 SSAVM.t -> (SSAVM.key * 'a1) list

    val max_elt_aux : (SSAVM.key * 'a1) list -> (SSAVM.key * 'a1) option

    val max_elt : 'a1 SSAVM.t -> (SSAVM.key * 'a1) option

    val min_elt : 'a1 SSAVM.t -> (SSAVM.key * 'a1) option

    val map_induction_max :
      ('a1 SSAVM.t -> __ -> 'a2) -> ('a1 SSAVM.t -> 'a1 SSAVM.t -> 'a2 ->
      SSAVM.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1 SSAVM.t -> 'a2

    val map_induction_min :
      ('a1 SSAVM.t -> __ -> 'a2) -> ('a1 SSAVM.t -> 'a1 SSAVM.t -> 'a2 ->
      SSAVM.SE.t -> 'a1 -> __ -> __ -> 'a2) -> 'a1 SSAVM.t -> 'a2

    val memP : SSAVM.key -> 'a1 SSAVM.t -> reflect

    val split : ('a1 * 'a2) SSAVM.t -> 'a1 SSAVM.t * 'a2 SSAVM.t

    module EFacts :
     sig
      module TO :
       sig
        type t = SSAVM.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

      val lt_dec : SSAVM.SE.t -> SSAVM.SE.t -> bool

      val eqb : SSAVM.SE.t -> SSAVM.SE.t -> bool
     end

    val max_opt : SSAVM.key -> SSAVM.key option -> SSAVM.key

    val max_key_elements : (SSAVM.key * 'a1) list -> SSAVM.key option

    val max_key : 'a1 SSAVM.t -> SSAVM.key option

    val min_opt : SSAVM.key -> SSAVM.key option -> SSAVM.key

    val min_key_elements : (SSAVM.key * 'a1) list -> SSAVM.key option

    val min_key : 'a1 SSAVM.t -> SSAVM.key option
   end

  type env = typ t

  val deftyp : typ

  val vtyp : SSAVarOrder.t -> env -> typ

  val vsize : SSAVarOrder.t -> env -> int

  val eequal : typ t -> typ t -> bool
 end

module TypEnvAgree :
 functor (V:EqOrder.EqOrder) ->
 functor (TE__4:TypEnv with module SE = V) ->
 functor (VS:EqFSet with module SE = V) ->
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

        val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool
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

            val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool
           end

          val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

          val of_list : (TE__4.key * 'a1) list -> 'a1 TE__4.t

          val to_list : 'a1 TE__4.t -> (TE__4.key * 'a1) list

          val fold_rec :
            (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
            TE__4.t -> __ -> 'a3) -> (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t
            -> 'a1 TE__4.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_bis :
            (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
            TE__4.t -> 'a1 TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
            (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t -> __ -> __ -> 'a3 ->
            'a3) -> 'a3

          val fold_rec_nodep :
            (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> 'a3 ->
            (TE__4.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_weak :
            (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE__4.t -> 'a1
            TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE__4.key -> 'a1
            -> 'a2 -> 'a1 TE__4.t -> __ -> 'a3 -> 'a3) -> 'a1 TE__4.t -> 'a3

          val fold_rel :
            (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> (TE__4.key -> 'a1 -> 'a3 ->
            'a3) -> 'a2 -> 'a3 -> 'a1 TE__4.t -> 'a4 -> (TE__4.key -> 'a1 ->
            'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

          val map_induction :
            ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2
            -> TE__4.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

          val map_induction_bis :
            ('a1 TE__4.t -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
            (TE__4.key -> 'a1 -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a1
            TE__4.t -> 'a2

          val cardinal_inv_2 : 'a1 TE__4.t -> int -> (TE__4.key * 'a1)

          val cardinal_inv_2b : 'a1 TE__4.t -> (TE__4.key * 'a1)

          val filter :
            (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

          val for_all : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

          val exists_ : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

          val partition :
            (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1
            TE__4.t

          val update : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

          val restrict : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

          val diff : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

          val coq_Partition_In :
            'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> bool

          val update_dec :
            'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> 'a1 -> bool

          val filter_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

          val filter_range : ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

          val for_all_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

          val for_all_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

          val exists_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

          val exists_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

          val partition_dom :
            (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t

          val partition_range :
            ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t
         end

        val gtb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

        val leb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

        val elements_lt :
          (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

        val elements_ge :
          (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

        val max_elt_aux : (TE__4.key * 'a1) list -> (TE__4.key * 'a1) option

        val max_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

        val min_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

        val map_induction_max :
          ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
          Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

        val map_induction_min :
          ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
          Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2
       end

      val eqb : Equality.sort -> Equality.sort -> bool

      val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool

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

          val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TE__4.key * 'a1) list -> 'a1 TE__4.t

        val to_list : 'a1 TE__4.t -> (TE__4.key * 'a1) list

        val fold_rec :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
          TE__4.t -> __ -> 'a3) -> (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t ->
          'a1 TE__4.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
          TE__4.t -> 'a1 TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
          (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t -> __ -> __ -> 'a3 -> 'a3)
          -> 'a3

        val fold_rec_nodep :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> 'a3 ->
          (TE__4.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE__4.t -> 'a1
          TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE__4.key -> 'a1 ->
          'a2 -> 'a1 TE__4.t -> __ -> 'a3 -> 'a3) -> 'a1 TE__4.t -> 'a3

        val fold_rel :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> (TE__4.key -> 'a1 -> 'a3 ->
          'a3) -> 'a2 -> 'a3 -> 'a1 TE__4.t -> 'a4 -> (TE__4.key -> 'a1 ->
          'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
          TE__4.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

        val map_induction_bis :
          ('a1 TE__4.t -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (TE__4.key -> 'a1 -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a1
          TE__4.t -> 'a2

        val cardinal_inv_2 : 'a1 TE__4.t -> int -> (TE__4.key * 'a1)

        val cardinal_inv_2b : 'a1 TE__4.t -> (TE__4.key * 'a1)

        val filter : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

        val for_all : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

        val exists_ : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

        val partition :
          (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1
          TE__4.t

        val update : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

        val restrict : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

        val diff : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

        val coq_Partition_In :
          'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> bool

        val update_dec :
          'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> 'a1 -> bool

        val filter_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

        val filter_range : ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

        val for_all_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

        val exists_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

        val partition_dom :
          (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t

        val partition_range :
          ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t
       end

      val gtb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

      val leb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

      val elements_lt :
        (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

      val elements_ge :
        (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

      val max_elt_aux : (TE__4.key * 'a1) list -> (TE__4.key * 'a1) option

      val max_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

      val min_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

      val map_induction_max :
        ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
        Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

      val map_induction_min :
        ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
        Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

      val memP : TE__4.key -> 'a1 TE__4.t -> reflect

      val split : ('a1 * 'a2) TE__4.t -> 'a1 TE__4.t * 'a2 TE__4.t

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

      val max_opt : TE__4.key -> TE__4.key option -> TE__4.key

      val max_key_elements : (TE__4.key * 'a1) list -> TE__4.key option

      val max_key : 'a1 TE__4.t -> TE__4.key option

      val min_opt : TE__4.key -> TE__4.key option -> TE__4.key

      val min_key_elements : (TE__4.key * 'a1) list -> TE__4.key option

      val min_key : 'a1 TE__4.t -> TE__4.key option
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

      val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool
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

          val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TE__4.key * 'a1) list -> 'a1 TE__4.t

        val to_list : 'a1 TE__4.t -> (TE__4.key * 'a1) list

        val fold_rec :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
          TE__4.t -> __ -> 'a3) -> (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t ->
          'a1 TE__4.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
          TE__4.t -> 'a1 TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
          (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t -> __ -> __ -> 'a3 -> 'a3)
          -> 'a3

        val fold_rec_nodep :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> 'a3 ->
          (TE__4.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE__4.t -> 'a1
          TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE__4.key -> 'a1 ->
          'a2 -> 'a1 TE__4.t -> __ -> 'a3 -> 'a3) -> 'a1 TE__4.t -> 'a3

        val fold_rel :
          (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> (TE__4.key -> 'a1 -> 'a3 ->
          'a3) -> 'a2 -> 'a3 -> 'a1 TE__4.t -> 'a4 -> (TE__4.key -> 'a1 ->
          'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
          TE__4.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

        val map_induction_bis :
          ('a1 TE__4.t -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (TE__4.key -> 'a1 -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a1
          TE__4.t -> 'a2

        val cardinal_inv_2 : 'a1 TE__4.t -> int -> (TE__4.key * 'a1)

        val cardinal_inv_2b : 'a1 TE__4.t -> (TE__4.key * 'a1)

        val filter : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

        val for_all : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

        val exists_ : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

        val partition :
          (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1
          TE__4.t

        val update : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

        val restrict : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

        val diff : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

        val coq_Partition_In :
          'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> bool

        val update_dec :
          'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> 'a1 -> bool

        val filter_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

        val filter_range : ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

        val for_all_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

        val exists_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

        val partition_dom :
          (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t

        val partition_range :
          ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t
       end

      val gtb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

      val leb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

      val elements_lt :
        (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

      val elements_ge :
        (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

      val max_elt_aux : (TE__4.key * 'a1) list -> (TE__4.key * 'a1) option

      val max_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

      val min_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

      val map_induction_max :
        ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
        Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

      val map_induction_min :
        ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
        Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2
     end

    val eqb : Equality.sort -> Equality.sort -> bool

    val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool

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

        val coq_In_dec : 'a1 TE__4.t -> TE__4.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TE__4.key * 'a1) list -> 'a1 TE__4.t

      val to_list : 'a1 TE__4.t -> (TE__4.key * 'a1) list

      val fold_rec :
        (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
        TE__4.t -> __ -> 'a3) -> (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t ->
        'a1 TE__4.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> ('a1
        TE__4.t -> 'a1 TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
        (TE__4.key -> 'a1 -> 'a2 -> 'a1 TE__4.t -> __ -> __ -> 'a3 -> 'a3) ->
        'a3

      val fold_rec_nodep :
        (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE__4.t -> 'a3 ->
        (TE__4.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE__4.t -> 'a1
        TE__4.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE__4.key -> 'a1 ->
        'a2 -> 'a1 TE__4.t -> __ -> 'a3 -> 'a3) -> 'a1 TE__4.t -> 'a3

      val fold_rel :
        (TE__4.key -> 'a1 -> 'a2 -> 'a2) -> (TE__4.key -> 'a1 -> 'a3 -> 'a3)
        -> 'a2 -> 'a3 -> 'a1 TE__4.t -> 'a4 -> (TE__4.key -> 'a1 -> 'a2 ->
        'a3 -> __ -> 'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
        TE__4.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

      val map_induction_bis :
        ('a1 TE__4.t -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE__4.key
        -> 'a1 -> 'a1 TE__4.t -> __ -> 'a2 -> 'a2) -> 'a1 TE__4.t -> 'a2

      val cardinal_inv_2 : 'a1 TE__4.t -> int -> (TE__4.key * 'a1)

      val cardinal_inv_2b : 'a1 TE__4.t -> (TE__4.key * 'a1)

      val filter : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

      val for_all : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

      val exists_ : (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> bool

      val partition :
        (TE__4.key -> 'a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t

      val update : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

      val restrict : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

      val diff : 'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t

      val coq_Partition_In :
        'a1 TE__4.t -> 'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> bool

      val update_dec : 'a1 TE__4.t -> 'a1 TE__4.t -> TE__4.key -> 'a1 -> bool

      val filter_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

      val filter_range : ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t

      val for_all_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

      val exists_dom : (TE__4.key -> bool) -> 'a1 TE__4.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TE__4.t -> bool

      val partition_dom :
        (TE__4.key -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t

      val partition_range :
        ('a1 -> bool) -> 'a1 TE__4.t -> 'a1 TE__4.t * 'a1 TE__4.t
     end

    val gtb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

    val leb : (TE__4.key * 'a1) -> (TE__4.key * 'a1) -> bool

    val elements_lt :
      (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

    val elements_ge :
      (TE__4.key * 'a1) -> 'a1 TE__4.t -> (TE__4.key * 'a1) list

    val max_elt_aux : (TE__4.key * 'a1) list -> (TE__4.key * 'a1) option

    val max_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

    val min_elt : 'a1 TE__4.t -> (TE__4.key * 'a1) option

    val map_induction_max :
      ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
      Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

    val map_induction_min :
      ('a1 TE__4.t -> __ -> 'a2) -> ('a1 TE__4.t -> 'a1 TE__4.t -> 'a2 ->
      Equality.sort -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE__4.t -> 'a2

    val memP : TE__4.key -> 'a1 TE__4.t -> reflect

    val split : ('a1 * 'a2) TE__4.t -> 'a1 TE__4.t * 'a2 TE__4.t

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

    val max_opt : TE__4.key -> TE__4.key option -> TE__4.key

    val max_key_elements : (TE__4.key * 'a1) list -> TE__4.key option

    val max_key : 'a1 TE__4.t -> TE__4.key option

    val min_opt : TE__4.key -> TE__4.key option -> TE__4.key

    val min_key_elements : (TE__4.key * 'a1) list -> TE__4.key option

    val min_key : 'a1 TE__4.t -> TE__4.key option
   end
 end
