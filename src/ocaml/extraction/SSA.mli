open BinNat
open BinNums
open BinaryString
open Bool
open Datatypes
open NBitsDef
open State
open String0
open Typ
open Var
open Eqtype
open Seq

type __ = Obj.t

module SSA :
 sig
  module VSLemmas :
   sig
    module F :
     sig
      val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = SSAVS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val lt_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
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
          val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
         end

        val coq_In_dec : SSAVS.elt -> SSAVS.t -> bool

        val of_list : SSAVS.elt list -> SSAVS.t

        val to_list : SSAVS.t -> SSAVS.elt list

        val fold_rec :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> __ ->
          'a2) -> (SSAVS.elt -> 'a1 -> SSAVS.t -> SSAVS.t -> __ -> __ -> __
          -> 'a2 -> 'a2) -> 'a2

        val fold_rec_bis :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> SSAVS.t
          -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t
          -> __ -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> 'a2 -> (SSAVS.elt ->
          'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.t -> SSAVS.t -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __ ->
          'a2 -> 'a2) -> SSAVS.t -> 'a2

        val fold_rel :
          (SSAVS.elt -> 'a1 -> 'a1) -> (SSAVS.elt -> 'a2 -> 'a2) -> 'a1 ->
          'a2 -> SSAVS.t -> 'a3 -> (SSAVS.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
          'a3) -> 'a3

        val set_induction :
          (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.elt
          -> __ -> __ -> 'a1) -> SSAVS.t -> 'a1

        val set_induction_bis :
          (SSAVS.t -> SSAVS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.elt ->
          SSAVS.t -> __ -> 'a1 -> 'a1) -> SSAVS.t -> 'a1

        val cardinal_inv_2 : SSAVS.t -> int -> SSAVS.elt

        val cardinal_inv_2b : SSAVS.t -> SSAVS.elt
       end

      val gtb : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val leb : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val elements_lt : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

      val elements_ge : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

      val set_induction_max :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1

      val set_induction_min :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1
     end

    val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = SSAVS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val lt_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
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
        val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
       end

      val coq_In_dec : SSAVS.elt -> SSAVS.t -> bool

      val of_list : SSAVS.elt list -> SSAVS.t

      val to_list : SSAVS.t -> SSAVS.elt list

      val fold_rec :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> __ -> 'a2)
        -> (SSAVS.elt -> 'a1 -> SSAVS.t -> SSAVS.t -> __ -> __ -> __ -> 'a2
        -> 'a2) -> 'a2

      val fold_rec_bis :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> SSAVS.t ->
        'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __
        -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_nodep :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> 'a2 -> (SSAVS.elt ->
        'a1 -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.t -> SSAVS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __ -> 'a2 ->
        'a2) -> SSAVS.t -> 'a2

      val fold_rel :
        (SSAVS.elt -> 'a1 -> 'a1) -> (SSAVS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
        -> SSAVS.t -> 'a3 -> (SSAVS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
        'a3

      val set_induction :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.elt ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1

      val set_induction_bis :
        (SSAVS.t -> SSAVS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.elt ->
        SSAVS.t -> __ -> 'a1 -> 'a1) -> SSAVS.t -> 'a1

      val cardinal_inv_2 : SSAVS.t -> int -> SSAVS.elt

      val cardinal_inv_2b : SSAVS.t -> SSAVS.elt
     end

    val gtb : SSAVS.SE.t -> SSAVS.SE.t -> bool

    val leb : SSAVS.SE.t -> SSAVS.SE.t -> bool

    val elements_lt : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

    val elements_ge : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

    val set_induction_max :
      (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
      __ -> __ -> 'a1) -> SSAVS.t -> 'a1

    val set_induction_min :
      (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
      __ -> __ -> 'a1) -> SSAVS.t -> 'a1

    val memP : SSAVS.elt -> SSAVS.t -> reflect

    val disjoint : SSAVS.t -> SSAVS.t -> bool
   end

  module TELemmas :
   sig
    module F :
     sig
      val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TypEnv.SSATE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TypEnv.SSATE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TypEnv.SSATE.key * 'a1) list -> 'a1 TypEnv.SSATE.t

        val to_list : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) list

        val fold_rec :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> __ -> 'a3) ->
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2
          -> __ -> 'a3 -> 'a3) -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 ->
          'a1 TypEnv.SSATE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> __ ->
          'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1
          TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 -> 'a3) ->
          'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> __
          -> 'a3 -> 'a3) -> 'a1 TypEnv.SSATE.t -> 'a3

        val fold_rel :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.SSATE.key -> 'a1
          -> 'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.SSATE.t -> 'a4 ->
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.key -> 'a1 -> __ -> __ ->
          'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

        val map_induction_bis :
          ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 -> 'a2) ->
          'a2 -> (TypEnv.SSATE.key -> 'a1 -> 'a1 TypEnv.SSATE.t -> __ -> 'a2
          -> 'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

        val cardinal_inv_2 :
          'a1 TypEnv.SSATE.t -> int -> (TypEnv.SSATE.key * 'a1)

        val cardinal_inv_2b : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1)

        val filter :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t

        val for_all :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_ :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val partition :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

        val update :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val restrict :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val diff :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val coq_Partition_In :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t ->
          TypEnv.SSATE.key -> bool

        val update_dec :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> 'a1
          -> bool

        val filter_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t

        val filter_range :
          ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val for_all_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val partition_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

        val partition_range :
          ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a1
          TypEnv.SSATE.t
       end

      val gtb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

      val leb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

      val elements_lt :
        (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
        (TypEnv.SSATE.key * 'a1) list

      val elements_ge :
        (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
        (TypEnv.SSATE.key * 'a1) list

      val max_elt_aux :
        (TypEnv.SSATE.key * 'a1) list -> (TypEnv.SSATE.key * 'a1) option

      val max_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

      val min_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

      val map_induction_max :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2

      val map_induction_min :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2
     end

    val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

    val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TypEnv.SSATE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = TypEnv.SSATE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TypEnv.SSATE.key * 'a1) list -> 'a1 TypEnv.SSATE.t

      val to_list : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) list

      val fold_rec :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> ('a1 TypEnv.SSATE.t -> __ -> 'a3) -> (TypEnv.SSATE.key -> 'a1 ->
        'a2 -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> __ -> __ ->
        'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 ->
        'a3) -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TypEnv.SSATE.t
        -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> __ -> 'a3 ->
        'a3) -> 'a1 TypEnv.SSATE.t -> 'a3

      val fold_rel :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.SSATE.key -> 'a1
        -> 'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.SSATE.t -> 'a4 ->
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.key -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2

      val map_induction_bis :
        ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 -> 'a2) -> 'a2
        -> (TypEnv.SSATE.key -> 'a1 -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 ->
        'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

      val cardinal_inv_2 :
        'a1 TypEnv.SSATE.t -> int -> (TypEnv.SSATE.key * 'a1)

      val cardinal_inv_2b : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1)

      val filter :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t

      val for_all :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val exists_ :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val partition :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

      val update :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val restrict :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val diff :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val coq_Partition_In :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t ->
        TypEnv.SSATE.key -> bool

      val update_dec :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> 'a1
        -> bool

      val filter_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val filter_range :
        ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val for_all_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val exists_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val partition_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

      val partition_range :
        ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a1
        TypEnv.SSATE.t
     end

    val gtb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

    val leb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

    val elements_lt :
      (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
      (TypEnv.SSATE.key * 'a1) list

    val elements_ge :
      (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
      (TypEnv.SSATE.key * 'a1) list

    val max_elt_aux :
      (TypEnv.SSATE.key * 'a1) list -> (TypEnv.SSATE.key * 'a1) option

    val max_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

    val min_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

    val map_induction_max :
      ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
      TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
      -> 'a1 TypEnv.SSATE.t -> 'a2

    val map_induction_min :
      ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
      TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
      -> 'a1 TypEnv.SSATE.t -> 'a2

    val memP : TypEnv.SSATE.key -> 'a1 TypEnv.SSATE.t -> reflect

    val split :
      ('a1 * 'a2) TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a2 TypEnv.SSATE.t

    module EFacts :
     sig
      module TO :
       sig
        type t = TypEnv.SSATE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
     end

    val max_opt :
      TypEnv.SSATE.key -> TypEnv.SSATE.key option -> TypEnv.SSATE.key

    val max_key_elements :
      (TypEnv.SSATE.key * 'a1) list -> TypEnv.SSATE.key option

    val max_key : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key option

    val min_opt :
      TypEnv.SSATE.key -> TypEnv.SSATE.key option -> TypEnv.SSATE.key

    val min_key_elements :
      (TypEnv.SSATE.key * 'a1) list -> TypEnv.SSATE.key option

    val min_key : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key option
   end

  type eexp = DSL.eexp

  val evar : SSAVarOrder.t -> eexp

  val econst : coq_Z -> eexp

  val eunary : DSL.eunop -> eexp -> eexp

  val ebinary : DSL.ebinop -> eexp -> eexp -> eexp

  val eneg : eexp -> eexp

  val eadd : eexp -> eexp -> eexp

  val esub : eexp -> eexp -> eexp

  val emul : eexp -> eexp -> eexp

  val esq : eexp -> eexp

  val epow : eexp -> coq_N -> DSL.eexp

  val eadds : eexp list -> eexp

  val emuls : eexp list -> eexp

  val z2expn : coq_Z -> coq_Z

  val e2expn : coq_Z -> DSL.eexp

  val emul2p : DSL.eexp -> coq_Z -> DSL.eexp

  val vars_eexp : eexp -> SSAVS.t

  val vars_eexps : eexp list -> SSAVS.t

  val eexp_eqP : eexp -> eexp -> reflect

  val eexp_eqMixin : eexp Equality.mixin_of

  val eexp_eqType : Equality.coq_type

  val limbsi : int -> coq_Z -> eexp list -> eexp

  val limbs : coq_Z -> eexp list -> eexp

  type rexp = DSL.rexp

  val size_of_rexp : rexp -> TypEnv.SSATE.env -> int

  val rvar : Equality.sort -> rexp

  val rconst : int -> bits -> rexp

  val rbits : bits -> rexp

  val runary : int -> DSL.runop -> rexp -> rexp

  val rbinary : int -> DSL.rbinop -> rexp -> rexp -> rexp

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

  val vars_rexp : rexp -> SSAVS.t

  val rexp_eqP : rexp -> rexp -> reflect

  val rexp_eqMixin : rexp Equality.mixin_of

  val rexp_eqType : Equality.coq_type

  type ebexp = DSL.ebexp

  val etrue : ebexp

  val eeq : eexp -> eexp -> ebexp

  val eeqmod : eexp -> eexp -> eexp list -> ebexp

  val eand : ebexp -> ebexp -> ebexp

  val eands : ebexp list -> ebexp

  val split_eand : ebexp -> ebexp list

  val vars_ebexp : ebexp -> SSAVS.t

  val ebexp_eqP : ebexp -> ebexp -> reflect

  val ebexp_eqMixin : ebexp Equality.mixin_of

  val ebexp_eqType : Equality.coq_type

  type rbexp = DSL.rbexp

  val rtrue : rbexp

  val rfalse : rbexp

  val req : int -> rexp -> rexp -> rbexp

  val rcmp : int -> DSL.rcmpop -> rexp -> rexp -> rbexp

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

  val vars_rbexp : rbexp -> SSAVS.t

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

  val vars_bexp : bexp -> SSAVS.t

  type atom =
  | Avar of SSAVarOrder.t
  | Aconst of typ * bits

  val atom_rect :
    (SSAVarOrder.t -> 'a1) -> (typ -> bits -> 'a1) -> atom -> 'a1

  val atom_rec : (SSAVarOrder.t -> 'a1) -> (typ -> bits -> 'a1) -> atom -> 'a1

  val atyp : atom -> TypEnv.SSATE.env -> typ

  val asize : atom -> TypEnv.SSATE.env -> int

  type instr =
  | Imov of SSAVarOrder.t * atom
  | Ishl of SSAVarOrder.t * atom * int
  | Icshl of SSAVarOrder.t * SSAVarOrder.t * atom * atom * int
  | Inondet of SSAVarOrder.t * typ
  | Icmov of SSAVarOrder.t * atom * atom * atom
  | Inop
  | Inot of SSAVarOrder.t * typ * atom
  | Iadd of SSAVarOrder.t * atom * atom
  | Iadds of SSAVarOrder.t * SSAVarOrder.t * atom * atom
  | Iadc of SSAVarOrder.t * atom * atom * atom
  | Iadcs of SSAVarOrder.t * SSAVarOrder.t * atom * atom * atom
  | Isub of SSAVarOrder.t * atom * atom
  | Isubc of SSAVarOrder.t * SSAVarOrder.t * atom * atom
  | Isubb of SSAVarOrder.t * SSAVarOrder.t * atom * atom
  | Isbc of SSAVarOrder.t * atom * atom * atom
  | Isbcs of SSAVarOrder.t * SSAVarOrder.t * atom * atom * atom
  | Isbb of SSAVarOrder.t * atom * atom * atom
  | Isbbs of SSAVarOrder.t * SSAVarOrder.t * atom * atom * atom
  | Imul of SSAVarOrder.t * atom * atom
  | Imull of SSAVarOrder.t * SSAVarOrder.t * atom * atom
  | Imulj of SSAVarOrder.t * atom * atom
  | Isplit of SSAVarOrder.t * SSAVarOrder.t * atom * int
  | Iand of SSAVarOrder.t * typ * atom * atom
  | Ior of SSAVarOrder.t * typ * atom * atom
  | Ixor of SSAVarOrder.t * typ * atom * atom
  | Icast of SSAVarOrder.t * typ * atom
  | Ivpc of SSAVarOrder.t * typ * atom
  | Ijoin of SSAVarOrder.t * atom * atom
  | Iassume of bexp

  val instr_rect :
    (SSAVarOrder.t -> atom -> 'a1) -> (SSAVarOrder.t -> atom -> int -> 'a1)
    -> (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom -> int -> 'a1) ->
    (SSAVarOrder.t -> typ -> 'a1) -> (SSAVarOrder.t -> atom -> atom -> atom
    -> 'a1) -> 'a1 -> (SSAVarOrder.t -> typ -> atom -> 'a1) -> (SSAVarOrder.t
    -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t -> atom ->
    atom -> 'a1) -> (SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t
    -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t -> atom ->
    atom -> 'a1) -> (SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> atom -> atom -> atom -> 'a1) -> (SSAVarOrder.t ->
    SSAVarOrder.t -> atom -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> atom
    -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom ->
    'a1) -> (SSAVarOrder.t -> atom -> atom -> 'a1) -> (SSAVarOrder.t ->
    SSAVarOrder.t -> atom -> int -> 'a1) -> (SSAVarOrder.t -> typ -> atom ->
    atom -> 'a1) -> (SSAVarOrder.t -> typ -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> typ -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> typ ->
    atom -> 'a1) -> (SSAVarOrder.t -> typ -> atom -> 'a1) -> (SSAVarOrder.t
    -> atom -> atom -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  val instr_rec :
    (SSAVarOrder.t -> atom -> 'a1) -> (SSAVarOrder.t -> atom -> int -> 'a1)
    -> (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom -> int -> 'a1) ->
    (SSAVarOrder.t -> typ -> 'a1) -> (SSAVarOrder.t -> atom -> atom -> atom
    -> 'a1) -> 'a1 -> (SSAVarOrder.t -> typ -> atom -> 'a1) -> (SSAVarOrder.t
    -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t -> atom ->
    atom -> 'a1) -> (SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t
    -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t -> atom ->
    atom -> 'a1) -> (SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> atom -> atom -> atom -> 'a1) -> (SSAVarOrder.t ->
    SSAVarOrder.t -> atom -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> atom
    -> atom -> 'a1) -> (SSAVarOrder.t -> SSAVarOrder.t -> atom -> atom ->
    'a1) -> (SSAVarOrder.t -> atom -> atom -> 'a1) -> (SSAVarOrder.t ->
    SSAVarOrder.t -> atom -> int -> 'a1) -> (SSAVarOrder.t -> typ -> atom ->
    atom -> 'a1) -> (SSAVarOrder.t -> typ -> atom -> atom -> 'a1) ->
    (SSAVarOrder.t -> typ -> atom -> atom -> 'a1) -> (SSAVarOrder.t -> typ ->
    atom -> 'a1) -> (SSAVarOrder.t -> typ -> atom -> 'a1) -> (SSAVarOrder.t
    -> atom -> atom -> 'a1) -> (bexp -> 'a1) -> instr -> 'a1

  type program = instr list

  val string_of_eunop : DSL.eunop -> char list

  val string_of_ebinop : DSL.ebinop -> char list

  val string_of_runop : DSL.runop -> char list

  val string_of_rbinop : DSL.rbinop -> char list

  val string_of_rcmpop : DSL.rcmpop -> char list

  val string_of_eexp : (Equality.sort -> char list) -> DSL.eexp -> char list

  val string_of_eexps :
    (Equality.sort -> char list) -> char list -> DSL.eexp list -> char list

  val string_of_ebexp : (Equality.sort -> char list) -> DSL.ebexp -> char list

  val string_of_rexp : (Equality.sort -> char list) -> DSL.rexp -> char list

  val string_of_rbexp : (Equality.sort -> char list) -> DSL.rbexp -> char list

  val vars_atom : atom -> SSAVS.t

  val vars_instr : instr -> SSAVS.t

  val lvs_instr : instr -> SSAVS.t

  val rvs_instr : instr -> SSAVS.t

  val vars_program : program -> SSAVS.t

  val lvs_program : program -> SSAVS.t

  val rvs_program : program -> SSAVS.t

  val eqn_instr : instr -> instr

  val rng_instr : instr -> instr

  val eqn_program : program -> program

  val rng_program : program -> program

  type spec = { sinputs : TypEnv.SSATE.env; spre : bexp; sprog : program;
                spost : bexp }

  val sinputs : spec -> TypEnv.SSATE.env

  val spre : spec -> bexp

  val sprog : spec -> program

  val spost : spec -> bexp

  type espec = { esinputs : TypEnv.SSATE.env; espre : bexp; esprog : 
                 program; espost : ebexp }

  val esinputs : espec -> TypEnv.SSATE.env

  val espre : espec -> bexp

  val esprog : espec -> program

  val espost : espec -> ebexp

  type rspec = { rsinputs : TypEnv.SSATE.env; rspre : rbexp;
                 rsprog : program; rspost : rbexp }

  val rsinputs : rspec -> TypEnv.SSATE.env

  val rspre : rspec -> rbexp

  val rsprog : rspec -> program

  val rspost : rspec -> rbexp

  val espec_of_spec : spec -> espec

  val rspec_of_spec : spec -> rspec

  val bv2z : typ -> bits -> coq_Z

  val acc2z : TypEnv.SSATE.env -> SSAVarOrder.t -> SSAStore.t -> coq_Z

  val eval_eunop : DSL.eunop -> coq_Z -> coq_Z

  val eval_ebinop : DSL.ebinop -> coq_Z -> coq_Z -> coq_Z

  val eval_runop : DSL.runop -> bits -> bits

  val eval_rbinop : DSL.rbinop -> bits -> bits -> bits

  val eval_rcmpop : DSL.rcmpop -> bits -> bits -> bool

  val eval_eexp : eexp -> TypEnv.SSATE.env -> SSAStore.t -> coq_Z

  val eval_eexps : eexp list -> TypEnv.SSATE.env -> SSAStore.t -> coq_Z list

  val eval_rexp : rexp -> SSAStore.t -> bits

  val eval_rbexp : rbexp -> SSAStore.t -> bool

  val eval_atom : atom -> SSAStore.t -> bits

  val instr_succ_typenv : instr -> TypEnv.SSATE.env -> TypEnv.SSATE.env

  val program_succ_typenv : program -> TypEnv.SSATE.env -> TypEnv.SSATE.env

  val well_typed_eexp : TypEnv.SSATE.env -> eexp -> bool

  val well_typed_eexps : TypEnv.SSATE.env -> eexp list -> bool

  val well_typed_rexp : TypEnv.SSATE.env -> rexp -> bool

  val well_typed_ebexp : TypEnv.SSATE.env -> ebexp -> bool

  val well_typed_rbexp : TypEnv.SSATE.env -> rbexp -> bool

  val well_typed_bexp : TypEnv.SSATE.env -> bexp -> bool

  val well_sized_atom : TypEnv.SSATE.env -> atom -> bool

  val size_matched_atom : atom -> bool

  val well_typed_atom : TypEnv.SSATE.env -> atom -> bool

  val well_typed_instr : TypEnv.SSATE.env -> instr -> bool

  module TEKS :
   sig
    module MLemmas :
     sig
      module F :
       sig
        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = TypEnv.SSATE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
         end

        module O :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = TypEnv.SSATE.SE.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

            val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

            val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
           end
         end

        module P :
         sig
          module F :
           sig
            val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

            val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
           end

          val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

          val of_list : (TypEnv.SSATE.key * 'a1) list -> 'a1 TypEnv.SSATE.t

          val to_list : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) list

          val fold_rec :
            (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
            TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> __ -> 'a3) ->
            (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> 'a1
            TypEnv.SSATE.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_bis :
            (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
            TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t ->
            'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TypEnv.SSATE.key -> 'a1 ->
            'a2 -> 'a1 TypEnv.SSATE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

          val fold_rec_nodep :
            (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
            TypEnv.SSATE.t -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> __ ->
            'a3 -> 'a3) -> 'a3

          val fold_rec_weak :
            (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1
            TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 -> 'a3)
            -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t
            -> __ -> 'a3 -> 'a3) -> 'a1 TypEnv.SSATE.t -> 'a3

          val fold_rel :
            (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.SSATE.key ->
            'a1 -> 'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.SSATE.t -> 'a4 ->
            (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

          val map_induction :
            ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
            TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.key -> 'a1 -> __ -> __ ->
            'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

          val map_induction_bis :
            ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 -> 'a2) ->
            'a2 -> (TypEnv.SSATE.key -> 'a1 -> 'a1 TypEnv.SSATE.t -> __ ->
            'a2 -> 'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

          val cardinal_inv_2 :
            'a1 TypEnv.SSATE.t -> int -> (TypEnv.SSATE.key * 'a1)

          val cardinal_inv_2b : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1)

          val filter :
            (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
            TypEnv.SSATE.t

          val for_all :
            (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

          val exists_ :
            (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

          val partition :
            (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
            TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

          val update :
            'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

          val restrict :
            'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

          val diff :
            'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

          val coq_Partition_In :
            'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t ->
            TypEnv.SSATE.key -> bool

          val update_dec :
            'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key ->
            'a1 -> bool

          val filter_dom :
            (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
            TypEnv.SSATE.t

          val filter_range :
            ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

          val for_all_dom :
            (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

          val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

          val exists_dom :
            (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

          val exists_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

          val partition_dom :
            (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
            TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

          val partition_range :
            ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a1
            TypEnv.SSATE.t
         end

        val gtb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

        val leb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

        val elements_lt :
          (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
          (TypEnv.SSATE.key * 'a1) list

        val elements_ge :
          (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
          (TypEnv.SSATE.key * 'a1) list

        val max_elt_aux :
          (TypEnv.SSATE.key * 'a1) list -> (TypEnv.SSATE.key * 'a1) option

        val max_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

        val min_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

        val map_induction_max :
          ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ ->
          'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

        val map_induction_min :
          ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ ->
          'a2) -> 'a1 TypEnv.SSATE.t -> 'a2
       end

      val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool

      module ME :
       sig
        module TO :
         sig
          type t = TypEnv.SSATE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TypEnv.SSATE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TypEnv.SSATE.key * 'a1) list -> 'a1 TypEnv.SSATE.t

        val to_list : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) list

        val fold_rec :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> __ -> 'a3) ->
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2
          -> __ -> 'a3 -> 'a3) -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 ->
          'a1 TypEnv.SSATE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> __ ->
          'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1
          TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 -> 'a3) ->
          'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> __
          -> 'a3 -> 'a3) -> 'a1 TypEnv.SSATE.t -> 'a3

        val fold_rel :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.SSATE.key -> 'a1
          -> 'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.SSATE.t -> 'a4 ->
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.key -> 'a1 -> __ -> __ ->
          'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

        val map_induction_bis :
          ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 -> 'a2) ->
          'a2 -> (TypEnv.SSATE.key -> 'a1 -> 'a1 TypEnv.SSATE.t -> __ -> 'a2
          -> 'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

        val cardinal_inv_2 :
          'a1 TypEnv.SSATE.t -> int -> (TypEnv.SSATE.key * 'a1)

        val cardinal_inv_2b : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1)

        val filter :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t

        val for_all :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_ :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val partition :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

        val update :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val restrict :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val diff :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val coq_Partition_In :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t ->
          TypEnv.SSATE.key -> bool

        val update_dec :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> 'a1
          -> bool

        val filter_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t

        val filter_range :
          ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val for_all_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val partition_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

        val partition_range :
          ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a1
          TypEnv.SSATE.t
       end

      val gtb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

      val leb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

      val elements_lt :
        (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
        (TypEnv.SSATE.key * 'a1) list

      val elements_ge :
        (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
        (TypEnv.SSATE.key * 'a1) list

      val max_elt_aux :
        (TypEnv.SSATE.key * 'a1) list -> (TypEnv.SSATE.key * 'a1) option

      val max_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

      val min_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

      val map_induction_max :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2

      val map_induction_min :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2

      val memP : TypEnv.SSATE.key -> 'a1 TypEnv.SSATE.t -> reflect

      val split :
        ('a1 * 'a2) TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a2 TypEnv.SSATE.t

      module EFacts :
       sig
        module TO :
         sig
          type t = TypEnv.SSATE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
       end

      val max_opt :
        TypEnv.SSATE.key -> TypEnv.SSATE.key option -> TypEnv.SSATE.key

      val max_key_elements :
        (TypEnv.SSATE.key * 'a1) list -> TypEnv.SSATE.key option

      val max_key : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key option

      val min_opt :
        TypEnv.SSATE.key -> TypEnv.SSATE.key option -> TypEnv.SSATE.key

      val min_key_elements :
        (TypEnv.SSATE.key * 'a1) list -> TypEnv.SSATE.key option

      val min_key : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key option
     end

    module SLemmas :
     sig
      module F :
       sig
        val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
       end

      module OP :
       sig
        module ME :
         sig
          module TO :
           sig
            type t = SSAVS.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

          val lt_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

          val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
         end

        module P :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
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
            val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
           end

          val coq_In_dec : SSAVS.elt -> SSAVS.t -> bool

          val of_list : SSAVS.elt list -> SSAVS.t

          val to_list : SSAVS.t -> SSAVS.elt list

          val fold_rec :
            (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> __ ->
            'a2) -> (SSAVS.elt -> 'a1 -> SSAVS.t -> SSAVS.t -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a2

          val fold_rec_bis :
            (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t ->
            SSAVS.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1
            -> SSAVS.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> 'a2 -> (SSAVS.elt
            -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.t -> SSAVS.t -> 'a1 ->
            __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __ ->
            'a2 -> 'a2) -> SSAVS.t -> 'a2

          val fold_rel :
            (SSAVS.elt -> 'a1 -> 'a1) -> (SSAVS.elt -> 'a2 -> 'a2) -> 'a1 ->
            'a2 -> SSAVS.t -> 'a3 -> (SSAVS.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
            'a3) -> 'a3

          val set_induction :
            (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.elt
            -> __ -> __ -> 'a1) -> SSAVS.t -> 'a1

          val set_induction_bis :
            (SSAVS.t -> SSAVS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.elt ->
            SSAVS.t -> __ -> 'a1 -> 'a1) -> SSAVS.t -> 'a1

          val cardinal_inv_2 : SSAVS.t -> int -> SSAVS.elt

          val cardinal_inv_2b : SSAVS.t -> SSAVS.elt
         end

        val gtb : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val leb : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val elements_lt : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

        val elements_ge : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

        val set_induction_max :
          (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t
          -> __ -> __ -> 'a1) -> SSAVS.t -> 'a1

        val set_induction_min :
          (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t
          -> __ -> __ -> 'a1) -> SSAVS.t -> 'a1
       end

      val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool

      module ME :
       sig
        module TO :
         sig
          type t = SSAVS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val lt_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
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
          val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
         end

        val coq_In_dec : SSAVS.elt -> SSAVS.t -> bool

        val of_list : SSAVS.elt list -> SSAVS.t

        val to_list : SSAVS.t -> SSAVS.elt list

        val fold_rec :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> __ ->
          'a2) -> (SSAVS.elt -> 'a1 -> SSAVS.t -> SSAVS.t -> __ -> __ -> __
          -> 'a2 -> 'a2) -> 'a2

        val fold_rec_bis :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> SSAVS.t
          -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t
          -> __ -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> 'a2 -> (SSAVS.elt ->
          'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.t -> SSAVS.t -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __ ->
          'a2 -> 'a2) -> SSAVS.t -> 'a2

        val fold_rel :
          (SSAVS.elt -> 'a1 -> 'a1) -> (SSAVS.elt -> 'a2 -> 'a2) -> 'a1 ->
          'a2 -> SSAVS.t -> 'a3 -> (SSAVS.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
          'a3) -> 'a3

        val set_induction :
          (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.elt
          -> __ -> __ -> 'a1) -> SSAVS.t -> 'a1

        val set_induction_bis :
          (SSAVS.t -> SSAVS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.elt ->
          SSAVS.t -> __ -> 'a1 -> 'a1) -> SSAVS.t -> 'a1

        val cardinal_inv_2 : SSAVS.t -> int -> SSAVS.elt

        val cardinal_inv_2b : SSAVS.t -> SSAVS.elt
       end

      val gtb : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val leb : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val elements_lt : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

      val elements_ge : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

      val set_induction_max :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1

      val set_induction_min :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1

      val memP : SSAVS.elt -> SSAVS.t -> reflect

      val disjoint : SSAVS.t -> SSAVS.t -> bool
     end

    val add_to_set : SSAVS.elt -> 'a1 -> SSAVS.t -> SSAVS.t

    val key_set : 'a1 TypEnv.SSATE.t -> SSAVS.t
   end

  val vars_env : TypEnv.SSATE.env -> SSAVS.t

  val is_defined : SSAVarOrder.t -> TypEnv.SSATE.env -> bool

  val are_defined : SSAVS.t -> TypEnv.SSATE.env -> bool

  val memenvP : TypEnv.SSATE.key -> typ TypEnv.SSATE.t -> reflect

  val well_defined_instr : TypEnv.SSATE.env -> instr -> bool

  val well_formed_instr : TypEnv.SSATE.env -> instr -> bool

  val well_formed_program : TypEnv.SSATE.env -> program -> bool

  val find_non_well_formed_instr : TypEnv.SSATE.env -> program -> instr option

  val well_formed_eexp : TypEnv.SSATE.env -> eexp -> bool

  val well_formed_eexps : TypEnv.SSATE.env -> eexp list -> bool

  val well_formed_rexp : TypEnv.SSATE.env -> rexp -> bool

  val well_formed_ebexp : TypEnv.SSATE.env -> ebexp -> bool

  val well_formed_rbexp : TypEnv.SSATE.env -> rbexp -> bool

  val well_formed_bexp : TypEnv.SSATE.env -> bexp -> bool

  val well_formed_spec : spec -> bool

  val defmemP : SSAVarOrder.t -> TypEnv.SSATE.env -> reflect

  val memdefP : TypEnv.SSATE.key -> typ TypEnv.SSATE.t -> reflect

  val defsubP : SSAVS.t -> TypEnv.SSATE.env -> reflect

  val is_assume : instr -> bool

  val force_conform_vars :
    TypEnv.SSATE.env -> SSAVarOrder.t list -> SSAStore.t -> SSAStore.t

  val force_conform :
    TypEnv.SSATE.env -> TypEnv.SSATE.env -> SSAStore.t -> SSAStore.t
 end

val string_of_ssavar : ssavar -> char list

type vmap = coq_N VM.t

val empty_vmap : vmap

val initial_index : coq_N

val first_assigned_index : coq_N

val get_index : var -> vmap -> coq_N

val upd_index : var -> vmap -> vmap

val ssa_var : vmap -> var -> ssavar

val svar : ssavar -> Equality.sort

val ssa_atom : vmap -> DSL.DSL.atom -> SSA.atom

val ssa_eexp : vmap -> DSL.DSL.eexp -> SSA.eexp

val ssa_eexps : vmap -> DSL.DSL.eexp list -> SSA.eexp list

val ssa_rexp : vmap -> DSL.DSL.rexp -> SSA.rexp

val ssa_ebexp : vmap -> DSL.DSL.ebexp -> SSA.ebexp

val ssa_rbexp : vmap -> DSL.DSL.rbexp -> SSA.rbexp

val ssa_bexp : vmap -> DSL.DSL.bexp -> SSA.ebexp * SSA.rbexp

val ssa_instr : vmap -> DSL.DSL.instr -> vmap * SSA.instr

val ssa_program : vmap -> DSL.DSL.program -> vmap * SSA.program

val add_to_ste : vmap -> var -> typ -> TypEnv.SSATE.env -> typ TypEnv.SSATE.t

val ssa_typenv : vmap -> TypEnv.TE.env -> TypEnv.SSATE.env

val ssa_spec : DSL.DSL.spec -> SSA.spec
