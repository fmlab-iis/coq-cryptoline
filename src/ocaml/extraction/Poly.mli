open BinInt
open BinNums
open BinPos
open BinaryString
open Bool
open Datatypes
open FSets
open Field_theory
open Int0
open List0
open Options0
open Ring_polynom
open Seqs
open String0
open Var
open ZAriths
open Eqtype
open Seq
open Ssrbool
open Ssrnat

type __ = Obj.t

type azbexp =
| Seq of SSA.SSA.eexp * SSA.SSA.eexp
| Seqmod of SSA.SSA.eexp * SSA.SSA.eexp * SSA.SSA.eexp list

val azbexp_eqn : azbexp -> azbexp -> bool

val string_of_azbexp : azbexp -> char list

val azbexp_eqP : azbexp -> azbexp -> reflect

val azbexp_eqMixin : azbexp Equality.mixin_of

val azbexp_eqType : Equality.coq_type

type arep = { apremises : azbexp list; aconseq : azbexp }

val is_arep_trivial : arep -> bool

val zexp_subst : SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp -> DSL.eexp

val zexps_subst :
  SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp list -> DSL.eexp list

val azbexp_subst : SSA.SSA.eexp -> SSA.SSA.eexp -> azbexp -> azbexp

val subst_azbexps : SSA.SSA.eexp -> SSA.SSA.eexp -> azbexp list -> azbexp list

val single_variables : SSA.SSA.eexp -> SSAVS.t

val num_occurrence : SSAVarOrder.t -> SSA.SSA.eexp -> int

val separate :
  Equality.sort -> SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp option

val get_rewrite_pattern : SSA.SSA.eexp -> (SSAVS.elt * SSA.SSA.eexp) option

val is_assignment : azbexp -> (ssavar * SSA.SSA.eexp) option

val simplify_arep_rec :
  azbexp list -> azbexp list -> azbexp -> azbexp list * azbexp

val simplify_arep : arep -> arep

val azbexp_subst_vars_cache :
  ssavar -> SSA.SSA.eexp -> SSAVS.t -> (SSAVS.t * azbexp) -> SSAVS.t * azbexp

val subst_azbexps_vars_cache :
  ssavar -> SSA.SSA.eexp -> SSAVS.t -> (SSAVS.t * azbexp) list ->
  (SSAVS.t * azbexp) list

val simplify_arep_vars_cache_rec :
  (SSAVS.t * azbexp) list -> (SSAVS.t * azbexp) list -> (SSAVS.t * azbexp) ->
  (SSAVS.t * azbexp) list * (SSAVS.t * azbexp)

val vars_azbexp : azbexp -> SSAVS.t

val pair_azbexp_with_vars : azbexp -> SSAVS.t * azbexp

val simplify_arep_vars_cache : arep -> arep

val split_zbexp : SSA.SSA.ebexp -> azbexp list

val areps_of_rep_full : ZSSA.ZSSA.rep -> arep list

val areps_of_rep : ZSSA.ZSSA.rep -> arep list

val areps_of_rep_simplified : options -> ZSSA.ZSSA.rep -> arep list

val coq_Znorm_subst : coq_Z coq_PExpr -> coq_Z coq_Pol

val coq_ZPeq : coq_Z coq_Pol -> coq_Z coq_Pol -> bool

val zpexpr_eqb : coq_Z coq_PExpr -> coq_Z coq_PExpr -> bool

val peadds : 'a1 coq_PExpr list -> 'a1 coq_PExpr

val pemuls : 'a1 coq_PExpr list -> 'a1 coq_PExpr list -> 'a1 coq_PExpr list

val zpexpr_is_zero : coq_Z coq_PExpr -> bool

val init_pos : positive

val init_vm : positive SSAVM.t

val zpexpr_of_var :
  positive -> positive SSAVM.t -> ssavar -> (positive * positive
  SSAVM.t) * coq_Z coq_PExpr

val zpexpr_of_eunop : DSL.eunop -> coq_Z coq_PExpr -> coq_Z coq_PExpr

val zpexpr_of_ebinop :
  DSL.ebinop -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr

val zpexpr_of_zexp :
  positive -> positive SSAVM.t -> SSA.SSA.eexp -> (positive * positive
  SSAVM.t) * coq_Z coq_PExpr

val zpexprs_of_zexps :
  positive -> positive SSAVM.t -> SSA.SSA.eexp list -> (positive * positive
  SSAVM.t) * coq_Z coq_PExpr list

val pvars : positive -> int -> coq_Z coq_PExpr list

val zpexpr_of_premise :
  positive -> positive SSAVM.t -> azbexp -> (positive * positive
  SSAVM.t) * coq_Z coq_PExpr

val zpexprs_of_premises :
  positive -> positive SSAVM.t -> azbexp list -> (positive * positive
  SSAVM.t) * coq_Z coq_PExpr list

val zpexpr_of_conseq :
  positive -> positive SSAVM.t -> azbexp -> ((positive * positive
  SSAVM.t) * coq_Z coq_PExpr) * coq_Z coq_PExpr list

val imp_of_arep :
  arep -> (((positive * positive SSAVM.t) * coq_Z coq_PExpr list) * coq_Z
  coq_PExpr list) * coq_Z coq_PExpr

module PS :
 sig
  module TS :
   sig
    module SE :
     sig
      val coq_T : Equality.coq_type

      type t = Equality.sort

      val ltn : t -> t -> bool

      val compare : t -> t -> t OrderedType.coq_Compare

      val eq_dec : t -> t -> bool
     end

    module X' :
     sig
      type t = Equality.sort

      val eq_dec : Equality.sort -> Equality.sort -> bool

      val compare : Equality.sort -> Equality.sort -> comparison
     end

    module MSet :
     sig
      module Raw :
       sig
        type elt = Equality.sort

        type tree =
        | Leaf
        | Node of Z_as_Int.t * tree * Equality.sort * tree

        val empty : tree

        val is_empty : tree -> bool

        val mem : Equality.sort -> tree -> bool

        val min_elt : tree -> elt option

        val max_elt : tree -> elt option

        val choose : tree -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

        val elements_aux : Equality.sort list -> tree -> Equality.sort list

        val elements : tree -> Equality.sort list

        val rev_elements_aux :
          Equality.sort list -> tree -> Equality.sort list

        val rev_elements : tree -> Equality.sort list

        val cardinal : tree -> int

        val maxdepth : tree -> int

        val mindepth : tree -> int

        val for_all : (elt -> bool) -> tree -> bool

        val exists_ : (elt -> bool) -> tree -> bool

        type enumeration =
        | End
        | More of elt * tree * enumeration

        val cons : tree -> enumeration -> enumeration

        val compare_more :
          Equality.sort -> (enumeration -> comparison) -> enumeration ->
          comparison

        val compare_cont :
          tree -> (enumeration -> comparison) -> enumeration -> comparison

        val compare_end : enumeration -> comparison

        val compare : tree -> tree -> comparison

        val equal : tree -> tree -> bool

        val subsetl : (tree -> bool) -> Equality.sort -> tree -> bool

        val subsetr : (tree -> bool) -> Equality.sort -> tree -> bool

        val subset : tree -> tree -> bool

        type t = tree

        val height : t -> Z_as_Int.t

        val singleton : Equality.sort -> tree

        val create : t -> Equality.sort -> t -> tree

        val assert_false : t -> Equality.sort -> t -> tree

        val bal : t -> Equality.sort -> t -> tree

        val add : Equality.sort -> tree -> tree

        val join : tree -> elt -> t -> t

        val remove_min : tree -> elt -> t -> t * elt

        val merge : tree -> tree -> tree

        val remove : Equality.sort -> tree -> tree

        val concat : tree -> tree -> tree

        type triple = { t_left : t; t_in : bool; t_right : t }

        val t_left : triple -> t

        val t_in : triple -> bool

        val t_right : triple -> t

        val split : Equality.sort -> tree -> triple

        val inter : tree -> tree -> tree

        val diff : tree -> tree -> tree

        val union : tree -> tree -> tree

        val filter : (elt -> bool) -> tree -> tree

        val partition : (elt -> bool) -> t -> t * t

        val ltb_tree : Equality.sort -> tree -> bool

        val gtb_tree : Equality.sort -> tree -> bool

        val isok : tree -> bool

        module MX :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = Equality.sort

              val compare : Equality.sort -> Equality.sort -> comparison

              val eq_dec : Equality.sort -> Equality.sort -> bool
             end

            module TO :
             sig
              type t = Equality.sort

              val compare : Equality.sort -> Equality.sort -> comparison

              val eq_dec : Equality.sort -> Equality.sort -> bool
             end
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        type coq_R_min_elt =
        | R_min_elt_0 of tree
        | R_min_elt_1 of tree * Z_as_Int.t * tree * Equality.sort * tree
        | R_min_elt_2 of tree * Z_as_Int.t * tree * Equality.sort * tree
           * Z_as_Int.t * tree * Equality.sort * tree * elt option
           * coq_R_min_elt

        type coq_R_max_elt =
        | R_max_elt_0 of tree
        | R_max_elt_1 of tree * Z_as_Int.t * tree * Equality.sort * tree
        | R_max_elt_2 of tree * Z_as_Int.t * tree * Equality.sort * tree
           * Z_as_Int.t * tree * Equality.sort * tree * elt option
           * coq_R_max_elt

        module L :
         sig
          module MO :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = Equality.sort

                val compare : Equality.sort -> Equality.sort -> comparison

                val eq_dec : Equality.sort -> Equality.sort -> bool
               end

              module TO :
               sig
                type t = Equality.sort

                val compare : Equality.sort -> Equality.sort -> comparison

                val eq_dec : Equality.sort -> Equality.sort -> bool
               end
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end
         end

        val flatten_e : enumeration -> elt list

        type coq_R_bal =
        | R_bal_0 of t * Equality.sort * t
        | R_bal_1 of t * Equality.sort * t * Z_as_Int.t * tree
           * Equality.sort * tree
        | R_bal_2 of t * Equality.sort * t * Z_as_Int.t * tree
           * Equality.sort * tree
        | R_bal_3 of t * Equality.sort * t * Z_as_Int.t * tree
           * Equality.sort * tree * Z_as_Int.t * tree * Equality.sort * 
           tree
        | R_bal_4 of t * Equality.sort * t
        | R_bal_5 of t * Equality.sort * t * Z_as_Int.t * tree
           * Equality.sort * tree
        | R_bal_6 of t * Equality.sort * t * Z_as_Int.t * tree
           * Equality.sort * tree
        | R_bal_7 of t * Equality.sort * t * Z_as_Int.t * tree
           * Equality.sort * tree * Z_as_Int.t * tree * Equality.sort * 
           tree
        | R_bal_8 of t * Equality.sort * t

        type coq_R_remove_min =
        | R_remove_min_0 of tree * elt * t
        | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
           * Equality.sort * tree * (t * elt) * coq_R_remove_min * t * 
           elt

        type coq_R_merge =
        | R_merge_0 of tree * tree
        | R_merge_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
        | R_merge_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
           tree * Z_as_Int.t * tree * Equality.sort * tree * t * elt

        type coq_R_concat =
        | R_concat_0 of tree * tree
        | R_concat_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
        | R_concat_2 of tree * tree * Z_as_Int.t * tree * Equality.sort
           * tree * Z_as_Int.t * tree * Equality.sort * tree * t * elt

        type coq_R_inter =
        | R_inter_0 of tree * tree
        | R_inter_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
        | R_inter_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
           tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
           t * tree * coq_R_inter * tree * coq_R_inter
        | R_inter_3 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
           tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
           t * tree * coq_R_inter * tree * coq_R_inter

        type coq_R_diff =
        | R_diff_0 of tree * tree
        | R_diff_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
        | R_diff_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
           tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
           t * tree * coq_R_diff * tree * coq_R_diff
        | R_diff_3 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
           tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
           t * tree * coq_R_diff * tree * coq_R_diff

        type coq_R_union =
        | R_union_0 of tree * tree
        | R_union_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
        | R_union_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
           tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
           t * tree * coq_R_union * tree * coq_R_union
       end

      module E :
       sig
        type t = Equality.sort

        val compare : Equality.sort -> Equality.sort -> comparison

        val eq_dec : Equality.sort -> Equality.sort -> bool
       end

      type elt = Equality.sort

      type t_ = Raw.t
        (* singleton inductive, whose constructor was Mkt *)

      val this : t_ -> Raw.t

      type t = t_

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val remove : elt -> t -> t

      val singleton : elt -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val empty : t

      val is_empty : t -> bool

      val elements : t -> elt list

      val choose : t -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val cardinal : t -> int

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val eq_dec : t -> t -> bool

      val compare : t -> t -> comparison

      val min_elt : t -> elt option

      val max_elt : t -> elt option
     end

    type elt = Equality.sort

    type t = MSet.t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val eq_dec : t -> t -> bool

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> int

    val elements : t -> elt list

    val choose : t -> elt option

    module MF :
     sig
      val eqb : Equality.sort -> Equality.sort -> bool
     end

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val compare : t -> t -> t OrderedType.coq_Compare

    module E :
     sig
      type t = Equality.sort

      val compare :
        Equality.sort -> Equality.sort -> Equality.sort
        OrderedType.coq_Compare

      val eq_dec : Equality.sort -> Equality.sort -> bool
     end
   end

  module Lemmas :
   sig
    module F :
     sig
      val eqb : TS.SE.t -> TS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TS.SE.t -> TS.SE.t -> bool

        val lt_dec : TS.SE.t -> TS.SE.t -> bool

        val eqb : TS.SE.t -> TS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : TS.SE.t -> TS.SE.t -> bool
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
          val eqb : TS.SE.t -> TS.SE.t -> bool
         end

        val coq_In_dec : TS.elt -> TS.t -> bool

        val of_list : TS.elt list -> TS.t

        val to_list : TS.t -> TS.elt list

        val fold_rec :
          (TS.elt -> 'a1 -> 'a1) -> 'a1 -> TS.t -> (TS.t -> __ -> 'a2) ->
          (TS.elt -> 'a1 -> TS.t -> TS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (TS.elt -> 'a1 -> 'a1) -> 'a1 -> TS.t -> (TS.t -> TS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (TS.elt -> 'a1 -> TS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (TS.elt -> 'a1 -> 'a1) -> 'a1 -> TS.t -> 'a2 -> (TS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (TS.elt -> 'a1 -> 'a1) -> 'a1 -> (TS.t -> TS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (TS.elt -> 'a1 -> TS.t -> __ -> 'a2 -> 'a2) ->
          TS.t -> 'a2

        val fold_rel :
          (TS.elt -> 'a1 -> 'a1) -> (TS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          TS.t -> 'a3 -> (TS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (TS.t -> __ -> 'a1) -> (TS.t -> TS.t -> 'a1 -> TS.elt -> __ -> __
          -> 'a1) -> TS.t -> 'a1

        val set_induction_bis :
          (TS.t -> TS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (TS.elt -> TS.t -> __
          -> 'a1 -> 'a1) -> TS.t -> 'a1

        val cardinal_inv_2 : TS.t -> int -> TS.elt

        val cardinal_inv_2b : TS.t -> TS.elt
       end

      val gtb : TS.SE.t -> TS.SE.t -> bool

      val leb : TS.SE.t -> TS.SE.t -> bool

      val elements_lt : TS.SE.t -> TS.t -> TS.SE.t list

      val elements_ge : TS.SE.t -> TS.t -> TS.SE.t list

      val set_induction_max :
        (TS.t -> __ -> 'a1) -> (TS.t -> TS.t -> 'a1 -> TS.SE.t -> __ -> __ ->
        'a1) -> TS.t -> 'a1

      val set_induction_min :
        (TS.t -> __ -> 'a1) -> (TS.t -> TS.t -> 'a1 -> TS.SE.t -> __ -> __ ->
        'a1) -> TS.t -> 'a1
     end

    val eqb : TS.SE.t -> TS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TS.SE.t -> TS.SE.t -> bool

      val lt_dec : TS.SE.t -> TS.SE.t -> bool

      val eqb : TS.SE.t -> TS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : TS.SE.t -> TS.SE.t -> bool
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
        val eqb : TS.SE.t -> TS.SE.t -> bool
       end

      val coq_In_dec : TS.elt -> TS.t -> bool

      val of_list : TS.elt list -> TS.t

      val to_list : TS.t -> TS.elt list

      val fold_rec :
        (TS.elt -> 'a1 -> 'a1) -> 'a1 -> TS.t -> (TS.t -> __ -> 'a2) ->
        (TS.elt -> 'a1 -> TS.t -> TS.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (TS.elt -> 'a1 -> 'a1) -> 'a1 -> TS.t -> (TS.t -> TS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (TS.elt -> 'a1 -> TS.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (TS.elt -> 'a1 -> 'a1) -> 'a1 -> TS.t -> 'a2 -> (TS.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (TS.elt -> 'a1 -> 'a1) -> 'a1 -> (TS.t -> TS.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (TS.elt -> 'a1 -> TS.t -> __ -> 'a2 -> 'a2) -> TS.t ->
        'a2

      val fold_rel :
        (TS.elt -> 'a1 -> 'a1) -> (TS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        TS.t -> 'a3 -> (TS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (TS.t -> __ -> 'a1) -> (TS.t -> TS.t -> 'a1 -> TS.elt -> __ -> __ ->
        'a1) -> TS.t -> 'a1

      val set_induction_bis :
        (TS.t -> TS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (TS.elt -> TS.t -> __ ->
        'a1 -> 'a1) -> TS.t -> 'a1

      val cardinal_inv_2 : TS.t -> int -> TS.elt

      val cardinal_inv_2b : TS.t -> TS.elt
     end

    val gtb : TS.SE.t -> TS.SE.t -> bool

    val leb : TS.SE.t -> TS.SE.t -> bool

    val elements_lt : TS.SE.t -> TS.t -> TS.SE.t list

    val elements_ge : TS.SE.t -> TS.t -> TS.SE.t list

    val set_induction_max :
      (TS.t -> __ -> 'a1) -> (TS.t -> TS.t -> 'a1 -> TS.SE.t -> __ -> __ ->
      'a1) -> TS.t -> 'a1

    val set_induction_min :
      (TS.t -> __ -> 'a1) -> (TS.t -> TS.t -> 'a1 -> TS.SE.t -> __ -> __ ->
      'a1) -> TS.t -> 'a1

    val memP : TS.elt -> TS.t -> reflect

    val equalP : TS.t -> TS.t -> reflect

    val subsetP : TS.t -> TS.t -> reflect

    val emptyP : TS.t -> reflect

    val disjoint : TS.t -> TS.t -> bool

    val proper_subset : TS.t -> TS.t -> bool
   end

  module SE :
   sig
    val coq_T : Equality.coq_type

    type t = Equality.sort

    val ltn : t -> t -> bool

    val compare : t -> t -> t OrderedType.coq_Compare

    val eq_dec : t -> t -> bool
   end

  module X' :
   sig
    type t = Equality.sort

    val eq_dec : Equality.sort -> Equality.sort -> bool

    val compare : Equality.sort -> Equality.sort -> comparison
   end

  module MSet :
   sig
    module Raw :
     sig
      type elt = Equality.sort

      type tree = TS.MSet.Raw.tree =
      | Leaf
      | Node of Z_as_Int.t * tree * Equality.sort * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : Equality.sort -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : Equality.sort list -> tree -> Equality.sort list

      val elements : tree -> Equality.sort list

      val rev_elements_aux : Equality.sort list -> tree -> Equality.sort list

      val rev_elements : tree -> Equality.sort list

      val cardinal : tree -> int

      val maxdepth : tree -> int

      val mindepth : tree -> int

      val for_all : (elt -> bool) -> tree -> bool

      val exists_ : (elt -> bool) -> tree -> bool

      type enumeration = TS.MSet.Raw.enumeration =
      | End
      | More of elt * tree * enumeration

      val cons : tree -> enumeration -> enumeration

      val compare_more :
        Equality.sort -> (enumeration -> comparison) -> enumeration ->
        comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> Equality.sort -> tree -> bool

      val subsetr : (tree -> bool) -> Equality.sort -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Z_as_Int.t

      val singleton : Equality.sort -> tree

      val create : t -> Equality.sort -> t -> tree

      val assert_false : t -> Equality.sort -> t -> tree

      val bal : t -> Equality.sort -> t -> tree

      val add : Equality.sort -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> t * elt

      val merge : tree -> tree -> tree

      val remove : Equality.sort -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = TS.MSet.Raw.triple = { t_left : t; t_in : bool;
                                           t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : Equality.sort -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> t * t

      val ltb_tree : Equality.sort -> tree -> bool

      val gtb_tree : Equality.sort -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Equality.sort

            val compare : Equality.sort -> Equality.sort -> comparison

            val eq_dec : Equality.sort -> Equality.sort -> bool
           end

          module TO :
           sig
            type t = Equality.sort

            val compare : Equality.sort -> Equality.sort -> comparison

            val eq_dec : Equality.sort -> Equality.sort -> bool
           end
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end

      type coq_R_min_elt = TS.MSet.Raw.coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_min_elt_2 of tree * Z_as_Int.t * tree * Equality.sort * tree
         * Z_as_Int.t * tree * Equality.sort * tree * elt option
         * coq_R_min_elt

      type coq_R_max_elt = TS.MSet.Raw.coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_max_elt_2 of tree * Z_as_Int.t * tree * Equality.sort * tree
         * Z_as_Int.t * tree * Equality.sort * tree * elt option
         * coq_R_max_elt

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = Equality.sort

              val compare : Equality.sort -> Equality.sort -> comparison

              val eq_dec : Equality.sort -> Equality.sort -> bool
             end

            module TO :
             sig
              type t = Equality.sort

              val compare : Equality.sort -> Equality.sort -> comparison

              val eq_dec : Equality.sort -> Equality.sort -> bool
             end
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal = TS.MSet.Raw.coq_R_bal =
      | R_bal_0 of t * Equality.sort * t
      | R_bal_1 of t * Equality.sort * t * Z_as_Int.t * tree * Equality.sort
         * tree
      | R_bal_2 of t * Equality.sort * t * Z_as_Int.t * tree * Equality.sort
         * tree
      | R_bal_3 of t * Equality.sort * t * Z_as_Int.t * tree * Equality.sort
         * tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_bal_4 of t * Equality.sort * t
      | R_bal_5 of t * Equality.sort * t * Z_as_Int.t * tree * Equality.sort
         * tree
      | R_bal_6 of t * Equality.sort * t * Z_as_Int.t * tree * Equality.sort
         * tree
      | R_bal_7 of t * Equality.sort * t * Z_as_Int.t * tree * Equality.sort
         * tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_bal_8 of t * Equality.sort * t

      type coq_R_remove_min = TS.MSet.Raw.coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * Equality.sort
         * tree * (t * elt) * coq_R_remove_min * t * elt

      type coq_R_merge = TS.MSet.Raw.coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_merge_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
         tree * Z_as_Int.t * tree * Equality.sort * tree * t * elt

      type coq_R_concat = TS.MSet.Raw.coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_concat_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
         tree * Z_as_Int.t * tree * Equality.sort * tree * t * elt

      type coq_R_inter = TS.MSet.Raw.coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_inter_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
         tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
         t * tree * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
         tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
         t * tree * coq_R_inter * tree * coq_R_inter

      type coq_R_diff = TS.MSet.Raw.coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_diff_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
         tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
         t * tree * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
         tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
         t * tree * coq_R_diff * tree * coq_R_diff

      type coq_R_union = TS.MSet.Raw.coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Z_as_Int.t * tree * Equality.sort * tree
      | R_union_2 of tree * tree * Z_as_Int.t * tree * Equality.sort * 
         tree * Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
         t * tree * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = Equality.sort

      val compare : Equality.sort -> Equality.sort -> comparison

      val eq_dec : Equality.sort -> Equality.sort -> bool
     end

    type elt = Equality.sort

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> int

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  type elt = Equality.sort

  type t = MSet.t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> bool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> int

  val elements : t -> elt list

  val choose : t -> elt option

  module MF :
   sig
    val eqb : Equality.sort -> Equality.sort -> bool
   end

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val compare : t -> t -> t OrderedType.coq_Compare

  module E :
   sig
    type t = Equality.sort

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare

    val eq_dec : Equality.sort -> Equality.sort -> bool
   end
 end

val vars_pexpr : 'a1 coq_PExpr -> PS.t

val subst_pexpr :
  ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> 'a1 coq_PExpr ->
  'a1 coq_PExpr

val subst_pexprs :
  ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> 'a1 coq_PExpr
  list -> 'a1 coq_PExpr list

val pexpr_single_variables : 'a1 coq_PExpr -> PS.t

val pexpr_num_occurrence : positive -> 'a1 coq_PExpr -> int

val pexpr_separate :
  positive -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> 'a1 coq_PExpr option

val pexpr_get_rewrite_pattern :
  'a1 coq_PExpr -> (PS.elt * 'a1 coq_PExpr) option

val pexpr_is_assignment : 'a1 coq_PExpr -> (positive * 'a1 coq_PExpr) option

val string_of_pexpr :
  char list -> char list -> ('a1 -> char list) -> 'a1 coq_PExpr -> char list

val string_of_zpexpr : coq_Z coq_PExpr -> char list

val simplify_zpexpr : coq_Z coq_PExpr -> coq_Z coq_PExpr

val subst_zpexpr :
  coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr

val subst_zpexprs :
  coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z coq_PExpr list -> coq_Z
  coq_PExpr list

val zpexpr_is_assignment :
  coq_Z coq_PExpr -> (positive * coq_Z coq_PExpr) option

val simplify_generator_rec :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z
  coq_PExpr list * coq_Z coq_PExpr

val simplify_generator :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr list * coq_Z
  coq_PExpr

val subst_zpexpr_vars_cache :
  positive -> coq_Z coq_PExpr -> PS.t -> (PS.t * coq_Z coq_PExpr) ->
  PS.t * coq_Z coq_PExpr

val subst_zpexprs_vars_cache :
  positive -> coq_Z coq_PExpr -> PS.t -> (PS.t * coq_Z coq_PExpr) list ->
  (PS.t * coq_Z coq_PExpr) list

val simplify_generator_vars_cache_rec :
  (PS.t * coq_Z coq_PExpr) list -> (PS.t * coq_Z coq_PExpr) list ->
  (PS.t * coq_Z coq_PExpr) -> (PS.t * coq_Z coq_PExpr) list * (PS.t * coq_Z
  coq_PExpr)

val pair_zpexpr_with_vars : coq_Z coq_PExpr -> PS.t * coq_Z coq_PExpr

val simplify_generator_vars_cache :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr list * coq_Z
  coq_PExpr

val validate_imp_answer :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z
  coq_PExpr list -> coq_Z coq_PExpr list -> bool
