open BinInt
open BinNums
open BinPos
open Bool
open Datatypes
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

val pair_with_vars : azbexp -> SSAVS.t * azbexp

val simplify_arep_vars_cache : arep -> arep

val split_zbexp : SSA.SSA.ebexp -> azbexp list

val areps_of_rep_full : ZSSA.ZSSA.rep -> arep list

val areps_of_rep : ZSSA.ZSSA.rep -> arep list

val areps_of_rep_simplified : options -> ZSSA.ZSSA.rep -> arep list

val coq_Znorm_subst : coq_Z coq_PExpr -> coq_Z coq_Pol

val coq_ZPeq : coq_Z coq_Pol -> coq_Z coq_Pol -> bool

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

val zpexpr_eqb : coq_Z coq_PExpr -> coq_Z coq_PExpr -> bool

val validate_imp_answer :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z
  coq_PExpr list -> coq_Z coq_PExpr list -> bool
