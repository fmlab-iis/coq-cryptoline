open BinInt
open BinNums
open BinPos
open Datatypes
open List0
open Options0
open Ring_polynom
open Seqs
open Var
open ZAriths
open Eqtype
open Seq
open Ssrnat

type szbexp =
| Seq of SSA.SSA.eexp * SSA.SSA.eexp
| Seqmod of SSA.SSA.eexp * SSA.SSA.eexp * SSA.SSA.eexp

type pspec = { ppremises : szbexp list; pconseq : szbexp }

val zexp_subst : SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp -> DSL.eexp

val szbexp_subst : SSA.SSA.eexp -> SSA.SSA.eexp -> szbexp -> szbexp

val subst_szbexps : SSA.SSA.eexp -> SSA.SSA.eexp -> szbexp list -> szbexp list

val is_assignment : szbexp -> (ssavar * SSA.SSA.eexp) option

val simplify_pspec_rec :
  szbexp list -> szbexp list -> szbexp -> szbexp list * szbexp

val simplify_pspec : pspec -> pspec

val szbexp_subst_vars_cache :
  ssavar -> SSA.SSA.eexp -> SSAVS.t -> (SSAVS.t * szbexp) -> SSAVS.t * szbexp

val subst_szbexps_vars_cache :
  ssavar -> SSA.SSA.eexp -> SSAVS.t -> (SSAVS.t * szbexp) list ->
  (SSAVS.t * szbexp) list

val simplify_pspec_vars_cache_rec :
  (SSAVS.t * szbexp) list -> (SSAVS.t * szbexp) list -> (SSAVS.t * szbexp) ->
  (SSAVS.t * szbexp) list * (SSAVS.t * szbexp)

val vars_szbexp : szbexp -> SSAVS.t

val pair_with_vars : szbexp -> SSAVS.t * szbexp

val simplify_pspec_vars_cache : pspec -> pspec

val split_zbexp : SSA.SSA.ebexp -> szbexp list

val pspecs_of_zspec : ZSSA.ZSSA.zspec -> pspec list

val pspecs_of_zspec_simplified : options -> ZSSA.ZSSA.zspec -> pspec list

val coq_Znorm_subst : coq_Z coq_PExpr -> coq_Z coq_Pol

val coq_ZPeq : coq_Z coq_Pol -> coq_Z coq_Pol -> bool

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

val zpexpr_of_premise :
  positive -> positive SSAVM.t -> szbexp -> (positive * positive
  SSAVM.t) * coq_Z coq_PExpr

val zpexprs_of_premises :
  positive -> positive SSAVM.t -> szbexp list -> (positive * positive
  SSAVM.t) * coq_Z coq_PExpr list

val zpexpr_of_conseq :
  positive -> positive SSAVM.t -> szbexp -> ((positive * positive
  SSAVM.t) * coq_Z coq_PExpr) * coq_Z coq_PExpr

val zpexprs_of_pspec :
  pspec -> (((positive * positive SSAVM.t) * coq_Z coq_PExpr list) * coq_Z
  coq_PExpr) * coq_Z coq_PExpr

val zpexpr_eqb : coq_Z coq_PExpr -> coq_Z coq_PExpr -> bool

val combine_coefficients_tr :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr list -> coq_Z coq_PExpr list

val sum_polys_rec : coq_Z coq_PExpr -> coq_Z coq_PExpr list -> coq_Z coq_PExpr

val sum_polys_tr : coq_Z coq_PExpr list -> coq_Z coq_PExpr

val coefficients_checker_tr :
  coq_Z coq_PExpr list -> coq_Z coq_PExpr -> coq_Z coq_PExpr -> coq_Z
  coq_PExpr list -> coq_Z coq_PExpr -> bool
