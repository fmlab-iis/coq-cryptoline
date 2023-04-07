open BinInt
open Bool
open DSLRaw
open Datatypes
open EqVar
open List0
open Options0
open Seqs
open String0
open Eqtype
open Seq
open Ssrbool
open Ssrnat

type rep = { premise : SSALite.SSALite.ebexp; conseq : SSALite.SSALite.ebexp }

val string_of_zexp : eexp -> char list

val string_of_zexps : char list -> eexp list -> char list

type azbexp =
| Seq of SSALite.SSALite.eexp * SSALite.SSALite.eexp
| Seqmod of SSALite.SSALite.eexp * SSALite.SSALite.eexp
   * SSALite.SSALite.eexp list

val azbexp_eqn : azbexp -> azbexp -> bool

val string_of_azbexp : azbexp -> char list

val azbexp_eqP : azbexp -> azbexp -> reflect

val azbexp_eqMixin : azbexp Equality.mixin_of

val azbexp_eqType : Equality.coq_type

type arep = { apremises : azbexp list; aconseq : azbexp }

val is_arep_trivial : arep -> bool

val zexp_subst :
  SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> eexp

val zexps_subst :
  SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp list
  -> eexp list

val azbexp_subst :
  SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> azbexp -> azbexp

val subst_azbexps :
  SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> azbexp list -> azbexp list

val single_variables : SSALite.SSALite.eexp -> SSAVS.t

val num_occurrence : SSAVarOrder.t -> SSALite.SSALite.eexp -> int

val separate :
  Equality.sort -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp ->
  SSALite.SSALite.eexp option

val get_rewrite_pattern :
  SSALite.SSALite.eexp -> (SSAVS.elt * SSALite.SSALite.eexp) option

val is_assignment : azbexp -> (ssavar * SSALite.SSALite.eexp) option

val simplify_arep_rec :
  azbexp list -> azbexp list -> azbexp -> azbexp list * azbexp

val simplify_arep : arep -> arep

val azbexp_subst_vars_cache :
  ssavar -> SSALite.SSALite.eexp -> SSAVS.t -> (SSAVS.t * azbexp) ->
  SSAVS.t * azbexp

val subst_azbexps_vars_cache :
  ssavar -> SSALite.SSALite.eexp -> SSAVS.t -> (SSAVS.t * azbexp) list ->
  (SSAVS.t * azbexp) list

val simplify_arep_vars_cache_rec :
  (SSAVS.t * azbexp) list -> (SSAVS.t * azbexp) list -> (SSAVS.t * azbexp) ->
  (SSAVS.t * azbexp) list * (SSAVS.t * azbexp)

val vars_azbexp : azbexp -> SSAVS.t

val pair_azbexp_with_vars : azbexp -> SSAVS.t * azbexp

val simplify_arep_vars_cache : arep -> arep

val split_zbexp : SSALite.SSALite.ebexp -> azbexp list

val areps_of_rep_full : rep -> arep list

val areps_of_rep : rep -> arep list

val areps_of_rep_simplified : options -> rep -> arep list
