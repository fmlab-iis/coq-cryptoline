open BinNums
open BitBlastingCacheHash
open BitBlastingInit
open CNF
open CacheHash
open QFBVHash
open SSA2QFBV
open Seqs
open Var
open Eqtype
open Seq

val bb_hbexps_cache :
  TypEnv.SSATE.env -> hbexp list -> ((word
  SSAVM.t * cache) * positive) * literal list list list

val qfbv_spec_safety_la_rec :
  QFBV.QFBV.bexp -> (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list ->
  QFBV.QFBV.bexp list

val qfbv_spec_safety_la : SSA.SSA.spec -> QFBV.QFBV.bexp list

val bb_range_safety_la : SSA.SSA.spec -> QFBV.QFBV.bexp list

val bb_range_safety_la_simplified : SSA.SSA.spec -> QFBV.QFBV.bexp list

val bexp_is_not_true : QFBV.QFBV.bexp -> bool

val filter_not_true : Equality.sort list -> Equality.sort list

val bb_range_safety_la_simplified_filtered :
  SSA.SSA.spec -> Equality.sort list
