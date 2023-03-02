open BinNums
open BitBlastingCacheHash
open BitBlastingInit
open CNF
open CacheHash
open Options0
open QFBVHash
open SSA2QFBV
open Seqs
open Var
open Eqtype

val bb_hbexps_cache :
  TypEnv.SSATE.env -> hbexp list -> ((word
  SSAVM.t * cache) * positive) * literal list list list

val simplify_bexps : QFBV.QFBV.bexp list -> QFBV.QFBV.bexp list

val bexp_is_not_true : QFBV.QFBV.bexp -> bool

val filter_not_true : Equality.sort list -> Equality.sort list

val bb_rngred_algsnd : options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list
