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

(** val bb_hbexps_cache :
    TypEnv.SSATE.env -> hbexp list -> ((word
    SSAVM.t * cache) * positive) * literal list list list **)

let rec bb_hbexps_cache e = function
| [] -> (((init_vm, init_hcache), init_gen), [])
| e0 :: es' ->
  let (p, cnfs) = bb_hbexps_cache e es' in
  let (p0, g) = p in
  let (m, c) = p0 in
  let (p1, lr) = bit_blast_bexp_hcache_tflatten e m (reset_ct c) g e0 in
  let (p2, cs) = p1 in
  (p2, ((add_prelude (((neg_lit lr) :: []) :: cs)) :: cnfs))

(** val simplify_bexps : QFBV.QFBV.bexp list -> QFBV.QFBV.bexp list **)

let simplify_bexps es =
  tmap QFBV.QFBV.simplify_bexp2 es

(** val bexp_is_not_true : QFBV.QFBV.bexp -> bool **)

let bexp_is_not_true = function
| QFBV.QFBV.Btrue -> false
| _ -> true

(** val filter_not_true : Equality.sort list -> Equality.sort list **)

let filter_not_true es =
  tfilter QFBV.bexp_eqType (Obj.magic bexp_is_not_true) es

(** val bb_rngred_algsnd :
    options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list **)

let bb_rngred_algsnd o s =
  Obj.magic filter_not_true
    (simplify_bexps
      (if o.apply_slicing_rspec
       then rngred_algsnd_slice_split_la o s
       else rngred_algsnd_split_la s))
