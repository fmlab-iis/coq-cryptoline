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

(** val qfbv_spec_safety_la_rec :
    QFBV.QFBV.bexp -> (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list ->
    QFBV.QFBV.bexp list **)

let rec qfbv_spec_safety_la_rec f = function
| [] -> []
| y :: tl ->
  let (pre_es, safe) = y in
  (qfbv_imp (qfbv_conj f (qfbv_conjs_la pre_es)) safe) :: (qfbv_spec_safety_la_rec
                                                            f tl)

(** val qfbv_spec_safety_la : SSA.SSA.spec -> QFBV.QFBV.bexp list **)

let qfbv_spec_safety_la s =
  let fE = SSA.SSA.program_succ_typenv (SSA.SSA.sprog s) (SSA.SSA.sinputs s)
  in
  qfbv_spec_safety_la_rec (bexp_rbexp (SSA.SSA.rng_bexp (SSA.SSA.spre s)))
    (bexp_program_safe_split_fixed_final fE (SSA.SSA.sprog s))

(** val bb_range_safety_la : SSA.SSA.spec -> QFBV.QFBV.bexp list **)

let bb_range_safety_la s =
  cat (qfbv_bexp_spec_split_la s) (qfbv_spec_safety_la s)

(** val bb_range_safety_la_simplified :
    SSA.SSA.spec -> QFBV.QFBV.bexp list **)

let bb_range_safety_la_simplified s =
  map QFBV.QFBV.simplify_bexp2 (bb_range_safety_la s)

(** val bexp_is_not_true : QFBV.QFBV.bexp -> bool **)

let bexp_is_not_true = function
| QFBV.QFBV.Btrue -> false
| _ -> true

(** val filter_not_true : Equality.sort list -> Equality.sort list **)

let filter_not_true es =
  tfilter QFBV.bexp_eqType (Obj.magic bexp_is_not_true) es

(** val bb_range_safety_la_simplified_filtered :
    SSA.SSA.spec -> Equality.sort list **)

let bb_range_safety_la_simplified_filtered s =
  filter_not_true (Obj.magic bb_range_safety_la_simplified s)
