open BBCommon
open BBConj
open BBConst
open BBDisj
open BBIte
open BBLneg
open BBVar
open BitBlastingCCacheDef
open CNF
open CacheHash
open QFBVHash
open Seqs
open Var
open Seq

val bit_blast_exp_hcache :
  TypEnv.SSATE.env -> vm -> cache -> generator -> hexp ->
  (((vm * cache) * generator) * cnf list) * word

val bit_blast_bexp_hcache :
  TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp ->
  (((vm * cache) * generator) * cnf list) * literal

val init_hcache : cache

val bit_blast_bexp_hcache_tflatten :
  TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp ->
  (((vm * cache) * generator) * clause list) * literal
