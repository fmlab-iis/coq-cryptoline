open Options0
open QFBV2CNF
open SSA2QFBV
open SSA2SSALite
open SSA2ZSSA
open Seqs
open VerifyLite
open Seq

val rngred_spec : options -> SSALite.SSALite.spec -> QFBV.QFBV.bexp list

val algsnd_spec : options -> SSALite.SSALite.spec -> QFBV.QFBV.bexp list

val algred_spec : options -> SSALite.SSALite.spec -> ZSSA.ZSSA.rep list

val verify_ssa : options -> SSA.SSA.spec -> bool

val verify_dsl : options -> DSL.DSL.spec -> bool
