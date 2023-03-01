open Options0
open QFBV2CNF
open SSA2QFBV
open SSA2ZSSA
open SSAFull2SSA
open Seqs
open Verify
open Seq

val rngred_spec : options -> SSA.SSA.spec -> QFBV.QFBV.bexp list

val algsnd_spec : options -> SSA.SSA.spec -> QFBV.QFBV.bexp list

val algred_spec : options -> SSA.SSA.spec -> ZSSA.ZSSA.rep list

val verify_fullssa : options -> SSAFull.SSAFull.spec -> bool

val verify_fulldsl : options -> DSLFull.DSLFull.spec -> bool
