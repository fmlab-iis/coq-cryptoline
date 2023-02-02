open Seqs

val rewrite_mov : SSAFull.SSAFull.spec -> SSAFull.SSAFull.spec

val ssa2lite_instr : SSAFull.SSAFull.instr -> SSA.SSA.instr

val ssa2lite_program : SSAFull.SSAFull.program -> SSA.SSA.program

val ssa2lite_spec : SSAFull.SSAFull.spec -> SSA.SSA.spec
