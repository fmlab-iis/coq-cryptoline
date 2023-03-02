open Seqs

val rewrite_mov : SSA.SSA.spec -> SSA.SSA.spec

val ssa2lite_instr : SSA.SSA.instr -> SSALite.SSALite.instr

val ssa2lite_program : SSA.SSA.program -> SSALite.SSALite.program

val ssa2lite_spec : SSA.SSA.spec -> SSALite.SSALite.spec
