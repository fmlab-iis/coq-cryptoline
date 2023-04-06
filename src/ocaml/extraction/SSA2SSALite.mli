open DSLRaw
open Datatypes
open EqVar
open Seqs
open Typ

val eexp_of_atom : SSA.SSA.atom -> SSA.SSA.eexp

val rexp_of_atom : SSA.SSA.atom -> SSA.SSA.rexp

val subst_eexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.eexp -> SSA.SSA.eexp

val subst_rexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.rexp -> SSA.SSA.rexp

val subst_eexps :
  SSA.SSA.atom SSAVM.t -> SSA.SSA.eexp list -> SSA.SSA.eexp list

val subst_ebexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.ebexp -> SSA.SSA.ebexp

val subst_rbexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.rbexp -> SSA.SSA.rbexp

val subst_bexp : SSA.SSA.atom SSAVM.t -> SSA.SSA.bexp -> SSA.SSA.bexp

val subst_atom : SSA.SSA.atom SSAVM.t -> SSA.SSA.atom -> SSA.SSA.atom

val subst_instr : SSA.SSA.atom SSAVM.t -> SSA.SSA.instr -> SSA.SSA.instr

val subst_program : SSA.SSA.atom SSAVM.t -> SSA.SSA.program -> SSA.SSA.program

val subst_spec : SSA.SSA.atom SSAVM.t -> SSA.SSA.spec -> SSA.SSA.spec

val subst_map_instr :
  SSA.SSA.atom SSAVM.t -> SSA.SSA.instr -> SSA.SSA.atom SSAVM.t

val subst_map_program_rec :
  SSA.SSA.atom SSAVM.t -> SSA.SSA.program -> SSA.SSA.atom SSAVM.t

val subst_map_program : SSA.SSA.program -> SSA.SSA.atom SSAVM.t

val subst_map_spec : SSA.SSA.spec -> SSA.SSA.atom SSAVM.t

val rewrite_mov : SSA.SSA.spec -> SSA.SSA.spec

val ssa2lite_instr : SSA.SSA.instr -> SSALite.SSALite.instr

val ssa2lite_program : SSA.SSA.program -> SSALite.SSALite.program

val ssa2lite_spec : SSA.SSA.spec -> SSALite.SSALite.spec
