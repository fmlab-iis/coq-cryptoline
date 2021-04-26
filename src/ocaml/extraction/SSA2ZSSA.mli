open BinInt
open BinNat
open BinNums
open Options0
open Typ
open Var
open Eqtype
open Seq
open Ssrnat

val max_svar : SSAVS.t -> VarOrder.t

val new_svar : SSAVS.t -> VarOrder.t

val bv2z_atomic : SSA.SSA.atomic -> SSA.SSA.eexp

val bv2z_assign : ssavar -> SSA.SSA.eexp -> SSA.SSA.ebexp

val bv2z_join :
  SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp -> int -> SSA.SSA.ebexp

val bv2z_split : ssavar -> ssavar -> SSA.SSA.eexp -> int -> SSA.SSA.ebexp

val bv2z_is_carry : ssavar -> SSA.SSA.ebexp

val carry_constr : options -> ssavar -> SSA.SSA.ebexp list

val bv2z_cast :
  VarOrder.t -> coq_N -> SSAVarOrder.t -> typ -> SSA.SSA.atomic -> typ ->
  coq_N * DSL.ebexp list

val bv2z_vpc :
  VarOrder.t -> coq_N -> ssavar -> SSA.SSA.atomic -> coq_N * DSL.ebexp list

val bv2z_instr :
  options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N -> SSA.SSA.instr ->
  coq_N * SSA.SSA.ebexp list

val bv2z_program :
  options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N -> SSA.SSA.program ->
  coq_N * SSA.SSA.ebexp list

val new_svar_spec : SSA.SSA.spec -> VarOrder.t

val bv2z_espec : options -> VarOrder.t -> SSA.SSA.espec -> ZSSA.ZSSA.zspec
