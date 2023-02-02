open BinInt
open BinNat
open BinNums
open DSLRaw
open Options0
open Typ
open Var
open Eqtype
open Seq
open Ssrnat

val max_svar : SSAVS.t -> VarOrder.t

val new_svar : SSAVS.t -> VarOrder.t

val algred_atom : SSA.SSA.atom -> SSA.SSA.eexp

val algred_assign : ssavar -> SSA.SSA.eexp -> SSA.SSA.ebexp

val algred_join :
  SSA.SSA.eexp -> SSA.SSA.eexp -> SSA.SSA.eexp -> int -> SSA.SSA.ebexp

val algred_split : ssavar -> ssavar -> SSA.SSA.eexp -> int -> SSA.SSA.ebexp

val algred_is_carry : ssavar -> SSA.SSA.ebexp

val carry_constr : options -> ssavar -> SSA.SSA.ebexp list

val algred_cast :
  VarOrder.t -> coq_N -> SSAVarOrder.t -> typ -> SSA.SSA.atom -> typ ->
  coq_N * ebexp list

val algred_vpc :
  VarOrder.t -> coq_N -> ssavar -> SSA.SSA.atom -> coq_N * ebexp list

val algred_instr :
  options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N -> SSA.SSA.instr ->
  coq_N * SSA.SSA.ebexp list

val algred_program :
  options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N -> SSA.SSA.program ->
  coq_N * SSA.SSA.ebexp list

val new_svar_spec : SSA.SSA.spec -> VarOrder.t

val algred_espec : options -> VarOrder.t -> SSA.SSA.espec -> ZSSA.ZSSA.rep
