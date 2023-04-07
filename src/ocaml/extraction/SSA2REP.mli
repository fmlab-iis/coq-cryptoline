open BinInt
open BinNat
open BinNums
open DSLRaw
open EqVar
open Options0
open REP
open Typ
open Eqtype
open Seq
open Ssrnat

val algred_atom : SSALite.SSALite.atom -> SSALite.SSALite.eexp

val algred_assign : ssavar -> SSALite.SSALite.eexp -> SSALite.SSALite.ebexp

val algred_join :
  SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> SSALite.SSALite.eexp -> int
  -> SSALite.SSALite.ebexp

val algred_split :
  ssavar -> ssavar -> SSALite.SSALite.eexp -> int -> SSALite.SSALite.ebexp

val algred_is_carry : ssavar -> SSALite.SSALite.ebexp

val carry_constr : options -> ssavar -> SSALite.SSALite.ebexp list

val algred_cast :
  VarOrder.t -> coq_N -> SSAVarOrder.t -> typ -> SSALite.SSALite.atom -> typ
  -> coq_N * ebexp list

val algred_vpc :
  VarOrder.t -> coq_N -> ssavar -> SSALite.SSALite.atom -> coq_N * ebexp list

val algred_instr :
  options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N -> SSALite.SSALite.instr
  -> coq_N * SSALite.SSALite.ebexp list

val algred_program :
  options -> TypEnv.SSATE.env -> VarOrder.t -> coq_N ->
  SSALite.SSALite.program -> coq_N * SSALite.SSALite.ebexp list

val new_svar_spec : SSALite.SSALite.spec -> VarOrder.t

val algred_espec : options -> VarOrder.t -> SSALite.SSALite.espec -> rep
