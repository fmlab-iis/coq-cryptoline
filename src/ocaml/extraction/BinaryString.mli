open BinNatDef
open BinNums

module Raw :
 sig
  val of_pos : positive -> char list -> char list
 end

val of_pos : positive -> char list

val of_N : coq_N -> char list

val of_Z : coq_Z -> char list

val of_nat : int -> char list
