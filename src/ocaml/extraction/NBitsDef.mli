open BinInt
open BinNums
open Datatypes
open String0
open Seq
open Ssrnat

val split_head : 'a1 -> 'a1 list -> 'a1 * 'a1 list

val lastd : 'a1 -> 'a1 list -> 'a1

val belastd : 'a1 list -> 'a1 list

val split_last : 'a1 -> 'a1 list -> 'a1 list * 'a1

type bits = bitseq

val b0 : bool

val b1 : bool

val zeros : int -> bits

val ones : int -> bits

val splitlsb : bits -> bool * bits

val splitmsb : bits -> bits * bool

val droplsb : bits -> bits

val dropmsb : bits -> bits

val joinlsb : 'a1 -> 'a1 list -> 'a1 list

val joinmsb : 'a1 list -> 'a1 -> 'a1 list

val lsb : bits -> bool

val msb : bits -> bool

val high : int -> bits -> bits

val low : int -> bits -> bits

val extract : int -> int -> bits -> bits

val zext : int -> bits -> bits

val sext : int -> bits -> bits

val repeat : int -> 'a1 list -> 'a1 list

val invB : bits -> bits

val to_nat : bits -> int

val from_nat : int -> int -> bits

val to_Zpos : bits -> coq_Z

val to_Zneg : bits -> coq_Z

val to_Z : bits -> coq_Z

val from_Zpos : int -> coq_Z -> bits

val from_Zneg : int -> coq_Z -> bits

val from_Z : int -> coq_Z -> bits

val nibble_to_char : bits -> char

val append_nibble_on_string : bits -> char list -> char list

val to_hex : bits -> char list
