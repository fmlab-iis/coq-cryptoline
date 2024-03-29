open Ascii
open BinNat
open BinNums
open BinPos
open Decimal
open DecimalString
open PeanoNat
open String0

val newline : char list

type signed_int =
| Pos of uint
| Neg of uint

val nat_to_signed_int : int -> signed_int

val coq_N_to_signed_int : coq_N -> signed_int

val coq_Z_to_signed_int : coq_Z -> signed_int

val string_of_signed_int : signed_int -> char list

val string_of_nat : int -> char list

val string_of_N : coq_N -> char list

val string_of_Z : coq_Z -> char list

module type Printer =
 sig
  type t

  val to_string : t -> char list
 end
