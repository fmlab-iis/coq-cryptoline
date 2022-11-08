open Ascii
open BinNat
open BinNums
open BinPos
open Decimal
open DecimalString
open PeanoNat
open String0

(** val newline : char list **)

let newline =
  (ascii_of_N (Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))::[]

type signed_int =
| Pos of uint
| Neg of uint

(** val nat_to_signed_int : int -> signed_int **)

let nat_to_signed_int n =
  Pos (Nat.to_uint n)

(** val coq_N_to_signed_int : coq_N -> signed_int **)

let coq_N_to_signed_int n =
  Pos (N.to_uint n)

(** val coq_Z_to_signed_int : coq_Z -> signed_int **)

let coq_Z_to_signed_int = function
| Z0 -> Pos (Nat.to_uint 0)
| Zpos m -> Pos (Pos.to_uint m)
| Zneg m -> Neg (Pos.to_uint m)

(** val string_of_signed_int : signed_int -> char list **)

let string_of_signed_int = function
| Pos d0 -> NilEmpty.string_of_uint d0
| Neg d0 -> append ('-'::[]) (NilEmpty.string_of_uint d0)

(** val string_of_nat : int -> char list **)

let string_of_nat n =
  string_of_signed_int (nat_to_signed_int n)

(** val string_of_N : coq_N -> char list **)

let string_of_N n =
  string_of_signed_int (coq_N_to_signed_int n)

(** val string_of_Z : coq_Z -> char list **)

let string_of_Z n =
  string_of_signed_int (coq_Z_to_signed_int n)

module type Printer =
 sig
  type t

  val to_string : t -> char list
 end
