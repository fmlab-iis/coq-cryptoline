open BinNatDef
open BinNums

module Raw =
 struct
  (** val of_pos : positive -> char list -> char list **)

  let rec of_pos p rest =
    match p with
    | Coq_xI p' -> of_pos p' ('1'::rest)
    | Coq_xO p' -> of_pos p' ('0'::rest)
    | Coq_xH -> '1'::rest
 end

(** val of_pos : positive -> char list **)

let of_pos p =
  '0'::('b'::(Raw.of_pos p []))

(** val of_N : coq_N -> char list **)

let of_N = function
| N0 -> '0'::('b'::('0'::[]))
| Npos p -> of_pos p

(** val of_Z : coq_Z -> char list **)

let of_Z = function
| Z0 -> '0'::('b'::('0'::[]))
| Zpos p -> of_pos p
| Zneg p -> '-'::(of_pos p)

(** val of_nat : int -> char list **)

let of_nat n =
  of_N (N.of_nat n)
