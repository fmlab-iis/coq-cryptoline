open BinInt
open BinNums
open Datatypes
open Seq
open Ssrnat

(** val split_head : 'a1 -> 'a1 list -> 'a1 * 'a1 list **)

let split_head d ls =
  ((head d ls), (behead ls))

(** val lastd : 'a1 -> 'a1 list -> 'a1 **)

let lastd d = function
| [] -> d
| hd :: tl -> last hd tl

(** val belastd : 'a1 list -> 'a1 list **)

let belastd = function
| [] -> []
| hd :: tl -> belast hd tl

(** val split_last : 'a1 -> 'a1 list -> 'a1 list * 'a1 **)

let split_last d ls =
  ((belastd ls), (lastd d ls))

type bits = bitseq

(** val b0 : bool **)

let b0 =
  false

(** val b1 : bool **)

let b1 =
  true

(** val zeros : int -> bits **)

let zeros n =
  nseq n b0

(** val ones : int -> bits **)

let ones n =
  nseq n b1

(** val splitlsb : bits -> bool * bits **)

let splitlsb bs =
  split_head b0 bs

(** val splitmsb : bits -> bits * bool **)

let splitmsb bs =
  split_last b0 bs

(** val droplsb : bits -> bits **)

let droplsb bs =
  snd (splitlsb bs)

(** val dropmsb : bits -> bits **)

let dropmsb bs =
  fst (splitmsb bs)

(** val joinlsb : 'a1 -> 'a1 list -> 'a1 list **)

let joinlsb x x0 =
  x :: x0

(** val joinmsb : 'a1 list -> 'a1 -> 'a1 list **)

let joinmsb =
  rcons

(** val lsb : bits -> bool **)

let lsb bs =
  fst (splitlsb bs)

(** val msb : bits -> bool **)

let msb bs =
  snd (splitmsb bs)

(** val high : int -> bits -> bits **)

let high n bs =
  cat (zeros (subn n (size bs))) (drop (subn (size bs) n) bs)

(** val low : int -> bits -> bits **)

let low n bs =
  cat (take n bs) (zeros (subn n (size bs)))

(** val extract : int -> int -> bits -> bits **)

let extract i j bs =
  high (addn (subn i j) (Pervasives.succ 0))
    (low (addn i (Pervasives.succ 0)) bs)

(** val zext : int -> bits -> bits **)

let zext n bs =
  cat bs (zeros n)

(** val sext : int -> bits -> bits **)

let sext n bs =
  cat bs (nseq n (msb bs))

(** val repeat : int -> 'a1 list -> 'a1 list **)

let rec repeat n s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> cat s (repeat m s))
    n

(** val invB : bits -> bits **)

let invB bs =
  map negb bs

(** val to_nat : bits -> int **)

let to_nat bs =
  foldr (fun b res -> addn (nat_of_bool b) (double res)) 0 bs

(** val from_nat : int -> int -> bits **)

let rec from_nat n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> joinlsb (odd x) (from_nat m (half x)))
    n

(** val to_Zpos : bits -> coq_Z **)

let to_Zpos bs =
  foldr (fun b res -> Z.add (Z.b2z b) (Z.mul res (Zpos (Coq_xO Coq_xH)))) Z0
    bs

(** val to_Zneg : bits -> coq_Z **)

let to_Zneg bs =
  foldr (fun b res ->
    Z.add (Z.b2z (negb b)) (Z.mul res (Zpos (Coq_xO Coq_xH)))) Z0 bs

(** val to_Z : bits -> coq_Z **)

let to_Z bs =
  let (bs0, b) = splitmsb bs in
  if b then Z.opp (Z.succ (to_Zneg bs0)) else to_Zpos bs0

(** val from_Zpos : int -> coq_Z -> bits **)

let rec from_Zpos n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> joinlsb (Z.odd x) (from_Zpos m (Z.div2 x)))
    n

(** val from_Zneg : int -> coq_Z -> bits **)

let rec from_Zneg n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> joinlsb (Z.even x) (from_Zneg m (Z.div2 x)))
    n

(** val from_Z : int -> coq_Z -> bits **)

let from_Z n x = match x with
| Z0 -> zeros n
| Zpos _ -> from_Zpos n x
| Zneg _ -> from_Zneg n (Z.pred (Z.opp x))
