open Eqtype
open Seq
open Ssrbool

(** val tflatten : 'a1 list list -> 'a1 list **)

let tflatten ss =
  foldl (fun r s -> catrev s r) [] ss

(** val mapr_rec : ('a1 -> 'a2) -> 'a2 list -> 'a1 list -> 'a2 list **)

let rec mapr_rec f res = function
| [] -> res
| hd :: tl -> mapr_rec f ((f hd) :: res) tl

(** val mapr : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapr f es =
  mapr_rec f [] es

(** val tfilter :
    Equality.coq_type -> Equality.sort pred -> Equality.sort list ->
    Equality.sort list **)

let tfilter _ p es =
  foldl (fun r x -> if p x then x :: r else r) [] es

(** val zipr_rec :
    ('a1 * 'a2) list -> 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec zipr_rec res_rev xs ys =
  match xs with
  | [] -> res_rev
  | x :: xs0 ->
    (match ys with
     | [] -> res_rev
     | y :: ys0 -> zipr_rec ((x, y) :: res_rev) xs0 ys0)

(** val zipr : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let zipr xs ys =
  zipr_rec [] xs ys
