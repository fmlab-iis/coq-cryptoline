open Eqtype
open Seq
open Ssrbool

val tflatten : 'a1 list list -> 'a1 list

val mapr_rec : ('a1 -> 'a2) -> 'a2 list -> 'a1 list -> 'a2 list

val mapr : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val tfilter :
  Equality.coq_type -> Equality.sort pred -> Equality.sort list ->
  Equality.sort list

val zipr_rec : ('a1 * 'a2) list -> 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val zipr : 'a1 list -> 'a2 list -> ('a1 * 'a2) list
