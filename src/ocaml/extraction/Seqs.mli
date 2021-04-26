open Eqtype
open Seq
open Ssrbool

val tflatten_rec : 'a1 list -> 'a1 list list -> 'a1 list

val tflatten : 'a1 list list -> 'a1 list

val mapr_rec : ('a1 -> 'a2) -> 'a2 list -> 'a1 list -> 'a2 list

val mapr : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val tfilter_rec :
  Equality.coq_type -> Equality.sort pred -> Equality.sort list ->
  Equality.sort list -> Equality.sort list

val tfilter :
  Equality.coq_type -> Equality.sort pred -> Equality.sort list ->
  Equality.sort list
