open BinNat
open BinPos
open Ring_polynom

val coq_PExpr_eq :
  ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> bool
