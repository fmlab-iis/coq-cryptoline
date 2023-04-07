open BinInt
open BinNums
open Ring_polynom
open Seqs
open ZAriths
open Eqtype
open Seq

val coq_Znorm_subst : coq_Z coq_PExpr -> coq_Z coq_Pol

val coq_ZPeq : coq_Z coq_Pol -> coq_Z coq_Pol -> bool

val zpexpr_eqb : coq_Z coq_PExpr -> coq_Z coq_PExpr -> bool

val peadds : 'a1 coq_PExpr list -> 'a1 coq_PExpr

val pemuls : 'a1 coq_PExpr list -> 'a1 coq_PExpr list -> 'a1 coq_PExpr list

val zpexpr_is_zero : coq_Z coq_PExpr -> bool
