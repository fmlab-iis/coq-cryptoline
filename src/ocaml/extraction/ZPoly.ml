open BinInt
open BinNums
open Ring_polynom
open Seqs
open ZAriths
open Eqtype
open Seq

(** val coq_Znorm_subst : coq_Z coq_PExpr -> coq_Z coq_Pol **)

let coq_Znorm_subst =
  norm_subst Z0 (Zpos Coq_xH) Z.add Z.mul Z.sub Z.opp Z.eqb Z.quotrem 0 []

(** val coq_ZPeq : coq_Z coq_Pol -> coq_Z coq_Pol -> bool **)

let coq_ZPeq =
  coq_Peq Z.eqb

(** val zpexpr_eqb : coq_Z coq_PExpr -> coq_Z coq_PExpr -> bool **)

let zpexpr_eqb p1 p2 =
  coq_ZPeq (coq_Znorm_subst p1) (coq_Znorm_subst p2)

(** val peadds : 'a1 coq_PExpr list -> 'a1 coq_PExpr **)

let peadds es =
  foldl (fun x x0 -> PEadd (x, x0)) PEO es

(** val pemuls :
    'a1 coq_PExpr list -> 'a1 coq_PExpr list -> 'a1 coq_PExpr list **)

let pemuls es1 es2 =
  mapr (fun pat -> let (x, y) = pat in PEmul (x, y)) (zipr es1 es2)

(** val zpexpr_is_zero : coq_Z coq_PExpr -> bool **)

let zpexpr_is_zero = function
| PEO -> true
| PEc n -> eq_op coq_Z_eqType (Obj.magic n) (Obj.magic Z0)
| _ -> false
