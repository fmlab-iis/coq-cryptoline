
module ZSSA =
 struct
  type rep = { premise : SSA.SSA.ebexp; conseq : SSA.SSA.ebexp }

  (** val premise : rep -> SSA.SSA.ebexp **)

  let premise r =
    r.premise

  (** val conseq : rep -> SSA.SSA.ebexp **)

  let conseq r =
    r.conseq
 end
