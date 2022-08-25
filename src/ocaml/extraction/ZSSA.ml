
module ZSSA =
 struct
  (** val string_of_zexp : DSL.eexp -> char list **)

  let string_of_zexp =
    SSA.SSA.string_of_eexp SSA.string_of_ssavar

  (** val string_of_zexps : char list -> DSL.eexp list -> char list **)

  let string_of_zexps =
    SSA.SSA.string_of_eexps SSA.string_of_ssavar

  type rep = { premise : SSA.SSA.ebexp; conseq : SSA.SSA.ebexp }

  (** val premise : rep -> SSA.SSA.ebexp **)

  let premise r =
    r.premise

  (** val conseq : rep -> SSA.SSA.ebexp **)

  let conseq r =
    r.conseq
 end
