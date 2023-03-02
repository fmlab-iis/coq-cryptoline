open DSLRaw

module ZSSA =
 struct
  (** val string_of_zexp : eexp -> char list **)

  let string_of_zexp =
    SSALite.SSALite.string_of_eexp

  (** val string_of_zexps : char list -> eexp list -> char list **)

  let string_of_zexps =
    SSALite.SSALite.string_of_eexps

  type rep = { premise : SSALite.SSALite.ebexp; conseq : SSALite.SSALite.ebexp }

  (** val premise : rep -> SSALite.SSALite.ebexp **)

  let premise r =
    r.premise

  (** val conseq : rep -> SSALite.SSALite.ebexp **)

  let conseq r =
    r.conseq
 end
