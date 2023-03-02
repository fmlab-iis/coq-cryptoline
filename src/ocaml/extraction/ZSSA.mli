open DSLRaw

module ZSSA :
 sig
  val string_of_zexp : eexp -> char list

  val string_of_zexps : char list -> eexp list -> char list

  type rep = { premise : SSALite.SSALite.ebexp; conseq : SSALite.SSALite.ebexp }

  val premise : rep -> SSALite.SSALite.ebexp

  val conseq : rep -> SSALite.SSALite.ebexp
 end
