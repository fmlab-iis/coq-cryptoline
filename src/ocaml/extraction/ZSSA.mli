
module ZSSA :
 sig
  val string_of_zexp : DSL.eexp -> char list

  val string_of_zexps : char list -> DSL.eexp list -> char list

  type rep = { premise : SSA.SSA.ebexp; conseq : SSA.SSA.ebexp }

  val premise : rep -> SSA.SSA.ebexp

  val conseq : rep -> SSA.SSA.ebexp
 end
