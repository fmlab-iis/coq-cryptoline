
module ZSSA :
 sig
  type rep = { premise : SSA.SSA.ebexp; conseq : SSA.SSA.ebexp }

  val premise : rep -> SSA.SSA.ebexp

  val conseq : rep -> SSA.SSA.ebexp
 end
