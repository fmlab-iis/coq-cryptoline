
module ZSSA :
 sig
  type zspec = { zspre : SSA.SSA.ebexp; zspost : SSA.SSA.ebexp }

  val zspre : zspec -> SSA.SSA.ebexp

  val zspost : zspec -> SSA.SSA.ebexp
 end
