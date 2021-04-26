
module ZSSA =
 struct
  type zspec = { zspre : SSA.SSA.ebexp; zspost : SSA.SSA.ebexp }

  (** val zspre : zspec -> SSA.SSA.ebexp **)

  let zspre z =
    z.zspre

  (** val zspost : zspec -> SSA.SSA.ebexp **)

  let zspost z =
    z.zspost
 end
