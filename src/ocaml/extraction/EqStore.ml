open Bool
open EqFSets
open Equalities

type __ = Obj.t

module TStateEqmod =
 functor (X:EqOrder.EqOrder) ->
 functor (V:Typ) ->
 functor (Store:sig
  type t

  val acc : X.t -> t -> V.t

  val upd : X.t -> V.t -> t -> t

  val upd2 : X.t -> V.t -> X.t -> V.t -> t -> t
 end) ->
 functor (VS:EqFSet with module SE = X) ->
 struct
  module VSLemmas = FSetLemmas(VS)
 end
