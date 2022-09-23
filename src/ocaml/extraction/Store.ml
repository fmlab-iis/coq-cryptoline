open Bool
open Equalities
open FSets

type __ = Obj.t

module TStateEqmod =
 functor (X:SsrOrder.SsrOrder) ->
 functor (V:Typ) ->
 functor (Store:sig
  type t

  val acc : X.t -> t -> V.t

  val upd : X.t -> V.t -> t -> t

  val upd2 : X.t -> V.t -> X.t -> V.t -> t -> t
 end) ->
 functor (VS:SsrFSet with module SE = X) ->
 struct
  module VSLemmas = FSetLemmas(VS)
 end
