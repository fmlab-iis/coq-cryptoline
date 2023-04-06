open BinNat
open BinNums
open Bool
open Datatypes
open EqFMaps
open EqFSets
open Int0
open String0
open Strings
open Eqtype

type __ = Obj.t

type var = coq_N

module VarOrder =
 struct
  (** val coq_T : Equality.coq_type **)

  let coq_T =
    EqOrder.NOrderMinimal.t

  type t = Equality.sort

  (** val ltn : t -> t -> bool **)

  let ltn =
    EqOrder.NOrderMinimal.ltn

  (** val compare : t -> t -> t OrderedType.coq_Compare **)

  let compare =
    EqOrder.NOrderMinimal.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    EqOrder.NOrder.eq_dec

  (** val succ : t -> t **)

  let succ =
    Obj.magic N.succ

  (** val default : t **)

  let default =
    Obj.magic N0
 end

module VarOrderPrinter =
 struct
  type t = VarOrder.t

  (** val to_string : VarOrder.t -> char list **)

  let to_string v =
    append ('v'::[]) (string_of_N (Obj.magic v))
 end

module VS = MakeTreeSetWithNew(VarOrder)

module VM = MakeTreeMapWithNew(VarOrder)

module SSAVarOrder = EqOrder.MakeProdOrderWithDefaultSucc(VarOrder)(VarOrder)

module SSAVarOrderPrinter =
 struct
  type t = SSAVarOrder.t

  (** val to_string : SSAVarOrder.t -> char list **)

  let to_string v =
    append ('v'::[])
      (append (string_of_N (fst (Obj.magic v)))
        (append ('_'::[]) (string_of_N (snd (Obj.magic v)))))
 end

type ssavar = SSAVarOrder.t

module SSAVS = MakeTreeSetWithNew(SSAVarOrder)

module SSAVM = MakeTreeMapWithNew(SSAVarOrder)
