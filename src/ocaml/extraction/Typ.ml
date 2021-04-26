open Bool
open Eqtype
open Ssrnat

let __ = let rec f _ = Obj.repr f in Obj.repr f

type typ =
| Tuint of int
| Tsint of int

(** val sizeof_typ : typ -> int **)

let sizeof_typ = function
| Tuint w -> w
| Tsint w -> w

(** val typ_eqn : typ -> typ -> bool **)

let typ_eqn x y =
  match x with
  | Tuint wx ->
    (match y with
     | Tuint wy -> eq_op nat_eqType (Obj.magic wx) (Obj.magic wy)
     | Tsint _ -> false)
  | Tsint wx ->
    (match y with
     | Tuint _ -> false
     | Tsint wy -> eq_op nat_eqType (Obj.magic wx) (Obj.magic wy))

(** val typ_eqP : typ -> typ -> reflect **)

let typ_eqP x y =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if typ_eqn x y then _evar_0_ __ else _evar_0_0 __

(** val typ_eqMixin : typ Equality.mixin_of **)

let typ_eqMixin =
  { Equality.op = typ_eqn; Equality.mixin_of__1 = typ_eqP }

(** val typ_eqType : Equality.coq_type **)

let typ_eqType =
  Obj.magic typ_eqMixin

(** val coq_Tbit : typ **)

let coq_Tbit =
  Tuint (Pervasives.succ 0)

(** val is_unsigned : typ -> bool **)

let is_unsigned = function
| Tuint _ -> true
| Tsint _ -> false

(** val unsigned_typ : typ -> typ **)

let unsigned_typ = function
| Tuint w -> Tuint w
| Tsint w -> Tuint w

(** val double_typ : typ -> typ **)

let double_typ = function
| Tuint w -> Tuint (muln (Pervasives.succ (Pervasives.succ 0)) w)
| Tsint w -> Tsint (muln (Pervasives.succ (Pervasives.succ 0)) w)

(** val compatible : typ -> typ -> bool **)

let compatible t1 t2 =
  eq_op nat_eqType (Obj.magic sizeof_typ t1) (Obj.magic sizeof_typ t2)
