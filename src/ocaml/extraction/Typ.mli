open Bool
open Eqtype
open Ssrnat

type typ =
| Tuint of int
| Tsint of int

val sizeof_typ : typ -> int

val typ_eqn : typ -> typ -> bool

val typ_eqP : typ -> typ -> reflect

val typ_eqMixin : typ Equality.mixin_of

val typ_eqType : Equality.coq_type

val coq_Tbit : typ

val is_unsigned : typ -> bool

val unsigned_typ : typ -> typ

val double_typ : typ -> typ

val compatible : typ -> typ -> bool
