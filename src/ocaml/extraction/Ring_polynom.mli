open BinInt
open BinNums
open BinPos
open Datatypes

type 'c coq_Pol =
| Pc of 'c
| Pinj of positive * 'c coq_Pol
| PX of 'c coq_Pol * positive * 'c coq_Pol

val coq_P0 : 'a1 -> 'a1 coq_Pol

val coq_P1 : 'a1 -> 'a1 coq_Pol

val coq_Peq : ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1 coq_Pol -> bool

val mkPinj : positive -> 'a1 coq_Pol -> 'a1 coq_Pol

val mkPinj_pred : positive -> 'a1 coq_Pol -> 'a1 coq_Pol

val mkPX :
  'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol ->
  'a1 coq_Pol

val mkXi : 'a1 -> 'a1 -> positive -> 'a1 coq_Pol

val mkX : 'a1 -> 'a1 -> 'a1 coq_Pol

val coq_Popp : ('a1 -> 'a1) -> 'a1 coq_Pol -> 'a1 coq_Pol

val coq_PaddC : ('a1 -> 'a1 -> 'a1) -> 'a1 coq_Pol -> 'a1 -> 'a1 coq_Pol

val coq_PsubC : ('a1 -> 'a1 -> 'a1) -> 'a1 coq_Pol -> 'a1 -> 'a1 coq_Pol

val coq_PaddI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 coq_Pol -> 'a1 coq_Pol -> 'a1 coq_Pol) -> 'a1
  coq_Pol -> positive -> 'a1 coq_Pol -> 'a1 coq_Pol

val coq_PsubI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 coq_Pol -> 'a1 coq_Pol -> 'a1
  coq_Pol) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol -> 'a1 coq_Pol

val coq_PaddX :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 coq_Pol -> 'a1 coq_Pol -> 'a1 coq_Pol)
  -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol -> 'a1 coq_Pol

val coq_PsubX :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 coq_Pol -> 'a1 coq_Pol
  -> 'a1 coq_Pol) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol -> 'a1 coq_Pol

val coq_Padd :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1
  coq_Pol -> 'a1 coq_Pol

val coq_Psub :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
  -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1 coq_Pol -> 'a1 coq_Pol

val coq_PmulC_aux :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1 ->
  'a1 coq_Pol

val coq_PmulC :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol ->
  'a1 -> 'a1 coq_Pol

val coq_PmulI :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 coq_Pol
  -> 'a1 coq_Pol -> 'a1 coq_Pol) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol ->
  'a1 coq_Pol

val coq_Pmul :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 coq_Pol -> 'a1 coq_Pol -> 'a1 coq_Pol

type coq_Mon =
| Coq_mon0
| Coq_zmon of positive * coq_Mon
| Coq_vmon of positive * coq_Mon

val mkZmon : positive -> coq_Mon -> coq_Mon

val zmon_pred : positive -> coq_Mon -> coq_Mon

val coq_CFactor :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1 coq_Pol ->
  'a1 -> 'a1 coq_Pol * 'a1 coq_Pol

val coq_MFactor :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1
  coq_Pol -> 'a1 -> coq_Mon -> 'a1 coq_Pol * 'a1 coq_Pol

val coq_POneSubst :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1 coq_Pol -> ('a1 * coq_Mon) -> 'a1
  coq_Pol -> 'a1 coq_Pol option

val coq_PNSubst1 :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1 coq_Pol -> ('a1 * coq_Mon) -> 'a1
  coq_Pol -> int -> 'a1 coq_Pol

val coq_PNSubst :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1 coq_Pol -> ('a1 * coq_Mon) -> 'a1
  coq_Pol -> int -> 'a1 coq_Pol option

val coq_PSubstL1 :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1 coq_Pol -> (('a1 * coq_Mon) * 'a1
  coq_Pol) list -> int -> 'a1 coq_Pol

val coq_PSubstL :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1 coq_Pol -> (('a1 * coq_Mon) * 'a1
  coq_Pol) list -> int -> 'a1 coq_Pol option

val coq_PNSubstL :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> 'a1 * 'a1) -> 'a1 coq_Pol -> (('a1 * coq_Mon) * 'a1
  coq_Pol) list -> int -> int -> 'a1 coq_Pol

type 'c coq_PExpr =
| PEO
| PEI
| PEc of 'c
| PEX of positive
| PEadd of 'c coq_PExpr * 'c coq_PExpr
| PEsub of 'c coq_PExpr * 'c coq_PExpr
| PEmul of 'c coq_PExpr * 'c coq_PExpr
| PEopp of 'c coq_PExpr
| PEpow of 'c coq_PExpr * coq_N

val mk_X : 'a1 -> 'a1 -> positive -> 'a1 coq_Pol

val coq_Ppow_pos :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 coq_Pol -> 'a1 coq_Pol) -> 'a1 coq_Pol -> 'a1 coq_Pol ->
  positive -> 'a1 coq_Pol

val coq_Ppow_N :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 coq_Pol -> 'a1 coq_Pol) -> 'a1 coq_Pol -> coq_N -> 'a1 coq_Pol

val norm_aux :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1 coq_Pol

val norm_subst :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> 'a1 * 'a1)
  -> int -> (('a1 * coq_Mon) * 'a1 coq_Pol) list -> 'a1 coq_PExpr -> 'a1
  coq_Pol
