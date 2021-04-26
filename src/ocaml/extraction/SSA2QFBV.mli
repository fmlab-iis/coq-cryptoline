open NBitsDef
open Typ
open Var
open Eqtype
open Seq
open Ssrnat

val qfbv_atomic : SSA.SSA.atomic -> QFBV.QFBV.exp

val qfbv_true : QFBV.QFBV.bexp

val qfbv_var : SSAVarOrder.t -> QFBV.QFBV.exp

val qfbv_const : int -> int -> QFBV.QFBV.exp

val qfbv_zero : int -> QFBV.QFBV.exp

val qfbv_one : int -> QFBV.QFBV.exp

val qfbv_not : QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_neg : QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_high : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_low : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_zext : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_sext : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_and : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_or : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_xor : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_add : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_sub : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_mul : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_mod : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_srem : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_smod : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_shl : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_lshr : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_ashr : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_concat : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val qfbv_eq : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_ult : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_ule : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_ugt : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_uge : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_slt : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_sle : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_sgt : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_sge : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_uaddo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_usubo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_umulo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_saddo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_ssubo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_smulo : QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.bexp

val qfbv_lneg : QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val qfbv_conj : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val qfbv_disj : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val qfbv_imp : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val exp_rexp : SSA.SSA.rexp -> QFBV.QFBV.exp

val bexp_rbexp : SSA.SSA.rbexp -> QFBV.QFBV.bexp

val qfbv_conjs_rec : QFBV.QFBV.bexp -> QFBV.QFBV.bexp list -> QFBV.QFBV.bexp

val qfbv_conjs_la : QFBV.QFBV.bexp list -> QFBV.QFBV.bexp

val bexp_instr : TypEnv.SSATE.env -> SSA.SSA.instr -> QFBV.QFBV.bexp

val bexp_program : TypEnv.SSATE.env -> SSA.SSA.program -> QFBV.QFBV.bexp list

type bexp_spec = { binputs : TypEnv.SSATE.env; bpre : QFBV.QFBV.bexp;
                   bprog : QFBV.QFBV.bexp list; bpost : QFBV.QFBV.bexp }

val bexp_of_rspec : TypEnv.SSATE.env -> SSA.SSA.rspec -> bexp_spec

val qfbv_bexp_spec_split_la : SSA.SSA.spec -> QFBV.QFBV.bexp list

val bexp_atomic_uaddB_safe :
  SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_saddB_safe :
  SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_addB_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_adds_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_uadcB_safe :
  int -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_sadcB_safe :
  int -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_adcB_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic ->
  QFBV.QFBV.bexp

val bexp_atomic_adcs_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic ->
  QFBV.QFBV.bexp

val bexp_atomic_usubB_safe :
  SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_ssubB_safe :
  SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_subB_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_subc_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_subb_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_usbbB_safe :
  int -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_ssbbB_safe :
  int -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_sbbB_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic ->
  QFBV.QFBV.bexp

val bexp_atomic_sbbs_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic ->
  QFBV.QFBV.bexp

val bexp_atomic_usbcB_safe :
  int -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_ssbcB_safe :
  int -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_sbcB_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic ->
  QFBV.QFBV.bexp

val bexp_atomic_sbcs_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> SSA.SSA.atomic ->
  QFBV.QFBV.bexp

val bexp_atomic_mulB_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_atomic_shl_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> int -> QFBV.QFBV.bexp

val bexp_atomic_cshl_safe :
  TypEnv.SSATE.env -> SSA.SSA.atomic -> SSA.SSA.atomic -> int ->
  QFBV.QFBV.bexp

val bexp_atomic_vpc_safe :
  TypEnv.SSATE.env -> typ -> SSA.SSA.atomic -> QFBV.QFBV.bexp

val bexp_instr_safe : TypEnv.SSATE.env -> SSA.SSA.instr -> QFBV.QFBV.bexp

val bexp_program_safe_split_fixed_final_rec :
  TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> SSA.SSA.instr list ->
  (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list

val bexp_program_safe_split_fixed_final :
  TypEnv.SSATE.env -> SSA.SSA.instr list -> (QFBV.QFBV.bexp
  list * QFBV.QFBV.bexp) list
