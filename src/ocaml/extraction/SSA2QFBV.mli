open NBitsDef
open Typ
open Var
open Eqtype
open Seq
open Ssrnat

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

val qfbv_atom : SSA.SSA.atom -> QFBV.QFBV.exp

val bexp_instr : TypEnv.SSATE.env -> SSA.SSA.instr -> QFBV.QFBV.bexp

val bexp_program : TypEnv.SSATE.env -> SSA.SSA.program -> QFBV.QFBV.bexp list

type bexp_spec = { binputs : TypEnv.SSATE.env; bpre : QFBV.QFBV.bexp;
                   bprog : QFBV.QFBV.bexp list; bpost : QFBV.QFBV.bexp }

val bexp_of_rspec : TypEnv.SSATE.env -> SSA.SSA.rspec -> bexp_spec

val rngred_rspec_split_la : SSA.SSA.spec -> QFBV.QFBV.bexp list

val bexp_atom_uaddB_algsnd : SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_saddB_algsnd : SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_addB_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_adds_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_uadcB_algsnd :
  int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_sadcB_algsnd :
  int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_adcB_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
  QFBV.QFBV.bexp

val bexp_atom_adcs_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
  QFBV.QFBV.bexp

val bexp_atom_usubB_algsnd : SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_ssubB_algsnd : SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_subB_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_subc_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_subb_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_usbbB_algsnd :
  int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_ssbbB_algsnd :
  int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_sbbB_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
  QFBV.QFBV.bexp

val bexp_atom_sbbs_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
  QFBV.QFBV.bexp

val bexp_atom_usbcB_algsnd :
  int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_ssbcB_algsnd :
  int -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_sbcB_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
  QFBV.QFBV.bexp

val bexp_atom_sbcs_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> SSA.SSA.atom ->
  QFBV.QFBV.bexp

val bexp_atom_mulB_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_atom_shl_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> int -> QFBV.QFBV.bexp

val bexp_atom_cshl_algsnd :
  TypEnv.SSATE.env -> SSA.SSA.atom -> SSA.SSA.atom -> int -> QFBV.QFBV.bexp

val bexp_atom_vpc_algsnd :
  TypEnv.SSATE.env -> typ -> SSA.SSA.atom -> QFBV.QFBV.bexp

val bexp_instr_algsnd : TypEnv.SSATE.env -> SSA.SSA.instr -> QFBV.QFBV.bexp

val bexp_program_algsnd_split_fixed_final_rec :
  TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> SSA.SSA.instr list ->
  (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list

val bexp_program_algsnd_split_fixed_final :
  TypEnv.SSATE.env -> SSA.SSA.instr list -> (QFBV.QFBV.bexp
  list * QFBV.QFBV.bexp) list
