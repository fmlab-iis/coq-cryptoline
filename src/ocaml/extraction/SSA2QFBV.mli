open DSLRaw
open NBitsDef
open NBitsOp
open Options0
open Seqs
open Typ
open Eqtype
open Seq
open Ssrnat

type bexp_spec = { binputs : TypEnv.SSATE.env; bpre : QFBV.QFBV.bexp;
                   bprog : QFBV.QFBV.bexp list; bpost : QFBV.QFBV.bexp }

val exp_rexp : SSALite.SSALite.rexp -> QFBV.QFBV.exp

val bexp_rbexp : SSALite.SSALite.rbexp -> QFBV.QFBV.bexp

val qfbv_atom : atom -> QFBV.QFBV.exp

val bexp_instr : TypEnv.SSATE.env -> SSALite.SSALite.instr -> QFBV.QFBV.bexp

val bexp_program :
  TypEnv.SSATE.env -> SSALite.SSALite.program -> QFBV.QFBV.bexp list

val bexp_of_rspec : TypEnv.SSATE.env -> SSALite.SSALite.rspec -> bexp_spec

val rngred_rspec_split_la : SSALite.SSALite.rspec -> QFBV.QFBV.bexp list

val rngred_rspec_split_las : SSALite.SSALite.rspec list -> QFBV.QFBV.bexp list

val rngred_rspec_slice_split_la :
  options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list

val bexp_atom_uaddB_algsnd : atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_saddB_algsnd : atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_addB_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_adds_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_uadcB_algsnd : int -> atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_sadcB_algsnd : int -> atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_adcB_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_adcs_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_usubB_algsnd : atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_ssubB_algsnd : atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_subB_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_subc_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_subb_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_usbbB_algsnd : int -> atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_ssbbB_algsnd : int -> atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_sbbB_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_sbbs_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_usbcB_algsnd : int -> atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_ssbcB_algsnd : int -> atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_sbcB_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_sbcs_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_mulB_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> QFBV.QFBV.bexp

val bexp_atom_shl_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> int -> QFBV.QFBV.bexp

val bexp_atom_cshl_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.atom -> atom -> int -> QFBV.QFBV.bexp

val bexp_atom_vpc_algsnd :
  TypEnv.SSATE.env -> typ -> SSALite.SSALite.atom -> QFBV.QFBV.bexp

val bexp_instr_algsnd :
  TypEnv.SSATE.env -> SSALite.SSALite.instr -> QFBV.QFBV.bexp

val bexp_program_algsnd_split_fixed_final_rec :
  TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> SSALite.SSALite.instr list ->
  (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list

val bexp_program_algsnd_split_fixed_final :
  TypEnv.SSATE.env -> SSALite.SSALite.instr list -> (QFBV.QFBV.bexp
  list * QFBV.QFBV.bexp) list

val qfbv_spec_algsnd_la_rec :
  QFBV.QFBV.bexp -> (QFBV.QFBV.bexp list * QFBV.QFBV.bexp) list ->
  QFBV.QFBV.bexp list

val qfbv_spec_algsnd_la : SSALite.SSALite.rspec -> QFBV.QFBV.bexp list

val make_sndcond :
  options -> TypEnv.SSATE.env -> SSALite.SSALite.rbexp ->
  SSALite.SSALite.instr list -> SSALite.SSALite.instr -> QFBV.QFBV.bexp

val algsnd_slice_la_rec :
  options -> TypEnv.SSATE.env -> SSALite.SSALite.program ->
  SSALite.SSALite.rbexp -> SSALite.SSALite.program -> QFBV.QFBV.bexp list

val algsnd_slice_la : options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list

val rngred_algsnd_split_la : SSALite.SSALite.rspec -> QFBV.QFBV.bexp list

val rngred_algsnd_slice_split_la :
  options -> SSALite.SSALite.rspec -> QFBV.QFBV.bexp list
