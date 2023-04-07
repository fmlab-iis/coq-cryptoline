
(** * Extraction of verification procedures *)

(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt.
From Coq Require Import Arith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun prime.
From ssrlib Require Import Var Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv.
From BBCache Require Import Cache.
From Cryptoline Require Import DSLLite SSALite DSL SSA SSA2QFBV SSA2REP VerifyLite Verify.
From nbits Require Import NBits.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String Options.

Extract Constant VerifyLite.ext_all_unsat => "External.ext_all_unsat_impl".
Extract Constant VerifyLite.ext_solve_imp => "External.ext_solve_imp_impl".
Extract Constant VerifyLite.ext_solve_imp_list => "External.ext_solve_imp_list_impl".

Cd "src/ocaml/extraction".
Separate Extraction
         (* Number conversion *)
         int_of_pos pos_of_int int_of_n n_of_int int_of_nat nat_of_int
         NBitsDef.from_Zpos NBitsDef.from_Zneg NBitsDef.from_Z
         (* String outputs *)
         QFBV.string_of_exp QFBV.string_of_bexp
         DSLLite.string_of_spec SSALite.string_of_spec
         DSLLite.string_of_espec SSALite.string_of_espec
         DSLLite.string_of_rspec SSALite.string_of_rspec
         DSL.string_of_spec SSA.string_of_spec
         REP.string_of_azbexp IMP.string_of_zpexpr
         (* Verification *)
         CNF.dimacs_cnf_with_header CNF.max_var_of_cnf CNF.num_clauses
         ZPoly.zpexpr_is_zero SSALite.slice_espec SSALite.slice_rspec
         SSALite.split_espec SSALite.split_rspec
         DSLLite.well_formed_spec DSL.well_formed_spec
         VerifyLite.verify_dsllite Verify.verify_dsl.
Cd "../../..".
