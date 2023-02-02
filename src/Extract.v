
(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt.
From Coq Require Import Arith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun prime.
From ssrlib Require Import Var Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv.
From BBCache Require Import Cache.
From Cryptoline Require Import DSL SSA SSA2QFBV SSA2ZSSA Verify VerifyFull.
From nbits Require Import NBits.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String Options.

Extract Constant Verify.ext_all_unsat => "External.ext_all_unsat_impl".
Extract Constant Verify.ext_solve_imp => "External.ext_solve_imp_impl".
Extract Constant Verify.ext_solve_imp_list => "External.ext_solve_imp_list_impl".

Cd "src/ocaml/extraction".
Separate Extraction
         (* Number conversion *)
         int_of_pos pos_of_int int_of_n n_of_int int_of_nat nat_of_int
         NBitsDef.from_Zpos NBitsDef.from_Zneg NBitsDef.from_Z
         (* String outputs *)
         QFBV.string_of_exp QFBV.string_of_bexp
         DSL.string_of_spec SSA.string_of_spec
         DSL.string_of_espec SSA.string_of_espec
         DSL.string_of_rspec SSA.string_of_rspec
         Poly.string_of_azbexp Poly.string_of_zpexpr
         (* Verification *)
         CNF.dimacs_cnf_with_header CNF.max_var_of_cnf CNF.num_clauses
         Poly.zpexpr_is_zero SSA.slice_espec SSA.slice_rspec
         SSA.split_espec SSA.split_rspec
         DSL.well_formed_spec Verify.verify_dsl
         VerifyFull.verify_fulldsl.
Cd "../../..".
