
(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt.
From Coq Require Import Arith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun prime.
From ssrlib Require Import Var Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv.
From BBCache Require Import Cache.
From Cryptoline Require Import DSL SSA SSA2QFBV SSA2ZSSA Verify.
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
         DSL.string_of_var SSA.string_of_ssavar
         DSL.string_of_ebexp SSA.string_of_ebexp
         DSL.string_of_rbexp SSA.string_of_rbexp
         Poly.string_of_azbexp Poly.string_of_zpexpr
         (* Verification *)
         CNF.dimacs_cnf_with_header CNF.max_var_of_cnf CNF.num_clauses
         Poly.zpexpr_is_zero
         DSL.well_formed_spec Verify.verify_dsl.
Cd "../../..".
