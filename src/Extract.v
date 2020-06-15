
(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
(* From Coq Require Import ExtrOcamlZInt ExtrOcamlIntConv. *)
From Coq Require Import Arith List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun prime.
From ssrlib Require Import Var Tactics Seqs.
From BitBlasting Require Import State QFBV TypEnv.
From Cryptoline Require Import DSL SSA SSA2QFBV SSA2ZSSA.
From nbits Require Import NBits.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/ocaml/extraction".
Separate Extraction
         DSL.well_formed_spec DSL.rspec_of_spec DSL.espec_of_spec
         SSA.ssa_spec
         SSA2QFBV.bexp_of_rspec SSA2QFBV.qfbv_bexp_spec .
Cd "../../..".
