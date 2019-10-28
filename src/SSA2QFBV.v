
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var.
From BitBlasting Require Import State QFBV.
From Cryptoline Require Import DSL SSA.

Import SSA.

(* Define the safety condition in terms of a QFBV expression *)
(* TODO: see bexp_program_safe in certified_qhasm_vcg/mqhasm/bvSSA2QFBV.v *)
Definition bexp_program_safe (p : program) : QFBV.bexp := QFBV.Btrue.
