
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From ssrlib Require Import Var Types SsrOrder ZAriths Store Tactics.
From BitBlasting Require Import State.
From Cryptoline Require Import DSL SSA ZSSA.

Import DSL.

(* Convert a bit-vector program to an integer program *)
(* TODO: see bv2z_program in certified_qhasm_vcg/mqhasm/bvSSA2zSSA.v *)
Definition bv2z_program (tmp : N) (idx : N) (p : program) : N * ZSSA.zprogram :=
  (tmp, [::]).
