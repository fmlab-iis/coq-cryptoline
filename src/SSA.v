
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq ssrfun.
From BitBlasting Require Import Typ Var TypEnv State.
From ssrlib Require Import SsrOrdered FMaps ZAriths Tactics.
From Cryptoline Require Import Cryptoline.

(* A map from a variable to its current index *)
Definition vmap : Type := VM.t N.

Definition empty_vmap : vmap := VM.empty N.

Definition initial_index : N := 0.

Definition first_assigned_index : N := 1.

(* Find the current index of a variable *)
Definition get_index (v : var) (m : vmap) : N :=
  match VM.find v m with
  | None => initial_index
  | Some i => i
  end.

(* Increment the current index of a variable *)
Definition upd_index (v : var) (m : vmap) : vmap :=
  match VM.find v m with
  | None => VM.add v first_assigned_index m
  | Some i => VM.add v (i + 1)%num m
  end.

Definition ssa_var (m : vmap) (v : var) : var :=
  {| vname := vname v; vidx := get_index v m |}.

Definition ssa_atomic (m : vmap) (a : atomic) : atomic :=
  match a with
  | Avar v => Avar (ssa_var m v)
  | Aconst ty n => Aconst ty n
  end.

(* TODO: Define SSA translation *)
Definition ssa_instr (m : vmap) (i : instr) : vmap * instr :=
  match i with
  | Imov v a =>
    let a := ssa_atomic m a in
    let m := upd_index v m in
    (m, Imov (ssa_var m v) a)
  | _ => (m, i)
  end.

(* TODO: Define SSA translation *)
Definition ssa_program (m : vmap) (p : program) : vmap * program := (m, p).

(* TODO: Define SSA translation *)
Definition ssa_spec (s : spec) : spec := s.


(* TODO: Check if all variables in a program are not indexed. *)
Definition unindexed_program (p : program) : bool := true.
