

Record options : Set :=
  mkOptions {
      (* true to add carry constraints to polynomial specifications *)
      add_carry_constraints : bool;
      (* true to rewrite assignments in atomic root entailment problems *)
      rewrite_assignments_arep : bool;
      (* true to rewrite assignments in ideal membership problems *)
      rewrite_assignments_imp : bool;
      (* true to use variable cache in rewriting assignments *)
      vars_cache_in_rewrite_assignments : bool;
      (* true to send polynomial specifications to external OCaml code one by one *)
      compute_coefficients_one_by_one : bool
    }.

Definition default_options : options :=
  {| add_carry_constraints := false;
     rewrite_assignments_arep := false;
     rewrite_assignments_imp := true;
     vars_cache_in_rewrite_assignments := true;
     compute_coefficients_one_by_one := false |}.
