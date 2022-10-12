

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
      compute_coefficients_one_by_one : bool;
      (* true to apply slicing to algebraic specifications *)
      apply_slicing_espec : bool;
      (* true to apply slicing to range specifications (both in range reduction and algebraic soundness) *)
      apply_slicing_rspec : bool
    }.

Definition default_options : options :=
  {|
    add_carry_constraints := false;
    rewrite_assignments_arep := true;
    rewrite_assignments_imp := true;
    vars_cache_in_rewrite_assignments := true;
    compute_coefficients_one_by_one := false;
    apply_slicing_espec := true;
    apply_slicing_rspec := true
  |}.
