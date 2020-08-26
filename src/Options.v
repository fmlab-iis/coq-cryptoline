

Record options : Set :=
  mkOptions {
      add_carry_constraints : bool;
      rewrite_assignments : bool;
      vars_cache_in_rewrite_assignments : bool
    }.

Definition default_options : options :=
  {| add_carry_constraints := false;
     rewrite_assignments := true;
     vars_cache_in_rewrite_assignments := true |}.
