

Record options : Set :=
  mkOptions {
      add_carry_constraints : bool;
      rewrite_assignments : bool
    }.

Definition default_options : options :=
  {| add_carry_constraints := false;
     rewrite_assignments := true |}.
