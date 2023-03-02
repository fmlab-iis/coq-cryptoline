
open Arg
open Options.Std
open Ast.Cryptoline
open Extraction.Options0

type action = Verify | Parse | PrintSSA

let action = ref Verify

let vars_cache_in_rewriting = ref true

let args = [
    ("-disable_vars_cache_in_rewriting", Clear vars_cache_in_rewriting, "\n\t     Disable variables cache in rewriting\n");
    ("-jobs", Int (fun j -> jobs := j),
     "N    Set number of jobs (default = 4)\n");
    ("-p", Unit (fun () -> action := Parse), "\t     Print the parsed specification\n")
  ]@Common.args_parsing@Common.args_io@Common.args_verifier@Common.args_coqcryptoline
let args = List.sort (fun (argname1, _, _) (argname2, _, _) -> Stdlib.compare argname1 argname2) args

let usage = "Usage: coqcryptoline.exe OPTIONS FILE\n"

let parse_and_check file =
  let (vs, s) = Common.parse_and_check file in
  let vs = VS.of_list vs in
  let coq_spec = Translator.Visitor.visit_spec vs s in
  if Extraction.DSL.DSL.well_formed_spec coq_spec then (vs, s, coq_spec)
  else failwith ("The program is not well-formed.")

let anon file =
  let _ = print_endline ("Input: " ^ file) in
  let string_of_inputs vs = String.concat ", " (List.map (fun v -> string_of_typ v.vtyp ^ " " ^ string_of_var v) (VS.elements vs)) in
  let t1 = Unix.gettimeofday() in
  let _ = Random.self_init() in
  match !action with
  | Verify ->
      let (_vs, _s, coq_spec) = parse_and_check file in
	  (* options : bool, true to add carry constraints *)
	  let o = { add_carry_constraints = !carry_constraint;
                rewrite_assignments_arep = !apply_rewriting_arep;
                rewrite_assignments_imp = !apply_rewriting_imp;
                vars_cache_in_rewrite_assignments = !vars_cache_in_rewriting;
                compute_coefficients_one_by_one = !jobs <= 1;
                apply_slicing_espec = !apply_slicing_espec;
                apply_slicing_rspec = !apply_slicing_rspec;
                apply_slicing_assume = !apply_slicing_assume }
      in
	  let res = Extraction.Verify.verify_dsl o coq_spec in
      let t2 = Unix.gettimeofday() in
      let _ = print_endline ("Verification result:\t\t\t"
                             ^ (if res then "[OK]\t" else "[FAILED]") ^ "\t"
                             ^ string_of_running_time t1 t2) in
      if res then exit 0 else exit 1
  | Parse ->
      let (vs, s, _) = parse_and_check file in
      print_endline ("proc main(" ^ string_of_inputs vs ^ ") =");
      print_endline (string_of_spec s)
  | PrintSSA ->
      let (vs, s, _) = parse_and_check file in
      let vs = VS.of_list (List.map (ssa_var VM.empty) (VS.elements vs)) in
      let s = ssa_spec s in
      print_endline ("proc main(" ^ string_of_inputs vs ^ ") =");
      print_endline (string_of_spec s)
