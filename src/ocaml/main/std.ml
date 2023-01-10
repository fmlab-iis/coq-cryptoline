
open Arg
open Options.Std
open Ast.Cryptoline
open Parsers.Std
open Extraction.Options0

type action = Verify | Parse | PrintSSA

let action = ref Verify

let vars_cache_in_rewriting = ref true

let args = [
    ("-disable_vars_cache_in_rewriting", Clear vars_cache_in_rewriting, "\n\t     Disable variables cache in rewriting\n");
    ("-jobs", Int (fun j -> jobs := j),
     "N    Set number of jobs (default = 4)\n");
    ("-p", Unit (fun () -> action := Parse), "\t     Print the parsed specification\n");
    ("-v", Set verbose, "\t     Display verbose messages\n")
  ]@Common.args
let args = List.sort Pervasives.compare args

let usage = "Usage: coqcryptoline.exe OPTIONS FILE\n"

let parse_spec file =
  let t1 = Unix.gettimeofday() in
  let _ = vprint ("Parsing Cryptoline file:\t\t") in
  try
    let spec = spec_from_file file in
    let t2 = Unix.gettimeofday() in
    let _ = vprintln ("[OK]\t\t" ^ string_of_running_time t1 t2) in
    spec
  with ex ->
    let t2 = Unix.gettimeofday() in
    let _ = vprintln ("[FAILED]\t" ^ string_of_running_time t1 t2) in
    raise ex

let parse_program file =
  let t1 = Unix.gettimeofday() in
  let _ = vprint ("Parsing Cryptoline file: ") in
  try
    let p = program_from_file file in
    let t2 = Unix.gettimeofday() in
    let _ = vprintln ("[OK]\t\t" ^ string_of_running_time t1 t2) in
    p
  with ex ->
    let t2 = Unix.gettimeofday() in
    let _ = vprintln ("[FAILED]\t" ^ string_of_running_time t1 t2) in
    raise ex

let check_well_formedness vs s =
  let t1 = Unix.gettimeofday() in
  let _ = vprint ("Checking well-formedness:\t\t") in
  let ropt = illformed_spec_reason vs s in
  let wf = ropt = None in
  let t2 = Unix.gettimeofday() in
  let _ = vprintln ((if wf then "[OK]\t" else "[FAILED]") ^ "\t" ^ string_of_running_time t1 t2) in
  let _ =
    match ropt with
    | Some (IllPrecondition e, r) -> vprintln("Ill-formed precondition: " ^ string_of_bexp e ^ ".\nReason: " ^ r)
    | Some (IllInstruction i, r) -> vprintln("Ill-formed instruction: " ^ string_of_instr i ^ ".\nReason: " ^ r)
    | Some (IllPostcondition e, r) -> vprintln("Ill-formed postcondition: " ^ string_of_bexp e ^ ".\nReason: " ^ r)
    | _ -> () in
  wf

let anon file =
  let string_of_inputs vs = String.concat ", " (List.map (fun v -> string_of_typ v.vtyp ^ " " ^ string_of_var v) (VS.elements vs)) in
  let parse_and_check file =
    let (vs, s) = parse_spec file in
    let coq_spec = Translator.Visitor.visit_spec vs s in
     if Extraction.DSL.DSL.well_formed_spec coq_spec then (vs, s, coq_spec)
     else failwith ("The program is not well-formed.") in
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
