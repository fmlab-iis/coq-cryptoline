
open Arg
open Options.Std
open Ast.Cryptoline
open Parsers.Std

type action = VerifyESpec | VerifyRSpec | VerifySafety

let action = ref VerifyESpec

let parse_action str =
  if str = "vespec" then action := VerifyESpec
  else if str = "vrspec" then action := VerifyRSpec
  else if str = "vsafety" then action := VerifySafety
  else failwith("Unknown command: " ^ str)

let instr_index = ref 0

let args =
  [
    ("-c", String (fun str -> parse_action str), "CMD\t\t Specify the command to be executed");
    ("-instr", Int (fun i -> instr_index := i), "N\t\t Specify the n-th instruction in safety checking")
  ]@Common.args
let args = List.sort Pervasives.compare args

let usage = "Usage: cv_cli -c CMD OPTIONS FILE"

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
  let _ = Random.self_init() in
  (* Always use a single thread *)
  let _ = Options.Std.jobs := 1 in
  match !action with
  | VerifyESpec ->
     let _spec = espec_from_file file in
     let res = failwith "withCli 0" in
     (*
     let vgen = Verify.Std.vgen_of_espec spec in
     let res = Verify.Std.verify_espec_single_conjunct vgen spec in
      *)
     print_endline (string_of_bool res)
  | VerifyRSpec ->
     let _spec = rspec_from_file file in
     let res = failwith "withCli 1" in
     (*
     let res = Verify.Std.verify_rspec_single_conjunct spec in
      *)
     print_endline (string_of_bool res)
  | VerifySafety ->
     let _spec = rspec_from_file file in
     failwith "withCli 2"
     (*
     try
       (match Verify.Std.verify_instruction_safety !Options.Std.incremental_safety_timeout spec.rspre spec.rsprog !instr_index with
       | Verify.Common.Solved Qfbv.Common.Sat -> print_endline "sat"
       | Verify.Common.Solved Qfbv.Common.Unsat -> print_endline "unsat"
       | Verify.Common.Solved Qfbv.Common.Unknown -> print_endline "unknown"
       | _ -> failwith "Unfinished tasks. Should not happen!")
     with Qfbv.Common.TimeoutException ->
       print_endline "timeout"
      *)
(*
let _ =
  parse args anon usage
*)
