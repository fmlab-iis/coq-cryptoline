(* open Big_int *)
(* open Set *)
open Options.Std
(* open Ast.Cryptoline *)
open Common
(* open Lwt.Infix *)

type result = Common.result

type exp = Common.exp

type bexp = Common.bexp

let string_of_exp = Common.string_of_exp
let string_of_bexp = Common.string_of_bexp

let run_minisat ?timeout:timeout ifile ofile errfile =
  let t1 = Unix.gettimeofday() in
  let timeoutarg =
    match timeout with
    | None -> ""
    | Some t -> "-cpu-lim=" ^ string_of_int t in
  let cmd =
    !minisat_path ^ " -verb=0 " ^ timeoutarg ^ " " ^ !smt_args ^ " "
    ^ "\"" ^ ifile ^ "\" 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\"" in
  let _ = trace ("Run Minisat with command: " ^ cmd) in
  unix cmd;
  let t2 = Unix.gettimeofday() in
  trace ("Execution time of Minisat: " ^ string_of_float (t2 -. t1) ^ " seconds");
  trace "OUTPUT FROM Minisat:";
  unix ("cat " ^ ofile ^ " >>  " ^ !logfile);
  unix ("cat " ^ errfile ^ " >>  " ^ !logfile);
  trace ""

let run_cryptominisat ?timeout:timeout ifile ofile errfile =
  let t1 = Unix.gettimeofday() in
  let timeoutarg =
    match timeout with
    | None -> ""
    | Some t -> "--maxtime " ^ string_of_int t in
  let cmd =
    !cryptominisat_path ^ " --verb 0 " ^ timeoutarg ^ " " ^ !smt_args ^ " "
    ^ "\"" ^ ifile ^ "\" 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\"" in
  let _ = trace ("Run Cryptominisat with command: " ^ cmd) in
  unix cmd;
  let t2 = Unix.gettimeofday() in
  trace ("Execution time of Cryptominisat: " ^ string_of_float (t2 -. t1) ^ " seconds");
  trace "OUTPUT FROM Cryptominisat:";
  unix ("cat " ^ ofile ^ " >>  " ^ !logfile);
  unix ("cat " ^ errfile ^ " >>  " ^ !logfile);
  trace ""

let read_minisat_output file =
  (* read the output *)
  let line = ref "" in
  let ch = open_in file in
  let _ =
    try
      while true do
        let _ = line := input_line ch in
        if Str.string_match (Str.regexp "WARNING:") !line 0 then ()
        else raise End_of_file
      done
    with End_of_file -> ()
       | _ ->
          fail "Failed to read the output file. Please check the log file for error messages."
  in
  let _ = close_in ch in
  (* parse the output *)
  let res = String.trim !line in
  if res = "UNSATISFIABLE" then Unsat
  else if res = "SATISFIABLE" then Sat
  else if res = "Terminated: 15" then raise TimeoutException
  else if res = "INDETERMINATE" then raise TimeoutException
  else if res = "*** INTERRUPTED ***" then raise TimeoutException
  else failwith ("Unknown result from Minisat: " ^ res)

let read_cryptominisat_output file =
  (* read the output *)
  let line = ref "" in
  let ch = open_in file in
  let _ =
    try
      while true do
        let _ = line := input_line ch in
        if Str.string_match (Str.regexp "s \\(SATISFIABLE\\|UNSATISFIABLE\\)") !line 0 then
          raise End_of_file
      done
    with End_of_file -> ()
       | _ ->
          fail "Failed to read the output file. Please check the log file for error messages."
  in
  let _ = close_in ch in
  (* parse the output *)
  let res = String.trim !line in
  if res = "s UNSATISFIABLE" then Unsat
  else if res = "s SATISFIABLE" then Sat
  else if res = "s INDETERMINATE" then raise TimeoutException
  else failwith ("Unknown result from Cryptominisat: " ^ res)

(**
 * Solve the implication e1 /\ e2 /\ ... /\ en -> e wheren fs = [e1; e2; ...; en; e].
 * Throw TimeoutException if timeout.
*)
let solve_simp ?timeout:timeout fs =
  let ifile = Filename.temp_file "inputqfbv_" "" in
  let ofile = Filename.temp_file "outputqfbv_" "" in
  let errfile = Filename.temp_file "errorqfbv_" "" in
  let res =
    match !smt_solver with
    | Minisat ->
       let ch = open_out ifile in
       let _ = cnf_imp_check_sat ch fs in
       let _ =
         match timeout with
         | None -> run_minisat ifile ofile errfile
         | Some ti -> run_minisat ~timeout:ti ifile ofile errfile in
       read_minisat_output ofile
    | Cryptominisat ->
       let ch = open_out ifile in
       let _ = cnf_imp_check_sat ch fs in
       let _ =
         match timeout with
         | None -> run_cryptominisat ifile ofile errfile
         | Some ti -> run_cryptominisat ~timeout:ti ifile ofile errfile in
       read_cryptominisat_output ofile
  in
  let _ = Unix.unlink ifile in
  let _ = Unix.unlink ofile in
  let _ = Unix.unlink errfile in
  res

