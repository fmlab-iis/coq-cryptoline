open Datatypes
open BinNums
open CNF
open Poly
open Ring_polynom
open ExtrOcamlIntConv
open Var
open ZAriths
open FSets

open Options.Std

exception ParseError of string

let keep_temp_files = ref false
let temp_file_prefix = "coqcryptoline_temp"
let use_fork = ref false

(** Basic numbers conversion *)

let string_of_bits bs =
  String.concat "" (List.map (fun b -> if b then "1" else "0") (List.rev bs))

let explode s = List.init (String.length s) (String.get s)

(*
let nat_of_z z = nat_of_int (Z.to_int z)

let z_of_nat n = Z.of_int (int_of_nat n)
*)

let bits_of_z size z =
  let binstr =
    if z >= Z.zero then
      Z.format ("%0" ^ (string_of_int size) ^ "b") z
    else
      Z.format ("%0" ^ (string_of_int size) ^ "b")
        (Z.add (Z.pow (Z.of_int 2) size) z) in
  let rec helper i max str res =
    if i >= max then res
    else match String.get str i with
    | '0' -> helper (succ i) max str (false::res)
    | '1' -> helper (succ i) max str (true::res)
    | _ -> assert false in
  helper 0 (String.length binstr) binstr []

let pos_of_z z =
  let str = Z.format "b" z in
  let str = String.sub str 1 (String.length str - 1) in
  List.fold_left (
  fun p c ->
	if c = '1' then Coq_xI p
	else Coq_xO p) Coq_xH (explode str)

let rec z_of_pos n =
  match n with
  | Coq_xH -> Z.succ Z.zero
  | Coq_xO p -> Z.shift_left (z_of_pos p) 1
  | Coq_xI p -> Z.succ (Z.shift_left (z_of_pos p) 1)

let coq_z_of_z z =
  if Z.equal z Z.zero then Z0
  else if Z.lt z Z.zero then Zneg (pos_of_z (Z.neg z))
  else Zpos (pos_of_z z)

let z_of_coq_z n =
  match n with
  | Z0 -> Z.zero
  | Zpos p -> z_of_pos p
  | Zneg p -> Z.neg (z_of_pos p)



(** Verify a sequence of Coq CNFs *)

(* ===== Output to DIMACS ===== *)

let coq_string_of_literal l =
  match l with
  | CNF.Pos v -> string_of_int (int_of_pos v)
  | CNF.Neg v -> "-" ^ string_of_int (int_of_pos v)

let coq_output_clause ch c = output_string ch (String.concat " " (List.map coq_string_of_literal c) ^ " 0")

let coq_output_cnf ch cs = List.iter (fun c -> coq_output_clause ch c; output_string ch "\n") cs

let coq_output_dimacs ch cs =
  let nvars = int_of_pos (CNF.max_var_of_cnf cs) in
  let nclauses = int_of_n (CNF.num_clauses cs) in
  let _ = output_string ch ("p cnf " ^ string_of_int nvars ^ " " ^ string_of_int nclauses ^ "\n") in
  let _ = coq_output_cnf ch cs in
  let _ = flush ch in
  ()

let coq_string_of_literal_reorder m g l =
  let (neg, var) =
    match l with
    | CNF.Pos v -> (false, v)
    | CNF.Neg v -> (true, v) in
  try
    (g, (if neg then "-" else "") ^ (Hashtbl.find m var))
  with Not_found ->
    let g' = g + 1 in
    let var_reorder = string_of_int g' in
    let _ = Hashtbl.add m var var_reorder in
    (g', (if neg then "-" else "") ^ var_reorder)

let coq_string_of_clause_reorder m g c =
  let (g', strs) = List.fold_left
                     (fun (g, strs) l ->
                       let (g', str) = coq_string_of_literal_reorder m g l in
                       (g', str::strs)
                     ) (g, []) c in
  (g', String.concat " " (List.rev strs) ^ " 0\n")

let coq_output_dimacs_reorder ch cs =
  let m = Hashtbl.create 10 in
  let g = 0 in
  let (g', cnf) = List.fold_left
                    (fun (g, strs) c ->
                      let (g', str) = coq_string_of_clause_reorder m g c in
                      (g', str::strs)) (g, []) cs in
  let nvars = g' in
  let nclauses = List.length cnf in
  let _ = output_string ch ("p cnf " ^ string_of_int nvars ^ " " ^ string_of_int nclauses ^ "\n") in
  let _ = List.iter (output_string ch) cnf in
  let _ = flush ch in
  ()

let coq_output_dimacs ch cs =
  (*if !unsat_certifier = Grat then coq_output_dimacs_reorder ch cs
  else*) coq_output_dimacs ch cs



(* ===== Single-thread solving ===== *)

let cleanup files =
  if not !keep_temp_files then List.iter Unix.unlink files

let run_sat_solver ?log:(logfile=(!logfile)) ifile ofile errfile dratfile =
  let t1 = Unix.gettimeofday() in
  let cmd =
    match !sat_solver with
    | Cryptominisat ->
       !cryptominisat_path ^ " "
       ^ !sat_args ^ " "
       ^ " --drat=" ^ dratfile ^ " "
       ^ " --verb=0 "
       ^ "\"" ^ ifile ^ "\" "
       ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\""
    | Cadical ->
       !cadical_path ^ " "
       ^ !sat_args ^ " "
       ^ "\"" ^ ifile ^ "\" "
       ^ "\"" ^ dratfile ^ "\" "
       ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\" "
    | Glucose ->
       !glucose_path ^ " "
       ^ !sat_args ^ " "
       ^ " -certified -certified-output=\"" ^ dratfile ^ "\" "
       ^ "\"" ^ ifile ^ "\" "
       ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\" "
    | Kissat ->
       !kissat_path ^ " -q \"" ^ ifile ^ "\" \"" ^ dratfile ^ "\" "
       ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\" "
  in
  let res = unix cmd in
  let t2 = Unix.gettimeofday() in
  let _ =
    let _ = trace ~log:logfile ("Execution time of SAT SOLVER: " ^ string_of_float (t2 -. t1) ^ " seconds") in
    let _ = trace ~log:logfile "OUTPUT FROM SAT SOLVER:" in
    let _ = trace_file ~log:logfile ofile in
    let _ = trace_file ~log:logfile errfile in
    () in
  res = Unix.WEXITED 0

let run_sat_certifier ifile dratfile =
  let res =
    match !unsat_certifier with
    | Drat ->
       unix (!Options.Std.drat_trim_path ^ " " ^ ifile ^ " "
             ^ dratfile ^ " | grep 's VERIFIED'"
             ^ " 2>& 1 > /dev/null")
    | Grat ->
       let gratl_file = tmpfile temp_file_prefix ".gratl" in
       let gratp_file = tmpfile temp_file_prefix ".gratp" in
       (* gratgen does not accept binary drat file generated by glucose *)
       let binary_format_flag =
         match !sat_solver with
         | Glucose -> ""
         | _ -> "-b" in
       let _ = unix (!Options.Std.gratgen_path ^ " " ^ ifile ^ " "
                     ^ dratfile ^ " " ^ binary_format_flag ^ " -l " ^ gratl_file
                     ^ " -o " ^ gratp_file
                     ^ " 2>& 1 | grep -v '^c.*' > /dev/null") in
       let res = unix (!Options.Std.gratchk_path ^ " unsat " ^ ifile ^ " "
                       ^ gratl_file ^ " " ^ gratp_file
                       ^ " | grep 'VERIFIED UNSAT'"
                       ^ " 2>& 1 > /dev/null") in
       let _ = cleanup [gratl_file; gratp_file] in
       res
    | Lrat ->
       let lrat_file = tmpfile temp_file_prefix ".lrat" in
       let tmp_file = tmpfile temp_file_prefix ".tmp" in
       let _ = unix (!Options.Std.drat_trim_path ^ " " ^ ifile ^ " "
                     ^ dratfile ^ " -L " ^ tmp_file ^ " > /dev/null") in
       let _ = unix ("grep -v \"^[0-9]* 0\" " ^ tmp_file
                     ^ " | sort -n > " ^ lrat_file) in
       let _ = unix ("tail " ^ tmp_file ^ " | grep \"^[0-9]* 0\" >> "
                     ^ lrat_file) in
       let ret = unix (!Options.Std.lrat_checker_path ^ " " ^ ifile ^ " "
                       ^ lrat_file ^ " | grep -v '^c.*' "
                       ^ " 2>& 1 > /dev/null") in
       let _ = cleanup [lrat_file; tmp_file] in
       ret
  in
  match res with
  | Unix.WEXITED 0 -> true
  | _ -> false

let coq_cnf_unsat (id, cnf) =
  let _ = vprint ("\t CNF #" ^ string_of_int id ^ ":\t\t\t") in
  let ifile = tmpfile temp_file_prefix ".cnf" in
  let ofile = tmpfile temp_file_prefix ".out" in
  let errfile = tmpfile temp_file_prefix ".err" in
  let dratfile = tmpfile temp_file_prefix ".drat" in
  let _ =
    let _ = trace ("CNF input file: " ^ ifile) in
    let _ = trace ("CNF output file: " ^ ofile) in
    let _ = trace ("CNF error file: " ^ errfile) in
    let _ = trace ("CNF drat file: " ^ dratfile) in
    () in
  let t1 = Unix.gettimeofday() in
  let unsat =
    let ch = open_out ifile in
    let _ = coq_output_dimacs ch cnf in
    let _ = close_out ch in
    run_sat_solver ifile ofile errfile dratfile in
  let t2 = Unix.gettimeofday() in
  let _ =
	if unsat then vprintln ("[UNSAT]\t\t" ^ string_of_running_time t1 t2)
	else vprintln ("[SAT]\t\t" ^ string_of_running_time t1 t2) in
  let certified =
    if unsat then
      let t1 = Unix.gettimeofday() in
      let certified = run_sat_certifier ifile dratfile in
      let t2 = Unix.gettimeofday() in
      let _ = if certified then
                let _ = trace ("Certified successfully") in
                let _ = vprintln("\t\t\t\t\t[CERTIFIED]\t" ^ string_of_running_time t1 t2) in
                ()
              else
                let _ = trace ("Failed to certify") in
                let _ = vprintln("\t\t\t\t\t[NOT CERTIFIED]\t" ^ string_of_running_time t1 t2) in
                () in
      certified
    else
      false in
  let _ = cleanup [ifile; ofile; errfile; dratfile] in
  certified

let coq_all_unsat id_cnf_pairs =
  if !Options.Std.disable_range then true
  else List.for_all coq_cnf_unsat id_cnf_pairs


(* ===== Multi-thread solving ===== *)

let coq_output_clause_lwt ch c = Lwt_io.write ch (String.concat " " (List.map coq_string_of_literal c) ^ " 0")

let coq_output_cnf_lwt ch cs = Lwt_list.iter_s (
                                   fun c ->
                                   let%lwt _ = coq_output_clause_lwt ch c in
                                   let%lwt _ = Lwt_io.write ch "\n" in
                                   Lwt.return_unit) cs

let coq_output_dimacs_lwt ch cs =
  let%lwt nvars = Lwt.return (int_of_pos (CNF.max_var_of_cnf cs)) in
  let%lwt nclauses = Lwt.return (int_of_n (CNF.num_clauses cs)) in
  let%lwt _ = Lwt_io.write ch ("p cnf " ^ string_of_int nvars ^ " " ^ string_of_int nclauses ^ "\n") in
  let%lwt _ = coq_output_cnf_lwt ch cs in
  let%lwt _ = Lwt_io.flush ch in
  Lwt.return_unit

let cleanup_lwt files =
  if not !keep_temp_files then Lwt_list.iter_p Lwt_unix.unlink files
  else Lwt.return_unit

let run_sat_solver_lwt header ifile ofile errfile dratfile =
  let%lwt t1 = Lwt.return (Unix.gettimeofday()) in
  let%lwt cmd =
    Lwt.return (
        match !sat_solver with
        | Cryptominisat ->
           !cryptominisat_path ^ " "
           ^ !sat_args ^ " "
           ^ " --drat=" ^ dratfile ^ " "
           ^ " --verb=0 "
           ^ "\"" ^ ifile ^ "\" "
           ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\""
        | Cadical ->
           !cadical_path ^ " "
           ^ !sat_args ^ " "
           ^ "\"" ^ ifile ^ "\" "
           ^ "\"" ^ dratfile ^ "\" "
           ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\""
        | Glucose ->
           !glucose_path ^ " "
           ^ !sat_args ^ " "
           ^ " -certified -certified-output=\"" ^ dratfile ^ "\" "
           ^ "\"" ^ ifile ^ "\" "
           ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\""
        | Kissat ->
           !kissat_path ^ " -q \"" ^ ifile ^ "\" \"" ^ dratfile ^ "\" "
           ^ "| grep 's UNSATISFIABLE' 1> \"" ^ ofile ^ "\" 2> \"" ^ errfile ^ "\" "
      )
  in
  let%lwt res = Options.WithLwt.unix cmd in
  let%lwt t2 = Lwt.return (Unix.gettimeofday()) in
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = Lwt_list.iter_s (fun h ->
                  let%lwt _ = Options.WithLwt.trace h in
                  Lwt.return_unit) header in
  let%lwt _ = Options.WithLwt.trace ("Run SAT solver with command: " ^ cmd) in
  let%lwt _ = Options.WithLwt.trace ("Execution time of SAT solver: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = Options.WithLwt.trace "OUTPUT FROM SAT solver:" in
  let%lwt _ = Options.WithLwt.trace_file ofile in
  let%lwt _ = Options.WithLwt.trace_file errfile in
  let%lwt _ = Options.WithLwt.trace "" in
  let%lwt _ = Lwt.return (Options.WithLwt.unlock_log ()) in
  Lwt.return (res = Unix.WEXITED 0)

let run_sat_certifier_lwt ifile dratfile =
  let%lwt res =
    match !unsat_certifier with
    | Drat ->
       Options.WithLwt.unix (!Options.Std.drat_trim_path ^ " " ^ ifile ^ " "
                             ^ dratfile ^ " | grep 's VERIFIED'"
                             ^ " 2>& 1 > /dev/null")
    | Grat ->
       let%lwt gratl_file = Lwt.return (tmpfile temp_file_prefix ".gratl") in
       let%lwt gratp_file = Lwt.return (tmpfile temp_file_prefix ".gratp") in
       (* gratgen does not accept binary drat file generated by glucose *)
       let%lwt binary_format_flag =
         Lwt.return (
             match !sat_solver with
             | Glucose -> ""
             | _ -> "-b"
           ) in
       let%lwt _ = Options.WithLwt.unix (!Options.Std.gratgen_path ^ " " ^ ifile ^ " "
                                     ^ dratfile ^ " " ^ binary_format_flag ^ " -l " ^ gratl_file
                                     ^ " -o " ^ gratp_file
                                     ^ " 2>& 1 | grep -v '^c.*' >  /dev/null") in
       let%lwt res = Options.WithLwt.unix (!Options.Std.gratchk_path ^ " unsat " ^ ifile ^ " "
                                           ^ gratl_file ^ " " ^ gratp_file
                                           ^ " | grep 'VERIFIED UNSAT'"
                                           ^ " 2>& 1 > /dev/null") in
       let%lwt _ = cleanup_lwt [gratl_file; gratp_file] in
       Lwt.return res
    | Lrat ->
       let%lwt lrat_file = Lwt.return (tmpfile temp_file_prefix ".lrat") in
       let%lwt tmp_file = Lwt.return (tmpfile temp_file_prefix ".tmp") in
       let%lwt _ = Options.WithLwt.unix (!Options.Std.drat_trim_path ^ " " ^ ifile ^ " "
                                         ^ dratfile ^ " -L " ^ tmp_file ^ " > /dev/null") in
       let%lwt _ = Options.WithLwt.unix ("grep -v \"^[0-9]* 0\" " ^ tmp_file
                                         ^ " | sort -n > " ^ lrat_file) in
       let%lwt _ = Options.WithLwt.unix ("tail " ^ tmp_file ^ " | grep \"^[0-9]* 0\" >> "
                                         ^ lrat_file) in
       let%lwt ret = Options.WithLwt.unix (!Options.Std.lrat_checker_path ^ " " ^ ifile ^ " "
                                           ^ lrat_file ^ " | grep -v '^c.*' "
                                           ^ " 2>& 1 > /dev/null") in
       let%lwt _ = cleanup_lwt [lrat_file; tmp_file] in
       Lwt.return ret
  in
  Lwt.return (res = Unix.WEXITED 0)

(*
  let%lwt res =
    match res with
    | Unix.WEXITED 0 -> Lwt.return true
    | _ -> Lwt.return false in
  Lwt.return res
 *)

let coq_cnf_unsat_lwt header cnf : (bool * string * bool * string) Lwt.t =
  let%lwt ifile = Lwt.return (tmpfile temp_file_prefix ".cnf") in
  let%lwt ofile = Lwt.return (tmpfile temp_file_prefix ".out") in
  let%lwt errfile = Lwt.return (tmpfile temp_file_prefix ".err") in
  let%lwt dratfile = Lwt.return (tmpfile temp_file_prefix ".drat") in
  let%lwt ch = Lwt_io.open_file ~mode:Lwt_io.output ifile in
  let%lwt _ = coq_output_dimacs_lwt ch cnf in
  let%lwt _ = Lwt_io.close ch in
  let%lwt (unsat, unsat_time) =
    let%lwt t1 = Lwt.return (Unix.gettimeofday()) in
    let%lwt res = run_sat_solver_lwt header ifile ofile errfile dratfile in
    let%lwt t2 = Lwt.return (Unix.gettimeofday()) in
    Lwt.return (res, string_of_running_time t1 t2) in
  let%lwt (certified, certified_time) =
    if unsat then
      let%lwt t1 = Lwt.return (Unix.gettimeofday()) in
      let%lwt certified = run_sat_certifier_lwt ifile dratfile in
      let%lwt t2 = Lwt.return (Unix.gettimeofday()) in
      Lwt.return (certified, string_of_running_time t1 t2)
    else
      Lwt.return (false, "N/A") in
  let%lwt _ = cleanup_lwt [ifile; ofile; errfile; dratfile] in
  Lwt.return (unsat, unsat_time, certified, certified_time)

let work_on_pending delivered_helper res pending =
  let (delivered, promised) = Lwt_main.run (Lwt.nchoose_split pending) in
  let res' = List.fold_left delivered_helper res delivered in
  (res', promised)

let rec finish_pending delivered_helper res pending =
  match pending with
  | [] -> res
  | _ -> let (res', pending') = work_on_pending delivered_helper res pending in
         finish_pending delivered_helper res' pending'

let coq_all_unsat_lwt id_cnf_pairs =
  let mk_promise (id, cnf) =
    let%lwt header = Lwt.return ["= Verifying CNF formula #" ^ string_of_int id ^ "="] in
    let%lwt (unsat, unsat_time, certified, certified_time) = coq_cnf_unsat_lwt header cnf in
	Lwt.return (id, unsat, unsat_time, certified, certified_time) in
  let delivered_helper all_unsat (id, unsat, unsat_time, certified, certified_time) =
    let _ = vprint ("\t CNF #" ^ string_of_int id ^ ":\t\t\t") in
    let _ = vprintln ((if unsat then "[UNSAT]\t\t" else "[SAT]\t\t") ^ unsat_time) in
    let _ = if unsat then vprintln ("\t\t\t\t\t" ^ (if certified then "[CERTIFIED]\t" else "[NOT CERTIFIED]\t") ^ certified_time) in
	all_unsat && certified in
  let fold_fun (all_unsat, pending) (id, cnf) =
	if all_unsat then
       if List.length pending < !jobs then
         let promise = mk_promise (id, cnf) in
         (all_unsat, promise::pending)
       else
         let (all_unsat', pending') = work_on_pending delivered_helper all_unsat pending in
         let promise = mk_promise (id, cnf) in
         (all_unsat', promise::pending')
	else
       (finish_pending delivered_helper all_unsat pending, []) in
  let (res, pending) = List.fold_left fold_fun (true, []) id_cnf_pairs in
  finish_pending delivered_helper res pending


(* ===== Multi-process solving ===== *)

let coq_cnf_unsat_fork cnf resfile logfile =
  let ifile = tmpfile temp_file_prefix ".cnf" in
  let ofile = tmpfile temp_file_prefix ".out" in
  let errfile = tmpfile temp_file_prefix ".err" in
  let dratfile = tmpfile temp_file_prefix ".drat" in
  let _ =
    let _ = trace ~log:logfile ("CNF input file: " ^ ifile) in
    let _ = trace ~log:logfile ("CNF output file: " ^ ofile) in
    let _ = trace ~log:logfile ("CNF error file: " ^ errfile) in
    let _ = trace ~log:logfile ("CNF drat file: " ^ dratfile) in
    () in
  let resch = open_out resfile in
  let t1 = Unix.gettimeofday() in
  let unsat =
    let ch = open_out ifile in
    let _ = coq_output_dimacs ch cnf in
    let _ = close_out ch in
    run_sat_solver ~log:logfile ifile ofile errfile dratfile in
  let t2 = Unix.gettimeofday() in
  let _ = output_string resch (if unsat then "UNSAT\n" else "SAT\n") in
  let _ = output_string resch (string_of_running_time t1 t2 ^ "\n") in
  let certified =
    if unsat then
      let t1 = Unix.gettimeofday() in
      let certified = run_sat_certifier ifile dratfile in
      let t2 = Unix.gettimeofday() in
      let _ = output_string resch (if certified then "CERTIFIED\n" else "NOT CERTIFIED\n") in
      let _ = output_string resch (string_of_running_time t1 t2 ^ "\n") in
      certified
    else
      false in
  let _ = cleanup [ifile; ofile; errfile; dratfile] in
  certified

let work_on_pending_fork delivered_helper res =
  try
    let (child, _) = Unix.wait () in
    let res' = delivered_helper res child in
    res'
  with _ ->
    res

let rec finish_pending_fork delivered_helper res =
  try
    let (child, _) = Unix.wait () in
    let res' = delivered_helper res child in
    finish_pending_fork delivered_helper res'
  with _ ->
    res

let read_resfile resfile =
  let lines = ref [] in
  let ch = open_in resfile in
  let _ =
    try
      while true do
	    lines := String.trim (input_line ch)::!lines
      done
    with
      End_of_file -> ()
    | _ -> failwith "Failed to read the output file" in
  let _ = close_in ch in
  let lines = List.rev !lines in
  let l = List.length lines in
  let unsat = if l > 0 then List.nth lines 0 = "UNSAT" else false in
  let unsat_time = if l > 1 then List.nth lines 1 else "" in
  let certified = if l > 2 then List.nth lines 2 = "CERTIFIED" else false in
  let certified_time = if l > 3 then List.nth lines 3 else "" in
  (unsat, unsat_time, certified, certified_time)

let coq_all_unsat_fork id_cnf_pairs =
  let ptable = Hashtbl.create !jobs in
  let run_task cnf resfile logfile = coq_cnf_unsat_fork cnf resfile logfile in
  let delivered_helper all_unsat child =
    let (id, resfile, logfile) = Hashtbl.find ptable child in
    let (unsat, unsat_time, certified, certified_time) = read_resfile resfile in
    let _ = vprint ("\t CNF #" ^ string_of_int id ^ ":\t\t\t") in
    let _ = vprintln ((if unsat then "[UNSAT]\t\t" else "[SAT]\t\t") ^ unsat_time) in
    let _ = if unsat then vprintln ("\t\t\t\t\t" ^ (if certified then "[CERTIFIED]\t" else "[NOT CERTIFIED]\t") ^ certified_time) in
    let _ = trace ("CNF #" ^ string_of_int id) in
    let _ = trace_file logfile in
    let _ = trace "" in
    let _ = cleanup [resfile; logfile] in
    let _ = Hashtbl.remove ptable child in
	all_unsat && certified in
  let rec verify all_unsat id_cnf_pairs =
    match id_cnf_pairs with
    | [] -> finish_pending_fork delivered_helper all_unsat
    | (id, cnf)::rest ->
       if Hashtbl.length ptable < !jobs then
         let resfile = tmpfile temp_file_prefix ".res" in
         let logfile = tmpfile temp_file_prefix ".log" in
         match Unix.fork() with
         | 0 ->
            let _ = run_task cnf resfile logfile in
            exit 0
         | child ->
            let _ = Hashtbl.add ptable child (id, resfile, logfile) in
            verify all_unsat rest
       else
         let all_unsat' = work_on_pending_fork delivered_helper all_unsat in
         verify all_unsat' rest
  in
  verify true id_cnf_pairs


(* ===== Implementation of ext_all_unsat ===== *)

let ext_all_unsat_impl cnfs =
  let _ = vprintln ("Checking CNF formulas (" ^ string_of_int (List.length cnfs) ^ "):") in
  let t1 = Unix.gettimeofday() in
  let res =
	let id_cnf_pairs = List.mapi (fun i cnf -> (i, cnf)) cnfs in
	if !jobs > 1 then
      if !use_fork then coq_all_unsat_fork id_cnf_pairs
      else coq_all_unsat_lwt id_cnf_pairs
	else coq_all_unsat id_cnf_pairs in
  let t2 = Unix.gettimeofday() in
  let _ =
	if res then vprintln ("Results of checking CNF formulas:\t[OK]\t\t" ^ string_of_running_time t1 t2)
	else vprintln ("Results of checking CNF formulas:\t[FAILED]\t" ^ string_of_running_time t1 t2) in
  res

let ext_all_unsat_impl cnfs =
  if !Options.Std.disable_range then true
  else ext_all_unsat_impl cnfs


(* ===== Find coefficients using Singular ===== *)

let vname = "x"

let coq_pexpr_string_of_var v = vname ^ string_of_int (int_of_pos v)

let coq_is_atomic p =
  match p with
  | PEO | PEI | PEc _ | PEX _ -> true
  | _ -> false

let coq_is_opp p =
  match p with
  | PEopp _ -> true
  | _ -> false

let coq_is_add p =
  match p with
  | PEadd _ -> true
  | _ -> false

let coq_is_sub p =
  match p with
  | PEsub _ -> true
  | _ -> false

let coq_is_mul p =
  match p with
  | PEmul _ -> true
  | _ -> false

let coq_is_pow p =
  match p with
  | PEpow _ -> true
  | _ -> false

let rec coq_singular_of_pexpr e =
  match e with
  | PEO -> "0"
  | PEI -> "1"
  | PEc c -> Z.to_string (z_of_coq_z c)
  | PEX v -> coq_pexpr_string_of_var v
  | PEadd (e1, e2) ->
	  (if not (coq_is_opp e1) then coq_singular_of_pexpr e1 else "(" ^ coq_singular_of_pexpr e1 ^ ")")
      ^ " + "
      ^ (if not (coq_is_opp e2) && not (coq_is_sub e2) then coq_singular_of_pexpr e2 else "(" ^ coq_singular_of_pexpr e2 ^ ")")
  | PEsub (e1, e2) ->
	  (if not (coq_is_opp e1) then coq_singular_of_pexpr e1 else "(" ^ coq_singular_of_pexpr e1 ^ ")")
      ^ " - "
      ^ (if not (coq_is_opp e2) && not (coq_is_add e2) && not (coq_is_sub e2) then coq_singular_of_pexpr e2 else "(" ^ coq_singular_of_pexpr e2 ^ ")")
  | PEmul (e1, e2) ->
	  (if coq_is_atomic e1 || coq_is_mul e1 || coq_is_pow e1 then coq_singular_of_pexpr e1 else "(" ^ coq_singular_of_pexpr e1 ^ ")")
      ^ " * "
      ^ (if coq_is_atomic e2 || coq_is_mul e2 || coq_is_pow e2 then coq_singular_of_pexpr e2 else "(" ^ coq_singular_of_pexpr e2 ^ ")")
  | PEopp e' ->
	  "-" ^ (if coq_is_atomic e' then coq_singular_of_pexpr e' else " (" ^ coq_singular_of_pexpr e' ^ ")")
  | PEpow (e', n) ->
	  (if coq_is_atomic e' then coq_singular_of_pexpr e' else " (" ^ coq_singular_of_pexpr e' ^ ")") ^ "^" ^ string_of_int (int_of_n n)

module PosOrder = struct
  type t = positive
  let compare = Pervasives.compare
end

module PS = Set.Make(PosOrder)

let coq_vars_in_appearing_order (es : coq_Z coq_PExpr list) : positive list =
  let add_var ((vlist : positive list), (vset : PS.t)) (v : positive) : (positive list * PS.t) =
    if PS.mem v vset then (vlist, vset)
    else (v::vlist, PS.add v vset) in
  let rec add_vars vpair (e : coq_Z coq_PExpr) =
    match e with
    | PEX (v : positive) -> add_var vpair v
    | PEadd (e1, e2)
	| PEsub (e1, e2)
	| PEmul (e1, e2) -> add_vars (add_vars vpair e1) e2
	| PEopp e'
	| PEpow (e', _) -> add_vars vpair e'
	| _ -> vpair in
  let (vlist_rev, _vset) = List.fold_left (fun vpair e -> add_vars vpair e) ([], PS.empty) es in
  List.rev vlist_rev

let coq_vars_in_lex_order es =
  let rec coq_vars_pexpr e =
    match e with
    | PEX v -> PS.singleton v
    | PEadd (e1, e2)
	| PEsub (e1, e2)
	| PEmul (e1, e2) -> PS.union (coq_vars_pexpr e1) (coq_vars_pexpr e2)
	| PEopp e'
	| PEpow (e', _) -> coq_vars_pexpr e'
	| _ -> PS.empty in
  PS.elements (List.fold_left (fun res e -> PS.union res (coq_vars_pexpr e)) PS.empty es)

let coq_vars_in_order es =
  match !variable_ordering with
  | LexOrder -> coq_vars_in_lex_order es
  | AppearingOrder -> coq_vars_in_appearing_order es
  | RevLexOrder -> List.rev (coq_vars_in_lex_order es)
  | RevAppearingOrder -> List.rev (coq_vars_in_appearing_order es)

let split_regexp rexp s =
  try (Str.split (Str.regexp rexp) s)
  with _ -> [s]

let replace e x s =
  Str.global_replace (Str.regexp e) x s

let coq_atomic_of_string str =
  let mk_const c = PEc (coq_z_of_z c) in
  let mk_pow t p =
	if p = 1 then t
	else PEpow (t, n_of_int p) in
  let mk_var vi = PEX (pos_of_z (Z.of_string vi)) in
  let (v, e) =
    match (split_regexp "\\^" str) with
    | [v] -> (v, 1)
    | [v; e] -> (v, int_of_string e)
    | _ -> raise (ParseError ("Failed to parse atomic: " ^ str)) in
  let (c, v, e) : Z.t * string * int =
    try
      let _ = Str.search_forward (Str.regexp "\\-*[0-9]+") v 0 in
	  (Z.of_string v, "", 1)
    with _ ->
      let v = replace vname "" v in
      if String.sub v 0 1 = "-"
      then (Z.of_int (-1), String.sub v 1 ((String.length v)-1), e)
      else (Z.of_int 1, v, e)
  in
  if v = "" then (if e = 1 then mk_const c else mk_pow (mk_const c) e)
  else if Z.equal c (Z.of_int 1) then mk_pow (mk_var v) e
  else if Z.equal c (Z.of_int (-1)) then PEopp (mk_pow (mk_var v) e)
  else raise (ParseError ("Failed to parse atomic: " ^ str ^ "."))

let coq_sum_terms ts =
  match ts with
  | [] -> PEO
  | t::ts -> List.fold_left (fun res t -> PEadd (res, t)) t ts

let coq_mul_terms ts =
  match ts with
  | [] -> PEO
  | t::ts -> List.fold_left (fun res t -> PEmul (res, t)) t ts

let coq_mon_of_string str =
  try
    let t = split_regexp "[\\*]" str in
    let mons = List.rev_map coq_atomic_of_string t in
    coq_mul_terms mons
  with ParseError msg ->
    raise (ParseError (msg ^ " " ^ "Failed to parse monomial: " ^ str ^ "."))

let coq_term_of_string str =
  try
    let str = replace "-" "+-" str in
    let mons = List.rev_map (coq_mon_of_string) (split_regexp "[\\+]" str) in
    coq_sum_terms mons
  with ParseError msg ->
    raise (ParseError (msg ^ " " ^ "Failed to parse term: " ^ str ^ "."))

let run_singular ifile ofile =
  let _ = unix (!singular_path ^ " -q " ^ !Options.Std.algebra_args ^ " " ^ ifile ^ " 1> " ^ ofile ^ " 2>&1") in
  let _ =
    trace "OUTPUT FROM SINGULAR:";
    trace_file ofile;
    trace "" in
  ()

let coq_compute_coefficients_by_div (vars, p, g) =
  let _ = trace "by div" in
  let singular_output_sep = "--" in
  let rec create_dummy len =
	if len = 0 then []
	else PEO::create_dummy (len - 1) in
  let write_to_singular file =
    let input_text =
      let varseq =
		match vars with
		| [] -> "x"
		| _ -> String.concat "," (List.map coq_pexpr_string_of_var vars) in
      let generator = coq_singular_of_pexpr g in
      let poly = coq_singular_of_pexpr p in
      "ring r = integer, (" ^ varseq ^ "), lp;\n"
      ^ "poly g = " ^ generator ^ ";\n"
      ^ "poly p = " ^ poly ^ ";\n"
      ^ "poly c = p / g;\n"
      ^ "\"" ^ singular_output_sep ^ "\";\n"
      ^ "c;\n"
(*
      ^ "ideal I = groebner(g);\n"
      ^ "if (size(I) == 0) {\n"
      ^ "  \"" ^ singular_output_sep ^ "\";\n"
      ^ "  \"0\";\n"
      ^ "} else {\n"
      ^ "  matrix M = lift(I, p);\n"
      ^ "  poly h = M[1,1];\n"
      ^ "  \"" ^ singular_output_sep ^ "\";\n"
      ^ "  h;\n"
      ^ "}\n"
 *)
      ^ "exit;\n" in
    let ch = open_out file in
    let _ = output_string ch input_text; close_out ch in
    let _ =
      trace "INPUT TO SINGULAR:";
      trace_file file;
      trace "" in
    () in
  let read_singular_output file =
    let rec split (coefs, sep_found) lines =
      match lines with
      | [] -> coefs
      | hd::tl when hd = singular_output_sep -> split (coefs, true) tl
      | hd::tl -> if sep_found then split (hd::coefs, sep_found) tl
                  else split (coefs, sep_found) tl in
    let lines = ref [] in
    let ch = open_in file in
    let _ =
      try
        while true do
	      lines := String.trim (input_line ch)::!lines
        done
      with
        End_of_file -> ()
      | _ -> failwith "Failed to read the output file" in
    let _ = close_in ch in
    split ([], false) (List.rev !lines) in
  let ifile = tmpfile "inputfgb_" "" in
  let ofile = tmpfile "outputfgb_" "" in
  let _ = write_to_singular ifile in
  let _ = run_singular ifile ofile in
  let coefs = read_singular_output ofile in
  let _ = cleanup [ifile; ofile] in
  match coefs with
  | c::[] -> [coq_term_of_string c]
  | _ -> create_dummy 1

let coq_compute_coefficients_by_lift (vars, p, gs) =
  let _ = trace "by lift" in
  let singular_output_sep = "--" in
  let rec create_dummy len =
	if len = 0 then []
	else PEO::create_dummy (len - 1) in
  let write_to_singular file =
    let input_text =
      let varseq =
		match vars with
		| [] -> "x"
		| _ -> String.concat "," (List.map coq_pexpr_string_of_var vars) in
      let generator = if List.length gs = 0 then "0" else (String.concat ",\n  " (List.map coq_singular_of_pexpr gs)) in
      let poly = coq_singular_of_pexpr p in
      "ring r = integer, (" ^ varseq ^ "), lp;\n"
      ^ "ideal gs' = " ^ generator ^ ";\n"
      ^ "poly p' = " ^ poly ^ ";\n"
      ^ "ideal I' = groebner(gs');\n"
      ^ "poly q' = reduce(p', I');\n"
      ^ "q';\n"
      ^ "if (q' == 0) {\n"
      ^ "  \"" ^ singular_output_sep ^ "\";\n"
      ^ "  lift(gs', p');\n"
      ^ "}\n"
      ^ "exit;\n" in
    let ch = open_out file in
    let _ = output_string ch input_text; close_out ch in
    let _ =
      trace "INPUT TO SINGULAR:";
      trace_file file;
      trace "" in
    () in
  let read_singular_output file =
    let rec split (is_in_ideal, p_coef_gs, i) lines =
      match lines with
      | [] -> (is_in_ideal, List.rev p_coef_gs)
      | hd::tl when hd = singular_output_sep -> split (is_in_ideal, p_coef_gs, i + 1) tl
      | hd::tl -> if i = 0 then split (hd = "0", p_coef_gs, i) tl
                  else split (is_in_ideal, hd::p_coef_gs, i) tl in
    let lines = ref [] in
    let ch = open_in file in
    let _ =
      try
        while true do
	      lines := String.trim (input_line ch)::!lines
        done
      with
        End_of_file -> ()
      | _ -> failwith "Failed to read the output file" in
    let _ = close_in ch in
    split (false, [], 0) (List.rev !lines) in
  let after_eq_sign str =
    let i = String.index str '=' + 1 in
    String.sub str i (String.length str - i) in
  let ifile = tmpfile "inputfgb_" "" in
  let ofile = tmpfile "outputfgb_" "" in
  let _ = write_to_singular ifile in
  let _ = run_singular ifile ofile in
  let (is_in_ideal, p_coef_gs) = read_singular_output ofile in
  let _ = cleanup [ifile; ofile] in
  let _ = trace("= in ideal? =\n" ^ string_of_bool is_in_ideal) in
  if is_in_ideal then
    let p_coef_gs = List.map (fun t -> coq_term_of_string (after_eq_sign t)) p_coef_gs in
    p_coef_gs
  else
    create_dummy (List.length gs)

let ext_find_coefficients_impl gs p m =
  let _ = vprint ("Finding polynomial coefficients\t\t") in
  let t1 = Unix.gettimeofday() in
  let (c_m, cs_gs) =
	let vars = coq_vars_in_order (gs@[m]@[p]) in
    let coefs =
      if gs = [] && not (Poly.zpexpr_is_zero m)
      then coq_compute_coefficients_by_div (vars, p, m)
      else coq_compute_coefficients_by_lift (vars, p, (m::gs)) in
	(List.hd coefs, List.tl coefs) in
  let t2 = Unix.gettimeofday() in
  let _ = vprintln ("[OK]\t\t" ^ string_of_running_time t1 t2) in
  (cs_gs, c_m)


(* ===== Find coefficients concurrently using Singular ===== *)

let write_header_to_log header =
  Lwt_list.iter_s (fun h ->
      let%lwt _ = Options.WithLwt.trace h in
      Lwt.return_unit) header

let run_singular_lwt header ifile ofile =
  let t1 = Unix.gettimeofday() in
  let%lwt _ =
    Options.WithLwt.unix (!singular_path ^ " -q " ^ !Options.Std.algebra_args ^ " \"" ^ ifile ^ "\" 1> \"" ^ ofile ^ "\" 2>&1") in
  let t2 = Unix.gettimeofday() in
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = write_header_to_log header in
  let%lwt _ = Options.WithLwt.trace "INPUT TO SINGULAR:" in
  let%lwt _ = Options.WithLwt.unix ("cat " ^ ifile ^ " >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let%lwt _ = Options.WithLwt.trace ("Execution time of Singular: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = Options.WithLwt.trace "OUTPUT FROM SINGULAR:" in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ ofile ^ "\" >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let _ = Options.WithLwt.unlock_log () in
  Lwt.return_unit

let coq_compute_coefficients_by_div_lwt header (vars, p, g) =
  let _ = trace "by div" in
  let singular_output_sep = "--" in
  let ifile = tmpfile "inputfgb_" "" in
  let ofile = tmpfile "outputfgb_" "" in
  let rec create_dummy len =
	if len = 0 then []
	else PEO::create_dummy (len - 1) in
  let write_to_singular file =
    let input_text =
      let varseq =
		match vars with
		| [] -> "x"
		| _ -> String.concat "," (List.map coq_pexpr_string_of_var vars) in
      let generator = coq_singular_of_pexpr g in
      let poly = coq_singular_of_pexpr p in
      "ring r = integer, (" ^ varseq ^ "), lp;\n"
      ^ "poly g = " ^ generator ^ ";\n"
      ^ "poly p = " ^ poly ^ ";\n"
      ^ "poly c = p / g;\n"
      ^ "\"" ^ singular_output_sep ^ "\";\n"
      ^ "c;\n"
      ^ "exit;\n" in
    let%lwt ifd = Lwt_unix.openfile file
                    [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC]
                    0o600 in
    let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
    let%lwt _ = Lwt_io.write ch input_text in
    let%lwt _ = Lwt_io.close ch in
    Lwt.return_unit in
  let read_singular_output ofile =
    let rec split (coefs, sep_found) lines =
      match lines with
      | [] -> coefs
      | hd::tl when hd = singular_output_sep -> split (coefs, true) tl
      | hd::tl -> if sep_found then split (hd::coefs, sep_found) tl
                  else split (coefs, sep_found) tl in
    let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
    let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
    let%lwt lines =
      try%lwt
            Lwt.return (Lwt_io.read_lines ch)
      with _ -> failwith "Failed to read the output file" in
    let%lwt lines = Lwt_stream.to_list lines in
    let%lwt _ = Lwt_io.close ch in
    Lwt.return (split ([], false) lines) in
  let%lwt t1 = Lwt.return (Unix.gettimeofday()) in
  let%lwt _ = write_to_singular ifile in
  let%lwt _ = run_singular_lwt header ifile ofile in
  let%lwt coefs = read_singular_output ofile in
  let%lwt _ = cleanup_lwt [ifile; ofile] in
  let%lwt res =
    Lwt.return (match coefs with
                | c::[] -> [coq_term_of_string c]
                | _ -> create_dummy 1) in
  let%lwt t2 = Lwt.return (Unix.gettimeofday()) in
  Lwt.return (res, string_of_running_time t1 t2)

let coq_compute_coefficients_by_lift_lwt header (vars, p, gs) =
  let _ = trace "by lift" in
  let singular_output_sep = "--" in
  let ifile = tmpfile "inputfgb_" "" in
  let ofile = tmpfile "outputfgb_" "" in
  let rec create_dummy len =
	if len = 0 then []
	else PEO::create_dummy (len - 1) in
  let write_to_singular file =
    let input_text =
      let varseq =
		match vars with
		| [] -> "x"
		| _ -> String.concat "," (List.map coq_pexpr_string_of_var vars) in
      let generator = if List.length gs = 0 then "0" else (String.concat ",\n  " (List.map coq_singular_of_pexpr gs)) in
      let poly = coq_singular_of_pexpr p in
      "ring r = integer, (" ^ varseq ^ "), lp;\n"
      ^ "ideal gs' = " ^ generator ^ ";\n"
      ^ "poly p' = " ^ poly ^ ";\n"
      ^ "ideal I' = groebner(gs');\n"
      ^ "poly q' = reduce(p', I');\n"
      ^ "q';\n"
      ^ "if (q' == 0) {\n"
      ^ "  \"" ^ singular_output_sep ^ "\";\n"
      ^ "  lift(gs', p');\n"
      ^ "}\n"
      ^ "exit;\n" in
    let%lwt ifd = Lwt_unix.openfile file
                    [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC]
                    0o600 in
    let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
    let%lwt _ = Lwt_io.write ch input_text in
    let%lwt _ = Lwt_io.close ch in
    Lwt.return_unit in
  let read_singular_output ofile =
    let rec split (is_in_ideal, p_coef_gs, i) lines =
      match lines with
      | [] -> (is_in_ideal, List.rev p_coef_gs)
      | hd::tl when hd = singular_output_sep -> split (is_in_ideal, p_coef_gs, i + 1) tl
      | hd::tl ->
         let hd = String.trim hd in
         if hd = "" then split (is_in_ideal, p_coef_gs, i) tl (* skip empty line *)
         else if i = 0 then split (hd = "0", p_coef_gs, i) tl
         else split (is_in_ideal, hd::p_coef_gs, i) tl in
    let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
    let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
    let%lwt lines =
      try%lwt
            Lwt.return (Lwt_io.read_lines ch)
      with _ -> failwith "Failed to read the output file" in
    let%lwt lines = Lwt_stream.to_list lines in
    let%lwt _ = Lwt_io.close ch in
    Lwt.return (split (false, [], 0) lines) in
  let after_eq_sign str =
    let i = String.index str '=' + 1 in
    String.sub str i (String.length str - i) in
  let%lwt t1 = Lwt.return (Unix.gettimeofday()) in
  let%lwt _ = write_to_singular ifile in
  let%lwt _ = run_singular_lwt header ifile ofile in
  let%lwt (is_in_ideal, p_coef_gs) = read_singular_output ofile in
  let%lwt _ = cleanup_lwt [ifile; ofile] in
  let%lwt res =
    if is_in_ideal then
      let%lwt p_coef_gs = Lwt_list.map_s (fun t -> Lwt.return (coq_term_of_string (after_eq_sign t))) p_coef_gs in
      Lwt.return p_coef_gs
    else
      Lwt.return (create_dummy (List.length gs)) in
  let%lwt t2 = Lwt.return (Unix.gettimeofday()) in
  Lwt.return (res, string_of_running_time t1 t2)

let coq_compute_coefficients_lwt poly_with_id_list =
  let mk_promise (id, ((gs, p), m)) =
    let%lwt (c_m, cs_gs, running_time) =
	  let%lwt vars = Lwt.return (coq_vars_in_order (gs@[m]@[p])) in
      let%lwt (coefs, running_time) =
        if gs = [] && not (Poly.zpexpr_is_zero m)
        then coq_compute_coefficients_by_div_lwt ["Polynomials #" ^ string_of_int id] (vars, p, m)
        else coq_compute_coefficients_by_lift_lwt ["Polynomials #" ^ string_of_int id] (vars, p, (m::gs)) in
	  Lwt.return (List.hd coefs, List.tl coefs, running_time) in
    Lwt.return (id, cs_gs, c_m, running_time) in
  let delivered_helper coef_list_unordered (id, cs_gs, cs_m, running_time) =
    let _ = vprint ("\t Polynomials #" ^ string_of_int id ^ ":\t\t") in
    let _ = vprintln ("[DONE]\t\t" ^ running_time) in
	(id, (cs_gs, cs_m))::coef_list_unordered in
  let fold_fun (coef_list_unordered, pending) (id, poly) =
    if List.length pending < !jobs then
      let promise = mk_promise (id, poly) in
      (coef_list_unordered, promise::pending)
    else
      let (coef_list_unordered', pending') = work_on_pending delivered_helper coef_list_unordered pending in
      let promise = mk_promise (id, poly) in
      (coef_list_unordered', promise::pending') in
  let (coef_list_unordered, pending) = List.fold_left fold_fun ([], []) poly_with_id_list in
  let coef_list_unordered = finish_pending delivered_helper coef_list_unordered pending in
  snd (List.split (List.sort (fun (id1, _) (id2, _) -> compare id1 id2) coef_list_unordered))

let rec ext_find_coefficients_list_impl polys =
  let _ = vprint ("Finding polynomial coefficients\n") in
  let t1 = Unix.gettimeofday() in
  let coef_list = coq_compute_coefficients_lwt (List.mapi (fun id poly -> (id, poly)) polys) in
  let t2 = Unix.gettimeofday() in
  let _ = vprintln ("Finished finding polynomial coefficients\t\t" ^ string_of_running_time t1 t2) in
  coef_list
