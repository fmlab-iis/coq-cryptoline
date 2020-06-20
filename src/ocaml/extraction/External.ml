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
open Qfbv.Common
open Qfbv.Std
open Overify.Std

exception ParseError of string

(* Basic numbers conversion *)

let string_of_bits bs =
  String.concat "" (List.map (fun b -> if b then "1" else "0") (List.rev bs))

let explode s = List.init (String.length s) (String.get s)

let nat_of_z z = nat_of_int (Z.to_int z)

let z_of_nat n = Z.of_int (int_of_nat n)

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

(*
let z_to_coq_z z =
  let sign = Z.sign z in
  let abs = Z.abs z in
  let rec to_bits cur res =
    if Z.sign cur = 0 then res
    else to_bits (Z.shift_right_trunc cur 1) ((Z.is_odd cur)::res) in
  let helper res is_odd =
    if is_odd then BinInt.Z.succ_double res
    else BinInt.Z.double res in
  if sign = 0 then
    BinInt.Z.zero
  else
    let abs_bits = to_bits abs [] in
    let _ = assert (List.hd abs_bits) in
    let abs_coq_z = List.fold_left helper BinInt.Z.one abs_bits in
    if sign > 0 then abs_coq_z else BinInt.Z.opp abs_coq_z
*)

let pos_of_z z =
  let str = Z.format "b" z in
  let str = String.sub str 1 (String.length str - 1) in
  List.fold_left (
  fun p c ->
	if c == '1' then Coq_xI p
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



(* Verify a sequence of Coq CNFs *)

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
  (* EXTREMELY SLOW
  let t1 = Unix.gettimeofday() in
  let str = CNF.dimacs_cnf_with_header cs in
  let t2 = Unix.gettimeofday() in
  let _ = vprintln ("Conversion to DIAMCS: " ^ string_of_running_time t1 t2) in
  let _ = List.iter (output_char ch) str in
   *)
  let _ = flush ch in
  ()



let coq_cnf_unsat ?timeout:timeout (id, cnf) =
  let _ = vprint ("\t CNF #" ^ string_of_int id ^ ":\t\t\t") in
  let ifile = Filename.temp_file "inputcnf_" "" in
  let ofile = Filename.temp_file "outputcnf_" "" in
  let errfile = Filename.temp_file "errorcnf_" "" in
  let _ = trace ("CNF input file: " ^ ifile) in
  let _ = trace ("CNF output file: " ^ ofile) in
  let _ = trace ("CNF error file: " ^ errfile) in
  let t1 = Unix.gettimeofday() in
  let res =
	match !smt_solver with
	| Minisat ->
		let ch = open_out ifile in
		let _ = coq_output_dimacs ch cnf in
		let _ =
          match timeout with
          | None -> run_minisat ifile ofile errfile
          | Some ti -> run_minisat ~timeout:ti ifile ofile errfile in
		(read_minisat_output ofile == Unsat)
	| Cryptominisat ->
		let ch = open_out ifile in
		let _ = coq_output_dimacs ch cnf in
		let _ =
          match timeout with
          | None -> run_cryptominisat ifile ofile errfile
          | Some ti -> run_cryptominisat ~timeout:ti ifile ofile errfile in
		(read_cryptominisat_output ofile == Unsat) in
  let t2 = Unix.gettimeofday() in
  let _ =
	if res then vprintln ("[UNSAT]\t\t" ^ string_of_running_time t1 t2)
	else vprintln ("[SAT]\t\t" ^ string_of_running_time t1 t2) in
  let _ = Unix.unlink ifile in
  let _ = Unix.unlink ofile in
  let _ = Unix.unlink errfile in
  res

let coq_all_unsat id_cnf_pairs =
  List.for_all coq_cnf_unsat id_cnf_pairs



let coq_cnf_unsat_lwt ?timeout:timeout header cnf : bool Lwt.t =
  let ifile = Filename.temp_file "inputcnf_" "" in
  let ofile = Filename.temp_file "outputcnf_" "" in
  let errfile = Filename.temp_file "errorcnf_" "" in
  let res =
	match !smt_solver with
	| Minisat ->
		let ch = open_out ifile in
		let _ = coq_output_dimacs ch cnf in
		let%lwt _ =
          match timeout with
          | None -> Qfbv.WithLwt.run_minisat header ifile ofile errfile
          | Some ti -> Qfbv.WithLwt.run_minisat ~timeout:ti header ifile ofile errfile in
        let%lwt res = Qfbv.WithLwt.read_minisat_output ofile in
		let%lwt _ = Lwt_unix.unlink ifile in
		let%lwt _ = Lwt_unix.unlink ofile in
		let%lwt _ = Lwt_unix.unlink errfile in
		Lwt.return (res == Unsat)
	| Cryptominisat ->
		let ch = open_out ifile in
		let _ = coq_output_dimacs ch cnf in
		let%lwt _ =
          match timeout with
          | None -> Qfbv.WithLwt.run_cryptominisat header ifile ofile errfile
          | Some ti -> Qfbv.WithLwt.run_cryptominisat ~timeout:ti header ifile ofile errfile in
        let%lwt res = Qfbv.WithLwt.read_cryptominisat_output ofile in
		let%lwt _ = Lwt_unix.unlink ifile in
		let%lwt _ = Lwt_unix.unlink ofile in
		let%lwt _ = Lwt_unix.unlink errfile in
		Lwt.return (res == Unsat) in
  res

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
  let mk_promise (id, cnf) : (int * bool) Lwt.t =
    let header = ["= Verifying CNF formula #" ^ string_of_int id ^ "="] in
    let unsat = coq_cnf_unsat_lwt header cnf in
	let%lwt unsat = unsat in
	Lwt.return (id, unsat) in
  let delivered_helper all_unsat (id, unsat) =
    let _ = vprint ("\t CNF #" ^ string_of_int id ^ ":\t\t\t") in
    let _ = vprintln (if unsat then "[UNSAT]" else "[SAT]") in
	all_unsat && unsat in
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



let ext_all_unsat_impl cnfs =
  let _ = vprintln ("Checking CNF formulas (" ^ string_of_int (List.length cnfs) ^ "):") in
  let t1 = Unix.gettimeofday() in
  let res =
	let id_cnf_pairs = List.mapi (fun i cnf -> (i, cnf)) cnfs in
	if !jobs > 1 then coq_all_unsat_lwt id_cnf_pairs
	else coq_all_unsat id_cnf_pairs in
  let t2 = Unix.gettimeofday() in
  let _ =
	if res then vprintln ("Results of checking CNF formulas:\t[OK]\t\t" ^ string_of_running_time t1 t2)
	else vprintln ("Results of checking CNF formulas:\t[FAILED]\t" ^ string_of_running_time t1 t2) in
  res



(* Find coefficients using Singular *)

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

let coq_write_singular_input ifile vars gen p =
  let input_text =
    let varseq =
      match vars with
      | [] -> "x"
      | _ -> String.concat "," (List.map coq_pexpr_string_of_var vars) in
    let generator = if List.length gen = 0 then "0" else (String.concat ",\n  " (List.map coq_singular_of_pexpr gen)) in
    let poly = coq_singular_of_pexpr p in
    "ring r = integer, (" ^ varseq ^ "), lp;\n"
    ^ "ideal gs = " ^ generator ^ ";\n"
    ^ "poly p = " ^ poly ^ ";\n"
    ^ "ideal I = groebner(gs);\n"
    ^ "reduce(p, I);\n"
    ^ "exit;\n" in
  let ch = open_out ifile in
  let _ = output_string ch input_text; close_out ch in
  trace "INPUT TO SINGULAR:";
  unix ("cat " ^ ifile ^ " >>  " ^ !logfile);
  trace ""

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

let rec coq_sum_terms ts =
  match ts with
  | [] -> PEO
  | t::[] -> t
  | t::ts -> PEadd (t, coq_sum_terms ts)

let rec coq_mul_terms ts =
  match ts with
  | [] -> PEO
  | t::[] -> t
  | t::ts -> PEmul (t, coq_mul_terms ts)

let coq_mon_of_string str =
  try
    let t = split_regexp "[\\*]" str in
    let mons = List.map coq_atomic_of_string t in
    coq_mul_terms mons
  with ParseError msg ->
    raise (ParseError (msg ^ " " ^ "Failed to parse monomial: " ^ str ^ "."))

let coq_term_of_string str =
  try
    let str = replace "-" "+-" str in
    let mons = List.map (coq_mon_of_string) (split_regexp "[\\+]" str) in
    coq_sum_terms mons
  with ParseError msg ->
    raise (ParseError (msg ^ " " ^ "Failed to parse term: " ^ str ^ "."))

let coq_compute_coefficients_by_lift (vars, p, gs) =
  let singular_args = ref ["-q"] in
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
  let run_singular ifile ofile =
    let _ = unix (!singular_path ^ " -q " ^ String.concat " " !singular_args ^ " " ^ ifile ^ " 1> " ^ ofile ^ " 2>&1") in
    let _ =
      trace "OUTPUT FROM SINGULAR:";
      trace_file ofile;
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
  let ifile = Filename.temp_file "inputfgb_" "" in
  let ofile = Filename.temp_file "outputfgb_" "" in
  let _ = write_to_singular ifile in
  let _ = run_singular ifile ofile in
  let (is_in_ideal, p_coef_gs) = read_singular_output ofile in
  let _ = Unix.unlink ifile in
  let _ = Unix.unlink ofile in
  let _ = trace("= in ideal? =\n" ^ string_of_bool is_in_ideal) in
  if is_in_ideal then
    let p_coef_gs = List.map (fun t -> coq_term_of_string (after_eq_sign t)) p_coef_gs in
    p_coef_gs
  else
    create_dummy (List.length gs)

let ext_find_coefficients_impl gs p m =
  let _ = vprint ("Finding polynomial coefficients\t\t") in
  let t1 = Unix.gettimeofday() in
  let ifile = Filename.temp_file "inputfgb_" "" in
  let ofile = Filename.temp_file "outputfgb_" "" in
  let (c_m, cs_gs) =
	let vars = coq_vars_in_order (gs@[m]@[p]) in
	let coefs = coq_compute_coefficients_by_lift (vars, p, (m::gs)) in
	(List.hd coefs, List.tl coefs) in
  let t2 = Unix.gettimeofday() in
  let _ = vprintln ("[OK]\t\t" ^ string_of_running_time t1 t2) in
  let _ = Unix.unlink ifile in
  let _ = Unix.unlink ofile in
  (cs_gs, c_m)
