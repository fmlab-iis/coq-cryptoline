
open Options.Std
open Ast.Cryptoline
open Qfbv.Common
open Qfbv.WithLwt
open Common
(* open Lwt.Infix *)

let rec flatten_espec s =
  match s.espost with
  | Eand (e1, e2) ->
     let res1 = flatten_espec { espre = s.espre; esprog = s.esprog;
                                espost = e1; espwss = s.espwss } in
     let res2 = flatten_espec { espre = s.espre; esprog = s.esprog;
                                espost = e2; espwss = s.espwss } in
     res1@res2
  | _ -> [s]

let rec flatten_rspec s =
  match s.rspost with
  | Rand (e1, e2) ->
     let res1 = flatten_rspec { rspre = s.rspre; rsprog = s.rsprog;
                                rspost = e1; rspwss = s.rspwss } in
     let res2 = flatten_rspec { rspre = s.rspre; rsprog = s.rsprog;
                                rspost = e2; rspwss = s.rspwss } in
     res1@res2
  | _ -> [s]

let work_on_pending delivered_helper res pending =
  let (delivered, promised) = Lwt_main.run (Lwt.nchoose_split pending) in
  let res' = List.fold_left delivered_helper res delivered in
  (res', promised)

let rec finish_pending delivered_helper res pending =
  match pending with
  | [] -> res
  | _ -> let (res', pending') = work_on_pending delivered_helper res pending in
         finish_pending delivered_helper res' pending'

let verify_safety_inc timeout f p qs =
  let mk_promise (id, i, q) =
    let header = ["= Verifying safety condition =";
                  "ID: " ^ string_of_int id ^ "\n"
                  ^ "Instruction: " ^ string_of_instr i] in
    let fp = safety_assumptions f p q in
    let solve = solve_simp ~timeout:timeout ~header:header (fp@[q]) in
    try%lwt
      let%lwt solve_res = solve in
      match solve_res with
      | Sat -> Lwt.return (id, i, q, "[FAILED]", Solved Sat)
      | Unknown -> Lwt.return (id, i, q, "[FAILED]", Solved Unknown)
      | Unsat -> Lwt.return (id, i, q, "[OK]", Solved Unsat)
    with TimeoutException ->
      Lwt.return (id, i, q, "[TIMEOUT]", Unfinished [(id, i, q)]) in
  let add_unsolved q res =
    match res with
    | Solved Unsat -> Unfinished [q]
    | Unfinished unsolved -> Unfinished (q::unsolved)
    | _ -> assert false in
  let delivered_helper r (id, i, q, ret_str, ret) =
    let _ = vprint ("\t\t Safety condition #" ^
                      string_of_int id ^ "\t") in
    let _ = vprintln ret_str in
    match r with
    | Solved Sat | Solved Unknown -> r
    | _ ->
       match ret with
       | Solved Sat | Solved Unknown -> ret
       | Solved Unsat -> r
       | Unfinished qs ->
          let _ = assert (List.length qs = 1) in
          add_unsolved (id, i, q) r in
  let fold_fun (res, pending) (id, i, q) =
    match res with
      Solved Sat
    | Solved Unknown ->
       (finish_pending delivered_helper res pending, [])
    | _ ->
       if List.length pending < !jobs then
         let promise = mk_promise (id, i, q) in
         (res, promise::pending)
       else
         let (res', pending') = work_on_pending delivered_helper res pending in
         let promise = mk_promise (id, i, q) in
         (res', promise::pending') in
  let (res, pending) = List.fold_left fold_fun ((Solved Unsat), []) qs in
  finish_pending delivered_helper res pending

let write_header_to_log header =
  Lwt_list.iter_s (fun h ->
      let%lwt _ = Options.WithLwt.trace h in
      Lwt.return_unit) header

let write_singular_input ifile vars gen p =
  let input_text =
    let varseq =
      match vars with
      | [] -> "x"
      | _ -> String.concat "," (List.map string_of_var vars) in
    let generator = if List.length gen = 0 then "0" else (String.concat ",\n  " (List.map singular_of_eexp gen)) in
    let poly = singular_of_eexp p in
    "ring r = integer, (" ^ varseq ^ "), lp;\n"
    ^ "ideal gs = " ^ generator ^ ";\n"
    ^ "poly p = " ^ poly ^ ";\n"
    ^ "ideal I = groebner(gs);\n"
    ^ "reduce(p, I);\n"
    ^ "exit;\n" in
  let%lwt ifd = Lwt_unix.openfile ifile
                  [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC]
                  0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
  let%lwt _ = Lwt_io.write ch input_text in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return_unit

let write_sage_input ifile vars gen p =
  let input_text =
    let varseq =
      match vars with
      | [] -> "x"
      | _ -> String.concat "," (List.map string_of_var vars) in
    let generator = if List.length gen = 0 then "0" else (String.concat ",\n  " (List.map sage_of_eexp gen)) in
    let poly = sage_of_eexp p in
    "R.<" ^ varseq ^ "> = PolynomialRing(ZZ," ^ string_of_int (max 1 (List.length vars)) ^ ")\n"
    ^ "I = (" ^ generator ^ ") * R\n"
    ^ "P = " ^ poly ^ "\n"
    ^ "assert P in I\n" in
  let%lwt ifd = Lwt_unix.openfile ifile
                  [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC]
                  0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
  let%lwt _ = Lwt_io.write ch input_text in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return_unit

let write_magma_input ifile vars gen p =
  let input_text =
    let varseq =
      match vars with
      | [] -> "x"
      | _ -> String.concat "," (List.map string_of_var vars) in
    let varlen = max 1 (List.length vars) in
    let generator = if List.length gen = 0 then "0" else (String.concat ",\n" (List.map magma_of_eexp gen)) in
    let poly = magma_of_eexp p in
    "R := IntegerRing();\n"
    ^ "S<" ^ varseq ^ "> := PolynomialRing(R, " ^ string_of_int varlen ^ ");\n"
      ^ "I := [\n"
      ^ generator ^ "\n];\n"
      ^ "J := GroebnerBasis(I);\n"
    ^ "g := " ^ poly ^ ";\n"
    ^ "g in J;\n"
    ^ "exit;\n" in
  let%lwt ifd = Lwt_unix.openfile ifile
                  [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC]
                  0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
  let%lwt _ = Lwt_io.write ch input_text in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return_unit

let write_mathematica_input ifile vars gen p =
  let input_text =
    let varseq =
      match vars with
      | [] -> "x"
      | _ -> String.concat "," (List.map mathematica_of_var vars) in
    let generator = if List.length gen = 0 then "0" else (String.concat ",\n" (List.map mathematica_of_eexp gen)) in
    let poly = mathematica_of_eexp p in
    "vars = {" ^ varseq ^ "};\n"
    ^ "gs = {" ^ generator ^ "};\n"
    ^ "p = " ^ poly ^ ";\n"
    ^ "gb = GroebnerBasis[gs, vars, CoefficientDomain -> Integers];\n"
    ^ "{q, r} = PolynomialReduce[p, gb, vars, CoefficientDomain -> Integers];\n"
    ^ "Print[r];\n" in
  let%lwt ifd = Lwt_unix.openfile ifile
                  [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC]
                  0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
  let%lwt _ = Lwt_io.write ch input_text in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return_unit

let write_macaulay2_input ifile vars gen p =
  let input_text =
    let (vars, gen, p, default_generator) =
      let dummy_var = mkvar "cryptoline'dummy'variable" (Tuint 0) (* The type is no matter here. *) in
      let no_var_in_generator = VS.is_empty (List.fold_left (fun vs e -> VS.union vs (vars_eexp e)) VS.empty gen) in
      if no_var_in_generator then
        (dummy_var::vars,
         List.map (fun e -> emul (evar dummy_var) e) gen,
         emul (evar dummy_var) p,
         string_of_var dummy_var ^ "*0")
      else
        (vars, gen, p, "0") in
    let varseq =
      match vars with
      | [] -> "x"
      | _ -> String.concat "," (List.map macaulay2_of_var vars) in
    let generator = if List.length gen = 0 then default_generator else (String.concat ",\n  " (List.map macaulay2_of_eexp gen)) in
    let poly = macaulay2_of_eexp p in
    "myRing = ZZ[" ^ varseq ^ ",MonomialOrder=>Lex]\n"
    ^ "myIdeal = ideal(" ^ generator ^ ")\n"
    ^ "myPoly = " ^ poly ^ "\n"
    ^ "myBasis = groebnerBasis myIdeal\n"
    ^ "myRes = toString (myPoly % myBasis)\n"
    ^ "print myRes\n" in
  let%lwt ifd = Lwt_unix.openfile ifile
                  [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC]
                  0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
  let%lwt _ = Lwt_io.write ch input_text in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return_unit

let run_singular header ifile ofile =
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

let run_sage header ifile ofile =
  let t1 = Unix.gettimeofday() in
  let%lwt _ =
    Options.WithLwt.unix (!sage_path ^ " " ^ !Options.Std.algebra_args ^ " \"" ^ ifile ^ "\" 1> \"" ^ ofile ^ "\" 2>&1") in
  let t2 = Unix.gettimeofday() in
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = write_header_to_log header in
  let%lwt _ = Options.WithLwt.trace "INPUT TO SAGE:" in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ ifile ^ "\" >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let%lwt _ = Options.WithLwt.trace ("Execution time of Sage: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = Options.WithLwt.trace "OUTPUT FROM SAGE:" in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ ofile ^ "\" >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let _ = Options.WithLwt.unlock_log () in
  Lwt.return_unit

let run_magma header ifile ofile =
  let t1 = Unix.gettimeofday() in
  let%lwt _ = Options.WithLwt.unix (!magma_path ^ " " ^ !Options.Std.algebra_args ^ " -b \"" ^ ifile ^ "\" 1> \"" ^ ofile ^ "\" 2>&1") in
  let t2 = Unix.gettimeofday() in
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = write_header_to_log header in
  let%lwt _ = Options.WithLwt.trace "INPUT TO MAGMA:" in
  let%lwt _ = Options.WithLwt.unix ("cat " ^ ifile ^ " >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let%lwt _ = Options.WithLwt.trace ("Execution time of Magma: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = Options.WithLwt.trace "OUTPUT FROM MAGMA:" in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ ofile ^ "\" >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let _ = Options.WithLwt.unlock_log () in
  Lwt.return_unit

let run_mathematica header ifile ofile =
  let t1 = Unix.gettimeofday() in
  let%lwt _ = Options.WithLwt.unix (!mathematica_path ^ " " ^ !Options.Std.algebra_args ^ " -file \"" ^ ifile ^ "\" 1> \"" ^ ofile ^ "\" 2>&1") in
  let t2 = Unix.gettimeofday() in
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = write_header_to_log header in
  let%lwt _ = Options.WithLwt.trace "INPUT TO MATHEMATICA:" in
  let%lwt _ = Options.WithLwt.unix ("cat " ^ ifile ^ " >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let%lwt _ = Options.WithLwt.trace ("Execution time of Mathematica: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = Options.WithLwt.trace "OUTPUT FROM MATHEMATICA:" in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ ofile ^ "\" >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let _ = Options.WithLwt.unlock_log () in
  Lwt.return_unit

let run_macaulay2 header ifile ofile =
  let t1 = Unix.gettimeofday() in
  let%lwt _ =
    Options.WithLwt.unix (!macaulay2_path ^ " --script \"" ^ ifile ^ "\" " ^ !Options.Std.algebra_args ^ " 1> \"" ^ ofile ^ "\" 2>&1") in
  let t2 = Unix.gettimeofday() in
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = write_header_to_log header in
  let%lwt _ = Options.WithLwt.trace "INPUT TO MACAULAY2:" in
  let%lwt _ = Options.WithLwt.unix ("cat " ^ ifile ^ " >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let%lwt _ = Options.WithLwt.trace ("Execution time of Macaulay2: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = Options.WithLwt.trace "OUTPUT FROM MACAULAY2:" in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ ofile ^ "\" >>  " ^ !logfile) in
  let%lwt _ = Options.WithLwt.trace "" in
  let _ = Options.WithLwt.unlock_log () in
  Lwt.return_unit

let read_singular_output ofile =
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt line =
    try%lwt
          Lwt_io.read_line ch
    with _ -> failwith "Failed to read the output file" in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return (String.trim line)

let read_sage_output ofile =
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt lines =
    try%lwt
      Lwt.return (Lwt_io.read_lines ch)
    with _ -> failwith "Failed to read the output file" in
  let%lwt lines = Lwt_stream.to_list lines in
  let%lwt _ = Lwt_io.close ch in
  if List.mem "AssertionError" lines then Lwt.return "false"
  else if List.length lines = 0 then Lwt.return "true"
  else failwith "Unknown error in Sage"

let read_magma_output ofile =
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt line =
    try%lwt
	  Lwt_io.read_line ch
    with _ -> failwith "Failed to read the output file" in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return (String.trim line)

let read_mathematica_output ofile =
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt line =
    try%lwt
	  Lwt_io.read_line ch
    with _ -> failwith "Failed to read the output file" in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return (String.trim line)

let read_macaulay2_output ofile =
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt line =
    try%lwt
          Lwt_io.read_line ch
    with _ -> failwith "Failed to read the output file" in
  let%lwt _ = Lwt_io.close ch in
  Lwt.return (String.trim line)

let is_in_ideal header vars ideal p =
  let ifile = Filename.temp_file "inputfgb_" "" in
  let ofile = Filename.temp_file "outputfgb_" "" in
  let res =
    match !algebra_system with
    | Singular ->
       let%lwt _ = write_singular_input ifile vars ideal p in
       let%lwt _ = run_singular header ifile ofile in
       let%lwt res = read_singular_output ofile in
       let%lwt _ = Lwt_unix.unlink ifile in
       let%lwt _ = Lwt_unix.unlink ofile in
       Lwt.return (res = "0")
    | Sage ->
       (* The input file to Sage must have file extension ".sage". *)
       let ifile = ifile ^ ".sage" in
       let%lwt _ = write_sage_input ifile vars ideal p in
       let%lwt _ = run_sage header ifile ofile in
       let%lwt res = read_sage_output ofile in
       let%lwt _ = Lwt_unix.unlink ifile in
       let%lwt _ = Lwt_unix.unlink ofile in
       Lwt.return (res = "true")
    | Magma ->
       let%lwt _ = write_magma_input ifile vars ideal p in
       let%lwt _ = run_magma header ifile ofile in
       let%lwt res = read_magma_output ofile in
       let%lwt _ = Lwt_unix.unlink ifile in
       let%lwt _ = Lwt_unix.unlink ofile in
       Lwt.return (res = "true")
    | Mathematica ->
       let%lwt _ = write_mathematica_input ifile vars ideal p in
       let%lwt _ = run_mathematica header ifile ofile in
       let%lwt res = read_mathematica_output ofile in
       let%lwt _ = Lwt_unix.unlink ifile in
       let%lwt _ = Lwt_unix.unlink ofile in
       Lwt.return (res = "0")
    | Macaulay2 ->
       let%lwt _ = write_macaulay2_input ifile vars ideal p in
       let%lwt _ = run_macaulay2 header ifile ofile in
       let%lwt res = read_macaulay2_output ofile in
       let%lwt _ = Lwt_unix.unlink ifile in
       let%lwt _ = Lwt_unix.unlink ofile in
       Lwt.return (res = "0")
  in
  res

let verify_rspec_assert header s =
  let verify_one s =
    let f = bexp_rbexp s.rspre in
    let p = bexp_program s.rsprog in
    let g = bexp_rbexp s.rspost in
    let gs = split_bexp g in
    Lwt_list.for_all_s
      (fun g ->
        let rheader = ["range condition: " ^ string_of_bexp g] in
        let%lwt r =
          solve_simp ~header:(header@rheader) (f::p@[g]) in
        Lwt.return (r = Unsat))
      gs in
  let rec verify_ands s =
    match s.rspost with
    | Rand (e1, e2) ->
       let%lwt r =
         verify_ands { rspre = s.rspre; rsprog = s.rsprog; rspost = e1;
                       rspwss = s.rspwss } in
       if r then
         verify_ands { rspre = s.rspre; rsprog = s.rsprog; rspost = e2;
                       rspwss = s.rspwss }
       else
         Lwt.return false
    | _ ->
       if !apply_slicing then verify_one (slice_rspec_ssa s)
       else verify_one s in
  let rec verify_rec i ss =
    match ss with
    | [] -> Lwt.return true
    | hd::tl ->
       let%lwt _ = Options.WithLwt.trace ("== Cut #" ^ string_of_int i ^ " ==") in
       let%lwt r = verify_ands hd in
       if r then
         verify_rec (i+1) tl
       else
         Lwt.return false in
  verify_rec 0 (cut_rspec s)

let verify_espec_assert header vgen s =
  let verify_one vgen s =
    let (_, entailments) = polys_of_espec vgen s in
    Lwt_list.fold_left_s
      (fun res (post, vars, ideal, p) ->
        if res then
          let eheader = ["algebraic condition: " ^ string_of_ebexp post;
                         "Try #0"] in
          let%lwt r = is_in_ideal (header@eheader) vars [] p in
          if r then
            Lwt.return_true
          else
            let eheader = ["algebraic condition: " ^ string_of_ebexp post;
                           "Try #1"] in
            let%lwt r = is_in_ideal (header@eheader) vars ideal p in
            Lwt.return r
        else
          Lwt.return false) true entailments in
  let rec verify_ands vgen s =
    match s.espost with
    | Eand (e1, e2) ->
       let%lwt r = verify_ands vgen { espre = s.espre; esprog = s.esprog;
                                      espost = e1; espwss = s.espwss } in
       if r then
         verify_ands vgen { espre = s.espre; esprog = s.esprog;
                            espost = e2; espwss = s.espwss }
       else
         Lwt.return false
    | _ ->
       if !apply_slicing then verify_one vgen (slice_espec_ssa s)
       else verify_one vgen s in
  let rec verify_rec i vgen ss =
    match ss with
    | [] -> Lwt.return true
    | hd::tl ->
       let%lwt _ = Options.WithLwt.trace ("== Cut #" ^ string_of_int i ^ " ==") in
       let%lwt r = verify_ands vgen hd in
       if r then verify_rec (i+1) vgen tl else Lwt.return false in
  verify_rec 0 vgen (cut_espec s)

let verify_eassert vgen s =
  let _ = trace "===== Verifying algebraic assertions =====" in
  let mkespec f p g = { espre = f; esprog = p; espost = g; espwss = [] } in
  let delivered_helper res (r, _e) = res && r in
  let mk_promise epre evisited e =
    let header = ["=== Checking algebraic assertion: " ^
                    Ast.Cryptoline.string_of_bexp e ^ " ==="] in
    let%lwt e_res =
      verify_espec_assert header vgen
        (mkespec epre (List.rev evisited) (eqn_bexp e)) in
    Lwt.return (e_res, e) in
  let rec verify res pending epre evisited p =
    if res then
      if List.length pending < !jobs then
        match p with
        | [] -> finish_pending delivered_helper res pending
        | Iassert e::tl ->
           let promise = mk_promise epre evisited e in
           verify res (promise::pending) epre evisited tl
        | Iecut (e, _)::tl -> verify res pending e [] tl
        | hd::tl ->
           verify res pending epre (hd::evisited) tl
      else
        let (res', promised) = work_on_pending delivered_helper res pending in
        verify res' promised epre evisited p
    else
      finish_pending delivered_helper res pending in
  verify true [] (eqn_bexp s.spre) [] s.sprog

let verify_rassert _vgen s =
  let _ = trace "===== Verifying range assertions =====" in
  let mkrspec f p g = { rspre = f; rsprog = p; rspost = g; rspwss = [] } in
  let delivered_helper res (r, _e) = res && r in
  let mk_promise rpre rvisited e =
    let header = ["=== Checking range assertion: " ^
                    Ast.Cryptoline.string_of_bexp e ^ " ==="] in
    let%lwt r_res =
      verify_rspec_assert header
        (mkrspec rpre (List.rev rvisited) (rng_bexp e)) in
    Lwt.return (r_res, e) in
  let rec verify res pending rpre rvisited p =
    if res then
      if List.length pending < !jobs then
        match p with
        | [] -> finish_pending delivered_helper res pending
        | Iassert e::tl ->
           let promise = mk_promise rpre rvisited e in
           verify res (promise::pending) rpre rvisited tl
        | Ircut (e, _)::tl -> verify res pending e [] tl
        | hd::tl ->
           verify res pending rpre (hd::rvisited) tl
      else
        let (res', promised) = work_on_pending delivered_helper res pending in
        verify res' promised rpre rvisited p
    else
      finish_pending delivered_helper res pending in
  verify true [] (rng_bexp s.spre) [] s.sprog

let verify_assert vgen s =
  let _ = trace "===== Verifying assertions =====" in
  let mkrspec f p g = { rspre = f; rsprog = p; rspost = g; rspwss = [] } in
  let mkespec f p g = { espre = f; esprog = p; espost = g; espwss = [] } in
  let delivered_helper res (r, _e) = res && r in
  let mk_promise (epre, rpre) (evisited, rvisited) e =
    let header = ["=== Checking assertion: " ^
                    Ast.Cryptoline.string_of_bexp e ^ " ==="] in
    let%lwt r_res =
      verify_rspec_assert header
        (mkrspec rpre (List.rev rvisited) (rng_bexp e)) in
    let%lwt e_res =
      if r_res then
        verify_espec_assert header vgen
          (mkespec epre (List.rev evisited) (eqn_bexp e))
      else
        Lwt.return false in
    Lwt.return (e_res, e) in
  let rec verify res pending (epre, rpre) (evisited, rvisited) p =
    if res then
      if List.length pending < !jobs then
        match p with
        | [] -> finish_pending delivered_helper res pending
        | Iassert e::tl ->
           let promise = mk_promise (epre, rpre) (evisited, rvisited) e in
           verify res (promise::pending) (epre, rpre) (evisited, rvisited) tl
        | Iecut (e, _)::tl -> verify res pending (e, rpre) ([], rvisited) tl
        | Ircut (e, _)::tl -> verify res pending (epre, e) (evisited, []) tl
        | hd::tl ->
           verify res pending (epre, rpre) (hd::evisited, hd::rvisited) tl
      else
        let (res', promised) = work_on_pending delivered_helper res pending in
        verify res' promised (epre, rpre) (evisited, rvisited) p
    else
      finish_pending delivered_helper res pending in
  verify true [] (eqn_bexp s.spre, rng_bexp s.spre) ([], []) s.sprog

let verify_rspec s =
  let _ = trace "===== Verifying range specification =====" in
  let verify_one s =
    let f = bexp_rbexp s.rspre in
    let p = bexp_program s.rsprog in
    let g = bexp_rbexp s.rspost in
    let gs = split_bexp g in
    Lwt_list.for_all_s
      (fun g ->
        let header = ["range condition: " ^ string_of_bexp g] in
        let%lwt r = solve_simp ~header:header (f::p@[g]) in
        Lwt.return (r = Unsat))
      gs in
  let mk_promise s =
    if !apply_slicing then verify_one (slice_rspec_ssa s)
    else verify_one s in
  let delivered_helper res r = res && r in
  let verify_ands s =
    let rec verify_ands_helper ss res pending =
      if res then
        if List.length pending < !jobs then
          match ss with
          | [] -> finish_pending delivered_helper res pending
          | hd::tl -> let promise = mk_promise hd in
                      verify_ands_helper tl res (promise::pending)
        else
          let (res', pending') =
            work_on_pending delivered_helper res pending in
          verify_ands_helper ss res' pending'
      else
        finish_pending delivered_helper res pending in
    let ss = flatten_rspec s in
    verify_ands_helper ss true [] in
  let rec verify_rec i ss =
    match ss with
    | [] -> true
    | hd::tl ->
       begin
         match !verify_rcuts with
         | Some cuts when not (List.mem i cuts) ->
            let _ = trace ("== Skip Cut #" ^ string_of_int i ^ " ==") in
            verify_rec (i+1) tl
         | _ ->
            let _ = trace ("== Cut #" ^ string_of_int i ^ " ==") in
            verify_ands hd && verify_rec (i+1) tl
       end in
  verify_rec 0 (cut_rspec s)

let verify_espec vgen s =
  let _ = trace "===== Verifying algebraic specification =====" in
  let verify_one vgen s =
    let (_, entailments) = polys_of_espec vgen s in
    Lwt_list.fold_left_s
      (fun res (post, vars, ideal, p) ->
        if res then
          let header = ["algebraic condition: " ^ string_of_ebexp post;
                        "Try #0"] in
          let%lwt r = is_in_ideal header vars [] p in
          if r then
            Lwt.return true
          else
            let header = ["algebraic condition: " ^ string_of_ebexp post;
                          "Try #1"] in
            let%lwt r = is_in_ideal header vars ideal p in
            Lwt.return r
        else
          Lwt.return false) true entailments in
  let mk_promise s =
    if !apply_slicing then verify_one vgen (slice_espec_ssa s)
    else verify_one vgen s in
  let delivered_helper res r = res && r in
  let verify_ands vgen s =
    let rec verify_and_helper vgen ss res pending =
      if res then
        if List.length pending < !jobs then
          match ss with
          | [] -> finish_pending delivered_helper res pending
          | hd::tl ->
             let promise = mk_promise hd in
             verify_and_helper vgen tl res (promise::pending)
        else
          let (res', pending') =
            work_on_pending delivered_helper res pending in
          verify_and_helper vgen ss res' pending'
      else
        finish_pending delivered_helper res pending in
    let ss = flatten_espec s in
    verify_and_helper vgen ss true [] in
  let rec verify_rec i vgen ss =
    match ss with
    | [] -> true
    | hd::tl ->
       begin
         match !verify_ecuts with
         | Some cuts when not (List.mem i cuts) ->
            let _ = trace ("== Skip Cut #" ^ string_of_int i ^ " ==") in
            verify_rec (i+1) vgen tl
         | _ ->
            let _ = trace ("== Cut #" ^ string_of_int i ^ " ==") in
            verify_ands vgen hd && verify_rec (i+1) vgen tl
       end in
  verify_rec 0 vgen (cut_espec s)

type cli_round_result =
  Solved of result
| Unfinished of (int * int * int * instr) list

(*
 * Run CLI to verify the safety of one instruction.
 * id: the ID of this safety verification
 * timeout: the timeout used in this safety verification
 * idx: the index of the instruction in the program containing the instruction
 * ifile: the range specification containing the program
 *)
let run_cli_vsafety id timeout idx instr ifile =
  let ofile = Filename.temp_file "safety_output_" "" in
  let lfile = Filename.temp_file "safety_log_" "" in
  (* Run CLI *)
  let cmd = String.concat " "
                          [!cli_path;
                           "-c vsafety";
                           "-instr " ^ string_of_int idx;
                           "-w " ^ string_of_int !wordsize;
                           ("-qfbv_solver " ^ Options.Std.string_of_smt_solver !Options.Std.smt_solver);
                           (if !Options.Std.smt_solver = Options.Std.Minisat then "-minisat " ^ !Options.Std.minisat_path
                            else if !Options.Std.smt_solver = Options.Std.Cryptominisat then "-cryptominisat " ^ !Options.Std.cryptominisat_path
                            else "");
                           (if !Options.Std.smt_args = "" then ""
                            else "-qfbv_args \"" ^ !Options.Std.smt_args ^ "\"");
                           (if !Options.Std.use_btor then "-btor"
                            else "");
                           (if !Options.Std.incremental_safety then "-isafety"
                            else "");
                           (if !Options.Std.incremental_safety then "-isafety_timeout " ^ string_of_int timeout
                            else "");
                           (if !Options.Std.apply_slicing then "-slicing"
                            else "");
                           (if !Options.Std.rename_local then "-rename_local"
                            else "");
                           "-o \"" ^ lfile ^ "\"";
                           "\"" ^ ifile ^ "\"";
                           "1> \"" ^ ofile ^ "\" 2>&1"
                          ] in
  let%lwt _ = Options.WithLwt.unix cmd in
  (* Read the output of CLI *)
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt line = try%lwt Lwt_io.read_line ch
                 with _ -> let%lwt _ = Lwt_io.printl "Failed to read the output file" in raise (Failure "Failed to read the output file") in
  let line = String.trim line in
  let%lwt _ = Lwt_io.close ch in
  (* Write to the log file *)
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ lfile ^ "\" >> \"" ^ !Options.Std.logfile ^ "\"") in
  let _ =
    (* Log abnormal outputs *)
    if not (List.mem line ["sat"; "unsat"; "unknown"; "timeout"]) then
      let _ = Options.WithLwt.trace ("Got abnormal output:\n"
                                 ^ line ^ "\n"
                                 ^ "From the instruction:\n"
                                 ^ "#" ^ string_of_int idx ^ ": " ^ string_of_instr instr) in
      let _ = Options.WithLwt.unix ("cat \"" ^ ifile ^ "\" >> \"" ^ !Options.Std.logfile ^ "\"") in
      ()
  in
  let _ = Options.WithLwt.unlock_log () in
  (* Remove temporary files *)
  let%lwt _ = Lwt_unix.unlink ofile in
  let%lwt _ = Lwt_unix.unlink lfile in
  (* Return the result *)
  Lwt.return (match line with
              | "sat" -> (id, timeout, idx, instr, "[FAILED]", Solved Sat)
              | "unsat" -> (id, timeout, idx, instr, "[OK]", Solved Unsat)
              | "unknown" -> (id, timeout, idx, instr, "[FAILED]", Solved Unknown)
              | "timeout" -> (id, timeout, idx, instr, "[TIMEOUT]", Unfinished [(id, timeout, idx, instr)])
              | _ -> failwith ("Unknown result from the CLI: " ^ line))

let verify_safety_cli f p =
  let ifile = Filename.temp_file "safety_input_" "" in
  let ch = open_out ifile in
  let _ = output_string ch (string_of_rspec ~typ:true {rspre = f; rsprog = p; rspost = Rtrue; rspwss = []}); close_out ch in
  let add_unsolved q res =
    match res with
    | Solved Unsat -> Unfinished [q]
    | Unfinished unsolved -> Unfinished (q::unsolved)
    | _ -> assert false in
  let delivered_helper r (id, timeout, idx, i, ret_str, ret) =
    let _ = vprint ("\t\t Safety condition #" ^ string_of_int id ^ "\t") in
    let _ = vprintln (ret_str ^ (match ret with Unfinished _ -> " timeout = " ^ string_of_int timeout | _ -> "")) in
    match r with
    | Solved Sat | Solved Unknown -> r
    | _ ->
       match ret with
       | Solved Sat | Solved Unknown -> ret
       | Solved Unsat -> r
       | Unfinished qs ->
          let _ = assert (List.length qs = 1) in
          (* Increase timeout for unsolved tasks *)
          add_unsolved (id, timeout * 2, idx, i) r in
  let rec verify_round qs (res, pending) =
    match res with
      Solved Sat
    | Solved Unknown -> (res, pending)
    | _ ->
       if List.length pending < !jobs then
         match qs with
         | [] -> (res, pending)
         | (id, timeout, idx, i)::tl ->
            let promise = run_cli_vsafety id timeout idx i ifile in
            verify_round tl (res, promise::pending)
       else
         let (res', pending') = work_on_pending delivered_helper res pending in
         verify_round qs (res', pending') in
  let rec verify_rec qs (res, pending) =
    let (res', pending') = verify_round qs (res, pending) in
    match res', pending' with
    | Solved r, [] -> if r = Unsat then true else false
    | Unfinished qs', _ -> verify_rec qs' (Solved Unsat, pending')
    | _ -> let (res'', pending'') = work_on_pending delivered_helper res' pending' in
           verify_rec [] (res'', pending'') in
  let add_index = fun p -> List.mapi (fun idx i -> (!Options.Std.incremental_safety_timeout, idx, i)) p in
  let filter_true = fun qs -> List.filter (fun (_, _, i) -> bexp_instr_safe i <> True) qs in
  let add_id = fun qs -> List.mapi (fun id (timeout, idx, i) -> (id, timeout, idx, i)) qs in
  let res = verify_rec (List.rev (add_id (filter_true (add_index p)))) (Solved Unsat, []) in
  let _ = vprint "\t Overall\t\t\t" in
  let _ = Unix.unlink ifile in
  res

(*
 * Verify a range or an algebraic specification using CLI to run verification tasks.
 * s: a range or an algebraic specification
 * run_cli_verify: a function that verifies an atomic predicate
 * header_gen: a function that generats the header output to the log for some cut
 * flatten_spec: a function that flattens the specification
 * cut_spec: a function that cuts the input specification
 * verify_cuts: a list option specifying the indices of cuts to be verified
 *)
let verify_spec_cli s run_cli_verify header_gen flatten_spec cut_spec verify_cuts =
  let delivered_helper res r = res && r in
  let rec verify_ands i ss (res, pending) =
    if res then
      if List.length pending < !jobs then
        match ss with
        | [] -> (res, pending)
        | hd::tl ->
           let promise = run_cli_verify (header_gen i) hd in
           verify_ands i tl (res, promise::pending)
      else
        let (res', pending') = work_on_pending delivered_helper res pending in
        verify_ands i ss (res', pending')
    else
      (res, pending) in
  let rec verify_rec i ss (res, pending) =
    match ss with
    | [] -> (res, pending)
    | hd::tl ->
       if res then
         begin
           match verify_cuts with
           | Some cuts when not (List.mem i cuts) ->
              let _ = trace ("== Skip Cut #" ^ string_of_int i ^ " ==") in
              verify_rec (i+1) tl (res, pending)
           | _ ->
              let (res', pending') = verify_ands i (flatten_spec hd) (res, pending) in
              verify_rec (i+1) tl (res', pending')
         end
       else
         (res, pending) in
  let (res, pending) = verify_rec 0 (cut_spec s) (true, []) in
  finish_pending delivered_helper res pending

(* Run CLI to verify an espec (no conjunction in the postcondition). *)
let run_cli_vespec header s =
  let ifile = Filename.temp_file "espec_input_" "" in
  let ofile = Filename.temp_file "espec_output_" "" in
  let lfile = Filename.temp_file "espec_log_" "" in
  (* Write the input to CLI *)
  let%lwt ifd = Lwt_unix.openfile ifile [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
  let%lwt _ = Lwt_io.write ch (string_of_espec ~typ:true s) in
  let%lwt _ = Lwt_io.close ch in
  (* Run CLI *)
  let cmd = String.concat " "
                          [!cli_path;
                           "-c vespec";
                           "-w " ^ string_of_int !wordsize;
                           ("-qfbv_solver " ^ Options.Std.string_of_smt_solver !Options.Std.smt_solver);
                           (if !Options.Std.smt_solver = Options.Std.Minisat then "-minisat " ^ !Options.Std.minisat_path
                            else if !Options.Std.smt_solver = Options.Std.Cryptominisat then "-cryptominisat " ^ !Options.Std.cryptominisat_path
                            else "");
                           (if !Options.Std.smt_args = "" then ""
                            else "-qfbv_args \"" ^ !Options.Std.smt_args ^ "\"");
                           (if !Options.Std.use_btor then "-btor"
                            else "");
                           (if !Options.Std.incremental_safety then "-isafety"
                            else "");
                           (if !Options.Std.incremental_safety then "-isafety_timeout " ^ string_of_int !Options.Std.incremental_safety_timeout
                            else "");
                           (if !Options.Std.algebra_system = Options.Std.Singular then "-singular " ^ !Options.Std.singular_path
                            else if !Options.Std.algebra_system = Options.Std.Magma then "-magma " ^ !Options.Std.magma_path
                            else if !Options.Std.algebra_system = Options.Std.Sage then "-sage " ^ !Options.Std.sage_path
                            else if !Options.Std.algebra_system = Options.Std.Mathematica then "-mathematica " ^ !Options.Std.mathematica_path
                            else if !Options.Std.algebra_system = Options.Std.Macaulay2 then "-macaulay2 " ^ !Options.Std.macaulay2_path
                            else "");
                           (if !Options.Std.algebra_args = "" then ""
                            else "-algebra_args \"" ^ !Options.Std.algebra_args ^ "\"");
                           (if not !Options.Std.apply_rewriting then "-disable_rewriting"
                            else "");
                           (if !Options.Std.carry_constraint then ""
                            else "-no_carry_constraint");
                           "-vo " ^ string_of_variable_ordering !Options.Std.variable_ordering;
                           (if !Options.Std.polys_rewrite_replace_eexp then "-re"
                            else "");
                           (if !Options.Std.apply_slicing then "-slicing"
                            else "");
                           (if !Options.Std.rename_local then "-rename_local"
                            else "");
                           "-o \"" ^ lfile ^ "\"";
                           "\"" ^ ifile ^ "\"";
                           "1> \"" ^ ofile ^ "\" 2>&1"
                          ] in
  let%lwt _ = Options.WithLwt.unix cmd in
  (* Read the output of CLI *)
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt line = try%lwt Lwt_io.read_line ch
                 with _ -> let%lwt _ = Lwt_io.printl "Failed to read the output file" in raise (Failure "Failed to read the output file") in
  let line = String.trim line in
  let%lwt _ = Lwt_io.close ch in
  (* Write to the log file *)
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = Options.WithLwt.trace header in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ lfile ^ "\" >> \"" ^ !Options.Std.logfile ^ "\" 2>&1") in
  let _ =
    (* Log abnormal outputs *)
    if line <> "true" && line <> "false" then
      let _ = Options.WithLwt.trace ("Got abnormal output:") in
      let _ = Options.WithLwt.trace line in
      let _ = Options.WithLwt.trace ("From the input:") in
      let _ = Options.WithLwt.unix ("cat \"" ^ ifile ^ "\" >> \"" ^ !Options.Std.logfile ^ "\" 2>&1") in
      ()
  in
  let _ = Options.WithLwt.unlock_log () in
  (* Remove temporary files *)
  let%lwt _ = Lwt_unix.unlink ifile in
  let%lwt _ = Lwt_unix.unlink ofile in
  let%lwt _ = Lwt_unix.unlink lfile in
  (* Return the result *)
  Lwt.return (String.trim line = "true")

(* Verify an espec using CLI to run verification tasks *)
let verify_espec_cli s =
  let _ = trace "===== Verifying algebraic specification =====" in
  verify_spec_cli s
                  run_cli_vespec (fun cutno -> "== Algebraic Specification at Cut #" ^ string_of_int cutno ^ " ==")
                  flatten_espec cut_espec !verify_ecuts

(* Run CLI to verify a rspec (no conjunction in the postcondition). *)
let run_cli_vrspec header s =
  let ifile = Filename.temp_file "rspec_input_" "" in
  let ofile = Filename.temp_file "rspec_output_" "" in
  let lfile = Filename.temp_file "rspec_log_" "" in
  (* Write the input to CLI *)
  let%lwt ifd = Lwt_unix.openfile ifile [Lwt_unix.O_WRONLY; Lwt_unix.O_CREAT; Lwt_unix.O_TRUNC] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.output ifd in
  let%lwt _ = Lwt_io.write ch (string_of_rspec ~typ:true s) in
  let%lwt _ = Lwt_io.close ch in
  (* Run CLI *)
  let cmd = String.concat " "
                          [!cli_path;
                           "-c vrspec";
                           "-w " ^ string_of_int !wordsize;
                           ("-qfbv_solver " ^ Options.Std.string_of_smt_solver !Options.Std.smt_solver);
                           (if !Options.Std.smt_solver = Options.Std.Minisat then "-minisat " ^ !Options.Std.minisat_path
                            else if !Options.Std.smt_solver = Options.Std.Cryptominisat then "-cryptominisat " ^ !Options.Std.cryptominisat_path
                            else "");
                           (if !Options.Std.smt_args = "" then ""
                            else "-qfbv_args \"" ^ !Options.Std.smt_args ^ "\"");
                           (if !Options.Std.use_btor then "-btor"
                            else "");
                           (if not !Options.Std.apply_rewriting then "-disable_rewriting"
                            else "");
                           (if !Options.Std.apply_slicing then "-slicing"
                            else "");
                           (if !Options.Std.rename_local then "-rename_local"
                            else "");
                           "-o \"" ^ lfile ^ "\"";
                           "\"" ^ ifile ^ "\"";
                           "1> \"" ^ ofile ^ "\" 2>&1"
                          ] in
  let%lwt _ = Options.WithLwt.unix cmd in
  (* Read the output of CLI *)
  let%lwt ofd = Lwt_unix.openfile ofile [Lwt_unix.O_RDONLY] 0o600 in
  let ch = Lwt_io.of_fd ~mode:Lwt_io.input ofd in
  let%lwt line = try%lwt Lwt_io.read_line ch
                 with _ -> let%lwt _ = Lwt_io.printl "Failed to read the output file" in raise (Failure "Failed to read the output file") in
  let line = String.trim line in
  let%lwt _ = Lwt_io.close ch in
  (* Write to the log file *)
  let%lwt _ = Options.WithLwt.lock_log () in
  let%lwt _ = Options.WithLwt.trace header in
  let%lwt _ = Options.WithLwt.unix ("cat \"" ^ lfile ^ "\" >> \"" ^ !Options.Std.logfile ^ "\" 2>&1") in
  let _ =
    (* Log abnormal outputs *)
    if line <> "true" && line <> "false" then
      let _ = Options.WithLwt.trace ("Got abnormal output:") in
      let _ = Options.WithLwt.trace line in
      let _ = Options.WithLwt.trace ("From the input:") in
      let _ = Options.WithLwt.unix ("cat \"" ^ ifile ^ "\" >> \"" ^ !Options.Std.logfile ^ "\" 2>&1") in
      ()
  in
  let _ = Options.WithLwt.unlock_log () in
  (* Remove temporary files *)
  let%lwt _ = Lwt_unix.unlink ifile in
  let%lwt _ = Lwt_unix.unlink ofile in
  let%lwt _ = Lwt_unix.unlink lfile in
  (* Return the result *)
  Lwt.return (String.trim line = "true")

(* Verify a rspec using CLI to run verification tasks *)
let verify_rspec_cli s =
  let _ = trace "===== Verifying range specification =====" in
  verify_spec_cli s
                  run_cli_vrspec (fun cutno -> "== Range Specification at Cut #" ^ string_of_int cutno ^ " ==")
                  flatten_rspec cut_rspec !verify_rcuts

let verify_eassert_cli s =
  let _ = trace "===== Verifying algebraic assertions =====" in
  let mkespec f p g = { espre = f; esprog = p; espost = g; espwss = [] } in
  let rec verify i epre evisited p =
    match p with
    | [] -> true
    | Iassert e::tl ->
       let verifiers = List.flatten [
                           (match eqn_bexp e with
                            | Etrue -> []
                            | _ -> [fun () -> verify_spec_cli (mkespec epre (List.rev evisited) (eqn_bexp e))
                                                              run_cli_vespec (fun _cutno -> "== Algebraic Properties in Assertion #" ^ string_of_int i ^ " ==")
                                                              flatten_espec cut_espec None]);
                           [fun () -> verify (i+1) epre evisited tl]
                         ] in
       List.for_all (fun f -> f()) verifiers
    | Iecut (e, _)::tl -> verify i e [] tl
    | hd::tl -> verify i epre (hd::evisited) tl in
  verify 0 (eqn_bexp s.spre) [] s.sprog

let verify_rassert_cli s =
  let _ = trace "===== Verifying range assertions =====" in
  let mkrspec f p g = { rspre = f; rsprog = p; rspost = g; rspwss = [] } in
  let rec verify i rpre rvisited p =
    match p with
    | [] -> true
    | Iassert e::tl ->
       let verifiers = List.flatten [
                           (match rng_bexp e with
                            | Rtrue -> []
                            | _ -> [fun () -> verify_spec_cli (mkrspec rpre (List.rev rvisited) (rng_bexp e))
                                                              run_cli_vrspec (fun _cutno -> "== Range Properties in Assertion #" ^ string_of_int i ^ " ==")
                                                              flatten_rspec cut_rspec None]);
                           [fun () -> verify (i+1) rpre rvisited tl]
                         ] in
       List.for_all (fun f -> f()) verifiers
    | Ircut (e, _)::tl -> verify i e [] tl
    | hd::tl -> verify i rpre (hd::rvisited) tl in
  verify 0 (rng_bexp s.spre) [] s.sprog

let verify_assert_cli s =
  let _ = trace "===== Verifying assertions =====" in
  let mkrspec f p g = { rspre = f; rsprog = p; rspost = g; rspwss = [] } in
  let mkespec f p g = { espre = f; esprog = p; espost = g; espwss = [] } in
  let rec verify i (epre, rpre) (evisited, rvisited) p =
    match p with
    | [] -> true
    | Iassert e::tl ->
       let verifiers = List.flatten [
                           (match rng_bexp e with
                            | Rtrue -> []
                            | _ -> [fun () -> verify_spec_cli (mkrspec rpre (List.rev rvisited) (rng_bexp e))
                                                              run_cli_vrspec (fun _cutno -> "== Range Properties in Assertion #" ^ string_of_int i ^ " ==")
                                                              flatten_rspec cut_rspec None]);
                           (match eqn_bexp e with
                            | Etrue -> []
                            | _ -> [fun () -> verify_spec_cli (mkespec epre (List.rev evisited) (eqn_bexp e))
                                                              run_cli_vespec (fun _cutno -> "== Algebraic Properties in Assertion #" ^ string_of_int i ^ " ==")
                                                              flatten_espec cut_espec None]);
                           [fun () -> verify (i+1) (epre, rpre) (evisited, rvisited) tl]
                         ] in
       List.for_all (fun f -> f()) verifiers
    | Iecut (e, _)::tl -> verify i (e, rpre) ([], rvisited) tl
    | Ircut (e, _)::tl -> verify i (epre, e) (evisited, []) tl
    | hd::tl -> verify i (epre, rpre) (hd::evisited, hd::rvisited) tl in
  verify 0 (eqn_bexp s.spre, rng_bexp s.spre) ([], []) s.sprog
