
open Extraction.ExtrOcamlIntConv

(* Cryptoline AST to Coq DSL *)

let visit_typ ty =
  match ty with
  | Ast.Cryptoline.Tuint s -> Extraction.Typ.Tuint (nat_of_int s)
  | Ast.Cryptoline.Tsint s -> Extraction.Typ.Tsint (nat_of_int s)

let visit_var m g v =
  try
    (m, g, Ast.Cryptoline.VM.find v m)
  with Not_found ->
    let coq_v' = Obj.repr (n_of_int g) in
    let m' = Ast.Cryptoline.VM.add v coq_v' m in
    (m', succ g, coq_v')

let visit_aconst (ty, n) =
  (visit_typ ty, Extraction.External.bits_of_z (Ast.Cryptoline.size_of_typ ty) n)

let visit_econst n = Extraction.External.coq_z_of_z n

let visit_rconst (size, n) = (nat_of_int size, Extraction.External.bits_of_z size n)

let visit_atom m g a =
  match a with
  | Ast.Cryptoline.Avar v ->
      let (m', g', coq_v') = visit_var m g v in
      (m', g', Extraction.DSLRaw.Avar coq_v')
  | Ast.Cryptoline.Aconst (ty, n) ->
      let (cty, bits) = visit_aconst (ty, n) in
      (m, g, Extraction.DSLRaw.Aconst (cty, bits))

let visit_int_atom a =
  match a with
  | Ast.Cryptoline.Avar _ -> failwith("The number of shifts must be an integer")
  | Ast.Cryptoline.Aconst (_, n) -> n

let rec visit_eexp m g e =
  match e with
  | Ast.Cryptoline.Evar v ->
      let (m', g', coq_v') = visit_var m g v in
      (m', g', Extraction.DSLRaw.Evar coq_v')
  | Ast.Cryptoline.Econst n ->
      (m, g, Extraction.DSLRaw.Econst (visit_econst n))
  | Ast.Cryptoline.Eunop (op, e) ->
      let cop =
		match op with
		| Ast.Cryptoline.Eneg -> Extraction.DSLRaw.Eneg in
      let (m', g', coq_e') = visit_eexp m g e in
      (m', g', Extraction.DSLRaw.Eunop (cop, coq_e'))
  | Ast.Cryptoline.Ebinop (op, e, Ast.Cryptoline.Econst n) when op = Ast.Cryptoline.Epow ->
     let (m', g', coq_e') = visit_eexp m g e in
     let coq_n' = Extraction.External.coq_n_of_z n in
     (m', g', Extraction.DSLRaw.Epow (coq_e', coq_n'))
  | Ast.Cryptoline.Ebinop (op, _, _) when op = Ast.Cryptoline.Epow ->
     assert false
  | Ast.Cryptoline.Ebinop (op, e1, e2) ->
     let cop =
	   match op with
	   | Ast.Cryptoline.Eadd -> Extraction.DSLRaw.Eadd
	   | Ast.Cryptoline.Esub -> Extraction.DSLRaw.Esub
	   | Ast.Cryptoline.Emul -> Extraction.DSLRaw.Emul
       | _ -> assert false in
     let (m', g', coq_e1') = visit_eexp m g e1 in
     let (m'', g'', coq_e2') = visit_eexp m' g' e2 in
     (m'', g'', Extraction.DSLRaw.Ebinop (cop, coq_e1', coq_e2'))

let rec visit_rexp m g e =
  match e with
  | Ast.Cryptoline.Rvar v ->
      let (m', g', coq_v') = visit_var m g v in
      (m', g', Extraction.DSLRaw.Rvar coq_v')
  | Ast.Cryptoline.Rconst (size, n) ->
      let (size, n) = visit_rconst (size, n)
      in (m, g, Extraction.DSLRaw.Rconst (size, n))
  | Ast.Cryptoline.Runop (size, op, e) ->
      let cop =
		match op with
		| Ast.Cryptoline.Rnegb -> Extraction.DSLRaw.Rnegb
		| Ast.Cryptoline.Rnotb -> Extraction.DSLRaw.Rnotb in
      let (m', g', coq_e') = visit_rexp m g e in
      (m', g', Extraction.DSLRaw.Runop (nat_of_int size, cop, coq_e'))
  | Ast.Cryptoline.Rbinop (size, op, e1, e2) ->
      let cop =
		match op with
		| Ast.Cryptoline.Radd -> Extraction.DSLRaw.Radd
		| Ast.Cryptoline.Rsub -> Extraction.DSLRaw.Rsub
		| Ast.Cryptoline.Rmul -> Extraction.DSLRaw.Rmul
		| Ast.Cryptoline.Rumod -> Extraction.DSLRaw.Rumod
		| Ast.Cryptoline.Rsrem -> Extraction.DSLRaw.Rsrem
		| Ast.Cryptoline.Rsmod -> Extraction.DSLRaw.Rsmod
		| Ast.Cryptoline.Randb -> Extraction.DSLRaw.Randb
		| Ast.Cryptoline.Rorb -> Extraction.DSLRaw.Rorb
		| Ast.Cryptoline.Rxorb -> Extraction.DSLRaw.Rxorb
        | Ast.Cryptoline.Rshl -> failwith("Binary range operator shl is unsupported by CoqCryptoLine")
        | Ast.Cryptoline.Rlshr -> failwith("Binary range operator lshr is unsupported by CoqCryptoLine")
        | Ast.Cryptoline.Rashr -> failwith("Binary range operator ashr is unsupported by CoqCryptoLine") in
      let (m', g', coq_e1') = visit_rexp m g e1 in
      let (m'', g'', coq_e2') = visit_rexp m' g' e2 in
      (m'', g'', Extraction.DSLRaw.Rbinop (nat_of_int size, cop, coq_e1', coq_e2'))
  | Ast.Cryptoline.Ruext (size, e, n) ->
      let (m', g', coq_e') = visit_rexp m g e in
      (m', g', Extraction.DSLRaw.Ruext (nat_of_int size, coq_e', nat_of_int n))
  | Ast.Cryptoline.Rsext (size, e, n) ->
      let (m', g', coq_e') = visit_rexp m g e in
      (m', g', Extraction.DSLRaw.Rsext (nat_of_int size, coq_e', nat_of_int n))

let rec visit_ebexp m g e =
  match e with
  | Ast.Cryptoline.Etrue -> (m, g, Extraction.DSLRaw.Etrue)
  | Ast.Cryptoline.Eeq (e1, e2) ->
      let (m', g', coq_e1') = visit_eexp m g e1 in
      let (m'', g'', coq_e2') = visit_eexp m' g' e2 in
      (m'', g'', Extraction.DSLRaw.Eeq (coq_e1', coq_e2'))
  | Ast.Cryptoline.Eeqmod (e1, e2, mes) ->
      let (m', g', coq_e1') = visit_eexp m g e1 in
      let (m'', g'', coq_e2') = visit_eexp m' g' e2 in
      let (m''', g''', coq_mes_rev') = List.fold_left (
                                           fun (m, g, ms_rev) me ->
                                           let (m', g', me') = visit_eexp m g me in
                                           (m', g', me'::ms_rev)
                                         ) (m'', g'', []) mes in
      (m''', g''', Extraction.DSLRaw.Eeqmod (coq_e1', coq_e2', List.rev coq_mes_rev'))
  | Ast.Cryptoline.Eand (e1, e2) ->
      let (m', g', coq_e1') = visit_ebexp m g e1 in
      let (m'', g'', coq_e2') = visit_ebexp m' g' e2 in
      (m'', g'', Extraction.DSLRaw.Eand (coq_e1', coq_e2'))

let rec visit_rbexp m g e =
  match e with
  | Ast.Cryptoline.Rtrue -> (m, g, Extraction.DSLRaw.Rtrue)
  | Ast.Cryptoline.Req (size, e1, e2) ->
      let (m', g', coq_e1') = visit_rexp m g e1 in
      let (m'', g'', coq_e2') = visit_rexp m' g' e2 in
      (m'', g'', Extraction.DSLRaw.Req (nat_of_int size, coq_e1', coq_e2'))
  | Ast.Cryptoline.Rcmp (size, op, e1, e2) ->
      let cop =
		match op with
		| Ast.Cryptoline.Rult -> Extraction.DSLRaw.Rult
		| Ast.Cryptoline.Rule -> Extraction.DSLRaw.Rule
		| Ast.Cryptoline.Rugt -> Extraction.DSLRaw.Rugt
		| Ast.Cryptoline.Ruge -> Extraction.DSLRaw.Ruge
		| Ast.Cryptoline.Rslt -> Extraction.DSLRaw.Rslt
		| Ast.Cryptoline.Rsle -> Extraction.DSLRaw.Rsle
		| Ast.Cryptoline.Rsgt -> Extraction.DSLRaw.Rsgt
		| Ast.Cryptoline.Rsge -> Extraction.DSLRaw.Rsge in
      let (m', g', coq_e1') = visit_rexp m g e1 in
      let (m'', g'', coq_e2') = visit_rexp m' g' e2 in
      (m'', g'', Extraction.DSLRaw.Rcmp (nat_of_int size, cop, coq_e1', coq_e2'))
  | Ast.Cryptoline.Rneg e ->
      let (m', g', coq_e') = visit_rbexp m g e in
      (m', g', Extraction.DSLRaw.Rneg coq_e')
  | Ast.Cryptoline.Rand (e1, e2) ->
      let (m', g', coq_e1') = visit_rbexp m g e1 in
      let (m'', g'', coq_e2') = visit_rbexp m' g' e2 in
      (m'', g'', Extraction.DSLRaw.Rand (coq_e1', coq_e2'))
  | Ast.Cryptoline.Ror (e1, e2) ->
      let (m', g', coq_e1') = visit_rbexp m g e1 in
      let (m'', g'', coq_e2') = visit_rbexp m' g' e2 in
      (m'', g'', Extraction.DSLRaw.Ror (coq_e1', coq_e2'))

let visit_bexp m g e =
  match e with
  | (eb, rb) ->
      let (m', g', coq_eb') = visit_ebexp m g eb in
      let (m'', g'', coq_rb') = visit_rbexp m' g' rb in
      (m'', g'', (coq_eb', coq_rb'))

let visit_bexp_prove_with m g (espwss, rspwss) =
  match Ast.Cryptoline.merge_ebexp_prove_with espwss, Ast.Cryptoline.merge_rbexp_prove_with rspwss with
  | (e, []), (r, []) -> visit_bexp m g (e, r)
  | _, _ -> failwith ("prove-with clauses are not supported by CoqCryptoLine")

let visit_instr m g i =
  match i with
  | Ast.Cryptoline.Imov (v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atom m' g' a in
     (m'', g'', [Extraction.DSL.DSL.Imov (coq_v', coq_a')])
  | Ast.Cryptoline.Ishl (v, a, n) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atom m' g' a in
     let nz = visit_int_atom n in
     (m'', g'', [Extraction.DSL.DSL.Ishl (coq_v', coq_a', Z.to_int nz)])
  | Ast.Cryptoline.Ishls _ -> failwith "shls is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Ishr _ -> failwith "shr is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Ishrs _ -> failwith "shrs is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Isar _ -> failwith "sar is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Isars _ -> failwith "sars is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Icshl (vh, vl, a1, a2, n) ->
     let (m', g', coq_vh') = visit_var m g vh in
     let (m'', g'', coq_vl') = visit_var m' g' vl in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     (m'''', g'''', [Extraction.DSL.DSL.Icshl (coq_vh', coq_vl', coq_a1', coq_a2', Z.to_int n)])
  | Ast.Cryptoline.Icshr _ -> failwith "cshr is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Icshrs _ -> failwith "cshrs is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Irol _ -> failwith "rol is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Iror _ -> failwith "ror is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Inondet v ->
     let (m', g', coq_v') = visit_var m g v in
     (m', g', [Extraction.DSL.DSL.Inondet (coq_v', visit_typ v.vtyp)])
  | Ast.Cryptoline.Icmov (v, c, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_c') = visit_atom m' g' c in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     (m'''', g'''', [Extraction.DSL.DSL.Icmov (coq_v', coq_c', coq_a1', coq_a2')])
  | Ast.Cryptoline.Inop ->
     (m, g, [Extraction.DSL.DSL.Inop])
  | Ast.Cryptoline.Inot (v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atom m' g' a in
     (m'', g'', [Extraction.DSL.DSL.Inot (coq_v', visit_typ v.vtyp, coq_a')])
  | Ast.Cryptoline.Iadd (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     (m''', g''', [Extraction.DSL.DSL.Iadd (coq_v', coq_a1', coq_a2')])
  | Ast.Cryptoline.Iadds (c, v, a1, a2) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     (m'''', g'''', [Extraction.DSL.DSL.Iadds (coq_c', coq_v', coq_a1', coq_a2')])
  | Ast.Cryptoline.Iadc (v, a1, a2, y) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     let (m'''', g'''', coq_y') = visit_atom m''' g''' y in
     (m'''', g'''', [Extraction.DSL.DSL.Iadc (coq_v', coq_a1', coq_a2', coq_y')])
  | Ast.Cryptoline.Iadcs (c, v, a1, a2, y) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     let (m''''', g''''', coq_y') = visit_atom m'''' g'''' y in
     (m''''', g''''', [Extraction.DSL.DSL.Iadcs (coq_c', coq_v', coq_a1', coq_a2', coq_y')])
  | Ast.Cryptoline.Isub (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     (m''', g''', [Extraction.DSL.DSL.Isub (coq_v', coq_a1', coq_a2')])
  | Ast.Cryptoline.Isubc (c, v, a1, a2) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     (m'''', g'''', [Extraction.DSL.DSL.Isubc (coq_c', coq_v', coq_a1', coq_a2')])
  | Ast.Cryptoline.Isubb (c, v, a1, a2) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     (m'''', g'''', [Extraction.DSL.DSL.Isubb (coq_c', coq_v', coq_a1', coq_a2')])
  | Ast.Cryptoline.Isbc (v, a1, a2, y) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     let (m'''', g'''', coq_y') = visit_atom m''' g''' y in
     (m'''', g'''', [Extraction.DSL.DSL.Isbc (coq_v', coq_a1', coq_a2', coq_y')])
  | Ast.Cryptoline.Isbcs (c, v, a1, a2, y) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     let (m''''', g''''', coq_y') = visit_atom m'''' g'''' y in
     (m''''', g''''', [Extraction.DSL.DSL.Isbcs (coq_c', coq_v', coq_a1', coq_a2', coq_y')])
  | Ast.Cryptoline.Isbb (v, a1, a2, y) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     let (m'''', g'''', coq_y') = visit_atom m''' g''' y in
     (m'''', g'''', [Extraction.DSL.DSL.Isbb (coq_v', coq_a1', coq_a2', coq_y')])
  | Ast.Cryptoline.Isbbs (c, v, a1, a2, y) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     let (m''''', g''''', coq_y') = visit_atom m'''' g'''' y in
     (m''''', g''''', [Extraction.DSL.DSL.Isbbs (coq_c', coq_v', coq_a1', coq_a2', coq_y')])
  | Ast.Cryptoline.Imul (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     (m''', g''', [Extraction.DSL.DSL.Imul (coq_v', coq_a1', coq_a2')])
  | Ast.Cryptoline.Imuls (_c, _v, _a1, _a2) -> failwith "muls is unsupported by CoqCryptoLine"
  | Ast.Cryptoline.Imull (vh, vl, a1, a2) ->
     let (m', g', coq_vh') = visit_var m g vh in
     let (m'', g'', coq_vl') = visit_var m' g' vl in
     let (m''', g''', coq_a1') = visit_atom m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atom m''' g''' a2 in
     (m'''', g'''', [Extraction.DSL.DSL.Imull (coq_vh', coq_vl', coq_a1', coq_a2')])
  | Ast.Cryptoline.Imulj (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     (m''', g''', [Extraction.DSL.DSL.Imulj (coq_v', coq_a1', coq_a2')])
  | Ast.Cryptoline.Isplit (vh, vl, a, n) ->
     let (m', g', coq_vh') = visit_var m g vh in
     let (m'', g'', coq_vl') = visit_var m' g' vl in
     let (m''', g''', coq_a') = visit_atom m'' g'' a in
     (m''', g''', [Extraction.DSL.DSL.Isplit (coq_vh', coq_vl', coq_a', Z.to_int n)])
  | Ast.Cryptoline.Ispl _ -> failwith "spl is unsupported by CoqCryptoLine"
  (* Instructions that cannot be translated to polynomials *)
  | Ast.Cryptoline.Iand (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     (m''', g''', [Extraction.DSL.DSL.Iand (coq_v', visit_typ v.vtyp, coq_a1', coq_a2')])
  | Ast.Cryptoline.Ior (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     (m''', g''', [Extraction.DSL.DSL.Ior (coq_v', visit_typ v.vtyp, coq_a1', coq_a2')])
  | Ast.Cryptoline.Ixor (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atom m' g' a1 in
     let (m''', g''', coq_a2') = visit_atom m'' g'' a2 in
     (m''', g''', [Extraction.DSL.DSL.Ixor (coq_v', visit_typ v.vtyp, coq_a1', coq_a2')])
  (* Type conversions *)
  | Ast.Cryptoline.Icast (_, v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atom m' g' a in
     (m'', g'', [Extraction.DSL.DSL.Icast (coq_v', visit_typ v.vtyp, coq_a')])
  | Ast.Cryptoline.Ivpc (v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atom m' g' a in
     (m'', g'', [Extraction.DSL.DSL.Ivpc (coq_v', visit_typ v.vtyp, coq_a')])
  | Ast.Cryptoline.Ijoin (v, ah, al) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_ah') = visit_atom m' g' ah in
     let (m''', g''', coq_al') = visit_atom m'' g'' al in
     (m''', g''', [Extraction.DSL.DSL.Ijoin (coq_v', coq_ah', coq_al')])
  (* Specifications *)
  | Ast.Cryptoline.Iassert e ->
     let (m', g', coq_e') = visit_bexp_prove_with m g e in
     (m', g', [Extraction.DSL.DSL.Iassume coq_e'])
  | Ast.Cryptoline.Iassume e ->
     let (m', g', coq_e') = visit_bexp m g e in
     (m', g', [Extraction.DSL.DSL.Iassume coq_e'])
  | Ast.Cryptoline.Icut e ->
     let (m', g', coq_e') = visit_bexp_prove_with m g e in
     (m', g', [Extraction.DSL.DSL.Icut coq_e'])
  | Ast.Cryptoline.Ighost (vs, e) ->
     let (m', g', coq_nondets_rev) =
       Ast.Cryptoline.VS.fold (
           fun v (m, g, coq_nondets_rev) ->
           let (m', g', coq_v') = visit_var m g v in
           (m', g', (Extraction.DSL.DSL.Inondet (coq_v', visit_typ v.vtyp))::coq_nondets_rev)
         ) vs (m, g, []) in
     let (m'', g'', coq_e') = visit_bexp m' g' e in
     (m'', g'', List.rev (Extraction.DSL.DSL.Iassume coq_e'::coq_nondets_rev))

let visit_program m g p =
  let helper (m, g, rev_res) i =
    let (m', g', coq_is') = visit_instr m g i in
    (m', g', List.rev_append coq_is' rev_res) in
  let (m'', g'', rev_coq_p') = List.fold_left helper (m, g, []) p in
  (m'', g'', List.rev rev_coq_p')

let visit_spec vs s =
  let helper v (m, te, g) =
    let (m', g', coq_v') = visit_var m g v in
    let coq_typ' = visit_typ (Ast.Cryptoline.typ_of_var v) in
    let te' = Extraction.TypEnv.TE.add coq_v' coq_typ' te in
    (m', te', g') in
  let (m0, te', g0) =
    Ast.Cryptoline.VS.fold helper vs
      (Ast.Cryptoline.VM.empty, Extraction.TypEnv.TE.empty, 1) in
  let (m', g', coq_spre') = visit_bexp m0 g0 s.Ast.Cryptoline.spre in
  let (m'', g'', coq_sprog') = visit_program m' g' s.Ast.Cryptoline.sprog in
  let (_, _, coq_spost') = visit_bexp_prove_with m'' g'' s.Ast.Cryptoline.spost in
  { Extraction.DSL.DSL.sinputs = te';
    Extraction.DSL.DSL.spre = coq_spre';
    Extraction.DSL.DSL.sprog = coq_sprog';
    Extraction.DSL.DSL.spost = coq_spost'
  }
