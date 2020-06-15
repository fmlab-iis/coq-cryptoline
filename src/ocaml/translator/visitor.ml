
let rec int_to_nat i =
  if i > 0 then
    Extraction.Datatypes.S (int_to_nat (pred i))
  else
    Extraction.Datatypes.O

let z_to_nat z =
  int_to_nat (Z.to_int z)

let z_to_bits size z =
  let binstr =
    if z >= Z.zero then
      Z.format ("%0" ^ (string_of_int size) ^ "b") z
    else
      Z.format ("%0" ^ (string_of_int size) ^ "b")
        (Z.add (Z.pow (Z.of_int 2) size) z) in
  let rec helper i str res =
    if i < 0 then res
    else match String.get str i with
         | '0' -> helper (pred i) str (false::res)
         | '1' -> helper (pred i) str (true::res)
         | _ -> assert false in
  helper (pred (String.length binstr)) binstr []

let z_to_coq_z z =
  let sign = Z.sign z in
  let abs = Z.abs z in
  let rec to_bits cur res =
    if Z.sign cur = 0 then res
    else to_bits (Z.shift_right_trunc cur 1) ((Z.is_odd cur)::res) in
  let helper res is_odd =
    if is_odd then Extraction.BinInt.Z.succ_double res
    else Extraction.BinInt.Z.double res in
  if sign = 0 then
    Extraction.BinInt.Z.zero
  else
    let abs_bits = to_bits abs [] in
    let _ = assert (List.hd abs_bits) in
    let abs_coq_z = List.fold_left helper Extraction.BinInt.Z.one abs_bits in
    if sign > 0 then abs_coq_z else Extraction.BinInt.Z.opp abs_coq_z

let visit_typ ty =
  match ty with
  | Ast.Cryptoline.Tuint s -> Extraction.Typ.Tuint (int_to_nat s)
  | Ast.Cryptoline.Tsint s -> Extraction.Typ.Tsint (int_to_nat s)

let visit_var m g v =
  try
    (m, g, Ast.Cryptoline.VM.find v m)
  with Not_found ->
    let coq_v' = Obj.repr (int_to_nat g) in
    let m' = Ast.Cryptoline.VM.add v coq_v' m in
    (m', succ g, coq_v') 

let visit_aconst (ty, n) =
  (visit_typ ty, z_to_bits (Ast.Cryptoline.size_of_typ ty) n)

let visit_econst n = z_to_coq_z n

let visit_rconst (size, n) = (int_to_nat size, z_to_bits size n)

let visit_atomic m g a =
  match a with
  | Ast.Cryptoline.Avar v ->
     let (m', g', coq_v') = visit_var m g v in
     (m', g', Extraction.DSL.DSL.Avar coq_v')
  | Ast.Cryptoline.Aconst (ty, n) ->
     let (cty, bits) = visit_aconst (ty, n) in
     (m, g, Extraction.DSL.DSL.Aconst (cty, bits))

let rec visit_eexp m g e =
  match e with
  | Ast.Cryptoline.Evar v ->
     let (m', g', coq_v') = visit_var m g v in
     (m', g', Extraction.DSL.Coq__1.Evar coq_v')
  | Ast.Cryptoline.Econst n ->
     (m, g, Extraction.DSL.Coq__1.Econst (visit_econst n))
  | Ast.Cryptoline.Eunop (op, e) ->
     let cop =
       match op with
       | Ast.Cryptoline.Eneg -> Extraction.DSL.Eneg in
     let (m', g', coq_e') = visit_eexp m g e in
     (m', g', Extraction.DSL.Coq__1.Eunop (cop, coq_e'))
  | Ast.Cryptoline.Ebinop (op, e1, e2) ->
     let cop = 
       match op with
       | Ast.Cryptoline.Eadd -> Extraction.DSL.Eadd
       | Ast.Cryptoline.Esub -> Extraction.DSL.Esub
       | Ast.Cryptoline.Emul -> Extraction.DSL.Emul in
     let (m', g', coq_e1') = visit_eexp m g e1 in
     let (m'', g'', coq_e2') = visit_eexp m' g' e2 in
     (m'', g'', Extraction.DSL.Coq__1.Ebinop (cop, coq_e1', coq_e2'))

let rec visit_rexp m g e =
  match e with
  | Ast.Cryptoline.Rvar v ->
     let (m', g', coq_v') = visit_var m g v in
     (m', g', Extraction.DSL.Coq__2.Rvar coq_v')
  | Ast.Cryptoline.Rconst (size, n) ->
     let (size, n) = visit_rconst (size, n)
     in (m, g, Extraction.DSL.Coq__2.Rconst (size, n))
  | Ast.Cryptoline.Runop (size, op, e) ->
     let cop =
       match op with
       | Ast.Cryptoline.Rnegb -> Extraction.DSL.Rnegb
       | Ast.Cryptoline.Rnotb -> Extraction.DSL.Rnotb in
     let (m', g', coq_e') = visit_rexp m g e in
     (m', g', Extraction.DSL.Runop (int_to_nat size, cop, coq_e'))
  | Ast.Cryptoline.Rbinop (size, op, e1, e2) ->
     let cop =
       match op with
       | Ast.Cryptoline.Radd -> Extraction.DSL.Radd
       | Ast.Cryptoline.Rsub -> Extraction.DSL.Rsub
       | Ast.Cryptoline.Rmul -> Extraction.DSL.Rmul
       | Ast.Cryptoline.Rumod -> Extraction.DSL.Rumod
       | Ast.Cryptoline.Rsrem -> Extraction.DSL.Rsrem
       | Ast.Cryptoline.Rsmod -> Extraction.DSL.Rsmod
       | Ast.Cryptoline.Randb -> Extraction.DSL.Randb
       | Ast.Cryptoline.Rorb -> Extraction.DSL.Rorb
       | Ast.Cryptoline.Rxorb -> Extraction.DSL.Rxorb in
     let (m', g', coq_e1') = visit_rexp m g e1 in
     let (m'', g'', coq_e2') = visit_rexp m' g' e2 in
     (m'', g'', Extraction.DSL.Rbinop (int_to_nat size, cop, coq_e1', coq_e2'))
  | Ast.Cryptoline.Ruext (size, e, n) ->
     let (m', g', coq_e') = visit_rexp m g e in
     (m', g', Extraction.DSL.Ruext (int_to_nat size, coq_e', int_to_nat n))
  | Ast.Cryptoline.Rsext (size, e, n) ->
     let (m', g', coq_e') = visit_rexp m g e in
     (m', g', Extraction.DSL.Rsext (int_to_nat size, coq_e', int_to_nat n))

let rec visit_ebexp m g e =
  match e with
  | Ast.Cryptoline.Etrue -> (m, g, Extraction.DSL.Etrue)
  | Ast.Cryptoline.Eeq (e1, e2) ->
     let (m', g', coq_e1') = visit_eexp m g e1 in
     let (m'', g'', coq_e2') = visit_eexp m' g' e2 in
     (m'', g'', Extraction.DSL.Eeq (coq_e1', coq_e2'))
  | Ast.Cryptoline.Eeqmod (e1, e2, modulus) ->
     let (m', g', coq_e1') = visit_eexp m g e1 in
     let (m'', g'', coq_e2') = visit_eexp m' g' e2 in
     let (m''', g''', coq_m') = visit_eexp m'' g'' modulus in
     (m''', g''', Extraction.DSL.Eeqmod (coq_e1', coq_e2', coq_m'))
  | Ast.Cryptoline.Eand (e1, e2) ->
     let (m', g', coq_e1') = visit_ebexp m g e1 in
     let (m'', g'', coq_e2') = visit_ebexp m' g' e2 in
     (m'', g'', Extraction.DSL.Eand (coq_e1', coq_e2'))

let rec visit_rbexp m g e =
  match e with
  | Ast.Cryptoline.Rtrue -> (m, g, Extraction.DSL.Rtrue)
  | Ast.Cryptoline.Req (size, e1, e2) ->
     let (m', g', coq_e1') = visit_rexp m g e1 in
     let (m'', g'', coq_e2') = visit_rexp m' g' e2 in
     (m'', g'', Extraction.DSL.Req (int_to_nat size, coq_e1', coq_e2'))
  | Ast.Cryptoline.Rcmp (size, op, e1, e2) ->
     let cop =
       match op with
       | Ast.Cryptoline.Rult -> Extraction.DSL.Rult
       | Ast.Cryptoline.Rule -> Extraction.DSL.Rule
       | Ast.Cryptoline.Rugt -> Extraction.DSL.Rugt
       | Ast.Cryptoline.Ruge -> Extraction.DSL.Ruge
       | Ast.Cryptoline.Rslt -> Extraction.DSL.Rslt
       | Ast.Cryptoline.Rsle -> Extraction.DSL.Rsle
       | Ast.Cryptoline.Rsgt -> Extraction.DSL.Rsgt
       | Ast.Cryptoline.Rsge -> Extraction.DSL.Rsge in
     let (m', g', coq_e1') = visit_rexp m g e1 in
     let (m'', g'', coq_e2') = visit_rexp m' g' e2 in
     (m'', g'', Extraction.DSL.Rcmp (int_to_nat size, cop, coq_e1', coq_e2'))
  | Ast.Cryptoline.Rneg e ->
     let (m', g', coq_e') = visit_rbexp m g e in
     (m', g', Extraction.DSL.Rneg coq_e')
  | Ast.Cryptoline.Rand (e1, e2) ->
     let (m', g', coq_e1') = visit_rbexp m g e1 in
     let (m'', g'', coq_e2') = visit_rbexp m' g' e2 in
     (m'', g'', Extraction.DSL.Rand (coq_e1', coq_e2'))
  | Ast.Cryptoline.Ror (e1, e2) ->
     let (m', g', coq_e1') = visit_rbexp m g e1 in
     let (m'', g'', coq_e2') = visit_rbexp m' g' e2 in
     (m'', g'', Extraction.DSL.Ror (coq_e1', coq_e2'))

let visit_bexp m g e =
  match e with
  | (eb, rb) ->
     let (m', g', coq_eb') = visit_ebexp m g eb in
     let (m'', g'', coq_rb') = visit_rbexp m' g' rb in
     (m'', g'', (coq_eb', coq_rb'))

let visit_instr m g i =
  match i with
  | Ast.Cryptoline.Imov (v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atomic m' g' a in
     (m'', g'', Extraction.DSL.DSL.Imov (coq_v', coq_a'))
  | Ast.Cryptoline.Ishl (v, a, n) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atomic m' g' a in
     (m'', g'', Extraction.DSL.DSL.Ishl (coq_v', coq_a', z_to_nat n))
  | Ast.Cryptoline.Icshl (vh, vl, a1, a2, n) ->
     let (m', g', coq_vh') = visit_var m g vh in
     let (m'', g'', coq_vl') = visit_var m' g' vl in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     (m'''', g'''', Extraction.DSL.DSL.Icshl (coq_vh', coq_vl', coq_a1', coq_a2', z_to_nat n))
  | Ast.Cryptoline.Inondet v ->
     let (m', g', coq_v') = visit_var m g v in
     (m', g', Extraction.DSL.DSL.Inondet (coq_v', visit_typ v.vtyp))
  | Ast.Cryptoline.Icmov (v, c, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_c') = visit_atomic m' g' c in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     (m'''', g'''', Extraction.DSL.DSL.Icmov (coq_v', coq_c', coq_a1', coq_a2'))
  | Ast.Cryptoline.Inop ->
     (m, g, Extraction.DSL.DSL.Inop)
  | Ast.Cryptoline.Iadd (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     (m''', g''', Extraction.DSL.DSL.Iadd (coq_v', coq_a1', coq_a2'))
  | Ast.Cryptoline.Iadds (c, v, a1, a2) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     (m'''', g'''', Extraction.DSL.DSL.Iadds (coq_c', coq_v', coq_a1', coq_a2'))
  | Ast.Cryptoline.Iaddr (_c, _v, _a1, _a2) ->
     failwith "addr is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Iadc (v, a1, a2, y) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     let (m'''', g'''', coq_y') = visit_atomic m''' g''' y in
     (m'''', g'''', Extraction.DSL.DSL.Iadc (coq_v', coq_a1', coq_a2', coq_y'))
  | Ast.Cryptoline.Iadcs (c, v, a1, a2, y) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     let (m''''', g''''', coq_y') = visit_atomic m'''' g'''' y in
     (m''''', g''''', Extraction.DSL.DSL.Iadcs (coq_c', coq_v', coq_a1', coq_a2', coq_y'))
  | Ast.Cryptoline.Iadcr (_c, _v, _a1, _a2, _y) ->
     failwith "adcr is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Isub (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     (m''', g''', Extraction.DSL.DSL.Isub (coq_v', coq_a1', coq_a2'))
  | Ast.Cryptoline.Isubc (c, v, a1, a2) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     (m'''', g'''', Extraction.DSL.DSL.Isubc (coq_c', coq_v', coq_a1', coq_a2'))
  | Ast.Cryptoline.Isubb (c, v, a1, a2) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     (m'''', g'''', Extraction.DSL.DSL.Isubb (coq_c', coq_v', coq_a1', coq_a2'))
  | Ast.Cryptoline.Isubr (_c, _v, _a1, _a2) ->
     failwith "subr is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Isbc (v, a1, a2, y) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     let (m'''', g'''', coq_y') = visit_atomic m''' g''' y in
     (m'''', g'''', Extraction.DSL.DSL.Isbc (coq_v', coq_a1', coq_a2', coq_y'))
  | Ast.Cryptoline.Isbcs (c, v, a1, a2, y) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     let (m''''', g''''', coq_y') = visit_atomic m'''' g'''' y in
     (m''''', g''''', Extraction.DSL.DSL.Isbcs (coq_c', coq_v', coq_a1', coq_a2', coq_y'))
  | Ast.Cryptoline.Isbcr (_c, _v, _a1, _a2, _y) ->
     failwith "sbcr is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Isbb (v, a1, a2, y) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     let (m'''', g'''', coq_y') = visit_atomic m''' g''' y in
     (m'''', g'''', Extraction.DSL.DSL.Isbb (coq_v', coq_a1', coq_a2', coq_y'))
  | Ast.Cryptoline.Isbbs (c, v, a1, a2, y) ->
     let (m', g', coq_c') = visit_var m g c in
     let (m'', g'', coq_v') = visit_var m' g' v in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     let (m''''', g''''', coq_y') = visit_atomic m'''' g'''' y in
     (m''''', g''''', Extraction.DSL.DSL.Isbbs (coq_c', coq_v', coq_a1', coq_a2', coq_y'))
  | Ast.Cryptoline.Isbbr (_c, _v, _a1, _a2, _y) ->
     failwith "sbbr is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Imul (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     (m''', g''', Extraction.DSL.DSL.Imul (coq_v', coq_a1', coq_a2'))
  | Ast.Cryptoline.Imuls (_c, _v, _a1, _a2) ->
     failwith "muls is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Imulr (_c, _v, _a1, _a2) ->
     failwith "mulr is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Imull (vh, vl, a1, a2) ->
     let (m', g', coq_vh') = visit_var m g vh in
     let (m'', g'', coq_vl') = visit_var m' g' vl in
     let (m''', g''', coq_a1') = visit_atomic m'' g'' a1 in
     let (m'''', g'''', coq_a2') = visit_atomic m''' g''' a2 in
     (m'''', g'''', Extraction.DSL.DSL.Imull (coq_vh', coq_vl', coq_a1', coq_a2'))
  | Ast.Cryptoline.Imulj (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     (m''', g''', Extraction.DSL.DSL.Imulj (coq_v', coq_a1', coq_a2'))
  | Ast.Cryptoline.Isplit (vh, vl, a, n) ->
     let (m', g', coq_vh') = visit_var m g vh in
     let (m'', g'', coq_vl') = visit_var m' g' vl in
     let (m''', g''', coq_a') = visit_atomic m'' g'' a in
     (m''', g''', Extraction.DSL.DSL.Isplit (coq_vh', coq_vl', coq_a', z_to_nat n))
  (* Instructions that cannot be translated to polynomials *)
  | Ast.Cryptoline.Iand (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     (m''', g''', Extraction.DSL.DSL.Iand (coq_v', visit_typ v.vtyp, coq_a1', coq_a2'))
  | Ast.Cryptoline.Ior (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     (m''', g''', Extraction.DSL.DSL.Ior (coq_v', visit_typ v.vtyp, coq_a1', coq_a2'))
  | Ast.Cryptoline.Ixor (v, a1, a2) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a1') = visit_atomic m' g' a1 in
     let (m''', g''', coq_a2') = visit_atomic m'' g'' a2 in
     (m''', g''', Extraction.DSL.DSL.Ixor (coq_v', visit_typ v.vtyp, coq_a1', coq_a2'))
  | Ast.Cryptoline.Inot (v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atomic m' g' a in
     (m'', g'', Extraction.DSL.DSL.Inot (coq_v', visit_typ v.vtyp, coq_a'))
  (* Type conversions *)
  | Ast.Cryptoline.Icast (v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atomic m' g' a in
     (m'', g'', Extraction.DSL.DSL.Icast (coq_v', visit_typ v.vtyp, coq_a'))
  | Ast.Cryptoline.Ivpc (v, a) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_a') = visit_atomic m' g' a in
     (m'', g'', Extraction.DSL.DSL.Ivpc (coq_v', visit_typ v.vtyp, coq_a'))
  | Ast.Cryptoline.Ijoin (v, ah, al) ->
     let (m', g', coq_v') = visit_var m g v in
     let (m'', g'', coq_ah') = visit_atomic m' g' ah in
     let (m''', g''', coq_al') = visit_atomic m'' g'' al in
     (m''', g''', Extraction.DSL.DSL.Ijoin (coq_v', coq_ah', coq_al'))
  (* Specifications *)
  | Ast.Cryptoline.Iassert _e ->
     failwith "assert is unsupported by coq-cryptoline"
  | Ast.Cryptoline.Iassume e ->
     let (m', g', coq_e') = visit_bexp m g e in
     (m', g', Extraction.DSL.DSL.Iassume coq_e')
  | Ast.Cryptoline.Iecut _ -> failwith "ecut is unsupported in coq-cryptoline"
  | Ast.Cryptoline.Ircut _ -> failwith "rcut is unsupported in coq-cryptoline"
  | Ast.Cryptoline.Ighost _ -> failwith "ghost is unsupported in coq-cryptoline"

let visit_program m g p =
  let helper (m, g, rev_res) i =
    let (m', g', coq_i') = visit_instr m g i in
    (m', g', coq_i'::rev_res) in
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
  let (_, _, coq_spost') = visit_bexp m'' g'' s.Ast.Cryptoline.spost in
  { Extraction.DSL.DSL.sinputs = te';
    Extraction.DSL.DSL.spre = coq_spre';
    Extraction.DSL.DSL.sprog = coq_sprog';
    Extraction.DSL.DSL.spost = coq_spost'
  }
