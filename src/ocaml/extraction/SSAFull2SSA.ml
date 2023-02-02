open Seqs

(** val rewrite_mov : SSAFull.SSAFull.spec -> SSAFull.SSAFull.spec **)

let rewrite_mov s =
  s

(** val ssa2lite_instr : SSAFull.SSAFull.instr -> SSA.SSA.instr **)

let ssa2lite_instr = function
| SSAFull.SSAFull.Imov (v, a) -> SSA.SSA.Imov (v, a)
| SSAFull.SSAFull.Ishl (v, a, n) -> SSA.SSA.Ishl (v, a, n)
| SSAFull.SSAFull.Icshl (v1, v2, a1, a2, n) ->
  SSA.SSA.Icshl (v1, v2, a1, a2, n)
| SSAFull.SSAFull.Inondet (v, t) -> SSA.SSA.Inondet (v, t)
| SSAFull.SSAFull.Icmov (v, c, a1, a2) -> SSA.SSA.Icmov (v, c, a1, a2)
| SSAFull.SSAFull.Inot (v, t, a) -> SSA.SSA.Inot (v, t, a)
| SSAFull.SSAFull.Iadd (v, a1, a2) -> SSA.SSA.Iadd (v, a1, a2)
| SSAFull.SSAFull.Iadds (c, v, a1, a2) -> SSA.SSA.Iadds (c, v, a1, a2)
| SSAFull.SSAFull.Iadc (v, a1, a2, y) -> SSA.SSA.Iadc (v, a1, a2, y)
| SSAFull.SSAFull.Iadcs (c, v, a1, a2, y) -> SSA.SSA.Iadcs (c, v, a1, a2, y)
| SSAFull.SSAFull.Isub (v, a1, a2) -> SSA.SSA.Isub (v, a1, a2)
| SSAFull.SSAFull.Isubc (c, v, a1, a2) -> SSA.SSA.Isubc (c, v, a1, a2)
| SSAFull.SSAFull.Isubb (c, v, a1, a2) -> SSA.SSA.Isubb (c, v, a1, a2)
| SSAFull.SSAFull.Isbc (v, a1, a2, y) -> SSA.SSA.Isbc (v, a1, a2, y)
| SSAFull.SSAFull.Isbcs (c, v, a1, a2, y) -> SSA.SSA.Isbcs (c, v, a1, a2, y)
| SSAFull.SSAFull.Isbb (v, a1, a2, y) -> SSA.SSA.Isbb (v, a1, a2, y)
| SSAFull.SSAFull.Isbbs (c, v, a1, a2, y) -> SSA.SSA.Isbbs (c, v, a1, a2, y)
| SSAFull.SSAFull.Imul (v, a1, a2) -> SSA.SSA.Imul (v, a1, a2)
| SSAFull.SSAFull.Imull (vh, vl, a1, a2) -> SSA.SSA.Imull (vh, vl, a1, a2)
| SSAFull.SSAFull.Imulj (v, a1, a2) -> SSA.SSA.Imulj (v, a1, a2)
| SSAFull.SSAFull.Isplit (vh, vl, a, n) -> SSA.SSA.Isplit (vh, vl, a, n)
| SSAFull.SSAFull.Iand (v, t, a1, a2) -> SSA.SSA.Iand (v, t, a1, a2)
| SSAFull.SSAFull.Ior (v, t, a1, a2) -> SSA.SSA.Ior (v, t, a1, a2)
| SSAFull.SSAFull.Ixor (v, t, a1, a2) -> SSA.SSA.Ixor (v, t, a1, a2)
| SSAFull.SSAFull.Icast (v, t, a) -> SSA.SSA.Icast (v, t, a)
| SSAFull.SSAFull.Ivpc (v, t, a) -> SSA.SSA.Ivpc (v, t, a)
| SSAFull.SSAFull.Ijoin (v, ah, al) -> SSA.SSA.Ijoin (v, ah, al)
| SSAFull.SSAFull.Iassume e -> SSA.SSA.Iassume e
| _ -> SSA.SSA.Inop

(** val ssa2lite_program : SSAFull.SSAFull.program -> SSA.SSA.program **)

let ssa2lite_program p =
  tmap ssa2lite_instr p

(** val ssa2lite_spec : SSAFull.SSAFull.spec -> SSA.SSA.spec **)

let ssa2lite_spec s =
  { SSA.SSA.sinputs = (SSAFull.SSAFull.sinputs s); SSA.SSA.spre =
    (SSAFull.SSAFull.spre s); SSA.SSA.sprog =
    (ssa2lite_program (SSAFull.SSAFull.sprog s)); SSA.SSA.spost =
    (SSAFull.SSAFull.spost s) }
