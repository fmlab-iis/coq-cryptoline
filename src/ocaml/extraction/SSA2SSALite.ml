open Seqs

(** val rewrite_mov : SSA.SSA.spec -> SSA.SSA.spec **)

let rewrite_mov s =
  s

(** val ssa2lite_instr : SSA.SSA.instr -> SSALite.SSALite.instr **)

let ssa2lite_instr = function
| SSA.SSA.Imov (v, a) -> SSALite.SSALite.Imov (v, a)
| SSA.SSA.Ishl (v, a, n) -> SSALite.SSALite.Ishl (v, a, n)
| SSA.SSA.Icshl (v1, v2, a1, a2, n) ->
  SSALite.SSALite.Icshl (v1, v2, a1, a2, n)
| SSA.SSA.Inondet (v, t) -> SSALite.SSALite.Inondet (v, t)
| SSA.SSA.Icmov (v, c, a1, a2) -> SSALite.SSALite.Icmov (v, c, a1, a2)
| SSA.SSA.Inot (v, t, a) -> SSALite.SSALite.Inot (v, t, a)
| SSA.SSA.Iadd (v, a1, a2) -> SSALite.SSALite.Iadd (v, a1, a2)
| SSA.SSA.Iadds (c, v, a1, a2) -> SSALite.SSALite.Iadds (c, v, a1, a2)
| SSA.SSA.Iadc (v, a1, a2, y) -> SSALite.SSALite.Iadc (v, a1, a2, y)
| SSA.SSA.Iadcs (c, v, a1, a2, y) -> SSALite.SSALite.Iadcs (c, v, a1, a2, y)
| SSA.SSA.Isub (v, a1, a2) -> SSALite.SSALite.Isub (v, a1, a2)
| SSA.SSA.Isubc (c, v, a1, a2) -> SSALite.SSALite.Isubc (c, v, a1, a2)
| SSA.SSA.Isubb (c, v, a1, a2) -> SSALite.SSALite.Isubb (c, v, a1, a2)
| SSA.SSA.Isbc (v, a1, a2, y) -> SSALite.SSALite.Isbc (v, a1, a2, y)
| SSA.SSA.Isbcs (c, v, a1, a2, y) -> SSALite.SSALite.Isbcs (c, v, a1, a2, y)
| SSA.SSA.Isbb (v, a1, a2, y) -> SSALite.SSALite.Isbb (v, a1, a2, y)
| SSA.SSA.Isbbs (c, v, a1, a2, y) -> SSALite.SSALite.Isbbs (c, v, a1, a2, y)
| SSA.SSA.Imul (v, a1, a2) -> SSALite.SSALite.Imul (v, a1, a2)
| SSA.SSA.Imull (vh, vl, a1, a2) -> SSALite.SSALite.Imull (vh, vl, a1, a2)
| SSA.SSA.Imulj (v, a1, a2) -> SSALite.SSALite.Imulj (v, a1, a2)
| SSA.SSA.Isplit (vh, vl, a, n) -> SSALite.SSALite.Isplit (vh, vl, a, n)
| SSA.SSA.Iand (v, t, a1, a2) -> SSALite.SSALite.Iand (v, t, a1, a2)
| SSA.SSA.Ior (v, t, a1, a2) -> SSALite.SSALite.Ior (v, t, a1, a2)
| SSA.SSA.Ixor (v, t, a1, a2) -> SSALite.SSALite.Ixor (v, t, a1, a2)
| SSA.SSA.Icast (v, t, a) -> SSALite.SSALite.Icast (v, t, a)
| SSA.SSA.Ivpc (v, t, a) -> SSALite.SSALite.Ivpc (v, t, a)
| SSA.SSA.Ijoin (v, ah, al) -> SSALite.SSALite.Ijoin (v, ah, al)
| SSA.SSA.Iassume e -> SSALite.SSALite.Iassume e
| _ -> SSALite.SSALite.Inop

(** val ssa2lite_program : SSA.SSA.program -> SSALite.SSALite.program **)

let ssa2lite_program p =
  tmap ssa2lite_instr p

(** val ssa2lite_spec : SSA.SSA.spec -> SSALite.SSALite.spec **)

let ssa2lite_spec s =
  { SSALite.SSALite.sinputs = (SSA.SSA.sinputs s); SSALite.SSALite.spre =
    (SSA.SSA.spre s); SSALite.SSALite.sprog =
    (ssa2lite_program (SSA.SSA.sprog s)); SSALite.SSALite.spost =
    (SSA.SSA.spost s) }
