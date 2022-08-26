open BinNat
open BinPos
open Ring_polynom

(** val coq_PExpr_eq :
    ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1 coq_PExpr -> bool **)

let rec coq_PExpr_eq ceqb e e' =
  match e with
  | PEc c -> (match e' with
              | PEc c' -> ceqb c c'
              | _ -> false)
  | PEX p -> (match e' with
              | PEX p' -> Pos.eqb p p'
              | _ -> false)
  | PEadd (e1, e2) ->
    (match e' with
     | PEadd (e1', e2') ->
       if coq_PExpr_eq ceqb e1 e1' then coq_PExpr_eq ceqb e2 e2' else false
     | _ -> false)
  | PEsub (e1, e2) ->
    (match e' with
     | PEsub (e1', e2') ->
       if coq_PExpr_eq ceqb e1 e1' then coq_PExpr_eq ceqb e2 e2' else false
     | _ -> false)
  | PEmul (e1, e2) ->
    (match e' with
     | PEmul (e1', e2') ->
       if coq_PExpr_eq ceqb e1 e1' then coq_PExpr_eq ceqb e2 e2' else false
     | _ -> false)
  | PEopp e0 ->
    (match e' with
     | PEopp e'0 -> coq_PExpr_eq ceqb e0 e'0
     | _ -> false)
  | PEpow (e0, n) ->
    (match e' with
     | PEpow (e'0, n') ->
       if N.eqb n n' then coq_PExpr_eq ceqb e0 e'0 else false
     | _ -> false)
  | _ -> false
