open BinNat
open BinNums
open BinPos
open Datatypes

module Z =
 struct
  (** val zero : coq_Z **)

  let zero =
    Z0

  (** val one : coq_Z **)

  let one =
    Zpos Coq_xH

  (** val double : coq_Z -> coq_Z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_xO p)
  | Zneg p -> Zneg (Coq_xO p)

  (** val succ_double : coq_Z -> coq_Z **)

  let succ_double = function
  | Z0 -> Zpos Coq_xH
  | Zpos p -> Zpos (Coq_xI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : coq_Z -> coq_Z **)

  let pred_double = function
  | Z0 -> Zneg Coq_xH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (Coq_xI p)

  (** val pos_sub : positive -> positive -> coq_Z **)

  let rec pos_sub x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> double (pos_sub p q)
       | Coq_xO q -> succ_double (pos_sub p q)
       | Coq_xH -> Zpos (Coq_xO p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> pred_double (pos_sub p q)
       | Coq_xO q -> double (pos_sub p q)
       | Coq_xH -> Zpos (Pos.pred_double p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Zneg (Coq_xO q)
       | Coq_xO q -> Zneg (Pos.pred_double q)
       | Coq_xH -> Z0)

  (** val add : coq_Z -> coq_Z -> coq_Z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : coq_Z -> coq_Z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val succ : coq_Z -> coq_Z **)

  let succ x =
    add x (Zpos Coq_xH)

  (** val pred : coq_Z -> coq_Z **)

  let pred x =
    add x (Zneg Coq_xH)

  (** val sub : coq_Z -> coq_Z -> coq_Z **)

  let sub m n =
    add m (opp n)

  (** val mul : coq_Z -> coq_Z -> coq_Z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : coq_Z -> positive -> coq_Z **)

  let pow_pos z =
    Pos.iter (mul z) (Zpos Coq_xH)

  (** val pow : coq_Z -> coq_Z -> coq_Z **)

  let pow x = function
  | Z0 -> Zpos Coq_xH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : coq_Z -> coq_Z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> coq_CompOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : coq_Z -> coq_Z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : coq_Z -> coq_Z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : coq_Z -> coq_Z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : coq_Z -> coq_Z -> coq_Z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val to_nat : coq_Z -> int **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> coq_Z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Pos.of_succ_nat n0))
      n

  (** val of_N : coq_N -> coq_Z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val quotrem : coq_Z -> coq_Z -> coq_Z * coq_Z **)

  let quotrem a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in ((of_N q), (of_N r))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((of_N q), (opp (of_N r))))

  (** val even : coq_Z -> bool **)

  let even = function
  | Z0 -> true
  | Zpos p -> (match p with
               | Coq_xO _ -> true
               | _ -> false)
  | Zneg p -> (match p with
               | Coq_xO _ -> true
               | _ -> false)

  (** val odd : coq_Z -> bool **)

  let odd = function
  | Z0 -> false
  | Zpos p -> (match p with
               | Coq_xO _ -> false
               | _ -> true)
  | Zneg p -> (match p with
               | Coq_xO _ -> false
               | _ -> true)

  (** val div2 : coq_Z -> coq_Z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | Coq_xH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val log2 : coq_Z -> coq_Z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | Coq_xI p -> Zpos (Pos.size p)
     | Coq_xO p -> Zpos (Pos.size p)
     | Coq_xH -> Z0)
  | _ -> Z0

  (** val eq_dec : coq_Z -> coq_Z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos p0 -> Pos.eq_dec p p0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg p0 -> Pos.eq_dec p p0
                 | _ -> false)

  (** val log2_up : coq_Z -> coq_Z **)

  let log2_up a =
    match compare (Zpos Coq_xH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> Z0

  (** val b2z : bool -> coq_Z **)

  let b2z = function
  | true -> Zpos Coq_xH
  | false -> Z0
 end
