
(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val get : int -> char list -> char option **)

let rec get n = function
| [] -> None
| c::s' ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some c)
     (fun n' -> get n' s')
     n)

(** val concat : char list -> char list list -> char list **)

let rec concat sep = function
| [] -> []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))
