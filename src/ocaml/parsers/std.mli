
open Ast.Cryptoline

val spec_from_file : ?vector:bool -> string -> VS.t * spec
val spec_from_string : ?vector:bool -> string -> VS.t * spec

val program_from_file : ?vector:bool -> string -> program
val program_from_string : ?vector:bool -> string -> program
