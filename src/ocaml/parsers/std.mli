
open Ast.Cryptoline

val spec_from_file : string -> VS.t * spec
val spec_from_string : string -> VS.t * spec

val program_from_file : string -> program
val program_from_string : string -> program
