
open Ast.Cryptoline

val spec_from_file : string -> var list * Typecheck.Std.spec
val spec_from_string : string -> var list * Typecheck.Std.spec

val program_from_file : string -> lined_program
val program_from_string : string -> lined_program
