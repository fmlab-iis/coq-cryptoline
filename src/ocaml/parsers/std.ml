
open Common

let spec_from_lexbuf lexbuf =
  try
    CryptolineParser.spec CryptolineLexer.token lexbuf
  with
  | Failure msg -> raise (Failure ("Error at line " ^ string_of_int !lnum ^ ". " ^ msg))
  | Parsing.Parse_error ->
    let l = !lnum in
    let c = !cnum in
    let msg = Printf.sprintf "Parser error at line %d char %d." l c in
    raise (Failure msg)

let spec_from_file file =
  spec_from_lexbuf (Lexing.from_channel (open_in file))

let spec_from_string str =
  spec_from_lexbuf (Lexing.from_string str)

let program_from_lexbuf lexbuf =
  try
    CryptolineParser.prog CryptolineLexer.token lexbuf
  with
  | Failure msg -> raise (Failure ("Error at line " ^ string_of_int !lnum ^ ". " ^ msg))
  | Parsing.Parse_error ->
    let l = !lnum in
    let c = !cnum in
    let msg = Printf.sprintf "Parser error at line %d char %d." l c in
    raise (Failure msg)

let program_from_file file =
  program_from_lexbuf (Lexing.from_channel (open_in file))

let program_from_string str =
  program_from_lexbuf (Lexing.from_string str)
