
open Common

let spec_from_lexbuf ?vector:(vector=false) lexbuf =
  try
    if vector then
      VectorCryptolineParser.spec VectorCryptolineLexer.token lexbuf
    else
      CryptolineParser.spec CryptolineLexer.token lexbuf
  with
  | Failure msg -> raise (Failure ("Error at line " ^ string_of_int !lnum ^ ". " ^ msg))
  | Parsing.Parse_error ->
    let l = !lnum in
    let c = !cnum in
    let msg = Printf.sprintf "Parser error at line %d char %d." l c in
    raise (Failure msg)

let spec_from_file ?vector:(vector=false) file =
  spec_from_lexbuf ~vector:vector (Lexing.from_channel (open_in file))

let spec_from_string ?vector:(vector=false) str =
  spec_from_lexbuf ~vector:vector (Lexing.from_string str)

let program_from_lexbuf ?vector:(vector=false) lexbuf =
  try
    if vector then
      VectorCryptolineParser.prog VectorCryptolineLexer.token lexbuf
    else
      CryptolineParser.prog CryptolineLexer.token lexbuf
  with
  | Failure msg -> raise (Failure ("Error at line " ^ string_of_int !lnum ^ ". " ^ msg))
  | Parsing.Parse_error ->
    let l = !lnum in
    let c = !cnum in
    let msg = Printf.sprintf "Parser error at line %d char %d." l c in
    raise (Failure msg)

let program_from_file ?vector:(vector=false) file =
  program_from_lexbuf ~vector:vector (Lexing.from_channel (open_in file))

let program_from_string ?vector:(vector=false) str =
  program_from_lexbuf ~vector:vector (Lexing.from_string str)
