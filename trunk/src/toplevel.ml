open Message

let read fn =
  let fin = open_in fn in
  let e = Parser.theory Lexer.token (Lexing.from_channel fin) in
    close_in fin ;
    e

let parse str = Parser.theory Lexer.token (Lexing.from_string str)
