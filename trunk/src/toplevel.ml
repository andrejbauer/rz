open Message

let read fn =
  let fin = open_in fn in
  let e = Parser.theoryspecs Lexer.token (Lexing.from_channel fin) in
    close_in fin ;
    e

let parse str = Parser.theoryspecs Lexer.token (Lexing.from_string str);;

read Sys.argv.(1);;
