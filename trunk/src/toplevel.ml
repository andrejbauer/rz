open Message

let read fn =
  let _ = print_string ("parsing " ^ fn ^ "\n") in
  let fin = open_in fn in
  let e = Parser.theoryspecs Lexer.token (Lexing.from_channel fin) in
    close_in fin ;
    e

let parse str = Parser.theoryspecs Lexer.token (Lexing.from_string str);;

if Array.length(Sys.argv) = 2 then 
  ignore (read Sys.argv.(1))
else
  print_string ("Usage:  " ^ Sys.argv.(0) ^ " <filename to parse>\n");;
