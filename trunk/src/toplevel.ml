open Message

let read fn =
  print_string ("Parsing " ^ fn ^ "\n") ;
  let fin = open_in fn in
  let e = Parser.theoryspecs Lexer.token (Lexing.from_channel fin) in
  let _ = print_string ("Successfully parsed.\n") in
    close_in fin ;
    e

let parse str = Parser.theoryspecs Lexer.token (Lexing.from_string str);;

exception BadArgs;;

if Array.length(Sys.argv) <> 2 then 
  (print_string ("Usage:  " ^ Sys.argv.(0) ^ " <filename to parse>\n");
   raise BadArgs)
else
  let thy = read Sys.argv.(1) in
  thy 


