open Message

let read fn =
  print_string ("Parsing " ^ fn ^ "\n") ;
  let fin = open_in fn in
  let e = Parser.theoryspecs Lexer.token (Lexing.from_channel fin) in
    close_in fin ;
    e

let parse str = Parser.theoryspecs Lexer.token (Lexing.from_string str);;

exception BadArgs;;

if Array.length(Sys.argv) <> 2 then 
  (print_string ("Usage:  " ^ Sys.argv.(0) ^ " <filename to parse>\n");
   raise BadArgs)
else
  let thy = read Sys.argv.(1) in
  let _ = print_string ("Parsed.\n") in
  let thy' = List.map (Infer.annotateTheorySpec Infer.emptyCtx) thy in
  let _ = print_string ("Typechecked.\n") in
  let lthy = List.map Logic.make_theoryspec thy' in
  let _ = print_string "Translated to Logic form\n" in
  lthy 


