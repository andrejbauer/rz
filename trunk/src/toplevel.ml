open Message

let read fn =
  print_endline ("Parsing " ^ fn) ;
  let fin = open_in fn in
  let e = Parser.theoryspecs Lexer.token (Lexing.from_channel fin) in
    close_in fin ;
    e

let parse str = Parser.theoryspecs Lexer.token (Lexing.from_string str);;

exception BadArgs;;

if Array.length(Sys.argv) <> 2 then 
  (print_endline ("Usage:  " ^ Sys.argv.(0) ^ " <filename to parse>");
   raise BadArgs)
else
  let thy = read Sys.argv.(1) in
  let _ = print_endline ("Parsed.") in
  let thy' = List.map (Infer.annotateTheorySpec Infer.emptyCtx) thy in
  let _ = print_endline ("Typechecked.") in
  let lthy = List.map Logic.make_theoryspec thy' in
  let _ = print_endline "Translated to Logic form" in
  let spec = List.map Translate.translateTheory lthy in
  let _ = print_endline "Translated to a specification:\n-----------\n" in
  let _ = List.iter (fun s -> print_string (Outsyn.string_of_signat s)) spec in
  let spec2 = List.map Opt.optSignat spec in
  let _ = print_endline "\n-------\nOptimized specification:\n-----------\n" in
    List.iter (fun s -> print_string (Outsyn.string_of_signat s)) spec2
