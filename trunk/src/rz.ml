open Message

let read fn =
  let fin = open_in fn in
  let e = Parser.toplevels Lexer.token (Lexing.from_channel fin) in
    close_in fin ;
    e

let parse str = Parser.toplevels Lexer.token (Lexing.from_string str);;

exception BadArgs;;

if Array.length(Sys.argv) <> 2 && Array.length(Sys.argv) <> 3 then 
  (print_endline ("Usage:  " ^ Sys.argv.(0) ^ " [--noopt] <filename to parse>");
   raise BadArgs)
else
  let opt = Sys.argv.(1) <> "--noopt" in
  let fn = (if opt then Sys.argv.(1) else Sys.argv.(2)) in
  let thy = read fn in
  let thy' = Infer.annotateToplevels Infer.emptyCtx thy in
  let lthy = List.map Logic.make_toplevel thy' in
  let spec = Translate.translateToplevels Translate.emptyCtx lthy in
  let spec2 = if opt then Opt.optToplevels Opt.emptyCtx spec else spec in
(List.iter (fun s -> print_string ((Outsyn.string_of_toplevel s) ^ "\n")) spec2;
print_string "-------------\n";
List.iter (fun s -> Pp.output_toplevel Format.std_formatter s) spec2)
