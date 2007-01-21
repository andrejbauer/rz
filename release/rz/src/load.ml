#load "name.cmo";;
#load "message.cmo";;
#load "coq_parser.cmo";;
#load "coq_lexer.cmo";;
(* #load "toplevel.cmo";; *)

let fin = open_in "t0.thy";;

let lexbuf = Lexing.from_channel fin;;

let f() = Coq_lexer.token lexbuf;;

let rec tokenize () = 
  let next = f()
  in if (next = Coq_parser.EOF) then 
      [Coq_parser.EOF]
    else next :: tokenize()


