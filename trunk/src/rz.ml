(** Top level
      @see <http://caml.inria.fr/ocaml/htmlman/libref/Arg.html> for information on adding further command-line options.
*)

open Message

exception BadArgs;;

(** Possible command-line options.  Ocaml automatically adds
    -help and --help.
*)
let command_line_options = 
  [("--opt", Arg.Set Flags.do_opt, "Turn on simplification optimations (default)");
   ("--noopt", Arg.Clear Flags.do_opt,"Turn off simplification optimizations");
   ("--show", Arg.Set Flags.do_print, "Show output on stdout (default)");
   ("--noshow", Arg.Clear Flags.do_print, "No output to stdout");
   ("--save", Arg.Set Flags.do_save, "Send output to .mli file (default)");
   ("--nosave", Arg.Clear Flags.do_save, "No output to file");
   ("--sigapp", Arg.Set Flags.do_sigapp, "Retain signature applications");
   ("--nosigapp", Arg.Clear Flags.do_sigapp, "Expand away signature applications (default)")
  ]

(** One-line usage message
 *)
let usage_msg = 
  "Usage:  " ^ Sys.argv.(0) ^ " <options> [filenames]"

(** A list of files to process, stored in REVERSE order *)
let filenames : string list ref = ref [] 

(** Add a file specified on the command-line to the list
    of files to process *)
let addFile strng = 
  filenames := strng :: !filenames

(* Helper function:  parses a given filename *)
let read fn =
  let _ = if (!Flags.do_print) 
             then print_string ("[Processing " ^ fn ^ "]\n") 
          else () in
  let fin = open_in fn in
  let lexbuf = Lexing.from_channel fin in
  try
    let e = Parser.toplevels Lexer.token lexbuf in
      (close_in fin ;
       e)
  with
    Message.Parse(_,_) ->
      let pos = lexbuf.Lexing.lex_curr_p in
      begin
        print_string "Syntax error detected at line ";
        print_string ( string_of_int pos.Lexing.pos_lnum );
        print_string " column ";
        print_string ( string_of_int ( pos.Lexing.pos_cnum - 
					 pos.Lexing.pos_bol ) );
        print_string "\n";
        raise Parsing.Parse_error 
      end

(* Helper function:  parses a string [currently unused]. *)
let parse str = Parser.toplevels Lexer.token (Lexing.from_string str);;

(* Helper function:  write the final output to a pretty-printing
   formatter. *)
let send_to_formatter ppf toplevels =
   List.iter (fun s -> Pp.output_toplevel ppf s) toplevels;;


(** Main function for translating theories into code.  Takes a
    filename and the current "states" (really the context obtained
    at the end of) type inference, translation, and optimization.
    Successively processes each file in turn, using each updated
    state to process the following file.  Thus, dependencies between
    files are allowed, as long filenames are given in an order
    that respects dependencies.
*)
let rec process = function
    ([], _, _, _) -> ()
  | (fn::fns, infer_state, translate_state, opt_state) ->
      let thy = read fn in

      let (thy', infer_state') = 
	Infer.annotateToplevels infer_state thy in

(*
      let _ = 
        let print_item tplvl = 
	   (print_endline (Syntax.string_of_toplevel tplvl);
	    print_endline "")
	in List.iter print_item thy' in
*)

      let lthy = 
	(* The translation to Logic form is syntax-directed and 
	   doesn't need to maintain any state *)
	List.map Logic.make_toplevel thy' in

      let (spec,translate_state') = 
	Translate.translateToplevel translate_state lthy in

      let (spec2,opt_state') = 
	Opt.optToplevels opt_state spec in
	
      (** The output file replaces the .thr extension by .mli *)
      let outfile = (Filename.chop_extension fn) ^ ".mli" in

      (** Write the output file 
      *)
      let _ = if (!Flags.do_save) then
 	        let outb = Buffer.create 1024 in
		let formatter = Format.formatter_of_buffer outb in
 		let outchan = open_out outfile in
		let _ = send_to_formatter formatter spec2 in
		let _ = Buffer.output_buffer outchan outb in
		close_out outchan
              else () in
	
      (** Optionally display to stdout as well.
      *)
      let _ = if (!Flags.do_print) then
	       send_to_formatter Format.std_formatter spec2
              else ()  in

      (** We put this message after any displayed code so that
          it is more likely to be seen. *)
      let _ = if (!Flags.do_save) then
                 print_string ("[Output saved in " ^ outfile ^ "]\n") 
              else () 
		
      in 
	process (fns, infer_state', translate_state', opt_state');;

(** MAIN PROGRAM *)

try
  (** Check that we have specified at least one file.
    (Of course, we could just as well omit this check and simply 
    do nothing if no filenames are specified)
  *)
  begin
    if Array.length(Sys.argv) >= 2 then
    (** If so, parse all the command-line options and store the names
      of all the files to be processed *)
      Arg.parse_argv Sys.argv command_line_options addFile usage_msg 
    else
      Arg.usage command_line_options usage_msg
  end ;

  (** Finally, translate the theories in the order specified on the
    command-line (which is the reverse of the order that they were
    stored).
  *)
  process (List.rev !filenames, 
	   Infer.emptyCtx, 
	   Translate.emptyCtx, 
	   Opt.emptyCtx)
with
    Arg.Bad s
  | Arg.Help s -> prerr_endline s
