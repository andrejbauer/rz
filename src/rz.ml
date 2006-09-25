(** Top level
      @see <http://caml.inria.fr/ocaml/htmlman/libref/Arg.html> for information on adding further command-line options.
*)

open Message

exception BadArgs;;

(** Possible command-line options.  Ocaml automatically adds
    -help and --help.
*)
let command_line_options = 
  let    fSet = ((fun x -> Arg.Set x), true)
  in let fClear = ((fun x -> Arg.Clear x), false)
  in let flag_data = 
    [("--opt", fSet, Flags.do_opt, "Turn on simplification optimations");
     ("--noopt", fClear, Flags.do_opt,"Turn off simplification optimizations");
     ("--thin", fSet, Flags.do_thin, "Strip top type from output");
     ("--nothin", fClear, Flags.do_thin, "Do not strip top type from output");
     ("--show", fSet, Flags.do_print, "Show output on stdout");
     ("--noshow", fClear, Flags.do_print, "No output to stdout");
     ("--save", fSet, Flags.do_save, "Send output to .mli file");
     ("--nosave", fClear, Flags.do_save, "No output to file");
     ("--hoist", fSet, Flags.do_hoist, "Hoist all assurances");
     ("--nohoist", fClear, Flags.do_hoist, "Don't hoist all assurances");
     ("--sigapp", fSet, Flags.do_sigapp, "Retain signature applications");
     ("--nosigapp", fClear, Flags.do_sigapp, "Expand away signature applications");
     ("--dump_infer", fSet, Flags.do_dumpinfer, "Dump result of type inference");
    ]
  in let other_flags = 
     [
     ("--columns", Arg.Int Format.set_margin, "Number of columns in output")
     ]
  in let processFlag (flag, (action,result) , boolref, description) =
    (flag, action boolref, 
     description ^ (if (!boolref = result) then " (default)" else ""))
  in
       (List.map processFlag flag_data) @ other_flags

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
    let e = Coq_parser.toplevels Coq_lexer.token lexbuf in
      (close_in fin ;
       e)
  with
    Message.Parse(_,msg) ->
      let pos = lexbuf.Lexing.lex_curr_p in
      begin
        print_string "Syntax error detected at line ";
        print_string ( string_of_int pos.Lexing.pos_lnum );
        print_string " column ";
        print_string ( string_of_int ( pos.Lexing.pos_cnum - 
					 pos.Lexing.pos_bol ) );
        print_string ":\n\n";
	print_endline msg;
        raise Parsing.Parse_error 
      end

(* Helper function:  parses a string [currently unused]. *)
let parse str = Coq_parser.toplevels Coq_lexer.token (Lexing.from_string str);;

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
    ([], _, _, _, _) -> ()
  | (fn::fns, infer_state, translate_state, thin_state, opt_state) ->
      let thy = read fn in

      let (infer_state', lthy) = 
	try
	  Newinfer.annotateToplevels infer_state thy 
	with 
	    Error.TypeError msgs -> 
	      (Error.printErrors msgs;
	       failwith "Typechecking failed.")

      in let _ = 
	(if (! Flags.do_dumpinfer) then
          let print_item tplvl = 
	    (print_endline (Logic.string_of_toplevel tplvl);
	     print_endline "")
	  in (print_endline "----------------";
	      print_endline "After Inference:";
	      print_endline "----------------";
	      List.iter print_item lthy;
	      print_string "\n\n\n";
	      Error.printAndResetWarnings())
	else ()) in


      let (spec,translate_state') = 
	Translate.translateToplevel translate_state lthy in

      let (spec, thin_state') =
	try (Thin.thinToplevels thin_state spec) with
	    (Thin.Impossible s) as exn -> (print_endline s; raise exn) in

      let (spec2,opt_state') = 
	(try ( Opt.optToplevels opt_state spec ) with
	    (Opt.Impossible s) as exn -> (print_endline s; raise exn) ) in

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

      (** We put these messages after any displayed code so that
          they are more likely to be seen. *)

      let _ = Error.printAndResetWarnings() in
      let _ = if (!Flags.do_save) then
                 print_string ("[Output saved in " ^ outfile ^ "]\n") 
              else () 
		
      in 
	process (fns, infer_state', translate_state', thin_state', opt_state');;

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
	   Logicrules.emptyContext, 
	   Translate.emptyCtx, 
	   Thin.emptyCtx,
	   Opt.emptyCtx)
with
    Arg.Bad s
  | Arg.Help s -> prerr_endline s
