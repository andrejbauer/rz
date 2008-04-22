(** Top Level *)

open Message

(************************)
(** Argument processing *)
(************************)

(** 
      @see <http://caml.inria.fr/ocaml/htmlman/libref/Arg.html> for information on adding further command-line options.
*)

exception BadArgs;;

(** Possible command-line options.  Ocaml automatically adds
    -help and --help.
*)
let command_line_options = 
  let    fSet = ((fun x -> Arg.Set x), true)
  in let fClear = ((fun x -> Arg.Clear x), false)
  in let booleanFlags = 
    [
     ("--hoist",      fSet,   Flags.do_hoist,     "Hoist all assurances");
     ("--nohoist",    fClear, Flags.do_hoist,     "Don't hoist assurances");
     ("--opt",        fSet,   Flags.do_opt,       "Optimize translation");
     ("--noopt",      fClear, Flags.do_opt,       "Don't optimize translation");
     ("--poly",       fSet,   Flags.do_poly,      "Convert functors to polymorphism");
     ("--nopoly",     fClear, Flags.do_poly,      "Don't convert functors to polymorphism");
     ("--save",       fSet,   Flags.do_save,      "Send output to .mli file");
     ("--nosave",     fClear, Flags.do_save,      "No output to .mli file");
     ("--show",       fSet,   Flags.do_print,     "Show output on stdout");
     ("--noshow",     fClear, Flags.do_print,     "No output on stdout");
     ("--sigapp",     fSet,   Flags.do_sigapp,    "Retain signature applications");
     ("--nosigapp",   fClear, Flags.do_sigapp,    "Expand away signature applications");
     ("--thin",       fSet,   Flags.do_thin,      "Remove trivial realizers");
     ("--nothin",     fClear, Flags.do_thin,      "Leave trivial realizers");
     ("--dump_infer", fSet,   Flags.do_dumpinfer, "Dump result of type inference");
    ]
  in let intFlags = 
     [
     ("--columns", Format.set_margin, Format.get_margin, 
      "<int>  Number of columns in output");
     ("--longerr",  Error.set_longerr, Error.get_longerr,
      "<int>  Minimum lines in a 'long' error message")
     ]
  in let extraFlags =
      [
	("--preamble", Arg.String (fun s -> Flags.preamble := Some s), "<file> Preload the given file");
	("-I", Arg.String (fun s -> Flags.include_dir := List.append !Flags.include_dir [s]), "<dir> Add <dir> to the list of include directories")
      ]
  in let processBooleanFlag (flag, (action,result) , boolref, description) =
    (flag, action boolref, 
     description ^ (if (!boolref = result) then " [default]" else ""))
  in let processIntFlag (flag, setter, getter, description) =
    (flag, Arg.Int setter, 
     description ^ " [" ^ string_of_int (getter()) ^ "]")
  in
    extraFlags @
    (List.map processBooleanFlag booleanFlags) @ 
    (List.map processIntFlag intFlags)

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

type state = {infer_state    : Logicrules.context;
               thin_state     : Thin.context;
               opt_state      : Outsynrules.context;
	       files_read     : string list}

let emptyState = {infer_state = Logicrules.emptyContext;
		  thin_state = Thin.emptyContext;
		  opt_state = Outsynrules.emptyContext;
		  files_read = []}




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
let parse str = Parser.toplevels Lexer.token (Lexing.from_string str);;

(* Helper function:  write the final output to a pretty-printing
   formatter. *)
let send_to_formatter ppf toplevels =
   Pp.output_toplevel ppf toplevels

(* Helper function:  find the file with given basename in directory,
   if present, or search also in directories from Flags.include_dir. *)
let find_file directory basename =
  let fn = Filename.concat directory basename in
    if Sys.file_exists fn then
      Some fn
    else begin
	try
	  let candidates =
	    List.map (fun d -> Filename.concat d basename) !Flags.include_dir
	  in
	    Some (List.find Sys.file_exists candidates)
	with Not_found -> None
      end

let rec processOne (state : state) (doWrap,writeOutput) filename =
  (* Normalize the filename; otherwise foo.thy and ./foo.thy
     get treated as different files.  

     XXX Doesn't distinguish between relative and absolute names
     for the same file, but I don't see any easy way to do this
     in OCaml at the moment. *)
  let filename = Filename.concat (Filename.dirname filename) 
                                 (Filename.basename filename)
  in

  (* Now check to see if we've already processed this file. *)
  if List.mem filename state.files_read then
    (* If so, do nothing. *)
    state
  else
    (* Otherwise, read in the file, after recording that the file has been 
       scheduled for reading (to avoid infinite require loops) *)
    let state = { state with files_read = filename :: state.files_read }

    in let (requires,thy_elts) = read filename

    (* Recursively (and silently, without emitting code) process the
       requires so that we can add all their definitions to our state
       (i.e., typing contexts) *)
    in let rec processRequires state = function
	[]    -> state
      | r::rs -> 
	  let directory = Filename.dirname filename
	  in let basename' = String.uncapitalize r ^ ".thy"
	  in
	    (match find_file directory basename' with
	      | None -> failwith ("Could not find " ^ basename')
	      | Some filename ->
		  let state = processOne state (doWrap,false) filename
		  in processRequires state rs)

    in let state = processRequires state requires

      
    (** Following OCaml convention, wrap the input from file foobar.thy
       in the implicit [Parameter Foobar: thy ... end.] *)
    in let thryname =
	String.capitalize 
	   (Filename.chop_extension (Filename.basename filename))
    in let elems = if doWrap then
                     [Syntax.Value(Syntax.Parameter,
			                      [([Name.mk_word(thryname)],
			                       Syntax.Thy thy_elts)])]
			       else 
			         thy_elts


    in let (infer_state', lthys) = 
      try
	     Infer.annotateTheoryElems state.infer_state elems 
      with 
	     Error.TypeError msgs -> 
	       (Error.printErrors msgs;
	       failwith "Typechecking failed.")

    in let _ = 
      (if writeOutput && (! Flags.do_dumpinfer) then
	  (print_endline "----------------";
	   print_endline "After Inference:";
	   print_endline "----------------";
	   print_endline (Logic.string_of_theory_elements lthys);
	   print_string "\n\n\n";
	   Error.printAndResetWarnings())
	else ()) 

    in let spec = 
	Translate.translateToplevel lthys in

(*      let _ = if (!Flags.do_print) 
             then print_string ("[Thinning " ^ fn ^ "]\n") 
          else () in
*)

      let (spec, thin_state') =
	try (Thin.thinToplevels state.thin_state spec) with
	    (Thin.Impossible s) as exn -> (print_endline s; raise exn) in

(*      let _ = if (!Flags.do_print) 
             then print_string ("[Optimizing " ^ fn ^ "]\n") 
          else () in
*)
      let (spec2,opt_state') = 
	Opt.optToplevels state.opt_state spec in


      let spec3 = 
        if (doWrap) then
	        match spec2 with
	          [Outsyn.Spec(_, Outsyn.ModulSpec(Outsyn.Signat elts), _)] ->
	               elts  
	        | _ -> failwith "Cannot unwrap translated code"
	    else
	        spec2
      in

      let spec4 = fst (Rename.renSignatElementList Rename.emptyRen spec3) in

      (** The output file replaces the .thr extension by .mli *)
      let outfile = (Filename.chop_extension filename) ^ ".mli" in

      (** Write the output file 
      *)
      let _ =
	if (!Flags.do_save) then
 	  let outb = Buffer.create 1024 in
	  let formatter = Format.formatter_of_buffer outb in
	    Format.pp_set_margin formatter (Format.get_margin ()) ;
	    let outchan = open_out outfile in
	    let _ = send_to_formatter formatter spec4 in
	    let _ = Buffer.output_buffer outchan outb in
	      close_out outchan
	else () in
	
      (** Optionally display to stdout as well.
      *)
      let _ = if (writeOutput && !Flags.do_print) then
	       send_to_formatter Format.std_formatter spec4
              else ()  in

      (** We put these messages after any displayed code so that
          they are more likely to be seen. *)

      let _ = Error.printAndResetWarnings() in
      let _ = if (!Flags.do_save) then
                 print_string ("[Output saved in " ^ outfile ^ "]\n") 
              else () 
		
      in 
	{state with infer_state = infer_state';
	  thin_state = thin_state';
	  opt_state = opt_state'}
	  
let rec process state = function
    [] -> ()
  | filename::filenames  ->
      let state = processOne state (true,true) filename
      in process state filenames


;;
  
let load_preamble state f = 
    processOne state (false,false) f
;;


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

  (** Load the preamble *)
  let initialState = begin
    match !Flags.preamble with
      | None -> emptyState
      | Some f -> load_preamble emptyState f
  end in

  (** Finally, translate the theories in the order specified on the
    command-line (which is the reverse of the order that they were
    stored).
  *)
    process initialState (List.rev !filenames)

with
    Arg.Bad s
  | Arg.Help s -> prerr_endline s

