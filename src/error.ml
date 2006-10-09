open Name
module S = Syntax
module L = Logic


(************************)
(** {2 Error Reporting} *)
(************************)

(*****************)
(** {3 Warnings} *)
(*****************)

(** Warnings are collected rather than being displayed immediately,
    because often the output runs for more than a page and
    the warnings would just scroll off the screen.

    A type error causes warnings to be displayed immediately (right
    before the type error message).  Otherwise, the top level is
    responsible for calling printAndResetWarnings() at an appropriate
    time when they are likely to be seen.
*)

let warnings = ref ([] : string list)

let tyGenericWarning msg =
  warnings := msg :: (!warnings)


let printAndResetWarnings () =
  let    warning_header = "\n-------------------------------\nWARNING:\n"
  in let warning_footer = "\n-------------------------------\n\n"
  in let printWarn msg  = print_string (warning_header ^ msg ^ warning_footer)
  in
    List.iter printWarn (!warnings);
    warnings := []

let noEqPropWarning prp1 prp2 context_expr =
  tyGenericWarning 
    ("Did not verify that " ^ L.string_of_prop prp1 ^ " and " ^
	L.string_of_prop prp2 ^ " are equivalent in " ^ 
	S.string_of_expr context_expr)

(********************)
(** {3 Type Errors} *)
(********************)

let newline = Str.regexp "[\n]+"
let splitByLine msg = List.rev (Str.split newline msg)

(** The TypeError exception is raised by all type errors 
 *)
exception TypeError of string list

let printErrors msgs =
  let    error_header = "\n-------------------------------\nTYPE ERROR:\n"
  in let error_footer = "-------------------------------\n\n"
  in let printed_long_msg = ref false
  in let lines_to_be_long = 3
  in let isLong str = (List.length (splitByLine str) >= lines_to_be_long)
  in let printError msg = 
    let doPrint() = (print_endline msg; print_endline "")
    in
       if isLong msg then
	 if !printed_long_msg then
	   ()
	 else
	   (printed_long_msg := true;
	    doPrint())
       else
	 doPrint()
  in
  (printAndResetWarnings();
   print_string error_header; 
   List.iter printError (List.rev msgs);
   print_string error_footer)

let tyGenericErrors msgs =
  raise (TypeError msgs)

let indent msg = 
  let lines = (Str.split newline msg)
  in let lines' = List.map (fun s -> "        " ^ s) lines
  in let msg' = String.concat "\n" lines'
  in msg'


let addSpecifically msgs =
  match (List.rev msgs) with
    [] -> []
  | (msg::msgs) ->
      let lines = Str.split newline msg
      in let lines' = ("Specifically: " ^ List.hd lines) :: List.tl lines
      in let msg' = String.concat "\n" lines'
      in List.rev (msg' :: msgs)

let tyGenericError msg = 
  tyGenericErrors [msg]

let generalizeError msgs msg =
  tyGenericErrors (msg ::  msgs)

let specificateError msgs msg =
  let msgs' = addSpecifically msgs
  in let msgs'' = List.map indent msgs'
  in
     tyGenericErrors (msgs'' @ [msg])

let inMsg expr =
  ("...in:  " ^ S.string_of_expr expr)

let inElemMsg elem =
  ("...in:  " ^ S.string_of_theory_element elem)


let tyUnboundMsg nm =
    ("Unbound name " ^ string_of_name nm)

let tyUnboundError nm =
  tyGenericError (tyUnboundMsg nm)


let notWhatsExpectedMsg expr expected =
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected")

let notWhatsExpectedInMsg expr expected context_expr =
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected, in " ^ S.string_of_expr context_expr)

let notWhatsExpectedInError expr expected context_expr =
  tyGenericError (notWhatsExpectedInMsg expr expected context_expr)


let noHigherOrderLogicMsg expr =
     ("The input " ^ S.string_of_expr expr ^ " requires higher-order-logic")

let noHigherOrderLogicError expr =
   tyGenericError (noHigherOrderLogicMsg expr)


let noPolymorphismMsg expr =
     ("The input " ^ S.string_of_expr expr ^ " requires polymorphism")

let noPolymorphismError expr =
   tyGenericError (noPolymorphismMsg expr)


let noNestedTheoriesMsg nm =
     ("Bad theory definition (" ^ string_of_name nm ^ 
	 "); theory definitions cannot be nested.")

let noNestedTheoriesError nm =
   tyGenericError (noNestedTheoriesMsg nm)


let noTypeInferenceMsg nm =
     ("The bound variable " ^ string_of_name nm ^ 
      " is not annotated explicitly or implicitly.")

let noTypeInferenceInError nm expr =
  tyGenericError (noTypeInferenceMsg nm)


let wrongTypeMsg expr hastype expectedsort =
    ("The term " ^ S.string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ 
      "\nbut it actually has type " ^ L.string_of_set hastype)

let wrongTypeError expr hastype expectedsort context_expr =
  tyGenericError (wrongTypeMsg expr hastype expectedsort)


let wrongPropTypeMsg expr hasPT expectedsort =
    ("The term " ^ S.string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^
      "\nbut it actually has type " ^ L.string_of_proptype hasPT)

let wrongPropTypeError expr hasPT expectedsort context_expr =
  tyGenericError (wrongPropTypeMsg expr hasPT expectedsort)


let wrongKindMsg expr hasK expectedsort =
    ("The set " ^ S.string_of_expr expr ^ "\nis used as if had a "
      ^ expectedsort ^ " kind" ^
      "\nbut it actually has kind " ^ L.string_of_kind hasK)

let wrongKindError expr hasK expectedsort context_expr =
  tyGenericError (wrongKindMsg expr hasK expectedsort)


let wrongTheoryMsg expr hasthry expectedsort =
    ("The model " ^ S.string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ 
      "\nbut it actually has the theory " ^ L.string_of_theory hasthry)

let wrongTheoryError expr hasthry expectedsort context_expr =
  tyGenericError (wrongTheoryMsg expr hasthry expectedsort)


let tyMismatchMsg expr expectedTy foundTy =
  ("The term " ^ S.string_of_expr expr ^ " was expected to have type " ^
      L.string_of_set expectedTy ^ " instead of type " ^ 
      L.string_of_set foundTy)
    
let tyMismatchError expr expectedTy foundTy context_expr =
  tyGenericError (tyMismatchMsg expr expectedTy foundTy)


let propTypeMismatchMsg expr expectedTy foundTy =
  ("The proposition " ^ S.string_of_expr expr ^ " was expected to have type " ^
	L.string_of_proptype expectedTy ^ " instead of type " ^ 
	L.string_of_proptype foundTy)

let propTypeMismatchError expr expectedTy foundTy context_expr =
  tyGenericError (propTypeMismatchMsg expr expectedTy foundTy)


let kindMismatchMsg expr expectedK foundK =
    ("The set " ^ S.string_of_expr expr ^ " was expected to have kind " ^
	L.string_of_kind expectedK ^ " instead of kind " ^ 
	L.string_of_kind foundK)

let kindMismatchError expr expectedK foundK context_expr =
  tyGenericError (kindMismatchMsg expr expectedK foundK)


let theoryMismatchMsg expr expectedT foundT =
  ("The model " ^ S.string_of_expr expr ^ 
      " was expected to satisfy theory\n\n" ^
      L.string_of_theory expectedT ^ "\n\ninstead of theory\n\n" ^ 
      L.string_of_theory foundT)

let theoryMismatchError expr expectedT foundT context_expr =
  tyGenericError (theoryMismatchMsg expr expectedT foundT)


let notEquivalenceOnMsg expr expectedDomExpr =
    ("The relation " ^ S.string_of_expr expr ^ 
	" is not an equivalence relation on " ^ 
	S.string_of_expr expectedDomExpr)

let notEquivalenceOnError expr expectedDomExpr =
  tyGenericError (notEquivalenceOnMsg expr expectedDomExpr)


let cantElimMsg nm ty expr =
    ("Inferred type " ^ L.string_of_set ty ^ " of " ^ S.string_of_expr expr ^ 
	"\nrefers to the variable " ^ string_of_name nm ^
	" going out of scope.  (Maybe a constraint would help?)")

let cantElimError nm ty expr =
  tyGenericError (cantElimMsg nm ty expr)


let cantElimPTMsg nm pt expr =
    ("Inferred type " ^ L.string_of_proptype pt ^ " of " 
      ^ S.string_of_expr expr ^ 
	"\nrefers to the variable " ^ string_of_name nm ^
	" going out of scope.  (Maybe a constraint would help?)")

let cantElimPTError nm pt expr =
  tyGenericError (cantElimPTMsg nm pt expr)


let tyJoinMsg ty1 ty2 =
     ("the types " ^ L.string_of_set ty1 ^ " and " ^
	 L.string_of_set ty2 ^ " are incompatible")

let tyJoinError ty1 ty2 =
   tyGenericError (tyJoinMsg ty1 ty2)


let tyPTJoinMsg pt1 pt2 =
     ("the types " ^ L.string_of_proptype pt1 ^ " and " ^
	 L.string_of_proptype pt2 ^ " are incompatible")

let tyPTJoinError pt1 pt2 =
   tyGenericError (tyPTJoinMsg pt1 pt2)


let badModelProjMsg nm expr why =
    ("Cannot project " ^ string_of_name nm ^ " in " ^ S.string_of_expr expr
      ^ "\n" ^ why )
	
let badModelProjectionError nm expr why =
  tyGenericError (badModelProjMsg nm expr why)


let innerModelBindingMsg context_expr =
    ("A non-top-level binding of a model variable was found:\n"
      ^ S.string_of_expr context_expr)

let innerModelBindingError context_expr =
  tyGenericError (innerModelBindingMsg context_expr)


let illegalBindingMsg nm where_type_came_from =
    ("The annotation " ^ (S.string_of_expr where_type_came_from) 
        ^ " for " ^ string_of_name nm ^
	" is the wrong sort of entity to appear in a binding")

let illegalBindingError nm annot_expr context_expr =
  tyGenericError (illegalBindingMsg nm annot_expr)

 
let illegalNameMsg nm what_kind_its_supposed_to_be =
    ("The name " ^ string_of_name nm ^ " is not legal for a " ^
	what_kind_its_supposed_to_be)

let illegalNameError nm what_kind_its_supposed_to_be =
  tyGenericError (illegalNameMsg nm what_kind_its_supposed_to_be)


let shadowingMsg nm =
    ("Illegal shadowing; the name " ^ string_of_name nm ^ 
	" appears twice in the same context," ^ 
        "\nand automatic renaming is not possible.")

let shadowingError nm =
  tyGenericError (shadowingMsg nm)
     

