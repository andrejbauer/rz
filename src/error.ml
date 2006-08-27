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

(** The TypeError exception is raised by all type errors 
 *)
exception TypeError


let tyGenericError msg = 
  let    error_header = "\n-------------------------------\nTYPE ERROR:\n"
  in let error_footer = "\n-------------------------------\n\n"
  in 
       (printAndResetWarnings();
	print_string (error_header ^ msg ^ error_footer);
	raise TypeError)

let tyUnboundError nm =
  tyGenericError
    ("Unbound name " ^ string_of_name nm)

let notWhatsExpectedError expr expected =
  tyGenericError
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected")

let notWhatsExpectedInError expr expected context_expr =
  tyGenericError
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected, in " ^ S.string_of_expr context_expr)

let noHigherOrderLogicError expr =
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires higher-order-logic")

let noPolymorphismError expr =
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires polymorphism")

let noNestedTheoriesError nm =
   tyGenericError
     ("Bad theory definition (" ^ string_of_name nm ^ 
	 "); theory definitions cannot be nested.")

let noTypeInferenceInError nm expr =
  tyGenericError
     ("The bound variable " ^ string_of_name nm ^ " in " ^
      S.string_of_expr expr ^ " is not annotated explicitly or implicitly.")

let wrongTypeError expr hastype expectedsort context_expr =
  tyGenericError
    ("The term " ^ S.string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ " in\n " ^ S.string_of_expr context_expr ^ 
      "\nbut it actually has type " ^ L.string_of_set hastype)

let wrongPropTypeError expr hasPT expectedsort context_expr =
  tyGenericError
    ("The term " ^ S.string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ " in\n " ^ S.string_of_expr context_expr ^ 
      "\nbut it actually has type " ^ L.string_of_proptype hasPT)

let wrongKindError expr hasK expectedsort context_expr =
  tyGenericError
    ("The set " ^ S.string_of_expr expr ^ "\nis used as if had a "
      ^ expectedsort ^ " kind in\n " ^ S.string_of_expr context_expr ^ 
      "\nbut it actually has kind " ^ L.string_of_kind hasK)

let wrongTheoryError expr hasthry expectedsort context_expr =
  tyGenericError
    ("The model " ^ S.string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ " in\n " ^ S.string_of_expr context_expr ^ 
      "\nbut it actually has the theory " ^ L.string_of_theory hasthry)

let tyMismatchError expr expectedTy foundTy context_expr =
  tyGenericError
    ("The term " ^ S.string_of_expr expr ^ " was expected to have type " ^
	L.string_of_set expectedTy ^ " instead of type " ^ 
	L.string_of_set foundTy ^ " in\n" ^ S.string_of_expr context_expr)

let propTypeMismatchError expr expectedTy foundTy context_expr =
  tyGenericError
    ("The proposition " ^ S.string_of_expr expr ^ " was expected to have type " ^
	L.string_of_proptype expectedTy ^ " instead of type " ^ 
	L.string_of_proptype foundTy ^ " in\n" ^ S.string_of_expr context_expr)

let kindMismatchError expr expectedK foundK context_expr =
  tyGenericError
    ("The set " ^ S.string_of_expr expr ^ " was expected to have kind " ^
	L.string_of_kind expectedK ^ " instead of kind " ^ 
	L.string_of_kind foundK ^ " in " ^ S.string_of_expr context_expr)

let theoryMismatchError expr expectedT foundT context_expr =
  tyGenericError
    ("The model " ^ S.string_of_expr expr ^ " was expected to satisfy theory\n\n" ^
	L.string_of_theory expectedT ^ "\n\ninstead of theory\n\n" ^ 
	L.string_of_theory foundT ^ "\n\nin " ^ S.string_of_expr context_expr)

let notEquivalenceOnError expr expectedDomExpr =
  tyGenericError
    ("The relation " ^ S.string_of_expr expr ^ 
	" is not an equivalence relation on " ^ 
	S.string_of_expr expectedDomExpr)

let cantElimError context_expr =
  tyGenericError 
    ("Inferred type of " ^ S.string_of_expr context_expr ^ 
	" refers to a locally-bound variable; " ^ 
	"maybe a constraint on the body would help?")

let tyJoinError ty1 ty2 =
   tyGenericError
     ("the types " ^ L.string_of_set ty1 ^ " and " ^
	 L.string_of_set ty2 ^ " are incompatible")

let tyPTJoinError pt1 pt2 =
   tyGenericError
     ("the types " ^ L.string_of_proptype pt1 ^ " and " ^
	 L.string_of_proptype pt2 ^ " are incompatible")
	
let badModelProjectionError nm expr why =
  tyGenericError
    ("Cannot project " ^ string_of_name nm ^ " in " ^ S.string_of_expr expr
      ^ "\n" ^ why )

let innerModelBindingError context_expr =
  tyGenericError
    ("A non-top-level binding of a model variable was found:\n"
      ^ S.string_of_expr context_expr)

let illegalBindingError nm where_type_came_from context_expr =
  tyGenericError
    ("The " ^ where_type_came_from ^ " type of " ^ string_of_name nm ^
	" is not suitable for a binding in " ^
	S.string_of_expr context_expr)
 
let illegalNameError nm what_kind_its_supposed_to_be =
  tyGenericError
    ("The name " ^ string_of_name nm ^ " is not legal for a " ^
	what_kind_its_supposed_to_be)

let shadowingError nm =
  tyGenericError
    ("Illegal shadowing; the name " ^ string_of_name nm ^ 
	" appears twice in the same context," ^ 
        "\nand automatic renaming is not possible.")
     

