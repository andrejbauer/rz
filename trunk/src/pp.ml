open Format
open Outsyn

let string_of_name = Syntax.string_of_name

let rec output_term ppf = function
    trm -> output_term_13 ppf trm

and output_term_13 ppf = function
     Case (t, lst) ->
       (let output_arm ppf = function
	    (lb, None, u) -> fprintf ppf "`%s -> %a" lb output_term_12 u
	  | (lb, Some (n,ty), u) -> 
	      fprintf ppf "`%s(%a : %a) -> %a"
                lb  output_name n  output_ty ty  output_term_12 u
	in let rec output_arms' ppf = function
	      [] -> ()
          | arm::arms -> fprintf ppf "@[| %a @]@,%a" 
	      output_arm arm  output_arms' arms
	in let output_arms ppf = function
	      arm::arms -> fprintf ppf "@[  %a @]@,%a" 
		output_arm arm  output_arms' arms
	in  
	  fprintf ppf "@[<v>@[<hv>match %a with@]@,@[<v>%a@]]" 
	    output_term_13 t  output_arms lst)

    | Let (n, t, u) ->
	fprintf ppf "@[let %a = @[<hov>%a@]@ in %a@]"
            output_name n  output_term_12 t  output_term_13 u

    | trm -> output_term_12 ppf trm

and output_term_12 ppf = function
    Lambda ((n, ty), t) ->
      fprintf ppf "fun (%a : %a) ->@ %a" 
        output_name n  output_ty ty  output_term_12 t
  | Obligation ((n, ty), p) ->
      fprintf ppf "[? %a : %a . %a]" 
        output_name n  output_ty ty  output_prop p
  | trm -> output_term_9 ppf trm
      
and output_term_9 ppf = function
    App (App (Id (Logic.LN(_,_, Syntax.Infix0) as ln), t), u) -> 
      fprintf ppf "%a %a %a"
        output_term_9 t  output_longname ln  output_term_8 u
  | trm -> output_term_8 ppf trm
      
and output_term_8 ppf = function
    App (App (Id (Logic.LN(_,_, Syntax.Infix1) as ln), t), u) -> 
      fprintf ppf "%a %a %a"
        output_term_8 t  output_longname ln  output_term_7 u
  | trm -> output_term_7 ppf trm
      
and output_term_7 ppf = function
    App (App (Id (Logic.LN(_,_, Syntax.Infix2) as ln), t), u) -> 
      fprintf ppf "%a %a %a"
        output_term_7 t  output_longname ln  output_term_6 u
  | trm -> output_term_6 ppf trm

and output_term_6 ppf = function
     App (App (Id (Logic.LN(_,_, Syntax.Infix3) as ln), t), u) -> 
      fprintf ppf "%a %a %a"
        output_term_6 t  output_longname ln  output_term_5 u
  | trm -> output_term_5 ppf trm

and output_term_5 ppf = function
     App (App (Id (Logic.LN(_,_, Syntax.Infix4) as  ln), t), u) -> 
      fprintf ppf "%a %a %a"
        output_term_5 t  output_longname ln  output_term_4 u
  | trm -> output_term_4 ppf trm

and output_term_4 ppf = function
    App (t, u) -> 
      fprintf ppf "@[<hov 2>%a@ %a@]"
         output_term_4 t   output_term_0 u
  | Proj (k, t) -> 
      fprintf ppf "pi%d %a" k   output_term_0 t
  | Inj (lb, None) -> 
      fprintf ppf "`%s" lb
  | Inj (lb, Some t) -> 
      fprintf ppf "`%s %a" lb   output_term_0 t
  | trm -> output_term_0 ppf trm

and output_term_components outputer separator ppf lst =
      let rec output_loop ppf = function
	  [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst

and output_prop_components outputer separator ppf lst =
      let rec output_loop ppf = function
	  [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst

and output_type_components outputer separator ppf lst =
      let rec output_loop ppf = function
	  [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst

and output_sum_components outputer separator ppf lst = 
      let rec output_loop ppf = function
	  [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst

and output_bind_components outputer separator ppf lst =
      let rec output_loop ppf = function
	  [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst


and output_term_0 ppf = function
    Id ln -> output_longname ppf ln
  | Star -> fprintf ppf "()"
  | Dagger -> fprintf ppf "DAGGER"
  | Tuple [] -> fprintf ppf "()"
  | Tuple [t] -> output_term_0 ppf t
  | Tuple lst -> 
	fprintf ppf "(%a)"   (output_term_components output_term_9 ",") lst
  | trm -> ((* print_string (string_of_term trm ^ "\n"); *)
	    fprintf ppf "(%a)"   output_term trm)

and output_name ppf nm = 
    fprintf ppf "%s" (Syntax.string_of_name nm)

and output_longname ppf ln = 
    fprintf ppf "%s" (string_of_ln ln)

and output_prop ppf = function
    prp -> output_prop_14 ppf prp

and output_prop_14 ppf = function
    Forall ((n, ty), p) -> 
      fprintf ppf "@[<hov 2>all (%s : %a) .@ %a@]" 
      (string_of_name n)  output_ty ty  output_prop_14 p
  | Cexists ((n, ty), p) -> 
     fprintf ppf "@[<hov 2>some (%s : %a) .@ %a@]" 
      (string_of_name n)  output_ty ty  output_prop_14 p
  | prp -> output_prop_13 ppf prp
    
and output_prop_13 ppf = function
    Imply (p, q) -> 
      fprintf ppf "%a =>@ %a"  output_prop_11 p   output_prop_13 q
  | Iff (p, q) ->
      fprintf ppf "%a <=>@ %a"  output_prop_11 p   output_prop_11 q
  | prp -> output_prop_11 ppf prp
  
and output_prop_11 ppf = function
   Cor (_::_ as lst) -> 
      output_prop_components output_prop_11 " cor " ppf lst
  | prp -> output_prop_10 ppf prp

and output_prop_10 ppf = function
    And (_::_ as lst) -> 
      output_prop_components output_prop_10 " and " ppf lst
  | prp -> output_prop_9 ppf prp

and output_prop_9 ppf = function
    NamedPer (ln, t, u) -> 
      fprintf ppf "%a =_%a %a" 
        output_term_9 t   output_longname ln   output_term_8 u
  | NamedProp (n, Dagger, u) -> 
       output_app ppf (n,u)  (* ??? *)
  | NamedProp (n, t, u) ->
      fprintf ppf "%a |= %a"   output_term t   output_app (n,u)
  | Equal (t, u) -> 
      fprintf ppf "%a = %a"  output_term_8 t   output_term_8 t
  | prp -> output_prop_8 ppf prp

and output_prop_8 ppf = function
    Not p -> 
      fprintf ppf "not %a"  output_prop_8 p
  | prp -> output_prop_0 ppf prp

and output_prop_0 ppf = function
    True -> fprintf ppf "true"
  | False -> fprintf ppf "false"
  | IsPer stnm -> fprintf ppf "PER(=_%s)" stnm
  | IsPredicate prdct -> fprintf ppf "PREDICATE(%s)" (string_of_name prdct)
  | NamedTotal (ln, t) -> 
      fprintf ppf "%a : ||%a||"  
	output_term t   output_longname ln
  | And [] -> fprintf ppf "true"
  | Cor [] -> fprintf ppf "false"
  | prp -> fprintf ppf "(%a)"   output_prop prp
    
and output_app ppf = function
    ((Logic.LN(_,_, (Syntax.Infix0|Syntax.Infix1|Syntax.Infix2|Syntax.Infix3|Syntax.Infix4)) as ln), [Tuple [u;v]]) ->
      fprintf ppf "%a %a %a" 
         output_term u  output_longname ln  output_term v
  | (ln, trms) -> 
      fprintf ppf "%a %a" 
	 output_longname ln   (output_term_components output_term " ") trms

and output_ty ppf = function
    typ -> output_ty_3 ppf typ

and output_ty_3 ppf = function
    ArrowTy(t1,t2) -> 
      fprintf ppf "%a -> %a"   output_ty_2 t1   output_ty_3  t2
  | typ -> output_ty_2 ppf typ

and output_ty_2 ppf = function
   TupleTy (_::_ as ts) -> 
     output_type_components output_ty_1 " * " ppf ts
  | typ -> output_ty_1 ppf typ

and output_ty_1 ppf = function
    SumTy (_::_ as ts) -> 
      let doOne ppf = function 
	  (lb, None) -> fprintf ppf "`%s" lb
	| (lb, Some t) -> fprintf ppf "`%s of %a" lb   output_ty_1 t
      in
	fprintf ppf "[%a]" (output_sum_components doOne " | ") ts

  | typ -> output_ty_0 ppf typ

and output_ty_0 ppf = function
    NamedTy ln -> output_longname ppf ln
  | UnitTy     -> fprintf ppf "unit"
  | TopTy      -> fprintf ppf "top"
  | TYPE       -> fprintf ppf "TYPE"
  | TupleTy [] -> fprintf ppf "top"
  | SumTy []   -> fprintf ppf "void"
  | typ        -> ((* print_string (string_of_ty typ); *)
		   fprintf ppf "(%a)"  output_ty typ)

and output_binds ppf binds = 
  output_bind_components 
    (fun ppf (n,t) -> fprintf ppf "%s : %a" (string_of_name n)  output_ty t)
    ", " ppf binds

and output_spec ppf = function
    ValSpec (nm, ty) ->
      fprintf ppf "@[val %s : %a@]" 
      (string_of_name nm)   output_ty ty
  | TySpec (tynm, None) -> 
      fprintf ppf "@[type %s@]"  tynm
  | TySpec (tynm, Some ty) -> 
      fprintf ppf "@[type %s = %a@]"  tynm   output_ty ty
  | AssertionSpec (nm, [], p) ->
      fprintf ppf "@[<hov 2>(** Assertion %s:@ %a@ *)@]"  nm   output_prop p
  | AssertionSpec (nm, binds, p) ->
      fprintf ppf "@[<hov 2>(** Assertion %s:@,%a@,%a@ *)@]" 
	nm   output_binds binds   output_prop p

and output_specs ppf = function
    [] -> ()
  | [spec] -> output_spec ppf spec
  | spec::specs -> 
      fprintf ppf "%a@,@,%a" output_spec spec output_specs specs

and output_signat ppf = function
    SignatID s -> fprintf ppf "%s" s
  | Signat body -> fprintf ppf "@[<v 2>sig@,%a@]@,end"  output_specs body

and output_signatdef ppf = function
    Signatdef (s, args, body) ->
      let rec output_args ppf = function
	  [] -> ()
	| (n,t)::args -> 
	    fprintf ppf "@,functor (%s : %a) -> %a" 
	      n   output_signat t   output_args args
      in
	fprintf ppf "@[<v>module type %s = %a@,%a@]@."  
	  s   output_args args   output_signat body
	  
