(** {1 Pretty-Printing of Caml Output} 
    @author Chris Stone
    @see <http://www.cs.uwm.edu/classes/cs790/types-f2003/ocaml-manual/manual055.html> for the % codes in format strings
    @see <http://caml.inria.fr/ocaml/htmlman/libref/Format.html#VALfprintf> for the @ codes in format strings.
*)

open Format
open Outsyn

exception Unimplemented
exception Impossible

(** Outputs a term to the pretty-printing formatter ppf.
      The various output_term_n functions each will display a term of 
      level <=n without enclosing parentheses, or a term of level
      >n with parens. *)
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
	      [] -> raise Impossible
	    | arm::arms -> fprintf ppf "@[  %a @]@,%a" 
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
      fprintf ppf "@[fun %a : %a =>@ %a@]" 
        output_name n  output_ty ty  output_term_12 t
(*
  | Obligation ((n, TopTy), p, trm) ->
      fprintf ppf "@[<hov 2>assure @[%a@]@ in %a@]" 
        output_prop_0 p  output_term_12 trm
  | Obligation ((n, ty), True, trm) ->
      fprintf ppf "@[<hov 2>assure @[%a : %a@]@ in %a@]" 
        output_name n  output_ty ty  output_term_12 trm
  | Obligation ((n, ty), p, trm) ->
      fprintf ppf "@[<hov 2>@[<hov 4>assure %a : %a .@ @[%a@]@]@ in %a@]" 
        output_name n  output_ty ty  output_prop p  output_term_12 trm
*)
  | Obligation ([], p, trm) ->
      fprintf ppf "@[<hov 2>@[<hov 4>assure %a@]@ in %a@]" 
        output_prop_0 p   output_term_12 trm
  | Obligation (bnds, p, trm) ->
      fprintf ppf "@[<hov 2>@[<hov 4>assure %a.@ @[%a@]@]@ in %a@]" 
        output_binds bnds   output_prop_0 p   output_term_12 trm
  | trm -> output_term_9 ppf trm
      
and output_term_9 ppf = function
    App (App (Id (LN(None, Name.N(op, Name.Infix0))), t), u) -> 
      fprintf ppf "%a %s %a"
(* DISABLED the default left-associativity of infix operators *)
(*        output_term_9 t  output_ln ln  output_term_8 u *)
        output_term_8 t   op   output_term_8 u
  | trm -> output_term_8 ppf trm
      
and output_term_8 ppf = function
    App (App (Id (LN(None, Name.N(op,Name.Infix1))), t), u) -> 
      fprintf ppf "%a %s %a"
(* DISABLED the default left-associativity of infix operators *)
(*        output_term_8 t  output_ln ln  output_term_7 u *)
        output_term_7 t  op  output_term_7 u
  | trm -> output_term_7 ppf trm
      
and output_term_7 ppf = function
    App (App (Id (LN(None, Name.N(op,Name.Infix2))), t), u) -> 
      fprintf ppf "%a %s %a"
(* DISABLED the default left-associativity of infix operators *)
(*        output_term_7 t  output_ln ln  output_term_6 u *)
        output_term_6 t  op  output_term_6 u
  | trm -> output_term_6 ppf trm

and output_term_6 ppf = function
     App (App (Id (LN(None, Name.N(op,Name.Infix3))), t), u) -> 
      fprintf ppf "%a %s %a"
(* DISABLED the default left-associativity of infix operators *)
(*        output_term_6 t  op  output_term_5 u *)
        output_term_5 t  op  output_term_5 u
  | trm -> output_term_5 ppf trm

and output_term_5 ppf = function
     App (App (Id (LN(None,Name.N(op,Name.Infix4))), t), u) -> 
      fprintf ppf "%a %s %a"
(* DISABLED the default left-associativity of infix operators *)
(*        output_term_5 t  output_ln ln  output_term_4 u *)
        output_term_4 t   op   output_term_4 u
  | trm -> output_term_4 ppf trm

and output_term_4 ppf = function
  | Proj (k, t) -> 
      fprintf ppf "pi%d %a" k   output_term_0 t  (* skip applications! *) 
(*  | Proj (k, t) -> 
      fprintf ppf "%a.%d"   output_term_4 t  k  (* skip applications! *) *)
  | Inj (lb, None) -> 
      fprintf ppf "`%s" lb
  | Inj (lb, Some t) -> 
      fprintf ppf "`%s %a" lb   output_term_0 t  (* skip applications! *)
  | trm -> output_term_3 ppf trm

and output_term_3 ppf = function
    (* Fix for nested binary applications; we don't want the
       inner ones to accidentally use the "default" case for
       ordinary non-infix applications
     *)
    App (App (Id (LN(None, Name.N(_, (Name.Infix1 | Name.Infix2 |
					    Name.Infix3 | Name.Infix4))   )), _), _) 
    as trm -> 
      output_term_0 ppf trm
         
  | App (t, u) -> 
      fprintf ppf "@[<hov 2>%a@ %a@]"
         output_term_3 t   output_term_0 u
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
	| trm::trms -> fprintf ppf "%a%s@,%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst

and output_type_components outputer separator ppf lst =
      let rec output_loop ppf = function
	  [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s@,%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst

and output_sum_components outputer separator ppf lst = 
      let rec output_loop ppf = function
	  [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s@,%a"
	    outputer trm  separator  output_loop trms
      in
	output_loop ppf lst

(** Specifically for comma-separated variable/type pairs *)
and output_binds ppf lst =
      let outputer ppf (n,t) = 
	fprintf ppf "%s:%a" (Name.string_of_name n)  output_ty t
      in let rec output_loop ppf = function
	    [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s@,%a"
	    outputer trm  ", "  output_loop trms
      in
	output_loop ppf lst

and output_assertion_binds ppf lst =
      let outputer ppf (n,t) = 
	fprintf ppf "%s:||%a||" (Name.string_of_name n)  output_ty t
      in let rec output_loop ppf = function
	    [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s@,%a"
	    outputer trm  ", "  output_loop trms
      in
	output_loop ppf lst

and output_totalbinds ppf lst =
      let outputer ppf (n,t) = 
	fprintf ppf "%s:||%a||" (Name.string_of_name n)  output_ty t
      in let rec output_loop ppf = function
	    [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s@,%a"
	    outputer trm  ", "  output_loop trms
      in
	output_loop ppf lst

and output_term_0 ppf = function
    Id ln -> output_ln ppf ln
  | EmptyTuple -> fprintf ppf "()"
  | Dagger -> fprintf ppf "DAGGER"
  | Tuple [] -> fprintf ppf "()"
  | Tuple [t] -> fprintf ppf "TUPLE %a"  output_term_0 t
  | Tuple lst -> 
	fprintf ppf "@[(%a)@]"   (output_term_components output_term_9 ",") lst
  | trm -> ((* print_string (string_of_term trm ^ "\n"); *)
	    fprintf ppf "@[(%a)@]"   output_term trm)

and output_term_apps ppf lst = output_term_components output_term_3 " " ppf lst

and output_name ppf nm = 
  fprintf ppf "%s" (Name.string_of_name nm)
      
and output_ln ppf ln = 
  fprintf ppf "%s" (string_of_ln ln)

(** Outputs a proposition to the pretty-printing formatter ppf.
      The various output_prop_n functions each will display a proposition of 
      level <=n without enclosing parentheses, or a proposition of level
      >n with parens. *)
and output_prop ppf = function
    prp -> output_prop_15 ppf prp

and output_prop_15 ppf = function
    PCase (t1, t2, lst) ->
      begin
	let output_bnd ppf = function
	    None -> fprintf ppf ""
	  | Some (n, ty) ->
	      fprintf ppf "(%a : %a)"
		output_name n  output_ty ty
	in
	let output_arm ppf (lb, bnd1, bnd2, u) =
	  fprintf ppf "`%s %a, `%s %a =>@ @[<hv>%a@]"
	    lb  output_bnd bnd1  lb  output_bnd bnd2  output_prop_14 u
	in let rec output_arms' ppf = function
	    [] -> ()
          | arm::arms ->
	      fprintf ppf "@[| %a @]@,%a" 
		output_arm arm  output_arms' arms
	in let output_arms ppf = function
	    [] -> raise Impossible
	  | arm::arms -> fprintf ppf "@[<hov 5>  %a @]@,%a" 
	      output_arm arm  output_arms' arms
	in  
	     fprintf ppf "@[<v>@[<hv>match %a, %a with@]@,@[<v>%a@]@]" 
	       output_term_13 t1  output_term_13 t2  output_arms lst
      end
  | prp -> output_prop_14 ppf prp

and output_prop_14 ppf = function
    Forall ((n, ty), p) as all_ty -> 
      let rec extract_foralls = function
	  (Forall((nm,typ),prp)) ->
	    let (alls,prp') = extract_foralls prp
	    in ((nm,typ) ::alls,prp')
	| prp -> ([],prp)
      in let (alls, prp') = extract_foralls all_ty
      in
	fprintf ppf "@[<hov 2>forall %a, @ %a@]" 
	  output_binds alls   output_prop_14 prp'
  | ForallTotal ((n, ty), p) as all_ty -> 
      let rec extract_foralls = function
	  (ForallTotal((nm,typ),prp)) ->
	    let (alls,prp') = extract_foralls prp
	    in ((nm,typ) ::alls,prp')
	| prp -> ([],prp)
      in let (alls, prp') = extract_foralls all_ty
      in
	fprintf ppf "@[<hov 2>forall (%a), @ %a@]" 
	  output_totalbinds alls   output_prop_14 prp'
  | Cexists ((n, ty), p) as cexists_ty -> 
      let rec extract_somes = function
	  (Cexists((nm,typ),prp)) ->
	    let (somes,prp') = extract_somes prp
	    in ((nm,typ) ::somes,prp')
	| prp -> ([],prp)
      in let (somes, prp') = extract_somes cexists_ty
      in
	fprintf ppf "@[<hov 2>exists %a, @ %a@]" 
	  output_binds  somes   output_prop_14 prp'
  | Imply (p, q) -> 
      fprintf ppf "%a ->@ %a"  output_prop_11 p   output_prop_14 q

  | PLambda ((n, ty), p) ->
      fprintf ppf "@[<hov 2>pfun %a : %a =>@ @[%a@]@]" 
        output_name n  output_ty ty  output_prop_14 p

  | PMLambda ((n, {ty=ty; tot=p}), q) ->
      fprintf ppf "@[<hov 2>pmfun %a : %a(%a) =>@ %a@]" 
        output_name n  output_ty ty  output_prop_14 p  output_prop_14 q
(*
  | PObligation ((_, TopTy), p, q) ->
      fprintf ppf "@[<hov2>assure %a in@ %a@]" 
        output_prop_13 p  output_prop_14 q

  | PObligation ((n, ty), p, q) ->
      fprintf ppf "@[<hov 2>assure %a : %a . %a in@ %a@]" 
        output_name n  output_ty ty  output_prop_13 p  output_prop_14 q
*)

  | PObligation ([], p, q) ->
      fprintf ppf "@[<hov 2>@[<hov 4>assure %a@]@ in %a@]" 
	output_prop_13 p   output_prop_14 q

  | PObligation (bnds, p, q) ->
      fprintf ppf "@[<hov 2>@[<hov 4>assure %a.@ @[%a@]@]@ in %a@]" 
        output_binds bnds   output_prop_13 p   output_prop_14 q

  | PLet (n, t, u) ->
	fprintf ppf "@[let %a = @[<hov>%a@]@ in %a@]"
            output_name n  output_term_12 t  output_prop_14 u

  | prp -> output_prop_13 ppf prp
    
and output_prop_13 ppf = function
    Iff (p, q) ->
      fprintf ppf "%a <->@ %a"  output_prop_11 p   output_prop_11 q
  | prp -> output_prop_11 ppf prp
  
and output_prop_11 ppf = function
   Cor (_::_ as lst) -> 
      output_prop_components output_prop_11 " cor " ppf lst
  | prp -> output_prop_10 ppf prp

and output_prop_10 ppf = function
    And (_::_ as lst) -> 
      output_prop_components output_prop_10 " /\\ " ppf lst
  | prp -> output_prop_9 ppf prp

and output_prop_9 ppf = function
    PApp (PApp (NamedPer (ln, []), t), u) -> 
      fprintf ppf "%a =%a= %a" 
        output_term_4 t   output_ln ln   output_term_4 u
  | PApp (PApp (NamedPer (ln, lst), t), u) -> 
      fprintf ppf "%a =(%a %a)= %a" 
        output_term_4 t   output_ln ln   output_term_apps lst   output_term_4 u
  | PApp (NamedTotal (ln, []), t) ->
      fprintf ppf "%a : ||%a||"
	output_term_9 t   output_ln ln
  | PApp (NamedTotal (ln, lst), t) ->
      fprintf ppf "%a : ||%a %a||"
	output_term_9 t   output_ln ln   output_term_apps lst
  | PApp (p, t) ->
      fprintf ppf "%a %a"
	output_prop_9 p   output_term_3 t
  | PMApp (p, t) ->
      fprintf ppf "(%a %a)"
	output_prop_9 p   output_term_3 t
  | NamedProp (ln, Dagger, lst) ->
      fprintf ppf "%a %a"
        output_ln ln   output_term_apps lst
  | NamedProp (ln, t, lst) ->
      fprintf ppf "%a |= %a %a"
	output_term_4 t   output_ln ln   output_term_apps lst
  | Equal (t, u) -> 
      fprintf ppf "%a = %a"  output_term_8 t   output_term_8 u
  | prp -> output_prop_8 ppf prp

and output_prop_8 ppf = function
    Not p -> 
      fprintf ppf "not %a"  output_prop_8 p
  | prp -> output_prop_0 ppf prp

and output_prop_0 ppf = function
    True -> fprintf ppf "true"
  | False -> fprintf ppf "false"
  | NamedPer (ln, []) -> fprintf ppf "=%a=" output_ln ln
  | NamedPer (ln, lst) ->
      fprintf ppf "=(%a %a)="
	output_ln ln   output_term_apps lst
  | IsPer (stnm, []) -> fprintf ppf "PER(=%s=)" (Name.string_of_name stnm)
  | IsPer (stnm, lst) -> fprintf ppf "PER(=%s %a=)"
      (Name.string_of_name stnm)   output_term_apps lst
  | IsPredicate (nm, None, _) ->
      fprintf ppf "@[PREDICATE(@[<hov>%s@])@]"
        (Name.string_of_name nm)
  | IsPredicate (nm, Some ty, _) ->
      fprintf ppf "@[PREDICATE(@[<hov>%s, %a@])@]"
        (Name.string_of_name nm)   output_ty ty
  | IsEquiv (p, {ty=t}) ->
      fprintf ppf "@[EQUIV(@[<hov>%a, %a@])@]"
	output_prop_11 p    output_ty t
  | NamedTotal (ln, []) -> fprintf ppf "||%a||" output_ln ln
  | NamedTotal (ln, lst) ->
      fprintf ppf "||%a %a||"
	output_ln ln   output_term_apps lst
  | And [] -> fprintf ppf "true"
  | Cor [] -> fprintf ppf "false"
  | prp ->
(*      prerr_endline ("Will parenthesise " ^ (string_of_proposition prp)); *)
      fprintf ppf "(@[<hov>%a@])"   output_prop prp
    
and output_app ppf = function
    ((LN(None, Name.N(op, (Name.Infix0|Name.Infix1|Name.Infix2|Name.Infix3|Name.Infix4)))), [u;v]) ->
       fprintf ppf "%a %s %a" 
         output_term u  op  output_term v
  | (ln, trms) -> 
      fprintf ppf "%a %a" 
	 output_ln ln   (output_term_components output_term_8 " ") trms

(** Outputs a type to the pretty-printing formatter ppf.
      The various output_ty_n functions each will display a type of 
      level <=n without enclosing parentheses, or a type of level
      >n with parens. *)
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
    NamedTy ln -> output_ln ppf ln
  | UnitTy     -> fprintf ppf "unit"
  | TopTy      -> fprintf ppf "top"
  | TupleTy [] -> fprintf ppf "top"
  | SumTy []   -> fprintf ppf "void"
  | typ        -> ((* print_string (string_of_ty typ); *)
		   fprintf ppf "(%a)"  output_ty typ)

and output_assertion ppf (nm, p) =
  fprintf ppf "@[<hov 2>Assertion %s = @ %a@]"  nm   output_prop p

and output_assertions ppf = function
    [] -> ()
  | assertions ->
      let rec loop ppf = function
	  [] -> ()
	| [assertion] ->
	      output_assertion ppf assertion
	| assertion::assertions -> 
	    fprintf ppf "%a@, @,%a" 
	      output_assertion assertion   loop assertions
      in
	fprintf ppf "@,@[<v>(**  @[<v>%a@]@,*)@]"  loop assertions

and output_spec ppf = function
    Spec(nm, ValSpec ty, assertions) ->
      fprintf ppf "@[<v>@[<hov 2>val %s : %a@]%a@]" 
      (Name.string_of_name nm)   output_ty ty  output_assertions assertions
  | Spec(tynm, TySpec None, assertions) -> 
      fprintf ppf "@[<v>@[<hov 2>type %s@]%a@]"  
	(Name.string_of_name tynm)   output_assertions assertions
  | Spec(tynm, TySpec (Some ty), assertions) -> 
      fprintf ppf "@[<v>@[<hov 2>type %s =@ %a@]%a@]"  
	(Name.string_of_name tynm)   output_ty ty   output_assertions assertions
  | Spec(nm, ModulSpec sgntr, assertions) ->
      fprintf ppf "@[<v>@[module %s : %a@]%a@]"
	(Name.string_of_name nm)   output_signat sgntr   output_assertions assertions
  | Spec(nm, SignatSpec sgntr, assertions) ->
      fprintf ppf "@[<v>@[module type %s =@, @[<v>%a@]@]%a@]"   
	(Name.string_of_name nm)   output_signat sgntr   output_assertions assertions
  | Assertion assertion -> output_assertions ppf [assertion]
  | Comment cmmnt ->
      fprintf ppf "(**%s*)" cmmnt

and output_specs ppf = function
    [] -> ()
  | [spec] -> output_spec ppf spec
  | spec::specs -> 
      fprintf ppf "%a@, @,%a" output_spec spec output_specs specs

(*
and output_signat_no_sigapp ppf = function
    SignatName s -> fprintf ppf "%s" (Name.string_of_name s)
  | Signat body -> fprintf ppf "@[<v>sig@,  @[<v>%a@]@,end@]"  output_specs body
  | SignatFunctor ((m,sgnt1),sgnt2) ->
      fprintf ppf "@[<v>functor (%s : %a) ->@, @[<v>%a@]@]"
         (Name.string_of_name m)   output_signat sgnt1   output_signat sgnt2
  | SignatApp (sgnt1,mdl) ->
      fprintf ppf "@[<v>(** %a(%a) *)@, SHOULD OUTPUT SignatApp beta-reduced@]"
         output_signat_sigapp sgnt1
         output_modul mdl
  | SignatProj (mdl, nm) -> 
      fprintf ppf "%a.%s"  output_modul mdl   (Name.string_of_name nm)

and output_signat_sigapp ppf = function
    SignatName s -> fprintf ppf "%s" (Name.string_of_name s)
  | Signat body -> fprintf ppf "@[<v>sig@,  @[<v>%a@]@,end@]"  output_specs body
  | SignatFunctor ((m,sgnt1),sgnt2) ->
      fprintf ppf "@[<v>functor (%s : %a) ->@, @[<v>%a@]@]"
         (Name.string_of_name m)   output_signat sgnt1   output_signat sgnt2
  | SignatApp (sgnt1,mdl) ->
      fprintf ppf "@[%a(%a)@]"
         output_signat_sigapp sgnt1    output_modul mdl
  | SignatProj (mdl, nm) -> 
      fprintf ppf "%a.%s"  output_modul mdl   (Name.string_of_name nm)
*)

and output_signat ppf = function
    SignatName s -> fprintf ppf "%s" (Name.string_of_name s)
  | Signat body -> fprintf ppf "@[<v>sig@,  @[<v>%a@]@,end@]"  output_specs body
  | SignatFunctor ((m,sgnt1),sgnt2) ->
      fprintf ppf "@[<v>functor (%s : %a) ->@ %a@]"
         (Name.string_of_name m)   output_signat sgnt1   output_signat sgnt2
  | (SignatApp (sgnt1,mdl)) (* as sgnt *) ->
      fprintf ppf "@[%a(%a)@]"
         output_signat sgnt1    output_modul mdl
(*      if ( ! Flags.do_sigapp ) then
        output_signat_no_sigapp ppf sgnt
      else
        output_signat_sigapp ppf sgnt
*)
  | SignatProj (mdl, nm) -> 
      fprintf ppf "%a.%s"  output_modul mdl   (Name.string_of_name nm)

and output_modul ppf = function
    ModulName s -> fprintf ppf "%s" (Name.string_of_name s)
  | ModulProj (mdl, s) -> 
      fprintf ppf "%a.%s"  output_modul mdl   (Name.string_of_name s)
  | ModulApp (mdl1, mdl2) -> 
      fprintf ppf "%a(%a)" output_modul mdl1   output_modul mdl2
  | ModulStruct defs -> 
      fprintf ppf "@[<v>struct@ %a@ end]"  output_defs defs

and output_defs ppf = function
    [] -> ()
  | [def] -> output_def ppf def
  | def::defs -> 
      fprintf ppf "%a@, @,%a"   output_def def   output_defs defs

and output_def ppf = function
    DefType(nm,ty) -> 
      fprintf ppf "type %a = %a"  output_name nm  output_ty ty
  | DefTerm(nm,ty,trm) ->
      fprintf ppf "let %a : %a = %a"  
	output_name nm   output_ty ty   output_term trm
  | DefModul(nm,signat,mdl) ->
      fprintf ppf "module %a = %a : %a"
	output_name nm   output_modul mdl   output_signat signat
  | DefSignat(nm,signat) ->
      fprintf ppf "@[<v>module type %a = @,@[<v>%a@]@]@.@." 
	output_name nm   output_signat signat

and output_toplevel ppf body =
  fprintf ppf "@[<v>%a@]@.@."  output_specs body
