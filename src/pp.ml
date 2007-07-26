(** {1 Pretty-Printing of Caml Output} 
    @author Chris Stone
    @see <http://www.cs.uwm.edu/classes/cs790/types-f2003/ocaml-manual/manual055.html> for the % codes in format strings
    @see <http://caml.inria.fr/ocaml/htmlman/libref/Format.html#VALfprintf> for the @ codes in format strings.
*)

open Format
open Outsyn

exception Unimplemented
exception Impossible


let output_components outputer separator ppf lst =
  let rec output_loop ppf = function
      [] -> ()
    | [trm] -> outputer ppf trm
    | trm::trms -> fprintf ppf "%a%s@,%a"
	  outputer trm  separator  output_loop trms
  in
  output_loop ppf lst

let output_components_nobreak outputer separator ppf lst =
  let rec output_loop ppf = function
      [] -> ()
    | [trm] -> outputer ppf trm
    | trm::trms -> fprintf ppf "%a%s%a"
	  outputer trm  separator  output_loop trms
  in
  output_loop ppf lst

(** Outputs a term to the pretty-printing formatter ppf.
      The various output_term_n functions each will display a term of 
      level <=n without enclosing parentheses, or a term of level
      >n with parens. *)
let rec output_term ppf = function
    trm -> output_term_13 ppf trm

and output_pattern ppf = function
    WildPat -> fprintf ppf "_"
  | VarPat nm -> fprintf ppf "%a"   output_name nm
  | TuplePat pats -> fprintf ppf "(%a)"  output_patterns pats
  | ConstrPat(lbl,None) -> fprintf ppf "`%s"  lbl
  | ConstrPat(lbl,Some(nm,ty)) -> 
      fprintf ppf "`%s(%a:%a)" lbl   output_name nm   output_ty ty

and output_patterns ppf = function
    [] -> ()
  | [pat] -> fprintf ppf "%a"  output_pattern pat
  | pat::pats -> fprintf ppf "%a,%a"  output_pattern pat   output_patterns pats

and output_term_13 ppf = function
     Case (t, lst) ->
       (let output_arm ppf (pat, u) =
	 fprintf ppf "%a -> %a" output_pattern pat output_term_12 u
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

    | Let (pat, t, u) ->
	fprintf ppf "@[let %a = @[<hov>%a@]@ in %a@]"
            output_pattern pat  output_term_12 t  output_term_13 u

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
      fprintf ppf "@[<hov 2>@[<hov 4>assure %a,@ @[%a@]@]@ in %a@]" 
        output_bnds bnds   output_prop_0 p   output_term_12 trm
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

(** Specifically for comma-separated variable/type pairs *)
and output_bnd ppf (n,t) = 
  fprintf ppf "%s:%a" (Name.string_of_name n)  output_ty t

and output_bnds ppf lst =
  output_components output_bnd ", " ppf lst

and output_mbnd ppf (n,mset) =
  fprintf ppf "%s:%a" (Name.string_of_name n)  output_modest mset
    
and output_mbnds ppf lst =
  output_components output_mbnd ", " ppf lst

and output_pbnd ppf (n,pt) = 
  fprintf ppf "%a:%a" output_name n  output_proptype pt

and output_pbnds ppf = function
    [] -> ()
  | lst -> fprintf ppf "[%a]"   (output_components output_pbnd ", ") lst

and output_modest ppf {ty=ty;tot=p} =
  fprintf ppf "%a(%a)"  output_ty ty  output_prop p
  

and output_proptype ppf = function
    Prop -> fprintf ppf "bool"
  | PropArrow(ty, pt) ->
      fprintf ppf "%a -> %a"  output_ty_2 ty   output_proptype pt

(* NOT USED
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
*)

and output_totalbinds ppf lst =
      let outputer ppf (n,sty) = 
	fprintf ppf "%s:||%a||" (Name.string_of_name n)  output_simple_ty sty
      in let rec output_loop ppf = function
	    [] -> ()
	| [trm] -> outputer ppf trm
	| trm::trms -> fprintf ppf "%a%s@,%a"
	    outputer trm  ", "  output_loop trms
      in
	output_loop ppf lst

and output_term_0 ppf = function
  | Id ln -> output_ln ppf ln
  | EmptyTuple -> fprintf ppf "()"
  | BTrue -> fprintf ppf "true"
  | BFalse -> fprintf ppf "false"
  | Dagger -> fprintf ppf "DAGGER"
  | Tuple [] -> fprintf ppf "()"
  | Tuple [t] -> fprintf ppf "TUPLE %a"  output_term_0 t
  | Tuple lst -> 
	fprintf ppf "@[(%a)@]"   (output_components output_term_9 ",") lst
  | trm -> ((* print_string (string_of_term trm ^ "\n"); *)
	    fprintf ppf "@[(%a)@]"   output_term trm)

and output_term_apps ppf lst = 
  output_components_nobreak output_term_0 " " ppf lst

and output_name ppf = function
  | Name.N (_, Name.Per) as nm ->
      fprintf ppf "(=%s=)" (Name.string_of_name nm)
  | Name.N (_, Name.Support) as nm ->
      fprintf ppf "||%s||" (Name.string_of_name nm)
  | nm ->
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
    PCase (t, lst) ->
      begin
	let output_arm ppf (pat, u) =
	  fprintf ppf "%a =>@ @[<hv>%a@]"
	    output_pattern pat   output_prop_14 u
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
	     fprintf ppf "@[<v>@[<hv>match %a with@]@,@[<v>%a@]@]" 
	       output_term_13 t   output_arms lst
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
	  output_bnds alls   output_prop_14 prp'
  | ForallSupport ((n, _), p) as all_sty -> 
      let rec extract_foralls = function
	  (ForallSupport((nm,sty),prp)) ->
	    let (alls,prp') = extract_foralls prp
	    in ((nm,sty) ::alls,prp')
	| prp -> ([],prp)
      in let (alls, prp') = extract_foralls all_sty
      in
	fprintf ppf "@[<hov 2>forall (%a), @ %a@]" 
	  output_totalbinds alls   output_prop_14 prp'
  | Imply (p, q) -> 
      fprintf ppf "%a ->@ %a"  output_prop_11 p   output_prop_14 q

  | PLambda ((n, ty), p) ->
      fprintf ppf "@[<hov 2>(pfun %a : %a =>@ @[%a@])@]" 
        output_name n  output_ty ty  output_prop_14 p

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
      fprintf ppf "@[<hov 2>@[<hov 4>assure %a,@ @[%a@]@]@ in %a@]" 
        output_bnds bnds   output_prop_13 p   output_prop_14 q

  | PLet (pat, t, u) ->
	fprintf ppf "@[let %a = @[<hov>%a@]@ in %a@]"
            output_pattern pat  output_term_12 t  output_prop_14 u

  | prp -> output_prop_13 ppf prp
    
and output_prop_13 ppf = function
    Iff (p, q) ->
      fprintf ppf "%a <->@ %a"  output_prop_11 p   output_prop_11 q
  | prp -> output_prop_11 ppf prp
  
and output_prop_11 ppf = function
  (* used to be Cor *)
  | prp -> output_prop_10 ppf prp

and output_prop_10 ppf = function
    And (_::_ as lst) -> 
      output_components output_prop_10 " /\\ " ppf lst
  | prp -> output_prop_9 ppf prp

and output_prop_9 ppf = function
    PApp (PApp (p, t), u) when isPerProp p -> 
      fprintf ppf "%a %a %a" 
        output_term_4 t   output_per p   output_term_4 u
  | PApp (p, t) when isSupportProp p ->
      fprintf ppf "%a : %a"
	output_term_9 t   output_support p
(* XXX the commented lines below do not work when something like "(<) x y z" appears because
   it would print "x < y z" when probably it should print "(<) x y z" or "(x < y) z":
  | PApp (PApp (BasicProp (LN(None, Name.N(op, Name.Infix0))), t), u) ->
      fprintf ppf "%a %s %a"
	output_term_8 u   op   output_term_8 u
*)
  | PApp (p, t) ->
      fprintf ppf "%a %a"
	output_prop_9 p   output_term_0 t
  | Equal (t, u) -> 
      fprintf ppf "%a = %a"  output_term_8 t   output_term_8 u
  | prp -> output_prop_8 ppf prp

and output_prop_8 ppf = function
    Not p -> 
      fprintf ppf "not %a"  output_prop_8 p
  | prp -> output_prop_0 ppf prp

and output_prop_0 ppf = function
  | True -> fprintf ppf "true"
  | False -> fprintf ppf "false"
  | BasicProp (LN (_, Name.N(_, Name.Per)) as ln) ->
      fprintf ppf "=%a="
	output_ln ln
  | BasicProp (LN (_, Name.N(_, Name.Support)) as ln) ->
      fprintf ppf "||%a||"
	output_ln ln
  | BasicProp ln -> output_ln ppf ln
  | SimpleSupport sty -> fprintf ppf "||%a||" output_simple_ty sty
  | SimplePer sty -> fprintf ppf "(=%a=)" output_simple_per sty
  | And [] -> fprintf ppf "true"
  | prp ->
(*      prerr_endline ("Will parenthesise " ^ (string_of_proposition prp)); *)
      fprintf ppf "(@[<hov>%a@])"   output_prop prp
    
and output_per ppf p =
  let rec output_per' ppf = function
    | BasicProp ln -> output_ln ppf ln
    | PApp (p, t) ->
	fprintf ppf "%a %a"
	  output_per' p   output_term_0 t
    | _ -> failwith "pp.ml: invalid call to output_per"
  in
    match p with
      | BasicProp ((LN (_, Name.N(_, Name.Per))) as ln) ->
	  fprintf ppf "=%a="
	    output_ln ln
      | SimplePer sty ->
	  fprintf ppf "=%a="
	    output_simple_per sty
      | _ ->
	  fprintf ppf "=(%a)="
	    output_per' p

and output_support ppf p =
  let rec output_support' ppf = function
    | BasicProp ln -> output_ln ppf ln
    | SimpleSupport sty ->
	fprintf ppf "%a"
	  output_simple_ty sty
    | PApp (p, t) ->
	fprintf ppf "%a %a"
	  output_support' p   output_term_0 t
    | _ -> failwith "pp.ml: invalid call to output_support"
  in
    match p with
      | BasicProp ((LN (_, Name.N(_, Name.Support))) as ln) ->
	  fprintf ppf "||%a||"
	    output_ln ln
      | SimpleSupport sty ->
	  fprintf ppf "||%a||"
	    output_simple_ty sty
      | _ ->
	  fprintf ppf "||%a||"
	    output_support' p

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
     output_components_nobreak output_ty_1 " * " ppf ts
  | typ -> output_ty_1 ppf typ

and output_ty_1 ppf = function
    SumTy (_::_ as ts) -> 
      let doOne ppf = function 
	  (lb, None) -> fprintf ppf "`%s" lb
	| (lb, Some t) -> fprintf ppf "`%s of %a" lb   output_ty_1 t
      in
	fprintf ppf "[%a]" (output_components doOne " | ") ts

  | typ -> output_ty_0 ppf typ

and output_ty_0 ppf = function
    NamedTy ln -> output_ln ppf ln
  | UnitTy     -> fprintf ppf "unit"
  | VoidTy     -> fprintf ppf "void"
  | BoolTy     -> fprintf ppf "bool"
  | TopTy      -> fprintf ppf "top"
  | TupleTy [] -> fprintf ppf "top"
  | SumTy []   -> fprintf ppf "void"
  | typ        -> ((* print_string (string_of_ty typ); *)
		   fprintf ppf "(%a)"  output_ty typ)

and output_simple_ty ppf sty = output_ty ppf (ty_of_simple_ty sty)

and output_simple_per ppf sty =
  match sty with
    | SNamedTy _ | SUnitTy | SVoidTy | STopTy | SBoolTy ->
	output_simple_ty ppf sty
    | STupleTy _ | SArrowTy _ ->
	fprintf ppf "(%a)"  output_simple_ty sty

and output_annots ppf = function
    [] -> ()
  | (Annot_Declare _ | Annot_NoOpt) :: rest -> output_annots ppf rest
(*  | Annot_NoOpt::rest -> fprintf ppf "[Definitional] %a"  output_annots rest *)


and output_assertion ppf asn =
  fprintf ppf "@[<hov 2>assertion %a%s%a%s%s %a: @ %a@]"  
    output_tyvars asn.atyvars 
    (if asn.atyvars = [] then "" else " ")
    output_pbnds asn.apbnds
    (if asn.apbnds = [] then "" else " ")
    asn.alabel  
    output_annots asn.aannots   
    output_prop asn.aprop

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

and output_tyvars ppf = function
    [] -> ()
  | [nm] -> fprintf ppf "%a"  output_name nm
  | nms -> fprintf ppf "(%a)"  output_names nms

and output_names ppf nms =
  output_components_nobreak output_name "," ppf nms

and output_spec ppf = function
    Spec(nm, ValSpec (_,ty), assertions) ->
      (* Unlike Revised SML, ocaml doesn't let you explicitly quantify
	 with type variables, so we ignore them when pretty-printing.
	 (We could show them in a comment, I suppose)
       *)
      fprintf ppf "@[<v>@[<hov 2>val %s : %a@]%a@]" 
      (Name.string_of_name nm)  output_ty ty  output_assertions assertions
  | Spec(tynm, TySpec None, assertions) -> 
      fprintf ppf "@[<v>@[<hov 2>type %s@]%a@]"  
	(Name.string_of_name tynm)   output_assertions assertions
  | Spec(tynm, TySpec (Some ty), assertions) -> 
      fprintf ppf "@[<v>@[<hov 2>type %s =@ %a@]%a@]"  
	(Name.string_of_name tynm)   output_ty ty   output_assertions assertions
  | Spec(nm, ModulSpec sgntr, assertions) ->
      fprintf ppf "@[<hov 2>@[module %s : %a@]%a@]"
	(Name.string_of_name nm)   output_signat sgntr   output_assertions assertions
  | Spec(nm, SignatSpec sgntr, assertions) ->
      fprintf ppf "@[<v>@[module type %s =@, @[<v>%a@]@]%a@]"   
	(Name.string_of_name nm)   output_signat sgntr   output_assertions assertions
  | Spec(nm, PropSpec pt, assertions) ->
      fprintf ppf "@[<v>@[<hov 2>(** predicate %a : %a *)@]%a@]" 
	output_name nm   output_proptype pt
	output_assertions assertions
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
  | SignatProj (mdl, nm) -> 
      fprintf ppf "%a.%s"  output_modul mdl   (Name.string_of_name nm)
*)

and output_signat ppf = function
    SignatName s -> fprintf ppf "%s" (Name.string_of_name s)
  | Signat body -> fprintf ppf "@[<v>sig@,  @[<v>%a@]@,end@]"  output_specs body
  | SignatFunctor ((m,sgnt1),sgnt2) ->
      fprintf ppf "@[<v>functor (%s : %a) ->@ %a@]"
         (Name.string_of_name m)   output_signat sgnt1   output_signat sgnt2
  | SignatApp (sgnt1,mdl)  ->
	    fprintf ppf "@[%a(%a)@]"    output_signat sgnt1    output_modul mdl
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
      fprintf ppf "@[<hov 2>module type %a =@ %a@]@.@." 
	output_name nm   output_signat signat

and output_toplevel ppf body =
  fprintf ppf "@[<v>%a@]@.@."  output_specs body
