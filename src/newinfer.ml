(*******************************************************************)
(** {1 Type Reconstruction and Checking}                           *)
(**                                                                *)
(** For now we assume that                                         *)
(** all bound variables are annotated, either when declared        *)
(** or through a prior "implicit" statement.                       *)
(*******************************************************************)

open Syntax

exception Unimplemented
exception Impossible

(************************)
(** {2 Error Reporting} *)
(************************)

exception TypeError

let type_error_header = "\n\nTYPE ERROR:  "
let type_error_footer = "\n\n"

let tyGenericError mssg = 
  (print_string (type_error_header ^ mssg ^ type_error_footer);
   raise TypeError)


let tyUnboundError nm =
  tyGenericError
    ("Unbound name " ^ S.string_of_name nm)

let notWhatsExpectedError expr expected =
  tyGenericError
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected")

let notWhatsExpectedInError expr expected context_expr =
  tyGenericError
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected, in " ^ S.string_of_expr context)

let noHigherOrderLogicError expr =
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires higher-order-logic")

let noPolymorphismError expr =
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires polymorphism")

let noPropositionsAsTypesError expr = 
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires polymorphism")

   

(*****************************************)
(** {2 Typechecking/Type Reconstruction} *)
(*****************************************)

type inferResult =
    ResPropType of L.proptype
  | ResKind     of L.setkind
  | ResSet      of L.set * L.setkind
  | ResTerm     of L.term * L.set
  | ResProp     of L.proposition * L.proptype
  | ResModel    of L.model * summary * substitution


fun annotateExpr cntxt = function 
    Ident nm -> 
      (match lookupId cntxt nm with
         CtxProp (_, pty) -> ResProp(L.Atomic(L.longname_of_name nm),
	                            pty)
       | CtxSet  (_, knd) -> ResSet(L.Basic(L.set_longname_of_name nm),
		 		   knd)
       | CtxTerm (_, ty)  -> ResTerm(L.Var(L.longname_of_name nm),
				     ty)
       | CtxModel(_, thry) -> ResModel(L.Model_name(L.model_name_of_name nm),
				      thry)
       | CtxUnbound -> tyUnboundError nm)

  | MProj (mdl, nm) ->
      let (mdl' as whereami, summary, subst) = annotateModel cntxt mdl
	raise Unimplemented
(*
      in ( match summary with
            Summary_Struct ( _ , items) ->
              (match (peekTypeof' subst items (Some whereami) nm) with
		  None -> tyGenericError ("Unknown component " ^
					     string_of_term orig_trm)
		| Some st -> ( Var ( Some mdl', nm ), st ) )
          | _ -> tyGenericError 
              ( "Term projection from parameterized model in:\n  " ^ 
		  string_of_term orig_trm ) )
*)
  | App (expr1, expr2) as orig_expr ->
      begin
	match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
	  | (ResProp(prp1',prpty1'), ResTerm(expr2',ty2')) -> 
	      raise Unimplemented
	  | (ResSet(st1',knd1'), ResTerm(expr2',ty2')) ->
	      raise Unimplemented
	    (ResTerm(expr1',ty1'), ResTerm(expr2',ty2')) -> 
	      raise Unimplemented
	  | _ -> tyGenericError ("Invalid application " ^ 
				    S.string_of_expr orig_expr) 
      end

  | Lambda (bnd, expr) as orig_expr ->
      begin
	let (bnd', cntxt') = annotateBinding cntxt bnd
	in  
	  match annotateExpr cntxt' expr' with
	      ResProp(expr'', ty'') ->
		raise Unimplemented
	    | ResSet (expr'',ty'') ->
		raise Unimplemented
	    | ResTerm(expr'',ty'') -> 
		raise Unimplemented
	    | _ -> tyGenericError("Invalid function body in " ^
				     S.string_of_expr orig_expr)
      end

  | Arrow (nm, expr1, expr2) as orig_expr ->
      begin
	let badDomainError() = 
	  if (S.isWild nm) then
	    notWhatsExpectedInError expr1 
	      "proper type or proposition" orig_expr
	  else
	    notWhatsExpectedInError expr1 
	      "proper type" orig_expr
	in
	  match annotateExpr cntxt expr1 with
	    | ResPropType _ ->
		noHigherOrderLogicError orig_expr
	    | ResKind _ ->
		noPolymorphismError orig_expr
	    | ResTerm _ | ResModel _ | ResSet (_, KindArrow _) ->
		badDomainError()
	    | ResProp (prp1', (Prop | EquivProp | StableProp) as stab) -> 
		if (S.isWild nm) then
		  begin
		    (* Typechecking an implication *)
		    raise Unimplemented
		  end
		else
		  badDomainError()
	    | ResProp _ ->
		badDomainError()
            | ResSet (st1', KindSet) ->
		begin
		  let cntxt' = insertTermVariable cntxt nm st1' None
		  in match annotateExpr cntxt' expr2 with
		      _ -> raise Unimplemented
		end
      end


and annotateModel cntxt expr = 
    (match annotateExpr cntxt expr with
	ResModel(mdl, smmry, sbst) -> (mdl, smmry, sbst)
      | _ -> notWhatsExpectedError expr "model")

and annotateTerm cntxt expr =
    (match annotateExpr cntxt trm with
	ResTerm(trm, ty) -> (trm, ty)
      | _ -> notWhatsExpectedError expr "term")

and annotateSet cntxt expr =
    (match annotateExpr cntxt trm with
	ResSet(st, knd) -> (st, knd)
      | _ -> notWhatsExpectedError expr "set")

and annotateProp cntxt expr =
    (match annotateProp cntxt trm with
	ResProp(prp, prpty) -> (prp, prpty)
      | _ -> notWhatsExpectedError expr "proposition")
    


    
