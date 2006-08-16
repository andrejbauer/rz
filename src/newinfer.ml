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

let noTypeInferenceInError nm expr =
  tyGenericError
     ("The bound variable " ^ S.string_of_name x ^ " in " ^
      S.string_of_expr expr ^ " is not annotated explicitly or implicitly.")

let wrongTypeError expr hastype expectedsort context_expr =
  tyGenericError
    ("The term " ^ string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ " in " ^ string_of_expr context_expr ^ 
      ", but it's actually has type " ^ L.string_of_set hastype)

let wrongPropTypeError expr hasPT expectedsort context_expr =
  tyGenericError
    ("The term " ^ string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ " in " ^ string_of_expr context_expr ^ 
      ", but it's actually has type " ^ L.string_of_proptype hasPT)

let wrongKindError expr hasK expectedsort context_expr =
  tyGenericError
    ("The set " ^ string_of_expr expr ^ " is used as if had a "
      ^ expectedsort ^ " kind in " ^ string_of_expr context_expr ^ 
      ", but it's actually has kind " ^ L.string_of_kind hasK)

let tyMismatchError expr expectedTy foundTy context_expr =
  tyGenericError
    ("The term " ^ string_of_expr expr ^ " was expected to have type " ^
	L.string_of_set expectedTy ^ " instead of type " ^ 
	L.string_of_set foundTy ^ " in " ^ string_of_expr context_expr)

let propTypeMismatchError expr expectedTy foundTy context_expr =
  tyGenericError
    ("The proposition " ^ string_of_expr expr ^ " was expected to have type " ^
	L.string_of_proptype expectedTy ^ " instead of type " ^ 
	L.string_of_proptype foundTy ^ " in " ^ string_of_expr context_expr)

let kindMismatchError expr expectedK foundK context_expr =
  tyGenericError
    ("The set " ^ string_of_expr expr ^ " was expected to have type " ^
	L.string_of_kind expectedK ^ " instead of type " ^ 
	L.string_of_kind foundK ^ " in " ^ string_of_expr context_expr)

let notEquivalenceOnError expr expectedDomExpr =
  tyGenericError
    ("The relation " ^ string_of_expr expr ^ 
	" is not an equivalence relation on " ^ 
	string_of_expr expectedDomExpr)
	

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

type ctx_member =
    CtxProp  of L.proposition * L.proptype
  | CtxSet   of L.set * L.kind
  | CtxTerm  of L.term * L.set
  | CtxModel of L.model * summary * substitution
  | CtxUnbound

type implicit_info =
      ImpTermvar of L.set
    | ImpUnknown


type context = {bindings : (name * ctx_member) list;
		implicits : (name * implicit_info) list}

let sertTermVariable cntxt nm st trmopt =
    (raise Unimplemented : context)
      
let lookupId cntxt name = (raise Unimplemented : ctx_member)

let lookupImplicit cntxt name = (raise Unimplemented : implicit_info)


let annotateExpr cntxt = function 
    Ident nm -> 
      begin
	match lookupId cntxt nm with
            CtxProp (_, pty) -> ResProp(L.Atomic(L.longname_of_name nm),
	                               pty)
	  | CtxSet  (_, knd) -> ResSet(L.Basic(L.set_longname_of_name nm),
		 		      knd)
	  | CtxTerm (_, ty)  -> ResTerm(L.Var(L.longname_of_name nm),
				       ty)
	  | CtxModel(_, smmry, subst) -> 
              ResModel(L.Model_name(L.model_name_of_name nm),
		      smmry, subst)
	  | CtxUnbound -> tyUnboundError nm
      end

  | MProj (mdl, nm) as orig_expr ->
      let (mdl' as whereami, summary, subst) = annotateModel cntxt orig_expr mdl
      in
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
	  | (ResProp(prp1,prpty1), ResTerm(expr2,ty2)) -> 
	      begin
		(* Application of a predicate to a term *)
		match prpty1 with
		    L.PropArrow(nm,domty,codprpty) -> 
		      begin
			(* Application of a predicate *)
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      ResProp( S.PApp(prp1, trm2'),
				       L.substTermInPropType nm trm2' codprpty )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end

                  | L.EquivProp(domty) ->
		      begin
			(* Partial application of an equivalence relation.
			   The result has type domty -> StableProp.        *)
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      ResProp( S.PApp(prp1, trm2'),
				       L.PropArrow(S.freshWildName(),
						   domty, L.StableProp) )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end
		  | _ -> wrongPropTypeError expr1 prpty1 "predicate" orig_expr
	      end

	  | (ResSet(st1,knd1), ResTerm(trm2,ty2)) ->
	      begin
		(* Application of a parameterized set to a term *)
		match knd1 with
		    L.KindArrow(nm,domty,codknd) -> 
		      begin
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      ResSet( S.SApp(st1, trm2'),
				      L.substTermInKind nm trm2' codknd )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end
		  | _ -> wrongKindError expr1 "arrow" orig-expr knd1
	      end
		
	  | (ResTerm(trm1,ty1), ResTerm(trm2,ty2)) -> 
	      begin
		(* Application of a term to a term *)
		match coerceFromSubset cntxt trm1 ty1 with
		    Some (trm1', L.Exp(nm,domty,codty)) ->
		      begin
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      ResTerm( S.App(trm1', trm2'),
				       L.substTermInSet nm trm2' codty )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end
		  | _ -> wrongTypeError expr1 "function" orig-expr ty1
	      end

	  | _ -> tyGenericError ("Invalid application " ^ 
				    S.string_of_expr orig_expr) 
      end

  | Lambda (bnd1, expr2) as orig_expr ->
      begin
	let (bnd1', cntxt') = annotateBinding cntxt orig_expr bnd1
	in  
	  (* Have to flatten out all the bound variables... *)
	  match annotateExpr cntxt' expr2 with
	      ResProp(prp2,prpty2) ->
		raise Unimplemented

	    | ResSet (st2,knd2) ->
		raise Unimplemented

	    | ResTerm(trm2,ty2) -> 
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
	    | ResProp (prp1, (L.Prop | L.StableProp) as stab1) -> 
		if (S.isWild nm) then
		  begin
		    (* Typechecking an implication *)
		    let (prp2, stab2) = annotateProperProp cntxt expr2 
		    in 
			ResProp ( L.Imply(prp1, prp2),
				  joinPropTypes [stab1; stab2] )
		  end
		else
		  badDomainError()
	    | ResProp _ ->
		(* Predicate that's not a proper proposition *)
		badDomainError()
            | ResSet (ty1, L.KindSet) ->
		begin
		  (* Typechecking a Pi *)
		  let cntxt' = insertTermVariable cntxt nm ty1 None
		  in match annotateExpr cntxt' expr2 with
		      ResSet(st2, knd2) -> 
			(* Typechecking a dependent type of a function *)
			ResSet ( L.Exp (nm, ty1, st2),
			         L.Kindarrow(nm, ty1, knd2) )

                    | ResPropType(prpty2) -> 
			(* Typechecking a dependent type of a proposition *)
			ResPropType( L.PropArrow(nm, ty1, prpty2) )

		    | ResKind(knd2) ->
			(* Typechecking a dependent kind of a family of sets *)
			ResKind( L.KindArrow(nm, ty1, knd2) )

		    | _ ->
			notWhatsExpectedInError expr2
			  "set, proposition-type, or kind" orig_expr
		end
      end

  | Constraint (expr1, expr2) as orig_expr ->
      begin
	match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
	    (ResTerm(trm1,ty1), ResSet(ty2,L.KindSet)) ->
	      (* Typecheck a term constrained by a type *)
	      begin
		match coerce cntxt trm1 ty1 ty2 with
		    trm1' -> ResTerm(trm1', ty2)
		  | _ -> tyMismatchError expr1 ty2 ty1 orig_expr
	      end

	  | (ResProp(prp1,prpty1), ResPropType(prpty2)) ->
	      (* Typecheck a proposition constrained by a prop. type *)
	      if (subPropType cntxt prpty1 prpty2) then
		ResProp( prp1, prpty2 )
	      else
		propTypeMismatchError prp1 prpty2 prpty1 orig_expr 

	  | (ResSet(st1,knd1), ResKind(knd2)) ->
	      (* Typecheck a set constrained by a kind *)
	      if (subKind cntxt knd1 knd2) then
		ResSet(st1, knd2)
	      else
		kindMismatchError st1 knd2 knd1 orig_expr
 
          | _ -> tyGenericError 
		 ("Incoherent constraint " ^ string_of_expr orig_expr)
      end

  | Empty -> ResSet(L.Empty, L.KindSet)

  | Unit  -> ResSet(L.Unit, L.KindSet)

  | Product _ -> 
      (* Either a [possibly dependent] type for a tuple, or
	 a use of the term-operator ( * ) . *)
      raise Unimplemented

  | Sum _ ->
      (* Either a sum type, or a use of the term-operator (+) *)
      raise Unimplemented

  | Subset ((nm, expropt1), expr2) as orig_expr ->
      begin
	let cntxt' = 
	  match expropt1 with
	      None -> 
		(* No type annotation; hope the variable's Implicit *)
		(match lookupImplicit cntxt nm with
		    ImpTermvar ty -> 
		      insertTermVariable cntxt nm st1'
		  | _ -> 
		      noTypeInferenceInError nm orig_expr)
	    | Some expr1 -> 
		(* Check the type annotation *)
		(match annotateExpr cntxt expr1 with
		    ResSet(st1',L.KindSet) -> 
		      insertTermVariable cntxt nm st1'
		  | _ -> 
		      notWhatsExpectedInError expr1 "proper set" orig_expr)
	in
	  match annotateExpr cntxt' expr2 with
	      ResProp(prp2', (L.Prop | L.StableProp)) ->
		ResSet( Subset((nm,None), prp2'), L.KindSet )
	    | _ ->
		notWhatsExpectedInError expr2 "proposition" orig_expr
      end
	
  | Quotient (expr1, expr2) as orig_expr -> 
      begin
	let badRelation() =
	  notWhatsExpectedInError expr2 "equivalence relation" orig_expr
	in
	  match (annotateExpr cntxt expr1) with
	      ResSet(ty1, L.KindSet) -> 
		(* Quotient of a set *)
		begin
		  match annotateProp cntxt expr2 with 
		      (prp2, Equiv(domty2)) ->
			if (subSet cntxt ty1 domty2) then
			  ResSet( L.Quotient (ty1, prp2),
			        L.KindSet )
			else
			  notEquivalenceOnError expr2 expr1
		    | _ -> badRelation()
		end
		  
	    | ResTerm(trm1, ty1) ->
		(* Quotient [equivalence class] of a term *)
		begin
		  match annotateProp cntxt expr2 with 
		      (prp2, Equiv(domty2)) ->
			begin
			  match coerce cntxt trm1 ty1 domty2 with
			      Some trm1' -> 
				ResSet( L.Quot (trm1', prp2),
			              L.Quotient (domty2, prp2) )
			    | _ -> notEquivalenceOnError expr2 expr1
			end
		    | _ -> badRelation()
		end
		   
	    | _ -> 
		notWhatsExpectedInError expr1 "term or proper set" orig_expr
      end

  | Rz (expr1) as orig_expr ->
      begin
	match annotateExpr cntxt expr1 with
	    ResSet(ty1, L.KindSet) -> 
	      (* Set of realizers for this set *)
	      ResSet (Rz ty1, L.KindSet)

	  | ResTerm(trm1, ty1) ->
	      begin
		(* Value realized by this term(?) *)
		match coerceFromSubset cntxt trm1 ty1 with
		    (trm1', L.Rz ty1') ->
		      ResTerm( L.RzQuot trm1', ty1')
		  | _ -> wrongTypeError expr1 ty1 "realizer" orig_expr
	      end			     

	  | _ -> 
	      notWhatsExpectedInError expr1 "realizer or proper set" orig_expr
      end

  | Set -> ResKind (L.KindSet)

  | Prop -> ResPropType (L.Prop)

  | Stable -> ResPropType (L.StableProp)

  | Equiv expr as orig_expr ->
      let equiv_domain_type = annotateType cntxt orig_expr expr
      in
	ResPropType ( L.EquivProp equiv_domain_type )

  | EmptyTuple -> ResTerm ( L.Star, L.Unit )

  | Tuple exprs as orig_expr ->
      let pairs = List.map (annotateTerm cntxt orig_expr) exprs
      in let (trms',tys') = List.split pairs
      in let addName t = (S.freshWildName(), t)
      in 
	   ResTerm( L.Tuple trms', 
		    L.Product (List.map addName tys') )

  | Proj(n1, expr2) as orig_expr ->
      begin
	let    (trm2',  ty2' ) = annotateTerm cntxt orig_expr expr2
	in let (trm2'', ty2'') = coerceFromSubset cntxt trm2' ty'
	in
	  match ty2'' with 
	      Product nmtys ->
		(* Project out the n1-st type *)
		raise Unimplemented
	    | _ -> wrongTypeError expr2 ty2' "tuple"  orig_expr
      end

  | Inj(label, None) -> ResTerm ( L.Inj(label, None),
				  L.Sum[(label, None)] )

  | Inj(label, Some expr2) as orig_expr ->
      let (trm2', ty2') = annotateTerm cntxt orig_expr expr2
      in 
	ResTerm ( L.Inj(label, Some trm2'),
		  L.Sum[ (label, Some ty2') ] )
	  
  | Case (expr1, arms2) as orig_expr ->
      raise Unimplemented

  | RzChoose(bnd1, expr2, expr3) as orig_expr ->
      raise Unimplemented

  | Subin(expr1, expr2) as orig_expr ->
      begin
	let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let ty2       = annotateType cntxt orig_expr expr2
	in  
	     match (hnfSet cntxt ty2) with
		 Subset _ -> 
		   raise Unimplemented
	       | _ ->
		   raise Unimplemented
      end

  | Subout(expr1, expr2) as orig_expr ->
      begin
	let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let ty2       = annotateType cntxt orig_expr expr2
	in  
	     match (hnfSet cntxt ty1) with
		 Subset _ -> 
		   raise Unimplemented
	       | _ ->
		   raise Unimplemented
      end

  | Let(bnd1, expr1, expr2) as orig_expr ->
      raise Unimplemented

  | The(bnd1, expr2) as orig_expr ->
      raise Unimplemented

  | False -> ResProp(L.False, L.StableProp)

  | True -> ResProp(L.False, L.StableProp)

  | And exprs as orig_expr ->
      begin
	let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	in let (prps, prptys) = List.split pairs
	in 
	     ResProp ( L.And prps,
		       joinPropTypes prptys )
      end

  | Or exprs as orig_expr ->
      begin
	let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	in let (prps, prptys) = List.split pairs
	in 
	     ResProp ( L.And prps,
		       joinPropTypes prptys )
      end

  | Not expr as orig_expr ->
      let (prp, prpty) = annotateProperProp cntxt orig_expr expr
      in
	ResProp ( L.Not prp, prpty )

  | Iff (expr1,expr2) as orig_expr ->
      begin
	let    (prp1, prpty1) = annotateProperProp cntxt orig_expr expr1
	in let (prp2, prpty2) = annotateProperProp cntxt orig_expr expr2
	in 
	     ResProp ( L.Iff(prp1, prp2),
		       joinPropTypes [prp1; prp2] )
      end

  | Equal (expropt1, expr2, expr3) ->
      raise Unimplemented

  | Forall (bnd1, expr2) ->
      raise Unimplemented

  | Exists (bnd1, expr2) ->
      raise Unimplemented

  | Unique (bnd1, expr2) ->
      raise Unimplemented
  
  | _ -> raise Unimplemented


and annotateModel cntxt surrounding_expr expr = 
    (match annotateExpr cntxt expr with
	ResModel(mdl, smmry, sbst) -> (mdl, smmry, sbst)
      | _ -> notWhatsExpectedInError expr "model" surrounding_expr)

and annotateTerm cntxt surrounding_expr expr = 
    (match annotateExpr cntxt trm with
	ResTerm(trm, ty) -> (trm, ty)
      | _ -> notWhatsExpectedInError expr "term" surrounding_expr)

and annotateSet cntxt surrounding_expr expr = 
    (match annotateExpr cntxt trm with
	ResSet(st, knd) -> (st, knd)
      | _ -> notWhatsExpectedInError expr "set" surrounding_expr)

and annotateType cntxt surrounding_expr expr = 
    (match annotateExpr cntxt trm with
	ResSet(st, L.KindSet) -> st
      | _ -> notWhatsExpectedInError expr "proper type" surrounding_expr)

and annotateProp cntxt surrounding_expr expr = 
    (match annotateProp cntxt trm with
	ResProp(prp, prpty) -> (prp, prpty)
      | _ -> notWhatsExpectedInError expr "proposition" surrounding_expr)

and annotateProperProp cntxt surrounding_expr expr = 
    (match annotateProp cntxt trm with
	ResProp(prp, (L.Prop | L.StableProp) as prpty) -> (prp, prpty)
      | ResProp _ -> 
	  notWhatsExpectedInError expr "proper proposition" surrounding_expr
      | _ -> 
	  notWhatsExpectedInError expr "proposition" surrounding_expr)
    


    
