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

let tyGenericError msg = 
  (print_string (type_error_header ^ msg ^ type_error_footer);
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

let cantElimError context_expr =
  tyGenericError 
    ("Inferred type of " ^ string_of_expr orig_expr ^ 
	"refers to a locally-bound variable; " ^ 
	"maybe a constraint on the body would help?")
	

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
    CtxProp  of L.proposition option * L.proptype
  | CtxSet   of L.set option         * L.kind
  | CtxTerm  of                      * L.set
  | CtxModel of L.model option       * summary * substitution
  | CtxUnbound

type implicit_info =
      ImpTermvar of L.set
    | ImpUnknown


type context = {bindings : (name * ctx_member) list;
		implicits : (name * implicit_info) list}

let emptyContext = {bindings = []; implicits = []}

let lookupImplicit {implicits} nm = 
  try Some (List.assoc nm implicits) with
      Not_Found -> ImpUnknown

let lookupId {bindings} nm =
  try Some (List.assoc nm bindings) with
      Not_Found -> CtxUnbound

let insertTermVariable cntxt nm ty =
  { cntxt with bindings =  (nm, CtxTerm ty) :: cntxt.bindings }

let insertSetVariable cntxt nm knd stopt =
  { cntxt with bindings =  (nm, CtxSet (stopt,knd)) :: cntxt.bindings }

let insertPropVariable cntxt nm prpty prpopt =
  { cntxt with bindings =  (nm, CtxProp (prpopt,prpty)) :: cntxt.bindings }

(*** XXX Does not check that names are of the right form,
     e.g., that set names are lowercased non-infix. *)

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
			   The result has type domty -> Stable.        *)
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      ResProp( S.PApp(prp1, trm2'),
				       L.PropArrow(S.freshWildName(),
						   domty, L.Stable) )
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

  | Lambda (binding1, expr2) as orig_expr ->
      begin
	let (cntxt', lbnds1) = annotateBinding cntxt orig_expr binding1
	in  
	  match annotateExpr cntxt' expr2 with
	      ResProp(prp2,prpty2) ->
		(* Defining a predicate *)
		ResProp ( List.fold_right L.fPlambda   lbnds1 prp2,
			  List.fold_right L.fPropArrow lbnds1 prpty2 )

	    | ResSet (st2,knd2) ->
		(* Defining a family of sets *)
		ResSet ( List.fold_right L.fSlambda   lbnds1 st2,
			 List.fold_right L.fKindArrow lbnds1 knd2 )

	    | ResTerm(trm2,ty2) -> 
		(* Defining a function term *)
		ResSet ( List.fold_right L.fLambda lbnds1 trm,
			 List.fold_right L.fExp    lbnds1 ty2 )

	    | _ -> tyGenericError("Invalid body in " ^
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
	    | ResProp (prp1, (L.Prop | L.Stable) as stab1) -> 
		if (S.isWild nm) then
		  begin
		    (* Typechecking an implication *)
		    let (prp2, stab2) = annotateProperProp cntxt expr2 
		    in 
		      (* case.pdf: "Almost negative formulas [are]
			 built from any combination of 
			 /\, ->, forall, =, and those
                         bas ic predicates known to be stable, but 
			 \/ and exists are only allowed to appear 
			 on the left side of a -> ..." *) 
		      ResProp ( L.Imply(prp1, prp2),
			        stab2 )
		  end
		else
		  badDomainError()
	    | ResProp _ ->
		(* Predicate that's not a proper proposition *)
		badDomainError()
            | ResSet (ty1, L.KindSet) ->
		begin
		  (* Typechecking a Pi *)
		  let cntxt' = insertTermVariable cntxt nm ty1
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

  | Product sbnds  as orig_expr ->
      begin
	(* A [possibly dependent] type for a tuple. *)
	let rec loop cntxt = function
	    [] -> []
	  | sbnd :: rest ->     
              let (cntxt', lbnd) = annotateSimpleBinding cntxt orig_expr sbnd
	      in 
		lbnd :: loop cntxt' rest
	in    
	  ResSet(L.Product (loop cntxt nes), L.KindSet) 
      end

  | Sum _ ->
      (* Either a sum type, or a use of the term-operator (+) *)
      raise Unimplemented

  | Subset (sbnd1, expr2) as orig_expr ->
      begin
	let (cntxt', lbnd1) = annotateSimpleBinding cntxt orig_expr sbnd1
	in
	  match annotateExpr cntxt' expr2 with
	      ResProp(prp2', (L.Prop | L.Stable)) ->
		ResSet( Subset(lbnd1, prp2'), L.KindSet )
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

  | Stable -> ResPropType (L.Stable)

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
	      L.Product nmtys ->
		let rec loop k subst = function
		    [] -> raise Impossible
		      (nm,ty) :: rest ->
			if (k = n1) then
			  ResType ( L.proj(n1, trm2''), 
			          L.substSet subst ty )
			else
			  loop (k+1) 
			    (L.insertTermvar subst nm (Proj(k,trm''))) rest
		in let len = List.length nmtys
		in 
		     if ( (n1 < 0) || (n1 >= len) ) then
		       tyGenericError ("Projection " ^ string_of_int n1 ^ 
					  " out of bounds in " ^
				          string_of_expr orig_expr)
		     else 
		       loop 0 emptysubst nmtys
			 
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

  | RzChoose(sbnd1, expr2, expr3) as orig_expr ->
      begin
	let (trm2, ty2) = annotateTerm cntxt orig_expr expr2
	  (* XXX : annotate...withCheckedDefault would be better *)
	in let (cntxt', (nm1,ty1) as lbnd1) = 
	      annotateSimpleBinding cntxt orig_expr sbnd1
	in 
	     match hnfSet cntxt ty1 with
		 RZ ty1' ->
		   if (subSet cntxt ty2 ty1') then 
		     let (trm3, ty3) = annotateTerm cntxt' expr3
		     in 
		       if NameSet.mem nm1 (L.fnSet ty3) then
			 cantElimErrorError orig_expr
		       else 
			 ResTerm ( L.RzChoose (lbnd1, trm2, trm3, ty3),
				   ty3 )
		   else
		     tyMismatchError expr2 ty1' ty2 orig_expr
	       | _ -> 
		   tyGenericError 
		     ("The bound variable " ^ 
		         L.string_of_name nm1 ^ 
		         " in the construct " ^ 
			 string_of_expr orig_expr ^ 
		         "should have a realizer type, but here it has type " ^ 
		         L.string_of_set ty1)
      end

  | Subin(expr1, expr2) as orig_expr ->
      begin
        (* Injection into a subset; incurs an obligation *)
	let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let ty2       = annotateType cntxt orig_expr expr2
	in  
	     match (hnfSet cntxt ty2) with
		 L.Subset _ -> 
		   begin
		     match coerce cntxt trm1 ty1 domty2 with
			 Some trm1' ->
			   ResTerm ( L.Subin ( trm1', ty2 ),
				     ty2 )
		       | None ->
			   tyMismatchError expr1 domty2 ty1 orig_expr
		   end
	       | _ ->
		   notWhatsExpectedInError expr2 "subset type" orig_expr
      end

  | Subout(expr1, expr2) as orig_expr ->
      begin
	let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let ty2       = annotateType cntxt orig_expr expr2
	in  
	     match (hnfSet cntxt ty1) with
		 L.Subset _ -> 
		   begin
		     match coerce cntxt trm1 ty1 ty2 with
			 Some trm1' ->
			   ResTerm ( L.SubOut ( trm1', ty2),
				   ty2)
		       | None -> 
			   tyGenericError
			     ("Could not coerce the subset term " ^ 
				 string_of_expr expr1 ^ " to type " ^
				 string_of_expr expr2 ^ " in " ^ 
			         string_of_expr orig_expr)
		   end
	       | _ ->
		   notWhatsExpectedInError expr1 "term in a subset" orig_expr
      end

  | Let(sbnd1, expr2, expr3) as orig_expr ->
      begin
	(* Right now, let is for terms only *)
	let (trm2, ty2) = annotateTerm cntxt orig_expr expr2
	  (* XXX: AnnotateSimpleBindingWithDefault CheckedDefault? 
	     Ideally, we don't need a type annotation since we 
	     already know what the type of the rhs is... *)

	in let (cntxt', (nm1,ty1)) = annotateSimpleBinding cntxt orig_expr sbnd1

          (* NB: If we ever start putting term definitions into the
             context, we'd need to do it here, since
             annotateSimpleBinding doesn't know the definition... *)
	in let (trm3, ty3) = annotateTerm cntxt' orig_expr expr3
	in 
	     if NameSet.mem nm1 (L.fnSet ty3) then
	       cantElimErrorError orig_expr
	     else 
	       ResTerm ( L.Let ((nm1,ty1), trm2, trm3),
		         ty3 )
      end

  | The(sbnd1, expr2) as orig_expr ->
      let (cntxt', lbnd1) = annotateSimpleBinding cntxt orig_expr sbnd1
      in let (trm2, ty2) = annotateTerm cntxt orig_expr expr2
      in
	   if NameSet.mem nm1 (L.fnSet ty2) then
	     cantElimErrorError orig_expr
	   else 
	     ResTerm ( L.The ((nm1,ty1), trm2),
		       ty2 )

  | False -> ResProp(L.False, L.Stable)

  | True -> ResProp(L.False, L.Stable)

  | And exprs as orig_expr ->
      begin
	let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	in let (prps, prptys) = List.split pairs
	in 
	     ResProp ( L.And prps,
		       L.joinPropTypes prptys )
      end

  | Or exprs as orig_expr ->
      begin
	let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	in let (prps, prptys) = List.split pairs
	in 
	     ResProp ( L.Or prps,
		       L.Prop )
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

  | Equal (expr1, expr2) as orig_expr ->
      begin
	let    (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let (trm2, ty2) = annotateTerm cntxt orig_expr expr2
	in let ty = joinTypes orig_expr [ty1; ty2]
	in 
	     ResProp( L.Equal(ty, trm1, trm2),
		      L.Stable )
      end

  | Forall (binding1, expr2) as orig_expr ->
      let (cntxt', lbnds1) = annotateBinding cntxt orig_expr binding1
      in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
      in let forallprp = 
	List.fold_right (fun lbnd p -> L.Forall(lbnd, p)) lbnds1 prp2
      in
	   ResProp ( forallprp, stab2 )
	     
  | Exists (bnd1, expr2) ->
      let (cntxt', lbnds1) = annotateBinding cntxt orig_expr binding1
      in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
      in let existsprp = 
	List.fold_right (fun lbnd p -> L.Exists(lbnd, p)) lbnds1 prp2
      in
	   ResProp ( existsprp, L.Prop )

  | Unique (bnd1, expr2) ->
      let (cntxt', lbnds1) = annotateBinding cntxt orig_expr binding1
      in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
      in let uniqueprp = 
	List.fold_right (fun lbnd p -> L.Unique(lbnd, p)) lbnds1 prp2
      in
	   ResProp ( uniqueprp, L.Prop )
	     


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
      ResProp(prp, (L.Prop | L.Stable) as prpty) -> (prp, prpty)
    | ResProp _ -> 
	notWhatsExpectedInError expr "proper proposition" surrounding_expr
    | _ -> 
	notWhatsExpectedInError expr "proposition" surrounding_expr)
    
(* annotateBinding: context -> S.expr -> S.binding -> L.binding list
*)
and annotateBinding cntxt surrounding_expr binders =
  (* Loop over variable-list/type pairs *)
  let rec bLoop cntxt' = function
      []                    -> []
    | ([],_)::rest          -> bLoop cntxt' rest
    | (ns, expropt)::rest ->
	let ty = 
	  begin
	    (* Figure out the type for variables in the name list ns *)
	    match expropt with
		None -> 
		  begin
		    (* No type annotation; hope the variable's Implicit *)
		    match lookupImplicit cntxt nm with
			ImpTermvar ty -> ty
		      | _ -> noTypeInferenceInError nm surrounding_expr
		  end
	      | Some expr -> 
		  annotateType cntxt surrounding_expr expr
	  end 

	(* Now loop to create this pair's bindings and extended context *)
	in let rec nLoop = function 
	    [] -> (cntxt', [])
	  | n::ns -> 
	      let (cntxt'', lbnds) = nLoop ns
	      in ((n,ty) :: lbnds,
		   insertTermVariable cntxt'' n ty)
	in let (cntxt'', lbnds) = nLoop ns

	(* Now handle the rest of the pairs *)
	in let (cntxt_final, lbnds_rest) = bLoop cntxt'' rest

	(* Combine results *)
	in
	     (cntxt_final, lbnds @ lbnds_rest)
  in
    bLoop cntxt binders

(*
   annotateSimpleBinding : context -> S.expr -> S.binding1 -> L.binding
*)
and annotateSimpleBinding cntxt surrounding_expr (nm, expropt) =
  begin
    match annotateBinding cntxt surrounding_expr [([nm], expropt)] with
	(cntxt', [lbnd]) -> (cntxt', lbnd)
      | _ -> raise Impossible
  end


