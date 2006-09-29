(*****************************************)
(** {1 Type Reconstruction and Checking} *)                         
(*****************************************)

(** For now we assume that all bound variables are annotated, either
    when declared or through a prior "implicit" statement.
*)

module S = Syntax
module L = Logic
module LR = Logicrules
module E = Error
open Syntax 
open Name

exception Unimplemented
exception Impossible

(**********************)
(** Utility Functions *)
(**********************)

let noDuplicates strngs =
  let sset = List.fold_right StringSet.add strngs StringSet.empty
  in
    List.length strngs = StringSet.cardinal sset

(*************************)
(** {3 Inference proper} *)
(*************************)

type inferResult =
    ResPropType of L.proptype
  | ResKind     of L.setkind
  | ResSet      of L.set         * L.setkind
  | ResTerm     of L.term        * L.set
  | ResProp     of L.proposition * L.proptype
  | ResModel    of L.model       * L.theory 
  | ResTheory   of L.theory      * L.theorykind
  | ResSentence of L.model_binding list * L.proposition

type genericBinding =
      TB of L.binding
    | MB of L.model_binding

let rec annotateExpr cntxt orig_expr = 
  try
    match orig_expr with 	
	Ident nm -> 
	  begin
	    let nm = LR.applyContextSubst cntxt nm 
	    in
	      match LR.lookupId cntxt nm with
		  Some(L.DeclProp (_, pty)) -> 
		    ResProp(L.Atomic(L.longname_of_name nm, pty), pty)
		| Some(L.DeclSet  (_, knd)) -> 
		    ResSet(L.Basic(L.set_longname_of_name nm, knd), knd)
		| Some(L.DeclTerm (_, ty))  -> 
		    ResTerm(L.Var(L.longname_of_name nm), ty)
		| Some(L.DeclModel  thry) -> 
		    ResModel(L.ModelName(L.model_name_of_name nm), thry )
		| Some(L.DeclTheory (thry, tk)) -> 
		    ResTheory (L.TheoryName(L.theory_name_of_name nm), tk)
		| Some(L.DeclSentence _ ) -> raise Impossible
		| None -> E.tyUnboundError nm
	  end

      | MProj (expr1, nm2) ->
	  begin
	    let (mdl, thry) = annotateModel cntxt orig_expr expr1 
	    in match LR.hnfTheory cntxt thry with
		L.Theory elems ->
		  begin
		    match LR.searchElems cntxt nm2 mdl elems with
			Some (L.DeclSet (_,knd)) -> 
			  ResSet(L.Basic(L.SLN(Some mdl, nm2), knd), knd)
		      | Some (L.DeclProp (_,pt)) -> 
			  ResProp(L.Atomic(L.LN(Some mdl, nm2), pt), pt)
		      | Some (L.DeclTerm (_,ty)) -> 
			  ResTerm(L.Var(L.LN(Some mdl, nm2)), ty)
		      | Some (L.DeclModel thry) -> 
			  ResModel(L.ModelProj(mdl,nm2), thry)
(* XXX: is this ok? (Andrej)
		      | Some (L.DeclTheory (thry, thryknd)) ->
			  ResTheory(L.TheoryProj(mdl,nm2), thryknd)
*)
		      | None -> 
			  E.badModelProjectionError nm2 orig_expr "Name not found"
		      | _ -> 
			  E.badModelProjectionError nm2 orig_expr "Name not projectable"
		  end
	      | _ -> E.notWhatsExpectedInError expr1 "theory of a model" orig_expr
	  end

      | App(Label label, expr2) ->
	  (** Special case:  a label applied to an expression is the parser's
	      way of writing an injection into a sum type *)
	  let (trm2', ty2') = annotateTerm cntxt orig_expr expr2
	  in 
	    ResTerm ( L.Inj(label, Some trm2'),
		    L.Sum[ (label, Some ty2') ] )

      | App (expr1, expr2) ->
	  begin
	    match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
	      | (ResProp(prp1,pt1), ResTerm(trm2,ty2)) -> 
		  begin
		    (* Application of a predicate to a term *)
		    match pt1 with
			L.PropArrow(nm,domty,codpt) -> 
			  (* Application of a predicate *)
			  let trm2' = 
			    try
			      LR.coerce cntxt trm2 ty2 domty 
			    with E.TypeError msgs -> 
			      E.specificateError msgs
				(E.tyMismatchMsg expr2 domty ty2)
			  in let sub = L.insertTermvar L.emptysubst nm trm2'
			  in
			       ResProp( L.PApp(prp1, trm2'),
				      L.substProptype sub codpt )
				 
                      | L.EquivProp(domty) ->
			  (* Partial application of an equivalence relation.
			     The result has type domty -> Stable.        *)
			  let trm2' = 
			    try 
			      LR.coerce cntxt trm2 ty2 domty 
			    with E.TypeError msgs -> 
			      E.specificateError msgs 
				(E.tyMismatchMsg expr2 domty ty2)
			  in 
			    ResProp( L.PApp(prp1, trm2'),
				   L.PropArrow(wildName(),
					      domty, L.StableProp) )
		      | _ -> E.wrongPropTypeError expr1 pt1 "predicate" orig_expr
		  end
		    
	      | (ResSet(st1,knd1), ResTerm(trm2,ty2)) ->
		  begin
		    (* Application of a parameterized set to a term *)
		    match knd1 with
			L.KindArrow(nm,domty,codknd) -> 
			  begin
			    let trm2' = 
			      try 
				LR.coerce cntxt trm2 ty2 domty
			      with E.TypeError msgs -> 
				E.specificateError msgs
				  (E.tyMismatchMsg expr2 domty ty2)
			    in let sub = L.insertTermvar L.emptysubst nm trm2'
			    in ResSet( L.SApp(st1, trm2'),
				     L.substSetkind sub codknd )
			  end
		      | _ -> E.wrongKindError expr1 knd1 "arrow" orig_expr 
		  end
		    
	      | (ResTerm(trm1,ty1), ResTerm(trm2,ty2)) -> 
		  begin
		    (* Application of a term to a term *)
		    match LR.coerceFromSubset cntxt trm1 ty1 with
			(trm1', L.Exp(nm,domty,codty)) ->
			  begin
			    let trm2' = 
			      try
				LR.coerce cntxt trm2 ty2 domty
			      with E.TypeError msgs -> 
				E.specificateError msgs
				  (E.tyMismatchMsg expr2 domty ty2)
			    in let sub = L.insertTermvar L.emptysubst nm trm2'
			    in
				 ResTerm( L.App(trm1', trm2'),
					L.substSet sub codty )
			  end
		      | _ -> E.wrongTypeError expr1 ty1 "function" orig_expr
		  end

	      | (ResModel(mdl1,thry1), ResModel(mdl2,thry2)) ->
		  begin
		    (* Application of a model to an argument. *)
		    match LR.hnfTheory cntxt thry1 with
			L.TheoryArrow((nm1, thry1a), thry1b) ->
			  let reqs = 
			    try 
			      LR.checkModelConstraint cntxt mdl2 thry2 thry1a 
			    with 
				E.TypeError msgs -> 
				  E.specificateError msgs
				    (E.theoryMismatchMsg expr2 thry1a thry2)
			  in let _ = if (reqs <> []) then
			      (* XXX *)
			      failwith "UNIMPLEMENTED annotateExpr/App/ResModel"
			  in let subst = L.insertModelvar L.emptysubst nm1 mdl2
			  in let thry = L.substTheory subst thry1b
			  in
			       ResModel( L.ModelApp(mdl1, mdl2), thry)
				 
		      | _ -> E.wrongTheoryError expr1 thry1 "arrow" orig_expr
		  end

	      | (ResTheory(thry1, L.TheoryKindArrow ((nm3,_),tk1) ),
		ResModel (mdl2, thry2) ) ->
		  begin
		    (* Application of a theory to an argument. *)
		    match LR.hnfTheory cntxt thry1 with
			L.TheoryLambda((nm1, thry1a), thry1b) ->
			  let reqs = 
			    try 
			      LR.checkModelConstraint cntxt mdl2 thry2 thry1a
			    with 
				E.TypeError msgs -> 
				  E.specificateError msgs
				    (E.theoryMismatchMsg expr2 thry1a thry2)
			  in let _ = if (reqs <> []) then
			      (* XXX *)
			      failwith "UNIMPLEMENTED annotateExpr/App/ResTheory"
			  in let sub = L.insertModelvar L.emptysubst nm3 mdl2
			  in let tk = L.substTheoryKind sub tk1
			  in
			       ResTheory( L.TheoryApp(thry1, mdl2), tk)
		      | _ -> E.wrongTheoryError expr1 thry1 
			  "parameterized theory" orig_expr
		  end

	      | (ResTheory(thry1, _), ResModel _) ->
		  begin
		    match LR.hnfTheory cntxt thry1 with
			L.TheoryArrow _ ->
			  E.tyGenericError 
			    ("Application of theory *arrow* to an argument; " ^ 
				"was a function intended?")
		      | _ -> E.tyGenericError ("Invalid application " ^
						  string_of_expr orig_expr)
		  end

	      | _ -> E.tyGenericError ("Invalid application " ^ 
					  string_of_expr orig_expr) 
	  end

      | Lambda (binding1, expr2)  ->
	  begin
	    match annotateBinding cntxt orig_expr binding1 with
		(cntxt', [], lbnds1) ->
		  begin
		    match annotateExpr cntxt' expr2 with
			ResProp(prp2,pt2) ->
			  (* Defining a predicate *)
			  ResProp ( List.fold_right L.fPLambda   lbnds1 prp2,
				  List.fold_right L.fPropArrow lbnds1 pt2 )
			    
		      | ResSet (st2,knd2) ->
			  (* Defining a family of sets *)
			  ResSet ( List.fold_right L.fSLambda   lbnds1 st2,
				 List.fold_right L.fKindArrow lbnds1 knd2 )
			    
		      | ResTerm(trm2,ty2) -> 
			  (* Defining a function term *)
			  ResTerm ( List.fold_right L.fLambda lbnds1 trm2,
		  		  List.fold_right L.fExp    lbnds1 ty2 )
			    
		      | _ -> E.notWhatsExpectedInError 
			  expr2 "proposition, set, or term" orig_expr
		  end
	      | (cntxt', mbnds, []) ->
		  begin
		    match annotateExpr cntxt' expr2 with 
			ResTheory (thry, tknd) ->
			  ResTheory(L.foldTheoryLambda mbnds thry,
				   L.foldTheoryKindArrow mbnds tknd)
		      | _ -> 
			  E.tyGenericError 
			    ("Cannot have model parameters in " ^ 
				string_of_expr orig_expr)
		  end
	      | _ ->
		  (* Non-empty model and term binding lists *)
		  E.tyGenericError
		    ("Cannot have model and term parameters in " ^ 
			string_of_expr orig_expr)
	  end
      | Arrow (nm, expr1, expr2)  ->
	  begin
            let badDomainError() = 
	      if (isWild nm) then
		E.notWhatsExpectedInError expr1 
		  "proper type or proposition" orig_expr
	      else
		E.notWhatsExpectedInError expr1 
		  "proper type" orig_expr
	    in
	      match annotateExpr cntxt expr1 with
		| ResPropType _ ->
		    E.noHigherOrderLogicError orig_expr
		| ResKind _ ->
		    E.noPolymorphismError orig_expr
		| ResTerm _ | ResSet (_, L.KindArrow _) 
		| ResModel _ | ResTheory(_, L.TheoryKindArrow _)
		| ResProp (_, (L.PropArrow _ | L.EquivProp _) )
		| ResSentence _ ->
		    badDomainError()
		| ResProp (prp1, (L.Prop | L.StableProp)) -> 
		    let (cntxt, nm) = LR.renameBoundVar cntxt nm in
		      if (isWild nm) then
			begin
			  (* Typechecking an implication *)
			  let (prp2, stab2) = 
			    annotateProperProp cntxt orig_expr expr2 
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
		| ResSet (ty1, L.KindSet) ->
		    begin
		      (* Typechecking a Pi *)
		      let (cntxt, nm) = LR.renameBoundVar cntxt nm
		      in let cntxt' = LR.insertTermVariable cntxt nm ty1 None
		      in match annotateExpr cntxt' expr2 with
			  ResSet(st2, knd2) -> 
			    (* Typechecking a dependent type of a function *)
			    ResSet ( L.Exp (nm, ty1, st2),
			           L.KindSet )

			| ResPropType(pt2) -> 
			    (* Typechecking a dependent type of a proposition *)
			    ResPropType( L.PropArrow(nm, ty1, pt2) )

			| ResKind(knd2) ->
			    (* Typechecking a dependent kind of a family of sets *)
			    ResKind( L.KindArrow(nm, ty1, knd2) )

			| _ ->
			    E.notWhatsExpectedInError expr2
			      "set, proposition-type, or kind" orig_expr
		    end
		| ResTheory(thry1, L.ModelTheoryKind) ->
		    begin
		      let (cntxt, nm) = LR.renameBoundVar cntxt nm
		      in let cntxt' = LR.insertModelVariable cntxt nm thry1
		      in match annotateExpr cntxt' expr2 with
		          ResTheory(thry2, L.ModelTheoryKind) ->
			    ResTheory(L.TheoryArrow((nm, thry1), thry2),
				     L.ModelTheoryKind) 
			| _ -> 
			    E.notWhatsExpectedInError expr2
			      "theory" orig_expr
		    end
	  end

      | Constraint (expr1, expr2) ->
	  begin
	    match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
		(ResTerm(trm1,ty1), ResSet(ty2,L.KindSet)) ->
		  begin
		    (* Typecheck a term constrained by a type *)
		    try 
		      let trm1' = LR.coerce cntxt trm1 ty1 ty2
		      in ResTerm(trm1', ty2)
		    with 
			E.TypeError msgs -> 
			  E.specificateError msgs
			    (E.tyMismatchMsg expr1 ty2 ty1)
		  end

              | (ResProp(prp1, ( (L.PropArrow(nm1a, st1a, 
					     L.PropArrow(_, st1b, 
							L.StableProp))) as pt1) ), 
		ResPropType( (L.EquivProp st2) as pt2 ) ) ->
		  begin
		    (* Special case of coercion into an equivalence relation!*)
		    let (cntxt, nm1a) = LR.renameBoundVar cntxt nm1a
		    in let cntxt' = LR.insertTermVariable cntxt nm1a st1a None
		    in 
			 try
			   let reqs = (LR.subSet cntxt st2 st1a) @ 
			     (LR.subSet cntxt' st2 st1b) @ 
			     [L.IsEquiv(prp1, st2)]
			     (** Is this enough to make translate happy about
				 using prp1 as an equivalence relation? *)
			   in 
			     ResProp(L.maybePAssure reqs prp1,
				    L.EquivProp(st2))
			 with
			     E.TypeError msgs -> 
			       E.specificateError msgs
				 (E.propTypeMismatchMsg expr1 pt2 pt1)
		  end

	      | (ResProp(prp1,pt1), ResPropType(pt2)) ->
		  begin
		    (* Typecheck a proposition constrained by a prop. type *)
		    try
		      let reqs = LR.subPropType cntxt pt1 pt2
		      in ResProp( L.maybePAssure reqs prp1, pt2 )
		    with
			E.TypeError msgs -> 
			  E.specificateError msgs
			    (E.propTypeMismatchMsg expr1 pt2 pt1)
		  end

	      | (ResSet(st1,knd1), ResKind(knd2)) ->
		  begin
		    (* Typecheck a set constrained by a kind *)
		    try
		      let reqs = LR.subKind cntxt knd1 knd2
		      in if (reqs <> []) then
			  (* XXX *)
			  failwith "UNIMPLEMENTED: annotateExpr/Constrant/ResSet"
			else ResSet(st1, knd2)
		    with 
			E.TypeError msgs -> 
			  E.specificateError msgs
			    (E.kindMismatchMsg expr1 knd2 knd1)
		  end

	      | (ResModel(mdl1,thry1), ResTheory (thry2, L.ModelTheoryKind)) ->
		  begin
		    (* Typecheck a model constrained by a theory *)
		    try
		      let reqs = LR.checkModelConstraint cntxt mdl1 thry1 thry2
		      in if (reqs <> []) then
			  (* XXX *)
			  failwith "UNIMPLEMENTED: annotateExpr/Constrant/ResModel"
			else
			  ResModel(mdl1, thry2)  
		    with 
			E.TypeError msgs -> 
			  E.specificateError msgs
			    (E.tyGenericError "Module constraint failed")
		  end
	      | (ResModel _, ResTheory _) -> 
		  E.tyGenericError "Can't constrain a model by a family of theories"
              | _ -> E.tyGenericError 
		  ("Incoherent constraint " ^ string_of_expr orig_expr)
	  end
	    
      | Empty -> ResSet(L.Empty, L.KindSet)

      | Unit  -> ResSet(L.Unit, L.KindSet)

      | Product sbnds   ->
	  begin
	    (* Check first item in the product to see whether it's
	       a product of sets or a product of terms *)
	    match annotateExpr cntxt (snd(List.hd sbnds)) with
		ResSet _ ->
		  (* A [possibly dependent] type for a tuple. *)
		  let rec loop cntxt = function
		      [] -> []
		    | (nm,expr) :: rest ->     
			let (cntxt', lbnd) = 
			  annotateSimpleBinding cntxt orig_expr (nm, Some expr)
			in 
			  lbnd :: loop cntxt' rest
		  in    
		    ResSet(L.Product (loop cntxt sbnds), L.KindSet) 
	    | ResTerm _ ->
		  (* Multiplication, or other operation on terms *)
		  let (nms, exprs) = List.split sbnds
		  in 
		    if (List.for_all isWild nms) then
		      let orig_expr' = 
			List.fold_left 
			  (fun e1 e2 -> App(App(Ident(N("*",Infix3)), e1), e2))
			  (List.hd exprs) (List.tl exprs)
		      in 
			annotateExpr cntxt orig_expr'
		    else
		      E.tyGenericError "Term products can't be labeled"
	    | _ -> 
		E.tyGenericError "Incoherent product"

	  end

      | Sum lsos  ->
	  begin
	    (* We assume that the parser has figured out this is really a sum type
               and not a use of the term operator +. *)
	    let process = function 
		(lbl, None) -> (lbl, None)
	      | (lbl, Some expr) -> (lbl, Some (annotateType cntxt orig_expr expr))
	    in
	      ResSet( L.Sum( List.map process lsos),
		    L.KindSet )
	  end

      | Subset (sbnd1, expr2)  ->
	  begin
	    let (cntxt', lbnd1) = annotateSimpleBinding cntxt orig_expr sbnd1
	    in
	      match annotateExpr cntxt' expr2 with
		  ResProp(prp2', (L.Prop | L.StableProp)) ->
		    ResSet( L.Subset(lbnd1, prp2'), L.KindSet )
		| _ ->
		    E.notWhatsExpectedInError expr2 "proposition" orig_expr
	  end
	    
      | Quotient (expr1, expr2)  -> 
	  begin
	    let badRelation() =
	      E.notWhatsExpectedInError expr2 "equivalence relation" orig_expr
	    in
	      match (annotateExpr cntxt expr1) with
		  ResSet(ty1, L.KindSet) -> 
		    (* Quotient of a set *)
		    begin
		      match annotateProp cntxt orig_expr expr2 with 
			  (prp2, L.EquivProp(domty2)) ->
			    begin
			      try 
				let reqs = LR.subSet cntxt ty1 domty2
				in let prp2' = L.maybePAssure reqs prp2
				in 
				     ResSet( L.Quotient (ty1, prp2'),
					   L.KindSet )
			      with
				  E.TypeError msgs ->
				    E.specificateError msgs
				      (E.notEquivalenceOnMsg expr2 expr1)
			    end
			| _ -> badRelation()
		    end
		      
		| ResTerm(trm1, ty1) ->
		    (* Quotient [equivalence class] of a term *)
		    begin
		      match annotateProp cntxt orig_expr expr2 with 
			  (prp2, L.EquivProp(domty2)) ->
			    begin
			      try
				let trm1' = LR.coerce cntxt trm1 ty1 domty2
				in 
				  ResTerm( L.Quot (trm1', prp2),
					 L.Quotient (domty2, prp2) )
			      with 
				  E.TypeError msgs ->
				    E.specificateError msgs
				      (E.notEquivalenceOnMsg expr2 expr1)
			    end
			| _ -> badRelation()
		    end
		      
		| _ -> 
		    E.notWhatsExpectedInError expr1 "term or proper set" orig_expr
	  end

      | Rz (expr1)  ->
	  begin
	    match annotateExpr cntxt expr1 with
		ResSet(ty1, L.KindSet) -> 
		  (* Set of realizers for this set *)
		  ResSet (L.Rz ty1, L.KindSet)

	      | ResTerm(trm1, ty1) ->
		  begin
		    (* Value realized by this term *)
		    match LR.coerceFromSubset cntxt trm1 ty1 with
			(trm1', L.Rz ty1') ->
			  ResTerm( L.RzQuot trm1', ty1')
		      | _ -> E.wrongTypeError expr1 ty1 "realizer" orig_expr
		  end			     

	      | _ -> 
		  E.notWhatsExpectedInError expr1 "realizer or proper set" orig_expr
	  end

      | Set -> ResKind (L.KindSet)

      | Prop -> ResPropType (L.Prop)

      | Stable -> ResPropType (L.StableProp)

      | Equiv expr  ->
	  let equiv_domain_type = annotateType cntxt orig_expr expr
	  in
	    ResPropType ( L.EquivProp equiv_domain_type )

      | EmptyTuple -> ResTerm ( L.EmptyTuple, L.Unit )

      | Tuple exprs  ->
	  let pairs = List.map (annotateTerm cntxt orig_expr) exprs
	  in let (trms',tys') = List.split pairs
	  in let addName t = (wildName(), t)
	  in 
	       ResTerm( L.Tuple trms', 
		      L.Product (List.map addName tys') )

      | Proj(n1, expr2)  ->
	  begin
	    let    (trm2',  ty2' ) = annotateTerm cntxt orig_expr expr2
	    in let (trm2'', ty2'') = LR.coerceFromSubset cntxt trm2' ty2'
	    in
		 match ty2'' with 
		     L.Product nmtys ->
		       begin
			 match (LR.typeOfProj cntxt nmtys trm2'' n1) with
			     None ->
			       E.tyGenericError ("Projection " ^ string_of_int n1 ^ 
						    " out of bounds in " ^
						    string_of_expr orig_expr)
			   | Some ty ->
			       ResTerm ( L.Proj(n1, trm2''), ty )
		       end
			 
		   | _ -> E.wrongTypeError expr2 ty2' "tuple"  orig_expr
	  end

      | Label label -> ResTerm ( L.Inj(label, None),
			       L.Sum[(label, None)] )

      | Case (expr1, arms2)  -> 
	  begin
	    (* Typecheck the term being cased on *)
	    let (trm1, ty1) = annotateTerm cntxt orig_expr expr1 

            (* Typecheck each arm individually *)	  
	    in let annotateArm = function
		(lbl, None, expr3) -> 
		  (lbl, None, annotateExpr cntxt expr3, expr3)
	      | (lbl, Some sbnd, expr3) ->
		  let (cntxt', lbnd) = annotateSimpleBinding cntxt orig_expr sbnd
		  in (lbl, Some lbnd, annotateExpr cntxt' expr3, expr3)
	    in let arms2' = List.map annotateArm arms2

	    (* Check that there are no duplicate labels *)
	    in let lbls = List.map (fun (l,_,_) -> l) arms2
	    in let _ = if (noDuplicates lbls) then () else
		E.tyGenericError ("There are duplicate labels in " ^ 
				     string_of_expr orig_expr)

            (* Check that the bindings match the term being cased on. *)
	    in let rec createSumtype = function
		[] -> []
	      | (lbl, None,_,_)::rest -> (lbl,None) :: createSumtype rest
	      | (lbl, Some(_,ty),_,_)::rest -> (lbl, Some ty) :: createSumtype rest
	    in let armty = L.Sum (createSumtype arms2')
	    in let reqs1 = 
	      try LR.subSet cntxt ty1 armty
	      with 
	        E.TypeError msgs -> 
		  E.specificateError msgs (E.tyMismatchMsg expr1 armty ty1)

	    in 
		 match arms2' with
		     (_,_,ResTerm _,_)::_ ->
		       begin
			 (* Term-level Case *)
			 let rec process = function
		             [] -> ([], [])
			   | (lbl, None, ResTerm(trm3,ty3), _)::rest -> 
			       let (arms, tys) = process rest
			       in ( (lbl,None,trm3) :: arms, ty3 :: tys )
			   | (lbl, (Some (nm,_) as bopt), ResTerm(trm3,ty3), expr3) :: rest ->
			       if (NameSet.mem nm (L.fnSet ty3)) then
				 E.cantElimError nm ty3 expr3
			       else
				 let (arms, tys) = process rest
				 in ( (lbl,bopt,trm3) :: arms, ty3 :: tys )
			   | (lbl,_,_,_)::_ -> E.tyGenericError 
			       ("Bad case arm " ^ string_of_label lbl ^
				   " in " ^ string_of_expr orig_expr)
			 in let (arms, tys) = process arms2'
			 in let (ty,reqs2) = LR.joinTypes cntxt tys
			 in let trm = L.Case (trm1, armty, arms, ty)
			 in let trm' = L.maybeAssure (reqs1@reqs2) trm ty
			 in ResTerm(trm', ty)
		       end
		   | (_,_,ResProp _, _)::_ ->
		       begin
			 (* Prop-level Case *)
			 let rec process = function
		             [] -> ([], [])
			   | (lbl, None, ResProp(prp3,pt3), _)::rest -> 
			       let (arms, pts) = process rest
			       in ( (lbl,None,prp3) :: arms, pt3 :: pts )
			   | (lbl, (Some (nm,_) as bopt), ResProp(prp3,pt3), expr3) :: rest ->
			       if (NameSet.mem nm (L.fnProptype pt3)) then
				 E.cantElimPTError nm pt3 expr3
			       else
				 let (arms, pts) = process rest
				 in ( (lbl,bopt,prp3) :: arms, pt3 :: pts )
			   | (lbl,_,_,_)::_ -> E.tyGenericError 
			       ("Bad case arm " ^ string_of_label lbl ^
				   " in " ^ string_of_expr orig_expr)
			 in let (arms, pts) = process arms2'
			 in let (pt,reqs2) = LR.joinPropTypes cntxt pts
			 in let prp = L.PCase (trm1, armty, arms)
			 in let prp' = L.maybePAssure (reqs1@reqs2) prp
			 in 
			      ResProp(prp', pt)
		       end
		   | _::_ ->
		       E.tyGenericError 
			 ("Invalid first case in " ^ string_of_expr orig_expr)
		   | _ ->
		       E.tyGenericError
			 ("Case must have at least one arm in " ^ 
			     string_of_expr orig_expr)
	  end

      | Choose(nm1, expr2, expr3)  ->
	  begin
	    let (trm2, ty2) = annotateTerm cntxt orig_expr expr2 
	    in let (trm2', ty2') = LR.coerceFromSubset cntxt trm2 ty2
	    in match ty2' with
		L.Quotient(dom2, prp2) ->
		  begin
		    let (cntxt, nm) = LR.renameBoundVar cntxt nm1
		    in let cntxt' = LR.insertTermVariable cntxt nm dom2 None
		    in let (trm3, ty3) = annotateTerm cntxt' orig_expr expr3
		    in 
			 if NameSet.mem nm1 (L.fnSet ty3) then
			   E.cantElimError nm ty3 orig_expr
			 else 
			   ResTerm ( L.Choose ((nm,dom2), prp2, trm2', trm3, ty3),
			           ty3 )
		  end

	      | _ -> 
		  E.notWhatsExpectedInError 
		    expr2 "equivalence class or realizers" orig_expr
	  end
	    
      | RzChoose(nm1, expr2, expr3)  ->
	  begin
	    let (trm2, ty2) = annotateTerm cntxt orig_expr expr2
	    in let (cntxt, nm) = LR.renameBoundVar cntxt nm1
	    in let cntxt' = LR.insertTermVariable cntxt nm (L.Rz ty2) None
	    in let (trm3, ty3) = annotateTerm cntxt' orig_expr expr3
	    in 
		 if NameSet.mem nm1 (L.fnSet ty3) then
		   E.cantElimError nm ty3 orig_expr
		 else 
		   ResTerm ( L.RzChoose ((nm,L.Rz ty2), trm2, trm3, ty3),
		           ty3 )
	  end

      | Subin(expr1, expr2)  ->
	  begin
            (* Injection into a subset; incurs an obligation *)
	    let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	    in let ty2       = annotateType cntxt orig_expr expr2
	    in  
		 match (LR.hnfSet cntxt ty2) with
		     L.Subset ((_,domty2), _) -> 
		       begin
			 try
			   let trm1' =  LR.coerce cntxt trm1 ty1 ty2
			   in 
			     ResTerm ( trm1',
				     ty2 )
			 with
			     E.TypeError msgs ->
			       E.specificateError msgs
				 (E.tyMismatchMsg expr1 domty2 ty1)
		       end
		   | _ ->
		       E.notWhatsExpectedInError expr2 "subset type" orig_expr
	  end

      | Subout(expr1, expr2)  ->
	  begin
	    let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	    in let ty2       = annotateType cntxt orig_expr expr2
	    in  
		 match (LR.hnfSet cntxt ty1) with
		     L.Subset _ -> 
		       begin
			 try
			   let trm1' = LR.coerce cntxt trm1 ty1 ty2
			   in 
			     ResTerm ( trm1',
				       ty2)
			 with 
			     E.TypeError msgs ->
			       E.specificateError msgs
				 ("Could not coerce the subset term " ^ 
				     string_of_expr expr1 ^ " to type " ^
				     string_of_expr expr2 ^ " in " ^ 
			             string_of_expr orig_expr)
		       end
		   | _ ->
		       E.notWhatsExpectedInError expr1 "term in a subset" orig_expr
	  end

      | Let(sbnd1, expr2, expr3)  ->
	  begin
	    (* Right now, let is for terms only *)
	    let (trm2, ty2) = annotateTerm cntxt orig_expr expr2

	    in let (cntxt', (nm1,ty1)) = 
	      (* Careful with error messages; nm1 might have been renamed *)
	      annotateSimpleBindingWithDefault cntxt orig_expr ty2 sbnd1

	    (* XXX term definitions missing from the context, since
	       annotateSimpleBinding doesn't know the definition... *)

	    in let trm2' =  try LR.coerce cntxt trm2 ty2 ty1 with
		E.TypeError msgs ->
		  E.specificateError msgs
		    (E.tyMismatchMsg expr2 ty1 ty2) 
	    in
		 match annotateExpr cntxt' expr3 with
		     ResTerm(trm3,ty3) ->
		       let ty3' = 
			 (* Eliminate dependencies. *)
			 (* A SLet would be nicer here. *)
			 L.substSet (L.insertTermvar L.emptysubst nm1 trm2') ty3
		       in
			 ResTerm ( L.Let ((nm1,ty1), trm2', trm3, ty3),
				 ty3' )
		   | ResProp(prp3,pt3) ->
		       let pt3' = 
			 (* Eliminate dependencies. *)
			 L.substProptype
			   (L.insertTermvar L.emptysubst nm1 trm2') pt3
		       in
		       ResProp(L.PLet((nm1,ty1), trm2', prp3),
			      pt3')
		   | _ ->
		       E.tyGenericError 
			 ("Let body is not a term or proposition")
	  end
	    
      | The(sbnd1, expr2)  ->
	  let (cntxt', ((nm1,ty1) as lbnd1) ) = 
	    (* Careful with error messages; nm1 might have been renamed *)
	    annotateSimpleBinding cntxt orig_expr sbnd1
	  in let (prp2,_) = annotateProperProp cntxt' orig_expr expr2
	  in
               (** We've agreed that Translate will add the appropriate
		   assure (that we have a singleton subset), since Logic
		   only generates stable assure's, and prp2 isn't necessarily
		   stable. (Its computational content gets attached by
		   Translate to the result anyway, since we've decided
		   that "The x:s.phi" now has type "{x:s | phi}").
               *)
               ResTerm ( L.The (lbnd1, prp2),
                       L.Subset((nm1,ty1), prp2) )

      | False -> ResProp(L.False, L.StableProp)

      | True -> ResProp(L.True, L.StableProp)

      | And exprs  ->
	  begin
	    let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	    in let (prps, pts) = List.split pairs
	    in 
		 ResProp ( L.And prps,
			 LR.joinProperPropTypes pts )
	  end

      | Or exprs  ->
	  begin
	    let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	    in let (prps, pts) = List.split pairs
	    in 
		 ResProp ( L.Or prps,
			 L.Prop )
	  end

      | Not expr  ->
	  let (prp, _) = annotateProperProp cntxt orig_expr expr
	  in
	    ResProp ( L.Not prp, L.StableProp )

      | Iff (expr1,expr2)  ->
	  begin
	    let    (prp1, pt1) = annotateProperProp cntxt orig_expr expr1
	    in let (prp2, pt2) = annotateProperProp cntxt orig_expr expr2
	    in 
		 ResProp ( L.Iff(prp1, prp2),
			 LR.joinProperPropTypes [pt1; pt2] )
	  end

      | Equal (expr1, expr2)  ->
	  begin
	    let    (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	    in let (trm2, ty2) = annotateTerm cntxt orig_expr expr2
	    in let (ty, reqs) = LR.joinTypes cntxt [ty1; ty2]
	    in 
		 ResProp( L.maybePAssure reqs (L.Equal(ty, trm1, trm2)),
			L.StableProp )
	  end

      | Forall (bnd1, expr2)  ->
	  begin
	    match annotateBinding cntxt orig_expr bnd1 with
		(cntxt', [], lbnds1) -> 
		  (* No model bindings, so it's just an ordinary abstraction *)
		  let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
		  in let forallprp = 
		    List.fold_right (fun lbnd p -> L.Forall(lbnd, p)) 
		      lbnds1 prp2
		  in
		       ResProp ( forallprp, stab2 )
			 
	      | (cntxt', mbnds, []) ->
		  begin
		    match annotateExpr cntxt' expr2 with
			ResSentence(mbnds_rest, prp) ->
			  ResSentence(mbnds @ mbnds_rest, prp)
		      | ResProp(prp, (L.Prop | L.StableProp)) ->
			  ResSentence(mbnds, prp)
		      | _ -> E.notWhatsExpectedInError expr2 "sentence" orig_expr
		  end
	      | (cntxt', mbnds, lbnds1) ->
		  let (prp2,_) = annotateProperProp cntxt' orig_expr expr2 
		  in let forallprp = 
		    List.fold_right (fun lbnd p -> L.Forall(lbnd, p)) 
		      lbnds1 prp2
		  in ResSentence(mbnds, forallprp)
	  end

		 
      | Exists (bnd1, expr2)  ->
	  let (cntxt', lbnds1) = annotateInnerBinding cntxt orig_expr bnd1
	  in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
	  in let existsprp = 
	    List.fold_right (fun lbnd p -> L.Exists(lbnd, p)) lbnds1 prp2
	  in
	       ResProp ( existsprp, L.Prop )

      | Unique (bnd1, expr2)  ->
	  let (cntxt', lbnds1) = annotateInnerBinding cntxt orig_expr bnd1
	  in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
	  in let uniqueprp = 
	    List.fold_right (fun lbnd p -> L.Unique(lbnd, p)) lbnds1 prp2
	  in
	       ResProp ( uniqueprp, L.Prop )

      | Theory elems -> 
	  let (_, lelems) = annotateTheoryElems cntxt elems
	  in  ResTheory(L.Theory lelems, L.ModelTheoryKind)
  with
      E.TypeError msgs ->
	E.generalizeError msgs (E.inMsg orig_expr)
    | _ -> 
	E.tyGenericErrors
	  ("Caught unexpected exception" :: [E.inMsg orig_expr])
  (* ********End of annotateExpr ********* *)

and annotateTerm cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResTerm(trm, ty) -> (trm, ty)
    | _ -> E.notWhatsExpectedInError expr "term" surrounding_expr)
    
and annotateSet cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResSet(st, knd) -> (st, knd)
    | _ -> E.notWhatsExpectedInError expr "set" surrounding_expr)
    
and annotateType cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResSet(st, L.KindSet) -> st
    | _ -> E.notWhatsExpectedInError expr "proper type" surrounding_expr)
    
and annotateProp cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResProp(prp, pt) -> (prp, pt)
    | _ -> E.notWhatsExpectedInError expr "proposition" surrounding_expr)
    
and annotateProperProp cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResProp(prp, ((L.Prop | L.StableProp) as pt)) -> (prp, pt)
    | ResProp _ -> 
	E.notWhatsExpectedInError expr "proper proposition" surrounding_expr
    | _ -> 
	E.notWhatsExpectedInError expr "proposition" surrounding_expr)

and annotateKind cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResKind k -> k
    | _ -> E.notWhatsExpectedInError expr "kind" surrounding_expr)

and annotateProptype cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResPropType k -> k
    | _ -> E.notWhatsExpectedInError expr "proposition-type" surrounding_expr)
    
and annotateModel cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResModel(mdl, thry) -> (mdl, thry)
    | _ -> E.notWhatsExpectedInError expr "model" surrounding_expr)

and annotateTheory cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResTheory(thry, tknd) -> (thry, tknd)
    | _ -> E.notWhatsExpectedInError expr "theory" surrounding_expr)


and annotateModelTheory cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResTheory(thry, L.ModelTheoryKind) -> thry
    | _ -> E.notWhatsExpectedInError expr "theory of a model" surrounding_expr)


(* annotateBinding: context -> expr -> binding -> L.binding list
*)
and annotateBinding cntxt surrounding_expr binders =
  (* Loop over variable-list/type pairs *)
  let rec bLoop cntxt' = function
      []                    -> (cntxt', [], [])
    | ([],_)::rest          -> bLoop cntxt' rest
    | (nms, expropt)::rest ->
	(* Now loop to create this pair's bindings and extended context *)
	let rec nLoop = function 
	    [] -> (cntxt', [], [])
	  | n::ns -> 
	      let (cntxt'', mbnds, lbnds) = nLoop ns
	      in let doTypeBinding ty =
		   let (cntxt'', n) = LR.renameBoundVar cntxt'' n
		   in (LR.insertTermVariable cntxt'' n ty None, 
		       mbnds, (n,ty) :: lbnds)
              in let doTheoryBinding thry =
		begin
		  if (lbnds = []) then
		    let (cntxt'', n) = LR.renameBoundVar cntxt'' n
		    in (LR.insertModelVariable cntxt'' n thry, 
		        (n,thry)::mbnds, lbnds)
		  else
		    E.innerModelBindingError surrounding_expr
		end
		  
	      in
		   begin
		     match expropt with
		       None -> 
			 begin
			   (* No type annotation; hope the variable was
			      declared in an Implicit *)
			   match LR.lookupImplicit cntxt n with
			       Some(L.DeclTerm(_, ty))  ->
				 doTypeBinding ty
			     | Some(L.DeclModel thry) ->
				 doTheoryBinding thry
			     | None -> 
		                 E.noTypeInferenceInError n surrounding_expr
			     | Some(L.DeclSet _) ->
				 E.noPolymorphismError surrounding_expr
			     | Some(L.DeclTheory _) 
			     | Some(L.DeclSentence _) ->
				 (* Can't implicitly declare a theory name
				    or a sentence *)
				 raise Impossible
			     | Some(L.DeclProp _) -> 
				 E.noHigherOrderLogicError surrounding_expr
			 end
		     | Some expr ->
			 begin
			   (* Explicitly-annotated binding *)
			   match annotateExpr cntxt expr with
			       ResSet( ty, L.KindSet ) -> 
				 doTypeBinding ty
			     | ResTheory (thry, L.ModelTheoryKind) ->
				 doTheoryBinding thry
			     | _ -> E.illegalBindingError n 
				 ("annotated ("  ^ string_of_expr expr ^ ")")
				   surrounding_expr
			 end
 		   end
	in let (cntxt'', mbnds, lbnds) = nLoop nms
	  
	(* Now handle the rest of the pairs *)
	in let (cntxt_final, mbnds_rest, lbnds_rest) = bLoop cntxt'' rest

	(* Combine results *)
	in
	     if (lbnds = [] || mbnds_rest = []) then
	       (cntxt_final, mbnds @ mbnds_rest, lbnds @ lbnds_rest)
	     else
	       E.innerModelBindingError surrounding_expr

in
    bLoop cntxt binders


and annotateInnerBinding cntxt surrounding_expr binders = 
  match annotateBinding cntxt surrounding_expr binders with
      (cntxt', [], lbnds) -> (cntxt', lbnds)
    | _ -> E.innerModelBindingError surrounding_expr

(*
   annotateSimpleBinding : context -> expr -> binding1 -> L.binding
*)
and annotateSimpleBinding cntxt surrounding_expr (nm, expropt) =
  begin
    match annotateInnerBinding cntxt surrounding_expr [([nm], expropt)] with
	(cntxt', [lbnd]) -> (cntxt', lbnd)
      | _ -> raise Impossible
  end

(** Like annotatebinding, but takes a (previously annotated) default set to
    be used if one is not implicitly specified in the binding or
    specified in an implicit declaration.

    Raises an error (indirectly) if the set in the binding is ill-formed
*)

and annotateSimpleBindingWithDefault cntxt surrounding_expr default_ty =
  function
      (nm, None) -> 
	begin
	  (** There's a reasonable argument to say that the default_ty
              should always be used, since it's most likely to get the
              input to typecheck.  On the other hand, if you say that n
              ranges over integers unless otherwise specified, and you
              bind it to a boolean, an error seems likely... *)
	  let ty = 
	    match (LR.lookupImplicit cntxt nm) with
		Some(L.DeclTerm(_, implicit_ty)) -> implicit_ty
	      | _                                -> default_ty
	  in let (cntxt, nm) = LR.renameBoundVar cntxt nm
	  in let cntxt' = LR.insertTermVariable cntxt nm ty None
	  in 
	       (cntxt',  (nm, ty) )
	end

    | (nm, Some expr) -> 
	let ty = annotateType cntxt surrounding_expr expr
	in let (cntxt, nm) = LR.renameBoundVar cntxt nm
	in 
	     (* NB:  No checking of binding annotation vs default! *)
	  (LR.insertTermVariable cntxt nm ty None,  (nm, ty) )

(* We explicitly do _not_ rename bound variables in
   annotateTheoryElem, as they will eventually become labels.  Thus, a
   Definition or a Value declaration is not permitted to shadow an
   earlier definition, which can only be an earlier top-level or
   theory-element definition.
*)
and annotateTheoryElem cntxt elem = 
  try
    match elem with
	Definition(nm1, expropt2, expr3) as orig_elem -> 
	  begin
	    match annotateExpr cntxt expr3 with
		ResTerm(trm3, ty3) ->
		  begin
		    (* Definition of a term constant *)
		    match expropt2 with
			None       -> 
			  [ L.Declaration(nm1, L.DeclTerm(Some trm3, ty3)) ]
		      | Some expr2 ->
			  let ty2 = annotateType cntxt (Ident nm1) expr2 
			  in 
			    try 
			      let trm3' = LR.coerce cntxt trm3 ty3 ty2
			      in [ L.Declaration
				     (nm1, L.DeclTerm(Some trm3', ty2)) ]
			    with 
				E.TypeError _ -> 
				  E.tyMismatchError expr3 ty2 ty3 (Ident nm1)
		  end

	      | ResSet(st3, k3) ->
		  begin
		    (* Definition of a set constant *)
		    match expropt2 with
			None       ->
			  [ L.Declaration(nm1, L.DeclSet(Some st3, k3)) ]
		      | Some expr2 ->
			  let k2 = annotateKind cntxt (Ident nm1) expr2
			  in
			    try
			      let reqs = LR.subKind cntxt k3 k2
			      in let _ = if reqs <> [] then
				  (* XXX *)
				  failwith "UNIMPLEMENTED: annotateTheoryElem"
			      in
				   [ L.Declaration(nm1, L.DeclSet(Some st3, k2)) ]
			    with
				E.TypeError _ ->
				  E.kindMismatchError expr3 k2 k3 (Ident nm1)
		  end

	      | ResProp(prp3, pt3) ->
		  begin
		    (* Definition of a propositional constant *)
		    match expropt2 with
			None       -> 
			  [ L.Declaration(nm1, L.DeclProp(Some prp3, pt3)) ]
		      | Some expr2 ->
			  let pt2 = annotateProptype cntxt (Ident nm1) expr2 
			  in
			    try
			      let reqs = LR.subPropType cntxt pt3 pt2
			      in let prp3' = L.maybePAssure reqs prp3
			      in 
				   [ L.Declaration(nm1, 
						  L.DeclProp(Some prp3', pt2)) ]
			    with
				E.TypeError _ ->
				  E.propTypeMismatchError expr3 pt2 pt3 (Ident nm1)
		  end

	      | ResTheory (thry3, tknd3) ->
		  begin
		    (* Definition of a theory *)
		    match expropt2 with
			None       ->
			  [ L.Declaration(nm1, L.DeclTheory(thry3, tknd3)) ]
		      | Some _ ->
			  E.tyGenericError ("A theory definitions must not" ^
					       " have a constraint")
		  end

	      | ResPropType _ | ResKind _ | ResModel _ | ResSentence _ ->
		  E.tyGenericError 
		    ("Invalid right-hand-side in " ^
			string_of_theory_element orig_elem)
	  end

      | Comment c -> [L.Comment c]

      | Include expr -> 
	  begin
	    let badTheory() = 
	      E.tyGenericError ("Theory " ^ string_of_expr expr ^ 
				   "is not includable.")
	    in
	      match annotateTheory cntxt expr(*X*) expr with
		  (thry, L.ModelTheoryKind) ->
		    begin
		      match LR.hnfTheory cntxt thry with
			  L.Theory elems -> elems
			| _ -> badTheory()
		    end
		| _ -> badTheory()
	  end

      | Implicit _ -> raise Impossible (* Implicits were already removed *)

      | Value (sentence_type, values) as orig_elem ->
	  let process res nm = 
	    begin
	      L.Declaration(nm,
			   match res with
			       ResSet(ty, L.KindSet) -> L.DeclTerm(None, ty)
			     | ResPropType pt        -> L.DeclProp(None, pt)
			     | ResKind k             -> L.DeclSet (None, k)
			     | ResTheory (thry, L.ModelTheoryKind) ->
				 L.DeclModel(thry)
			     | ResProp(prp, (L.Prop | L.StableProp)) ->
				 L.DeclSentence([], prp)
			     | ResSentence(mbnds, prp) ->
				 L.DeclSentence(mbnds, prp)
			     | ResSet _ | ResTerm _ | ResProp _ 
			     | ResModel _ | ResTheory _ -> 
				 E.tyGenericError 
				   ("Invalid classifier for " ^ string_of_name nm ^
				       " in " ^ string_of_theory_element orig_elem))
	    end
	  in let rec loop cntxt = function
	      [] -> []
            | (nms,expr)::rest ->
		begin
		  let res = annotateExpr cntxt expr 
	          in let elems = List.map (process res) nms
		  in let cntxt' = LR.updateContextForElems cntxt elems
		  in 
		       elems @ (loop cntxt' rest)
		end
	  in 
	       loop cntxt values

  with
      E.TypeError msgs ->
	E.generalizeError msgs (E.inElemMsg elem)

and annotateTheoryElems cntxt = function
    [] -> (cntxt, [])

  | Implicit(names, expr)::rest ->    (** Eliminated here *)
      let cntxt' = 
	begin
	  match annotateExpr cntxt expr with
	      ResSet(ty, L.KindSet) -> 
		LR.insertImplicits cntxt names (L.DeclTerm(None, ty))
	    | ResKind knd ->
		LR.insertImplicits cntxt names (L.DeclSet(None, knd))
	    | ResTheory (thry, L.ModelTheoryKind) ->
		LR.insertImplicits cntxt names (L.DeclModel thry)
	    | ResPropType pt ->
		LR.insertImplicits cntxt names (L.DeclProp(None, pt))
	    | _ -> E.notWhatsExpectedInError expr "classifier" expr
	end
      in
	annotateTheoryElems cntxt' rest

  | elem :: rest ->
      let    lelems1 = annotateTheoryElem cntxt elem
      in let cntxt'  = LR.updateContextForElems cntxt lelems1
      in let (cntxt_final, lelems2) = annotateTheoryElems cntxt' rest
      in (cntxt_final, lelems1 @ lelems2)
 

and annotateToplevel cntxt = function
    TopComment c -> (cntxt, L.TopComment c)

  | Theorydef(nm, expr) ->
      begin
	let (thry, tknd) = annotateTheory cntxt False(*X*) expr
	in (LR.insertTheoryVariable cntxt nm thry tknd, 
	   L.Theorydef(nm, thry))
      end
	  
  | TopModel (nm, thry) -> 
      let lthry = annotateModelTheory cntxt False(*X*) thry
      in (LR.insertModelVariable cntxt nm lthry,
	 L.TopModel(nm, lthry))

and annotateToplevels cntxt = function
    [] -> (cntxt, [])
  | tl::tls -> 
      let    (cntxt',  tl' ) = annotateToplevel cntxt tl
      in let (cntxt'', tls') = annotateToplevels cntxt' tls
      in (cntxt'', tl'::tls')



