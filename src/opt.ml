(** XXX: Can we avoid expanding out all the type definitions? *)

(********************************************************************)
(** {1 Simplification}                                              *)
(**                                                                 *)
(********************************************************************)

open Name
open Outsyn
open Outsynrules

exception Unimplemented
exception Impossible of string


(** allequalTy : ctx -> ty -> bool

    Check whether the given type is a unit (or void) type, i.e., one in
    which any two terms of the type are equal.
*)
let rec allequalTy ctx ty = 
  match hnfTy ctx ty with
      VoidTy -> true
    | UnitTy -> true
    | TupleTy tys -> List.for_all (allequalTy ctx) tys
    | SumTy [] -> true
    | SumTy [(_,None)] -> true
    | SumTy [(_,Some ty)] -> allequalTy ctx ty
    | _ -> false

(*************************)
(** Equation Elimination *)
(*************************)

(** Some common "overcomplicated" propositions involve unnecessary
    quantification, e.g.,

          exists x:s,  x = t and P(x)
          forall x:s,  ( x = t and P(x) ) => Q(x)
          assure x:s.  x = t and P(x) in Q(x)
 
    which can be simplified to

          P(t)
          P(t) => Q(t)
          assure P(t) in Q(t)

    respectively.
 
    These functions are given the bound variable x and the body R(x) of
    the quantifier, and search R for an equation x = t (or t = x) where
    t is not free in x.  If found, they return Some(t, R'(x)) where
    R'(x) is what is left over from R(x) after you remove the equation. 
    No substitution is done here: R'(x) may contain x free.
    If no such equation is found, the functions return None.


    Note that we are only looking for Equal equality, not NamedPer
    equality.  NamedPer equality would only suffice if the rest of the
    proposition is invariant under choice of representative, and we
    aren't checking for that.
*)


(** findEq: name -> proposition -> (term * proposition) option

     Check for a definition for the given name in the given proposition,
     if it's atomic or a conjunction. 

     Used for simplifying bodies of existentials and assumes.
*)
let rec findEq nm orig_prop =
  let validDefn trm =
    if not(List.mem nm (fvTerm trm)) then
      Some (trm, True)
    else
      None
  in 
    match orig_prop with
      (* Have to be a little careful with how the pattern-matching
	 is structured here, since if orig_prop is a comparison of
	 two variables, either one might be the one we're looking for. *)

      Equal(Id(LN(None,nm')), trm) when nm = nm' -> validDefn trm

    | Equal(trm, Id(LN(None,nm'))) when nm = nm' -> validDefn trm

    | And prps -> 
	begin
	  match findEqs nm prps with
	      None -> None
	    | Some (trm, prps') -> Some (trm, And prps')
	end 
    | _ -> 	  
	None

(** findEqs: name -> proposition list -> (term * proposition) option

    Given a list of propositions, see if one of them contains an
    x = t definition; if so, return t and the list with that equation
    in that proposition removed.  
*)
and findEqs nm = function
    [] -> None
  | p::ps ->
      match findEq nm p with
	  None -> 
	    begin
	      match findEqs nm ps with
	          None -> None
		| Some (trm, ps') -> Some(trm, p :: ps')
	    end
	| Some(trm, p') ->
	    Some(trm, p' :: ps)

(** findEqPremise: name -> proposition -> (term * proposition) option

    Given a name x and a proposition, see if it is an implication whose
    hypothesis provides a definition for x.

    Used for simplifying universally quantified propositions.
*)
and findEqPremise nm = function
    Imply(prp1, prp2) -> 
      begin
	match findEq nm prp1 with
	    None -> 
	      begin
(*	      if not (List.mem nm (fvProp prp1)) then *)
		match findEqPremise nm prp2 with
		    None -> None
		  | Some (trm, prp2') -> Some(trm, Imply(prp1, prp2'))
(*	      else
		None *)
	      end
	  | Some (trm, prp1') -> Some(trm, Imply(prp1', prp2))
      end
  | Forall((nm',ty1),prp2) ->
      begin
	match findEq nm prp2 with
	    None -> None
	  | Some (trm, prp2') ->
	      if not (List.mem nm (fvTerm trm)) then
		Some(trm, Forall((nm',ty1),prp2'))
	      else
		(* Can't pull the definition of the term outside its binding *)
		None
      end
  | _ -> None

(************************************)
(** {2: Polymorphization functions} *)
(***********************************)

let tryPolymorph ctx nm signat =
  match (hnfSignat ctx signat) with
      SignatFunctor((nm1,Signat[Spec(nm2,TySpec None,assns2)]),
		    Signat[Spec(nm3,ValSpec([],ty3),assns3)]) ->
	let nm2' = tyvarize nm2
	in let subst = 
	  insertTy emptysubst (NamedTy(LN(Some(ModulName nm1),nm2)))
	    (NamedTy(LN(None,nm2')))
	in
	  Some(ValSpec([nm2'], substTy subst ty3))
    | _ -> None

    


(*************************************)
(** {2: Main Optimization functions} *)
(*************************************)



(* optTy : ty -> ty
    
   We should probably optimize modules that appear in types, but
   this shouldn't happen often.
 *)
let rec optTy ctx ty = ty

let rec optTyOption ctx = function
    None    -> None
  | Some ty -> Some (optTy ctx ty)

(** optBinds: ctx -> binding list -> binding list

   Nothing to do here either.
*)
let rec optBinds ctx bnds = bnds

(* optTerm ctx e = (t, e')
      where t  is the type of e under ctx
            e' is the optimized version of e
*)       
let rec optTerm ctx orig_term = 
  try
    match orig_term with
        Id (LN(None, nm)) ->
	  (** We maintain a renaming substitution as we go along to make
	      sure that shadowing is eliminated.  The renaming is extended
              whenever we encounter a bound variable; so when we see the
              use of a variable (here), we must apply the renaming. 

              No actual "optimization" occurs.
          *)
	  let nm' = applyTermRenaming ctx nm
	  in let ty = lookupTermVariable ctx nm'
	  in (ty, Id(LN(None,nm')))

      |	Id (LN(Some mdl, nm)) ->
	  begin
            (** We only rename local bound variables; projections from
		modules remain unchanged.
            *)
	    let mdl' = optModul' ctx mdl
	    in
	      match hnfSignat ctx (modulToSignat ctx mdl') with
		  Signat elems ->
		    (findTermvarInElems elems mdl nm, 
		     Id (LN(Some mdl', nm)))
		| _ -> failwith "Opt.optTerm: invalid path"
	  end

      | EmptyTuple -> 
	  (** The unit value is already as simple as possible. *)
	  (UnitTy, EmptyTuple)

      | Dagger -> 
	  (TopTy, Dagger)

      | App(e1,e2) -> 
	  begin
	    (** Optimize the subexpressions, and then see if beta-reduction
		is applicable. *)
	    let (ty1, e1') = optTerm ctx e1
	    in let (ty2, e2') = optTerm ctx e2
	    in match (hnfTy ctx ty1) with
		ArrowTy(_, ty) ->
		  (ty, optReduce ctx (App(e1',e2')))
	      | ty1' -> (print_string "In application ";
			 print_string (Outsyn.string_of_term (App(e1,e2)));
			 print_string " the operator has type ";
			 print_endline (Outsyn.string_of_ty ty1');
			 raise (Impossible "App"))
	  end

      | Lambda((nm1, ty1), trm2) ->
	  (** Optimize the subexpressions, and then see if eta-reduction
	      is applicable *)
	  let (ctx,nm1) = renameBoundTermVar ctx nm1
	  in let ty1' = optTy ctx ty1
	  in let ctx' = insertTermVariable ctx nm1 ty1
	  in let (ty2', trm2') = optTerm ctx' trm2
	  in let ty = ArrowTy(ty1',ty2')
	  in 
	       (ty,  optReduce ctx (Lambda((nm1,ty1'),trm2')))

      | Tuple es -> 
	  (** Optimize the subexpressions. *)
	  let (ts, es') = optTerms ctx es
	  in (TupleTy ts, Tuple es')

      | Proj (n,e) ->
	  (** Optimize the subexpression, and see if the projection
	      can be reduced. *)
	  let (ty, e') = optTerm ctx e
	  in let tys = 
	    match hnfTy ctx ty with
		TupleTy tys -> tys
	      | ty_bad -> (print_string (Outsyn.string_of_ty ty ^ "\n");
			   print_string (Outsyn.string_of_ty ty_bad ^ "\n");
			   print_endline (Outsyn.string_of_term orig_term);
			   raise (Impossible "Proj"))
	  in 
               (List.nth tys n, optReduce ctx (Proj(n,e')))

      | Inj (lbl, None) -> 
	  (** Non-value-carrying injections are as simple as possible. *)
	  (SumTy [(lbl,None)], Inj(lbl, None))

      | Inj (lbl, Some e) ->
	  (** Optimize the subexpression *)
	  let (ty, e') = optTerm ctx e in
	    (SumTy [(lbl,Some ty)], Inj(lbl, Some e'))

      | Case (e, arms) ->
	  (** Optimize the subexpressions, and see if the case can
	      be reduced *)
	  let (ty, e') = optTerm ctx e
	  in let doArm = function
	      (lbl, Some (name2,ty2),  e3) -> 
		let (ctx,name2) = renameBoundTermVar ctx name2
		in let ty2' = optTy ctx ty2 
		in let ctx' = insertTermVariable ctx name2 ty
		in let (ty3, e3') = optTerm ctx' e3
		in (ty3, (lbl, Some (name2, ty2'), e3'))
	    | (lbl, None,  e3) -> 
		let (ty3, e3') = optTerm ctx e3
		in (ty3, (lbl, None, e3'))
	  in let rec doArms = function
	      [] -> raise (Impossible "Case")
	    | [arm] -> let (tyarm, arm') = doArm arm
	      in (tyarm, [arm'])
	    | arm::arms -> let (tyarm, arm') = doArm arm
              in let (tyarms, arms') = doArms arms
	      in (joinTy ctx tyarm tyarms,
		 arm' :: arms')
	  in let (tyarms, arms') = doArms arms
	  in (tyarms, optReduce ctx (Case(e',arms')))

      | Let(name1, term1, term2) ->
	  (** Phase 1: Basic Optimization: optimize subexpressions
	      and see if the let can be reduced *)
	  let (ty1, term1') = optTerm ctx term1
	  in let (ctx', name1) = renameBoundTermVar ctx name1
	  in let ctx' = insertTermVariable ctx' name1 ty1
	  in let (ty2, term2') = optTerm ctx' term2
	  in let trm' = optReduce ctx (Let(name1, term1', term2'))
	  in let trm'' =
	    (** More complicated optimizations *)
	    match trm' with
		Let(name1, Tuple trms, term2) when opTerm name1 term2 ->
		  (** Turn a let of a tuple into a sequence of bindings
		      of the components, if the tuple is never referred
		      to as a whole *)
		  let nms = refreshList (List.map (fun _ -> name1) trms)
		  in let trm'' = nested_let nms trms term2
		  in optTerm' ctx trm'' (* if nothing else, remove shadowing *)
	      | Let(nm1, (Obligation([(nm2,ty2)], prp2, 
				    Id(LN(None,nm2'))) as obprp), trm3) 
		  when nm2 = nm2' ->
		  (** Now that assures start out like indefinite
		      descriptions, one pattern that has cropped up 
		      occasionally is:
		      let y = (assure x:s. phi(x) in x) in trm.
		      When optimizing trm, we should be able to use the
		      fact that phi(y) holds, so we do that here.
                  *)
		  let (ctx',nm1) = renameBoundTermVar ctx nm1
                  in let prp2' = substProp (renaming nm2 nm1) prp2
		  in let ctx' = insertTermVariable ctx' nm1 ty2
		  in let ctx' = insertFact ctx' prp2'
		  in let trm3' = optTerm' ctx' trm3
		  in 
		       optReduce ctx (Let(nm1, obprp, trm3'))
	      | Let(nm1, (Obligation([(nm2,ty2);(nm3,ty3)], prp2, 
				    (Tuple[Id(LN(None,nm2'));
					   Id(LN(None,nm3'))])) as obprp), 
		   trm3)
		  when nm2 = nm2' && nm3 = nm3' && nm2 <> nm3  ->
		  (** Now that assures start out like indefinite
		      descriptions, one pattern that has cropped up 
		      occasionally is:
		      let y = (assure (x,r). phi(x,r) in (x,r) in trm.
		      When optimizing trm, we should be able to use the
		      fact that phi(pi0 y, pi1 y) holds, so we do that here.
                  *)
		  let subst = insertTermvar emptysubst nm2 (Proj(0,Id(LN(None,nm1))))
		  in let subst = insertTermvar subst nm3 (Proj(1,Id(LN(None,nm1))))
                  in let prp2' = substProp subst prp2
		  in let (ctx',nm1) = renameBoundTermVar ctx nm1
		  in let ctx' = insertTermVariable ctx' nm1 (TupleTy[ty2;ty3])
		  in let ctx' = insertFact ctx' prp2'
		  in let trm3' = optTerm' ctx' trm3
		  in 
		       optReduce ctx (Let(nm1, obprp, trm3'))
	      | _ -> trm'
	  in (ty2, trm'')

      | Obligation(bnds, prop, trm) ->
	  (** Part 1: Optimize the subexpressions *)
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (optTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = renameTermBindings ctx bnds'
	  in let prop' = optProp ctx' prop
	    
	  in let ty2, trm' = optTerm ctx' trm

	  (** Part 2: Try to reduce. *)
	  in let doObligation = function
	      ([], True, trm3) -> 
		(** If there are no bindings or obligations (presumably
		    because they were optimized away), then drop the
		    obligation altogether. *)
		trm3

	    | ([(nm,_)] as bnds1, prp2, trm3) ->
		begin
		  if (string_of_name nm = "y'" && 
		      string_of_term trm3 = "y") then failwith "XXXXX";
		  (** The one-binding case.  Check for an equation
		      in prp2 that tells us what term nm must be. *)
		  match findEq nm prp2 with 
		      None -> Obligation(bnds1, prp2, trm3)
		    | Some (trm,prp2') ->
			optReduce ctx'
			  (Let(nm, trm, Obligation([], prp2', trm3)))
		end

	    | (bnds1, prp2, trm3) -> Obligation(bnds1, prp2, trm3)

	  in 
	       (ty2, doObligation (bnds'', prop', trm'))

      | PolyInst _ ->
	  failwith "Opt.opTerm:  unexpected PolyInst"

  with e ->
    (** If any exception is raised then either there's a bug in the
	optimizer or the input was ill-formed.  Make sure we can
	figure out where any exception came from. *)
    (print_endline ("\n\n...in " ^ string_of_term orig_term);
     raise e)

(** optReduce     : ctx -> term        -> term
    optReduceProp : ctx -> proposition -> proposition

    Try to head-reduce the term or proposition.  If anything changes,
    (recursively) thoroughly optimize the result.
*)
and optReduce ctx trm =
  try
    let trm' = reduce trm
    in 
      if trm <> trm' then
	let (_,trm'') = optTerm ctx trm' in trm''
      else
	trm'
  with e ->
    (print_endline ("\n\n...in " ^ string_of_term trm);
     raise e)


and optReduceProp ctx prp =
  try
    let prp' = reduceProp prp
    in 
      if prp <> prp' then
	optProp ctx prp'
      else
	prp'
  with e ->
    (print_endline ("\n\n...in " ^ string_of_proposition prp);
     raise e)
      
(** optTerms: ctx -> term list -> ty list * term list

    Apply optTerm to a list of terms, and return the respective types
    and terms.
*)
and optTerms ctx trms = 
  List.split (List.map (optTerm ctx) trms)


(** optTerm' : ctx -> term      -> term
    optTerms': ctx -> term list -> term list

    Exactly like optTerm and optTerms but don't return the type.
*)
and optTerm' ctx trm =
  let (_,trm') = optTerm ctx trm 
  in trm'      

and optTerms' ctx trms =
  let (_, trms') = optTerms ctx trms 
  in trms'

(** optProp: ctx -> proposition -> proposition

    Optimize the given proposition.
*)
and optProp ctx orig_prp = 
  try
    let result_prop = 
      match orig_prp with
	  True                      -> True
	| False                     -> False
	| PApp(PApp(NamedPer(n,lst),t1),t2) when optTerm ctx t1 = optTerm ctx t2 ->
	    (** The comparision   trm =set= trm   can be simplified
                to   trm : ||set||. *)
	    optProp ctx (PApp(NamedTotal(n,lst), t1))
	| NamedTotal(n, lst)         -> NamedTotal(n, optTerms' ctx lst)
	| NamedPer  (n, lst)         -> NamedPer  (n, optTerms' ctx lst)
	| NamedProp (n, Dagger, lst) -> NamedProp (n, Dagger, optTerms' ctx lst)
	| NamedProp (n, t, lst)      -> NamedProp (n, optTerm' ctx t, 
						  optTerms' ctx lst)

	    
	| Equal(e1, e2) -> 
	    begin
	      (** Optimize subexpressions *)
	      let (ty1,e1') = optTerm ctx e1
	      in let (ty2,e2') = optTerm ctx e2
	      in let ty = joinTy ctx ty1 ty2
	      in
		   if (e1 = e2) then
		     (** Both sides are exactly the same; simplify to True *)
		     True
		   else if (allequalTy ctx ty) then
		     (** The type ensures that any equality must be true. *)
		     True
		   else
		     match (hnfTy ctx ty1) with
			 SumTy _ ->
			   begin
			     (** Equality of two injections with
			 	 different labels is trivially false.
			 	 Two injections with the same label
			 	 can be reduced to equality of the
			 	 carried values. *)
			     match e1', e2' with
				 Inj (lbl1, None), Inj (lbl2, None) ->
				   if lbl1 = lbl2 then True else False
			       | Inj (lbl1, Some t1), Inj (lbl2, Some t2) ->
				   if lbl1 = lbl2 then
				     optProp ctx (Equal (t1, t2))
				   else
				     False
			       | Inj (_, None), Inj (_, Some _)
			       | Inj (_, Some _), Inj (_, None) -> False
			       | _ -> Equal (e1', e2')
			   end
		       | _ -> Equal(e1',e2') 
	    end

	| And ps ->
	    (** Optimize all the subexpressions, dropping any Trues,
		and replacing the whole thing with False if any term
		is known to be false.  We also remember the truth of
		each term when optimizing the remaining terms; in
		addition to the normal benefits, this has the nice
		side-effect of deleting exact duplicates. 
	        Also, if we see two Implies that are converses
	        of each other, combine them into a single Iff. *)
	    let rec extendRaccum p = function
		[] -> [p]
	      | r::rs ->
		  begin
		    match (p,r) with
		      (Imply(q1,q2), Imply(q1',q2')) when (q1=q2') && (q2=q1') ->
			Iff(q1,q2) :: rs
		    | _ -> p :: r :: rs
		  end
		
	    in let rec loop ctx = function
              | ([], []) -> True
	      | ([], raccum) -> And (List.rev raccum)
	      | (p::ps, raccum) -> 
		  (match optProp ctx p with
		      True -> loop ctx (ps,raccum)
		    | False -> False
		    | p' -> loop (insertFact ctx p') 
			      (ps, extendRaccum p' raccum))
	    in loop ctx (ps,[])

	| Cor ps ->
	    (** Optimize all the subexpressions, dropping any Falses,
		and replacing the whole thing with True if any term
		is known to be true.  

		`Someday we might want to implement duplicate removal.
	    *)
	    let rec loop = function
              | ([], []) -> False
	      |  ([], raccum) -> Cor (List.rev raccum)
	      | (p::ps, raccum) -> 
		  (match optProp ctx p with
		      True -> True
		    | False -> loop(ps,raccum)
		    | p' -> loop(ps, p' :: raccum))
	    in loop(ps,[])

	| Imply (p1, p2) -> 
	    (** Optimize subexpressions, using the truth of the
		premise in optimizing the conclusion.  This has the
		nice side-effect of automatically catching the P => P
		case for us (by first turning p2' into True, and then
		turning the whole implication into True below *)
	    let p1' = optProp ctx p1
	    in let p2' =  optProp (insertFact ctx p1') p2
	    in
		 (** Try some simple optimizations *)
		 (match (p1',p2') with
		     (True,  _  )   -> p2'
		   | (False, _    ) -> True
		   | (_,     True ) -> True
		   | (_,   False)   -> Not p1'
		   | _              -> Imply(p1', p2'))

	| Iff (p1, p2) -> 
	    (match (optProp ctx p1, optProp ctx p2) with
		(p1',   p2'  ) when p1' = p2' -> True
	      | (True,  p2'  ) -> p2'
	      | (False, p2'  ) -> Not p2'
	      | (p1',   True ) -> p1'
	      | (p1',   False) -> Not p1'
	      | (p1',   p2'  ) -> Iff(p1', p2'))

	| Not p -> (match optProp ctx p with
	      True  -> False
	    | False -> True
	    | Not (Not p') -> p'
	    | p'    -> Not p')
	    
	| Forall((n,ty), p) ->
	    let (ctx, n) = renameBoundTermVar ctx n
            in let p' = optProp (insertTermVariable ctx n ty) p
	    in let doForall(nm1,ty1,prp2) =
	      begin
		match findEqPremise nm1 prp2 with
		    None -> Forall((nm1,ty1),prp2)
		  | Some(trm,prp2') -> 
		      optReduceProp ctx (PLet(n,trm,prp2'))
	      end
	    in (match (optTy ctx ty, p') with
		(_, True) -> True
	      | (UnitTy, _) -> optReduceProp ctx (PLet(n,EmptyTuple,p'))
	      | (VoidTy, _) -> True
	      | (NamedTy n1, Imply (PApp (NamedTotal (n2, []), Id n3), p'')) ->
		  if (n3 = LN(None,n)) && 
		    (hnfTy ctx (NamedTy n1) = hnfTy ctx (NamedTy n2)) then
		    ForallTotal((n, n2), p'')
		  else
		    doForall(n, NamedTy n1, p')
	      | (ty',_) -> doForall(n, ty', p'))
	      
	| ForallTotal((n,ln),p) ->
	    let (ctx, n) = renameBoundTermVar ctx n
	    in let doForallTotal(nm1,ln1,prp2) =
	      begin
		match findEqPremise nm1 prp2 with
		    None -> ForallTotal((nm1,ln1),prp2)
		  | Some(trm,prp2') -> 
		      optReduceProp ctx (PLet(n,trm,prp2'))
	      end
	    in let ctx' = insertTermVariable ctx n (NamedTy ln)
	    in let ctx'' = ctx'  (* XXX Should insert fact that n is total! *)
	    in let p' = optProp ctx'' p
	    in (match (optTy ctx (NamedTy ln), p') with
		(_, True) -> True
	      | (UnitTy, _) -> optReduceProp ctx (PLet(n,EmptyTuple,p'))
	      | (VoidTy, _) -> True
	      | (NamedTy ln',_) -> doForallTotal(n, ln', p')
	      | (_, _) -> failwith "XXX Andrej messed up here.")
	      
	| Cexists ((n, ty), p) ->
	    let (ctx, n) = renameBoundTermVar ctx n
	    in let doExists(nm1,ty1,prp2) =
	      begin
		match findEq nm1 prp2 with
		    None -> Cexists((nm1,ty1),prp2)
		  | Some(trm,prp2') -> 
		      optReduceProp ctx (PLet(n,trm,prp2'))
	      end
	    in let p' = optProp (insertTermVariable ctx n ty) p in
		 (match optTy ctx ty, p' with
		     (_, False) -> False
		   | (VoidTy, _) -> False
		   | (UnitTy, _) -> optReduceProp ctx (PLet(n,EmptyTuple,p'))
		   | (ty', _) -> doExists(n, ty', p'))

	| PObligation (bnds, p, q) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (optTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = renameTermBindings ctx bnds'
	  in let p' = optProp ctx' p

	  in let ctx'' = if bnds = [] then insertFact ctx' p else ctx'
	  in let q' = optProp ctx'' q
	    in 
		 begin
		   match (bnds'', p') with
		       ([], True) -> q'
		     | _ -> PObligation(bnds'', p', q')
		 end

	| PMLambda ((n, ms), p) ->
	    let (ctx, n) = renameBoundTermVar ctx n
	    in let ms' = optModest ctx ms in
	    let p' = optProp (insertTermVariable ctx n ms.ty) p
	    in let pre = (PMLambda ((n,ms'), p'))
	    in optReduceProp ctx pre
	      
	| PMApp (p, t) -> 
	    optReduceProp ctx (PMApp (optProp ctx p, optTerm' ctx t))

	| PLambda ((n,ty), p) ->
	    let (ctx, n) = renameBoundTermVar ctx n
	    in let p' = optProp (insertTermVariable ctx n ty) p
	    in let ty' = optTy ctx ty
	    in
		 optReduceProp ctx (PLambda((n,ty'), p'))
		   
	| PApp (p, t) -> 
	    let p' = optProp ctx p
	    in let t' = optTerm' ctx t
	    in
		 optReduceProp ctx (PApp(p', t'))
		   
	| PCase (e1, e2, arms) ->
	    let doBind ctx0 = function
		None -> None, ctx0
	      | Some (nm, ty) ->
		  let (ctx0, nm) = renameBoundTermVar ctx0 nm
		  in let ty' = optTy ctx ty
		  in 
		       (Some (nm, ty'), insertTermVariable ctx0 nm ty)
	    in
	    let doArm (lbl, bnd1, bnd2, p) =
	      let bnd1', ctx1 = doBind ctx  bnd1 in
	      let bnd2', ctx2 = doBind ctx1 bnd2 in
	      let p' = optProp ctx2 p in
		(lbl, bnd1', bnd2', p')
	    in
	      optReduceProp ctx
		(PCase (optTerm' ctx e1, optTerm' ctx e2, List.map doArm arms))

	| PLet(nm, trm1, prp2) ->

	    let (ty1, trm1') = optTerm ctx trm1
	    in let (ctx', nm) = renameBoundTermVar ctx nm
	    in let ctx' = insertTermVariable ctx' nm ty1
	    in let prp2' = optProp ctx' prp2
	    in let prp' = optReduceProp ctx (PLet(nm, trm1', prp2'))
	    in let prp'' = 
	      match prp' with
		  PLet(name1, Tuple trms, prp2) when opProp name1 prp2 ->
		    (* Turn a let of a tuple into a sequence of lets, if
		       the tuple is never referred to as a whole *)
		    let nms = refreshList (List.map (fun _ -> name1) trms)
		    in let subst = 
		      insertTermvar emptysubst name1 (Tuple (List.map id nms))
		    in let prp2' = substProp subst prp2
		    in let prp'' = nested_plet nms trms prp2'
		    in optProp ctx prp''
		| PLet(nm1, (Obligation([(nm2,ty2)], prp2, 
				       Id(LN(None,nm2'))) as obprp), prp3) 
		    when nm2 = nm2' ->
		    (** Now that assures start out like indefinite
			descriptions, one pattern that has cropped up 
			occasionally is:
		        let y = (assure x:s. phi(x) in x) in prp3.
			When optimizing prp3, we should be able to use the
			fact that phi(y) holds, so we do that here.
                    *)
		    let (ctx',nm1) = renameBoundTermVar ctx nm1
                    in let prp2' = substProp (renaming nm2 nm1) prp2
		    in let ctx' = insertTermVariable ctx' nm1 ty2
		    in let ctx' = insertFact ctx' prp2'
		    in let prp3' = optProp ctx' prp3
		    in 
			 optReduceProp ctx (PLet(nm1, obprp, prp3'))

		| PLet(nm1, (Obligation([(nm2,ty2);(nm3,ty3)], prp2, 
				       (Tuple[Id(LN(None,nm2'));
					      Id(LN(None,nm3'))])) as obprp), 
		      prp3)
		    when nm2 = nm2' && nm3 = nm3' && nm2 <> nm3 ->
		    (** Now that assures start out like indefinite
			descriptions, one pattern that has cropped up 
			occasionally is:
		        let y = (assure (x,r). phi(x,r) in (x,r) in trm.
			When optimizing trm, we should be able to use the
			fact that phi(pi0 y, pi1 y) holds, so we do that here.
                    *)
		    let subst = insertTermvar emptysubst nm2 (Proj(0,Id(LN(None,nm1))))
		    in let subst = insertTermvar subst nm3 (Proj(1,Id(LN(None,nm1))))
                    in let prp2' = substProp subst prp2
		    in let (ctx',nm1) = renameBoundTermVar ctx nm1
		    in let ctx' = insertTermVariable ctx' nm1 (TupleTy[ty2;ty3])
		    in let ctx' = insertFact ctx' prp2'
		    in let prp3' = optProp ctx' prp3
		    in 
			 optReduceProp ctx (PLet(nm1, obprp, prp3'))
		| _ -> prp'
	    in 
		 prp''   
    in
      (*
	print_string ">>> ";
	print_endline (string_of_proposition orig_prp);
	print_string "<<< ";
	print_endline (string_of_proposition result_prop);
      *)	
      if (checkFact ctx result_prop) then
	begin
	  (*	  print_endline "--> True";  *)
	  True
	end
      else
	result_prop
  with e ->
    (print_endline ("\n\n...in " ^
		       string_of_proposition orig_prp);
     raise e)

and optAssertion ctx (name, annots, prop) = 
  if List.mem Annot_NoOpt annots then
    (name, annots, prop)
  else
    let prop' = optProp ctx prop
    in 
      
    let prop'' = if (!Flags.do_hoist) then
	let (obs, prp') = hoistProp prop' in
	  optProp ctx (foldPObligation obs prp') 
      else
	prop'
    in
      (name, annots, prop'')
      
and optModest ctx {ty=t; tot=p; per=q} =
  {ty = optTy ctx t;
   tot = optProp ctx p;
   per = optProp ctx q}

and optElems ctx orig_elems = 
(*  try *)
    match orig_elems with
	[] -> ([], ctx)
      |  Spec(name, ValSpec (tyvars,ty), assertions) :: rest ->
	   let ty'  = optTy ctx ty in
	   let ctx' = insertTermVariable ctx name ty' in
	   let assertions' = List.map (optAssertion ctx') assertions
	   in let ctx' = 
	     insertFacts ctx' (List.map (fun (_,_,p)->p) assertions')
	   in let (rest', ctx'') = optElems ctx' rest in
		(Spec (name, ValSpec (tyvars,ty'), assertions') :: rest', 
		ctx'')
		  
      |  Assertion assertion  ::  rest ->
	   let assertion' = optAssertion ctx assertion in
	   let (rest', ctx') = optElems ctx rest in
	     (Assertion assertion' :: rest'), ctx'
(*
      |  Spec(name, ModulSpec 
	   (SignatFunctor((nm1,Signat[Spec(nm2,TySpec None,assns2)]),
			  Signat[Spec(nm3,ValSpec([],ty3),assns3)])),
	     assns1) ->
	   (* XXX What to do with the assertions? *)
	   Spec(name, 
*)	        

      |  Spec(name, ModulSpec signat, assertions) :: rest -> 
	   let signat' = optSignat ctx signat
	   in let ctx' = insertModulVariable ctx name signat'
	   in let assertions' = List.map (optAssertion ctx') assertions
	   in let ctx'' = 
	     insertFacts ctx' (List.map (fun (_,_,p)->p) assertions')
	   in let (rest', ctx''') = optElems ctx'' rest 
	   in let spec' = Spec(name, ModulSpec signat', assertions')
	   in 
	      spec' :: rest', ctx'''
(*
	   in begin
	       match tryPolymorph ctx name signat' with
		   None -> 
		 | Some decl' -> Spec(uncapitalize name, 
				     decl', assertions')::rest', ctx'''
	     end
*)

      |  Spec(nm, TySpec None, assertions) :: rest -> 
	   let ctx' = insertTypeVariable ctx nm None
	   in let assertions' = List.map (optAssertion ctx') assertions 
	   in let ctx'' = 
	     insertFacts ctx' (List.map (fun (_,_,p)->p) assertions')
	   in let rest', ctx''' = optElems ctx'' rest 
	   in
		(Spec (nm, TySpec None, assertions') :: rest'), ctx'''

      |  Spec(nm, TySpec (Some ty), assertions) :: rest ->
	   let ty' = optTy ctx ty 
	   in let ctx' = insertTypeVariable ctx nm (Some ty) 
	   in let assertions' = List.map (optAssertion ctx') assertions 
	   in let ctx'' = 
	     insertFacts ctx' (List.map (fun (_,_,p)->p) assertions')
	   in let rest', ctx''' = optElems ctx'' rest 
	   in
	     (Spec(nm, TySpec(Some ty'), assertions') :: rest', 
	     ctx''')

      | Spec(nm, SignatSpec sg, assertions) :: rest ->
	  let sg' = optSignat ctx sg
	  in let ctx' = insertSignatVariable ctx nm sg
	  in let assertions' = List.map (optAssertion ctx') assertions
	  in let ctx'' = 
	    insertFacts ctx' (List.map (fun (_,_,p)->p) assertions')
	  in let (rest', ctx''') = optElems ctx'' rest 
	  in (Spec(nm, SignatSpec sg', assertions') :: rest',
	     ctx''')

      |  Comment cmmnt :: rest -> 
	   let rest', ctx' = optElems ctx rest in
	     (Comment cmmnt :: rest', ctx')
(*  with e ->
    (print_endline ("\n\n...in " ^
		       (String.concat "\n" (List.map string_of_spec orig_elems)));
     raise e)
*)

and optSignat ctx = function
    SignatName s -> SignatName s
  | Signat body -> 
      let body', ctx' = optElems ctx body in
	Signat body'
  | SignatFunctor(arg, body) ->
      let    ( (mdlnm, _) as arg', ctx'  ) = optStructBinding ctx arg
      in let body' = optSignat ctx' body
      in SignatFunctor ( arg', body' )
  | SignatApp(sg1,mdl) ->
      let sg1' = optSignat ctx sg1
      in let mdl' = optModul' ctx mdl
      in SignatApp(sg1', mdl')
  | SignatProj(mdl, nm) ->
      let mdl' = optModul' ctx mdl
      in SignatProj(mdl',nm)
	     
and optStructBinding ctx (m, signat) =
  let signat' = optSignat ctx signat in
    ( (m, signat'), insertModulVariable ctx m signat')

and optStructBindings ctx = function
    [] -> [], ctx
  | (m, signat) :: bnd ->
      let signat' = optSignat ctx signat in
      let bnd', ctx'' = optStructBindings ctx bnd in
	( (m, signat') :: bnd',
	insertModulVariable ctx'' m signat')

and optModul' ctx orig_mdl = 
  match orig_mdl with
      ModulName nm -> orig_mdl
    | ModulProj (mdl, nm) ->  
	ModulProj(optModul' ctx mdl, nm)
    | ModulApp (mdl1, mdl2) -> 
	ModulApp(optModul' ctx mdl1, optModul' ctx mdl2)
    | ModulStruct defs -> ModulStruct (optDefs ctx defs)

and optDefs ctx = function
    [] -> []
  | DefTerm(nm, ty, trm) :: rest-> 
      let ty' = optTy ctx ty
      in let trm' = optTerm' ctx trm
      in let ctx' = insertTermVariable ctx nm ty'
      in DefTerm(nm,ty',trm') :: optDefs ctx' rest
  | DefType(nm, ty) :: rest-> 
      let ty' = optTy ctx ty
      in let ctx' = insertTypeVariable ctx nm (Some ty')
      in DefType(nm,ty') :: optDefs ctx' rest
  | DefModul(nm, sg, mdl) :: rest-> 
      let sg' = optSignat ctx sg
      in let mdl' = optModul' ctx mdl
      in let ctx' = insertModulVariable ctx nm sg'
      in DefModul(nm,sg',mdl') :: optDefs ctx' rest
  | DefSignat(nm, sg) :: rest-> 
      let sg' = optSignat ctx sg
      in let ctx' = insertSignatVariable ctx nm sg'
      in DefSignat(nm,sg') :: optDefs ctx' rest

let optToplevels ctx elems =
  if !Flags.do_thin && !Flags.do_opt then 
    optElems ctx elems 
  else 
    (if !Flags.do_opt then
	(print_endline "WARNING:  ";
	 print_endline "Optimization skipped (it requires thinning)");
    (elems,ctx))
   
