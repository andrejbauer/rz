
(********************************************************************)
(** {1 Simplification}                                              *)
(**                                                                 *)
(** Invariant:  the optimization functions always preserve          *)
(** type (unlike thinning).                                         *)
(********************************************************************)

open Name
open Outsyn
open Outsynrules

(** allequalTy : ctx -> ty -> bool

    Check whether the given type is has the property that 
    any two terms of the type are equal.  (i.e., all types
    isomorphic to Unit or Void).
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

    The following functions are given the bound variable x and the
    body R(x) of the quantifier, and search R for an equation x = t or
    t = x where t is not free in x.  If found, they return Some(t,
    R'(x)) where R'(x) is what is left over from R(x) after you remove
    the equation.  No substitution is done here: R'(x) may contain x
    free.  If no such equation is found, the functions return None.


    Note that we are only looking for Equal equality, not NamedPer
    equality.  NamedPer equality would only suffice if the rest of the
    proposition is invariant under choice of representative, and we
    don't (yet) check for that.
*)


(** findEq: name -> proposition -> (term * proposition) option

     Check for a definition for the given name in the given proposition,
     if it's atomic or a conjunction. 

     Used for bodies of existentials, bodies of assumes, and
     premises of implications.
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
    hypothesis provides a definition for x (i.e., contains a top-level 
    proposition x=e where x is not free in x).

    Used for bodies of universally quantified propositions.
*)
and findEqPremise nm = function
    Imply(prp1, prp2) -> 
      begin
	match findEq nm prp1 with
	    None -> 
	      begin
		match findEqPremise nm prp2 with
		    None -> None
		  | Some (trm, prp2') -> Some(trm, Imply(prp1, prp2'))
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

(* Collects 
      - defined type variables
      - value specifications
      - predicate specifications
      - assertions
   from a list of signature elements.

   Returns None if the parameter is "too complex" (e.g., higher-order)
   to be turned into arguments of a polymorphic function; otherwise
   returns Some and the 4 lists.
*)
let rec extractPolyInfo = function
    [] -> Some ([], [], [], [])
  | first::rest ->
      match extractPolyInfo rest with
	  None -> None
	| Some (tynames, vals, prps, assns_rest) ->
	    match first with
		Spec(nm, TySpec None, assns) ->
		  Some (nm::tynames, vals, prps, assns @ assns_rest)
	      | Spec(nm, ValSpec([], ty), assns)  ->
		  Some (tynames, (nm,ty)::vals, prps, assns @ assns_rest)
	      | Assertion asn ->
		  Some (tynames, vals, prps, asn :: assns_rest)
	      | Spec(nm, PropSpec pt, assns) ->
		  Some (tynames, vals, (nm,pt)::prps, assns @ assns_rest)
	      | _ -> None


let tryPolymorph ctx nm signat =
  match (hnfSignat ctx signat) with
    SignatFunctor((nm1,Signat argElems),
		  Signat[Spec(nm3,ValSpec([],ty3),assns3)]) ->
      begin
	match extractPolyInfo argElems with
	  Some (tynames, vals, prps, ([] as argassns)) ->
	    let tyvars =
	      (* Functor's type parameters but with a leading ' character *)
	      List.map tyvarize tynames
		
	    in let arg_subst = 
	      (* Mapping from t -> 't, for type parameters *)
	      renamingList tynames tyvars
		
	    in let (argnames,argtypes) = 
	      (* Functor's term arguments and their types *)
	      List.split vals
	    in let argtypes' = 
	      (* New term arguments should refer to 't, not t *)
	      List.map (substTy arg_subst) argtypes

	    in let argassns' =
	      (* Assertions taken from the argument should use 't, not t *)
	      List.map (substAssertion arg_subst) argassns
		
	    in let (argprpnames, argpts) = 
	      (* Functor's predicate arguments and their proptypes *)
	      List.split prps
	    in let argpts' =
	      (* We will quantify over propositions mentioned in the
		 functor argument; these also must refer to 't, not t *)
	      List.map (substProptype arg_subst) argpts
		
	    in let resSubstTyIn nm  = LN(Some(ModulName nm1),nm)
	    in let resSubstTyOut tv = (NamedTy(LN(None,tv)))
	    in let res_subst_ty = 
	      (* Mapping from nm1.foo -> 'foo, i.e., type parameters *)
	      List.fold_left2 insertTyLN emptysubst
		(List.map resSubstTyIn tynames)
		(List.map resSubstTyOut tyvars)
		
	    in let resSubstTermIn nm = LN(Some(ModulName nm1), nm)
	    in let resSubstTermOut nm = id nm
	    in let res_subst_term =
	      (* Mapping from nm1.bar -> bar, i.e, term parameters *)
	      List.fold_left2 insertTermLN emptysubst
		(List.map resSubstTermIn argnames)
		(List.map resSubstTermOut argnames)

	    in let res_subst_term =
	      (* EXTEND term mapping with nm1.p -> p, i.e, prop parameters *)
	      List.fold_left2 insertPropLN res_subst_term (* extending subst!*)
		(List.map resSubstTermIn argprpnames)
		(List.map (fun n -> LN(None,n)) argprpnames)

(*		
	    in let _ = 
	      (print_endline "\nres_subst_ty:";
	       display_subst res_subst_ty;
	       print_endline "\nres_subst_term:";
	       display_subst res_subst_term)
*)
	    in let final_ty =
	      (* Type of the final polymorphic value [without any
		 type foralls] *)
	      nested_arrowty argtypes' (substTy res_subst_ty ty3)


	    in let updateResAssertion asn =
   	      (* XXX Something's not quite right here --- there
   		 should be an implication where the And of the argument
   		 assertions implies the result assertion. 

		 So, this whole optimization has been disabled if
		 argassns is non-empty.
	       *)
	      let aprop' = substProp res_subst_term asn.aprop
	      in let aprop'' = substProp res_subst_ty aprop'
	      in let apbnds' = 
		(List.combine argprpnames argpts') @
		(fst (substPBnds res_subst_term asn.apbnds))
	      in
	      {alabel = asn.alabel;
	       atyvars = tyvars @ asn.atyvars;
	       apbnds = apbnds';
	       aannots = asn.aannots;
	       aprop = nested_forall (List.combine argnames argtypes') aprop''}
		
	    in let assns3' =
	      List.map updateResAssertion assns3
	    in
	    Some(Spec(uncapitalize nm3,
		      ValSpec(tyvars, final_ty), 
		      argassns' @ assns3'))
	  | _ -> None
      end
  | _ -> None

    


(*************************************)
(** {2: Main Optimization functions} *)
(*************************************)

(* optTy : ty -> ty
    
   We should probably optimize the modules that appear in types, but
   this shouldn't happen often.
 *)
let rec optTy ctx ty = ty

let rec optSimpleTy ctx sty = sty

let rec optTyOption ctx = function
    None    -> None
  | Some ty -> Some (optTy ctx ty)

(**
   optBnd : context -> binding      -> context * binding
   optBnds: context -> binding list -> context * binding list

   Renames and adds the (new) bound term variables to the context.
   Also optimizes the types.
*)
let rec optBnd ctx (nm,ty) = 
  let ty' = optTy ctx ty
  in let ctx', nm' = renameBoundTermVar ctx nm
  in let ctx' = insertTermVariable ctx' nm' ty'
  in (ctx', (nm',ty'))

and optBnds ctx bnds =
  mapWithAccum optBnd ctx bnds


(**
   optModestBnd : context -> (name*modest)      -> context * (name*modest)
   optModestBnds: context -> (name*modest) list -> context * (name*modest) list

   Renames and adds the (new) bound term variables to the context.
   Also optimizes the modest sets.
*)
and optModestBnd ctx (nm, mset) =
  let mset' = optModest ctx mset
  in let ctx', nm' = renameBoundTermVar ctx nm
  in (ctx', (nm', mset'))

and optModestBnds ctx modestbnds =
  mapWithAccum optModestBnd ctx modestbnds

(**
   optPBnd : context -> (name*proptype)      -> context * (name*proptype)
   optPBnds: context -> (name*proptype) list -> context * (name*proptype) list

   Renames and adds the (new) bound propositional variables to the context.
   Also optimizes the proposition-types.
*)
and optPBnd ctx (nm, pt) =
  let pt' = optPt ctx pt
  in let ctx', nm' = renameBoundPropVar ctx nm
  in (ctx', (nm', pt'))

and optPBnds ctx pbnds =
  mapWithAccum optPBnd ctx pbnds

(**
   optPt : ctx -> proptype -> proptype

   Optimization function for proposition-types.
 *)

and optPt ctx = function
    Prop -> Prop
  | PropArrow(ty, pt) ->
      let ty' = optTy ctx ty
      in let pt' = optPt ctx pt
      in PropArrow(ty', pt')

(* optTerm ctx e = (t, e')
      where t  is the type of e under ctx
            e' is the optimized version of e
*)       
and optTerm ctx orig_term = 
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
			 failwith "Opt.optTerm: App")
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
			   failwith "Opt.optTerm: Proj")
	  in 
               (List.nth tys n, reduce (Proj(n,e')))

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
	  in let doArm (pat, e3) =
	    let (ctx',pat') = optPattern ctx pat
	    in let ctx'' = insertPattern ctx' pat'
	    in let (ty3, e3') = optTerm ctx'' e3
	    in (ty3, (pat', e3'))
	  in let rec doArms = function
	      [] -> failwith "Opt.optTerm: Case: doArms"
	    | [arm] -> let (tyarm, arm') = doArm arm
	      in (tyarm, [arm'])
	    | arm::arms -> let (tyarm, arm') = doArm arm
              in let (tyarms, arms') = doArms arms
	      in (joinTy ctx tyarm tyarms,
		 arm' :: arms')
	  in let (tyarms, arms') = doArms arms
	  in (tyarms, optReduce ctx (Case(e',arms')))

      | Let(pat1, term1, term2) ->
	  (** Phase 1: Basic Optimization: optimize subexpressions
	      and see if the let can be reduced *)
	  let (ty1, term1') = optTerm ctx term1
	  in let (ctx', pat1') = optPattern ctx pat1
	  in let ctx' = insertTermVariableLet ctx' pat1' ty1
	  in let (ty2, term2') = optTerm ctx' term2
	  in let trm' = optReduce ctx (Let(pat1', term1', term2'))
	  in let trm'' =
	    (** More complicated optimizations *)
	    match trm' with
		Let(TuplePat pats, Tuple trms, term2) ->
		  (** Turn a let of a tuple into a sequence of bindings
		      of the components, if the tuple is never referred
		      to as a whole *)
		  let trm'' = nested_let' pats trms term2
		  in optTerm' ctx trm'' 
	      | Let(VarPat nm1, (Obligation([(nm2,ty2)], prp2, 
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
		       optReduce ctx (Let(VarPat nm1, obprp, trm3'))
	      | Let(VarPat nm1, (Obligation([(nm2,ty2);(nm3,ty3)], prp2, 
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
		       optReduce ctx (Let(VarPat nm1, obprp, trm3'))
	      | Let(VarPat nm1, trm2, trm3) ->
		  begin
		    match hnfTy ctx (typeOf ctx trm2) with
		      TupleTy tys ->
			let nUses = 
			  countTerm (occurrencesOfTermName nm1) trm3
			in let nProjs =
			  countTerm (occurrencesOfNameInProj nm1) trm3
			in
			  if nProjs >= max 1 (nUses - 2) then
			  let nms = refreshList 
			      (List.map (fun _ -> nm1) tys)
			  in let pat = 
			    TuplePat(List.map (fun n -> VarPat n) nms)
			  in 
			  optTerm' ctx
			    (Let(pat, trm2,
				 substTerm 
				   (insertTermvar emptysubst nm1
				      (Tuple(List.map id nms))) trm3))
			else
			  trm'
		    | _ -> trm'
		  end
	      | _ -> trm'

	  in (ty2, trm'')

      | Obligation(bnds, prop, trm) ->
	  (** Part 1: Optimize the subexpressions *)
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (optTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = optBnds ctx bnds'
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
		  (** The one-binding case.  Check for an equation
		      in prp2 that tells us what term nm must be. *)
		  match findEq nm prp2 with 
		      None -> Obligation(bnds1, prp2, trm3)
		    | Some (trm,prp2') ->
			optReduce ctx'
			  (Let(VarPat nm, trm, Obligation([], prp2', trm3)))
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

and optPattern ctx pat = 
  try
    match pat with
      WildPat -> (ctx, pat)
    | VarPat nm -> (ctx, pat)
    | TuplePat pats ->
	let (ctx', pats') = optPatterns ctx pats
	in (ctx', TuplePat pats')
    | ConstrPat(_, None) -> (ctx, pat)
    | ConstrPat(lbl, Some (nm,ty)) ->
	let (ctx', nm') = renameBoundTermVar ctx nm
	in (ctx', ConstrPat(lbl, Some(nm', optTy ctx' ty)))
  with e ->
    (print_endline ("\n\n...in " ^ string_of_pat pat);
     raise e)


and optPatterns ctx = function
    [] -> (ctx, [])
  | pat::pats ->
      let (ctx', pat') = optPattern ctx pat
      in let (ctx'', pats') = optPatterns ctx' pats
      in (ctx'', pat'::pats')


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
	    optProp ctx (PApp(NamedSupport(n,lst), t1))
	| SimpleSupport sty          -> SimpleSupport (optSimpleTy ctx sty)
	| NamedSupport(n, [])        -> SimpleSupport (SNamedTy n)
	| NamedSupport(n, lst)       -> NamedSupport (n, optTerms' ctx lst)
	| NamedPer  (n, lst)         -> NamedPer (n, optTerms' ctx lst)
	| NamedProp (n, Dagger, lst) -> 
	    let n' = applyPropRenamingLN ctx n
	    in NamedProp (n', Dagger, optTerms' ctx lst)
	| NamedProp (n, t, lst)      -> 
	    let n' = applyPropRenamingLN ctx n
	    in NamedProp (n', optTerm' ctx t, optTerms' ctx lst)
	    
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
		      (* XXX: Replace with alpha-equivalence someday? *)
		      (Imply(q1,q2), Imply(q1',q2')) when (q1=q2')&&(q2=q1') ->
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
		      optReduceProp ctx (PLet(VarPat n,trm,prp2'))
	      end
	    in (match (optTy ctx ty, p') with
		(_, True) -> 
		  (* forall x:t. True  ===  True *)
		  True
	      | (UnitTy, _) -> 
		  (* forall x:Unit. p'  ===  let x=() in p' *)
		  optReduceProp ctx (PLet(VarPat n,EmptyTuple,p'))
	      | (VoidTy, _) -> 
		  (* forall x:Void. p'  ===   True *)
		  True
	      | (ty1, Imply (PApp (SimpleSupport sty2, Id n3), p'')) when (ty1 = ty_of_simple_ty sty2 && n3 = LN(None,n)) ->
		  ForallSupport((n,sty2), p'')
	      | (ty',_) -> 
		  (* forall x:t. ((... /\ x=e /\ ...) -> p) 
		      ===  let x=e in ((... /\ ...) -> p)
		     when x is not free in e.  *)
		  doForall(n, ty', p'))
	      
	| ForallSupport((n,sty),p) ->
	    let (ctx, n) = renameBoundTermVar ctx n
	    in let doForallSupport(nm1,sty1,prp2) =
	      begin
		match findEqPremise nm1 prp2 with
		    None -> ForallSupport((nm1,sty1),prp2)
		  | Some(trm,prp2') -> 
		      optReduceProp ctx (PLet(VarPat n,trm,prp2'))
	      end
	    in let ctx' = insertTermVariable ctx n (ty_of_simple_ty sty)
	    in let ctx'' = ctx'  (* XXX Should insert fact that n is total! *)
	    in let p' = optProp ctx'' p
	    in (match (optSimpleTy ctx sty, p') with
		(_, True) -> True
	      | (SUnitTy, _) -> optReduceProp ctx (PLet(VarPat n,EmptyTuple,p'))
	      | (SVoidTy, _) -> True
	      | (sty',_) -> doForallSupport(n, sty', p'))

	| PObligation (bnds, p, q) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (optTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = optBnds ctx bnds'
	  in let p' = optProp ctx' p

	  in let ctx'' = if bnds = [] then insertFact ctx' p else ctx'
	  in let q' = optProp ctx'' q
	    in 
		 begin
		   match (bnds'', p') with
		       ([], True) -> q'
		     | _ -> PObligation(bnds'', p', q')
		 end

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
		   
	| PCase (e, arms) ->
	  let (ty, e') = optTerm ctx e
	  in let doArm (pat, p3) =
	    let (ctx',pat') = optPattern ctx pat
	    in let ctx'' = insertPattern ctx' pat'
	    in let p3' = optProp ctx'' p3
	    in (pat', p3')
	  in let arms' = List.map doArm arms
	  in optReduceProp ctx (PCase(e',arms'))

	| PLet(pat, trm1, prp2) ->

	    let (ty1, trm1') = optTerm ctx trm1
	    in let (ctx', pat') = optPattern ctx pat
	    in let ctx' = insertTermVariableLet ctx' pat' ty1
	    in let prp2' = optProp ctx' prp2
	    in let prp' = optReduceProp ctx (PLet(pat', trm1', prp2'))
	    in let prp'' = 
	      match prp' with

		PLet(TuplePat pats, Tuple trms, prp2) ->
		  (** Turn a let of a tuple into a sequence of bindings
		      of the components, if the tuple is never referred
		      to as a whole *)
		  let prp'' = nested_plet' pats trms prp2
		  in optProp ctx prp'' 
		| PLet(VarPat nm1, (Obligation([(nm2,ty2)], prp2, 
				       Id(LN(None,nm2'))) as obprp), prp3) 
		    when nm2 = nm2' ->
	       		    (** Now that assures start out looking like indefinite
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
			 optReduceProp ctx (PLet(VarPat nm1, obprp, prp3'))

		| PLet(VarPat nm1, (Obligation([(nm2,ty2);(nm3,ty3)], prp2, 
				       (Tuple[Id(LN(None,nm2'));
					      Id(LN(None,nm3'))])) as obprp), 
		      prp3)
		    when nm2 = nm2' && nm3 = nm3' && nm2 <> nm3 ->
		    (** Now that assures start out looking like indefinite
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
			 optReduceProp ctx (PLet(VarPat nm1, obprp, prp3'))
		| PLet(VarPat nm1, trm2, prp3) ->
		  begin
		    match hnfTy ctx (typeOf ctx trm2) with
		      TupleTy tys ->
			let nUses = 
			  countProp (occurrencesOfTermName nm1) prp3
			in let nProjs =
			  countProp (occurrencesOfNameInProj nm1) prp3
			in
			  if nProjs >= max 1 (nUses - 2) then
			    let nms = refreshList 
				(List.map (fun _ -> nm1) tys)
			    in let pat =
			      TuplePat(List.map (fun n -> VarPat n) nms)
			    in 
			    optProp ctx
			      (PLet(pat, trm2,
				    substProp 
				      (insertTermvar emptysubst nm1
					 (Tuple(List.map id nms))) prp3))
			  else
			    prp'
		    | _ -> prp'
		  end
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

and optAssertion ctx asn = 
  if List.mem Annot_NoOpt asn.aannots then
    asn
  else
    let ctx', atyvars' = renameBoundTypeVars ctx asn.atyvars
    in let ctx' = insertTypeVariables ctx' atyvars' None

    in let ctx', apbnds' = optPBnds ctx' asn.apbnds

    in let aprop' = optProp ctx' asn.aprop
      
    in let aprop'' = if (!Flags.do_hoist) then
	let (obs, prp') = hoistProp aprop' in
	  optProp ctx' (foldPObligation obs prp') 
      else
	aprop'
    in
    {alabel = asn.alabel;
     atyvars = atyvars';
     apbnds = apbnds';
     aannots = asn.aannots;
     aprop = aprop''}

and optAssertions ctx assertions =
  List.filter (fun {aprop=a} -> a <> True) (List.map (optAssertion ctx) assertions)

and insertAssertionFacts ctx = function
    [] -> ctx
  | asn::rest -> 
      if (asn.atyvars = [] && asn.apbnds = []) then
	insertAssertionFacts (insertFact ctx asn.aprop) rest
      else
      (* We don't have syntax for forall-set quantified propositions,
	 or for forall-proposition quantified propositions,
	 so we can't "remember" such a proposition as one of our facts.
	 We just forget about it. *)
	insertAssertionFacts ctx rest
      
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
	   let assertions' = optAssertions ctx' assertions
	   in let ctx' = insertAssertionFacts ctx' assertions'
	   in let (rest', ctx'') = optElems ctx' rest in
		(Spec (name, ValSpec (tyvars,ty'), assertions') :: rest', 
		ctx'')
		  
      |  Assertion assertion  ::  rest ->
	   let assertion' = optAssertion ctx assertion in
	   let (rest', ctx') = optElems ctx rest in
	     (if assertion'.aprop = True then rest' else Assertion assertion' :: rest'), ctx'
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
	   in let assertions' = optAssertions ctx' assertions
	   in let ctx'' = insertAssertionFacts ctx' assertions'
	   in let (rest', ctx''') = optElems ctx'' rest 
	   in let default_spec = Spec(name, ModulSpec signat', assertions')
	   in let spec' = 
	     if (!Flags.do_poly) then
	       match tryPolymorph ctx name signat' with
		 None       -> default_spec
	       | Some spec' -> spec'
	     else
	       default_spec
	   in
	      (spec'::rest'), ctx''

      |  Spec(nm, TySpec None, assertions) :: rest -> 
	   let ctx' = insertTypeVariable ctx nm None
	   in let assertions' = List.filter (fun {aprop=a} -> a <> True) (List.map (optAssertion ctx') assertions )
	   in let ctx'' = insertAssertionFacts ctx' assertions'
	   in let rest', ctx''' = optElems ctx'' rest 
	   in
		(Spec (nm, TySpec None, assertions') :: rest'), ctx'''

      |  Spec(nm, TySpec (Some ty), assertions) :: rest ->
	   let ty' = optTy ctx ty 
	   in let ctx' = insertTypeVariable ctx nm (Some ty') 
	   in let assertions' = optAssertions ctx' assertions
	   in let ctx'' = insertAssertionFacts ctx' assertions'
	   in let rest', ctx''' = optElems ctx'' rest 
	   in
	     (Spec(nm, TySpec(Some ty'), assertions') :: rest', 
	     ctx''')

      | Spec(nm, SignatSpec sg, assertions) :: rest ->
	  let sg' = optSignat ctx sg
	  in let ctx' = insertSignatVariable ctx nm sg'
	  in let assertions' = optAssertions ctx' assertions
	  in let ctx'' = insertAssertionFacts ctx' assertions'
	  in let (rest', ctx''') = optElems ctx'' rest 
	  in (Spec(nm, SignatSpec sg', assertions') :: rest',
	     ctx''')

      | Spec(nm, PropSpec pt, assertions) :: rest ->
	  let pt' = optPt ctx pt
	  in let ctx' = insertPropVariable ctx nm pt'
	  in let assertions' = optAssertions ctx' assertions
	  in let ctx'' = insertAssertionFacts ctx' assertions'
	  in let (rest', ctx''') = optElems ctx'' rest 
	  in (Spec(nm, PropSpec pt', assertions') :: rest',
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
  | SignatApp(sg1,mdl) as sg->
      if ( ! Flags.do_sigapp ) then
        let sg1' = optSignat ctx sg1
        in let mdl' = optModul' ctx mdl
        in SignatApp(sg1', mdl')
      else	
	optSignat ctx (hnfSignat ctx sg)
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
  if !Flags.do_opt then 
    optElems ctx elems 
  else 
    (elems,ctx)
   
