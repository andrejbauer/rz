open Name
open Logic
open Possibility
module E = Error


(*****************)
(** {2 Contexts} *)
(*****************)

(*******************)
(** {3 Definition} *)
(*******************)

(* A context contains three components:
     1) The traditional typing context, containing mappings from bound
        variables to their sorts (and, optionally a value for this variable.)
     2) Implicit type (or, more generally, kind/theory/etc.) information
        declared by the user.  If a bound variable is introduced without
        an explicit classifier or definition, we look here to see if the
        variable name was previously declared to range over a certain sort.
        (For convenience, we use the same datatype, but in
        these we know there will never be a value specified for the variable.)
     3) A renaming mapping variables to variables.  The typechecker removes
        shadowing whenever possible by renaming bound variables, and this
        mapping keeps track of what renamings are currently are being done.
        If a bound variable is not in the domain of this mapping, it is not
        being renamed.
*)

type context = {bindings : declaration NameMap.t;
		implicits : declaration NameMap.t;
	        renaming  : name NameMap.t}

let emptyContext = {bindings = NameMap.empty; 
		    implicits = NameMap.empty;
		    renaming = NameMap.empty}

(**************)
(* {3 Lookup} *)
(**************)

let lookupImplicit cntxt nm = 
  try Some (NameMap.find nm cntxt.implicits) with
      Not_found -> None

let lookupId cntxt nm =
  try Some (NameMap.find nm cntxt.bindings) with
      Not_found -> None

let isUnbound cntxt nm =
  not (NameMap.mem nm cntxt.bindings)


(******************)
(* {3 Insertion } *)
(******************)

let rec insertImplicits cntxt names info = 
  let infos = List.map (fun _ -> info) names
  in 
    {cntxt with
      implicits = List.fold_right2 NameMap.add names infos cntxt.implicits}


(** The remaining insert functions need to detect and complain about shadowing.
   In most cases, the system will already have renamed bound variables
   before this point.  For module labels we can't rename, and so we
   have to just give up here with an error.
*)


(** Wrapper for the non-checking (primed) insert functions to check for
    shadowing and for proper variable names (e.g., capitalization)
*)
let doInsert validator idString cntxt nm info =
    if validator nm then
      if isUnbound cntxt nm then
	{cntxt with bindings = NameMap.add nm info cntxt.bindings }
      else
	E.shadowingError nm
    else
      E.illegalNameError nm idString

let insertTermVariable cntxt nm ty trmopt = 
  doInsert validTermName "term" cntxt nm (DeclTerm (trmopt,ty))

let insertSetVariable cntxt nm knd stopt = 
  doInsert validSetName "set" cntxt nm (DeclSet (stopt,knd)) 

let insertPropVariable cntxt nm pt prpopt = 
  doInsert validPropName "proposition" cntxt nm (DeclProp (prpopt,pt))

let insertModelVariable cntxt nm thry =
  doInsert validModelName "model" cntxt nm (DeclModel thry)

let insertTheoryVariable cntxt nm thry tknd = 
  doInsert validTheoryName "theory" cntxt nm (DeclTheory (thry,tknd))



let rec updateContextForElem cntxt = function
    Declaration(nm, DeclSet(stopt, knd)) -> 
      insertSetVariable  cntxt nm knd stopt
  | Declaration(nm, DeclProp(prpopt, pt)) -> 
      insertPropVariable cntxt nm pt prpopt
  | Declaration(nm, DeclTerm(trmopt, ty)) -> 
      insertTermVariable cntxt nm ty trmopt
  | Declaration(nm, DeclModel(thry)) -> 
      insertModelVariable cntxt nm thry
  | Declaration(nm, DeclSentence _) ->
      begin
	(* We need to check for bound variable shadowing and appropriate
	   capitalization (because axiom names appear in the final
	   program code). *)
	ignore (insertPropVariable cntxt nm Prop None); 
	(* But the input langauge isn't allowed to refer to the
	   names of axioms, so the axiom-name isn't bound in the
	   context we return. *)
	cntxt 
      end 
  | Comment _   -> cntxt
  | Declaration(_, DeclTheory _) -> 
      failwith "updateContextForElem : DeclTheory"

and updateContextForElems cntxt elems = 
  List.fold_left updateContextForElem cntxt elems
    
(************************************)
(** {3 Renaming of Bound Variables} *)
(************************************)

(** To avoid shadowing, we rename bound variables as soon as we encounter
    them in a context where the same name is already bound in the typing
    context.  Instead of eagerly/immediately replacing all uses of the
    inner bound variable via a substitution, we take the slightly more
    efficient route of maintaining a renaming substitution (in the context)
    as we traverse the term; whenever we see a name used, we first apply
    this renaming substitution before examining it further.
*)


(** Given a context and a name, return the a variant of the name (preferably
    the name unchanged) which is not bound in the context, and extend
    the renaming substitution to map the provided name to the returned
    unbound name.
*)
let renameBoundVar cntxt nm =
  let rec findUnusedName nm =
    if (isUnbound cntxt nm) then 
      nm
    else 
      findUnusedName (nextName nm)
  in let nm' = findUnusedName nm
  in 
       if (nm = nm') then
	 (cntxt, nm)
       else
	 begin
	   E.tyGenericWarning
	     ("Shadowing of " ^ string_of_name nm ^ " detected.");
	   ({cntxt with renaming = NameMap.add nm nm' cntxt.renaming}, nm')
	 end

(** Apply the context's renaming substitution to the given name.
*)
let applyContextSubst cntxt nm = 
  try  NameMap.find nm cntxt.renaming  with
      Not_found -> nm


    
(** When comparing two expressions with bound variables for alpha-equivalence,
    we first replace the two bound variables with a common fresh
    name, and then compare the bodies.
*)
	



(** Given two names, return a third joint name and substitutions respectively
    mapping each given name to the joint name as a term. *)
let rec jointNameSubsts nm1 nm2 = 
  jointNameSubsts' nm1 nm2 emptysubst emptysubst

(** Given two names, return a third joint name and substitutions respectively
    mapping each given name to the joint name as a model. *)
and jointModelNameSubsts nm1 nm2 =
    jointModelNameSubsts' nm1 nm2 emptysubst emptysubst


(** The primed forms jointNameSubsts and jointModelNameSubsts work as above
    but extend two given substitutions rather than returning new
    substitutions.
*)
and jointNameSubsts' nm1 nm2 subst1 subst2 = 
  let freshname = jointName nm1 nm2
  in let trm = Var(LN(None, freshname))
  in let sub1 = insertTermvar subst1 nm1 trm
  in let sub2 = insertTermvar subst2 nm2 trm
  in (freshname, sub1, sub2)

and jointModelNameSubsts' nm1 nm2 subst1 subst2 = 
  let freshname = jointName nm1 nm2
  in let trm = ModelName freshname
  in let sub1 = insertModelvar subst1 nm1 trm
  in let sub2 = insertModelvar subst2 nm2 trm
  in (freshname, sub1, sub2)


(**********************)
(* {2 Theory Lookup } *)
(**********************)

(** *)

let rec searchElems cntxt nm' mdl = 
  let rec loop subst = function 
      [] -> None
    | elem :: rest ->
	match substTheoryElt subst elem with
	  | Declaration(nm, (DeclSet(_,knd) as decl)) ->
	      if (nm = nm') then
		Some decl (** XXX Or selfify? *)
	      else 
		loop (insertSetvar subst nm 
			 (Basic(SLN(Some mdl, nm), knd)))
		  rest
	  | Declaration(nm, (DeclProp(_,pt) as decl)) ->
	      if (nm = nm') then
		Some decl
	      else 
		loop (insertPropvar subst nm 
			 (Atomic(LN(Some mdl, nm), pt)))
		  rest
	  | Declaration(nm, (DeclTerm _ as decl))  -> 
	      if (nm = nm') then
		Some decl
	      else 
		loop (insertTermvar subst nm (Var(LN(Some mdl, nm))))
		  rest
	  | Declaration(nm, (DeclModel _ as decl) ) ->
	      if (nm = nm') then
		Some decl
	      else 
		loop (insertModelvar subst nm (ModelProj(mdl, nm))) 
		  rest
	  | Declaration(nm, (DeclSentence _ as decl)) ->
	      if (nm = nm') then
		Some decl
	      else 
		loop subst rest
	  | Comment _  -> 
	      (** Comments cannot be searched for, currently *)
	      loop subst rest
	  | Declaration(_, (DeclTheory _)) ->
	      failwith "SearchElems : DeclTheory"
  in
    loop emptysubst 

(*********************************)
(** {3 Floating out assumptions} *)
(*********************************)

(*XXX:  Should we get a list of assurances out, or a single assurance? *)

let floatList floatFn things =
  let (assrss, things') = 
    List.split (List.map floatFn things)
  in let assrs = List.flatten assrss
  in (assrs, things)

(* If we lift
     forall x : t ( assure y :u .... )
   what do we have to do if the type u depends on x !!?? 
*)

let rec floatAssure univ hyps = function
    (EmptyTuple | Var _ | Inj(_, None)) as trm -> ([], trm)
  | Assure (None, prp, trm) ->
      let    (assrs1, prp') = floatAssureProp univ hyps prp
      in let (assrs2, trm') = floatAssure univ hyps trm
      in let assr = (None, foldForall (List.rev univ) 
	                     (foldImply hyps prp) )
      in 
	   ( assrs1 @ [assr] @ assrs2, trm' )
  | Assure (Some (nm, ty), prp, trm) ->
      (* Assrs0 and assrs1 can't refer to the variable being assured. *)
      let    (assrs0, ty') = floatAssureSet univ hyps ty
      in let    (assrs1, prp') = floatAssureProp univ hyps prp
	(* Assrs2 can, and these references shouldn't be univ. quantified.
	   We also don't have to add this assertion as a new hypothesis
	   for assrs2, since this assertion will appear first. *)
      in let (assrs2, trm') = floatAssure univ hyps trm
      in let assr = (Some (nm, ty'), foldForall (List.rev univ)
 	                                (foldImply hyps prp) )
      in 
	   ( assrs0 @ assrs1 @ [assr] @ assrs2, trm' )
  | Tuple trms ->
      let (assrs, trms') = floatList (floatAssure univ hyps) trms
      in (assrs, Tuple trms')
  | Proj(n, trm) ->
      let (assrs, trm') = floatAssure univ hyps trm
      in ( assrs, Proj(n, trm') )
  | App(trm1, trm2) ->
      let    (assrs1, trm1') = floatAssure univ hyps trm1
      in let (assrs2, trm2') = floatAssure univ hyps trm2
      in ( assrs1 @ assrs2, App(trm1', trm2') )
  | Lambda((nm, ty), trm) ->
      let (assrs1, ty') = floatAssureSet univ hyps ty
      in let univ' = (nm,ty') :: univ
      in let (assrs2, trm') = floatAssure univ' hyps trm
      in (assrs1 @ assrs2, Lambda((nm,ty'), trm'))
  | The((nm, ty), prp) ->
      let (assrs1, ty') = floatAssureSet univ hyps ty
      in let univ' = (nm,ty') :: univ
      in let (assrs2, prp') = floatAssureProp univ' hyps prp
      in (assrs1 @ assrs2, The((nm,ty'), prp'))
  | Inj(lbl, Some trm) ->
      let (assrs, trm') = floatAssure univ hyps trm
      in ( assrs, Inj(lbl, Some trm'))

  | Case(trm, ty, arms) ->
      let (assrs3, trm') = floatAssure univ hyps trm
      in let (assrs4, ty') = floatAssureSet univ hyps ty
      in let floatArm = function
	  (lbl, None, trm) ->
	    let hyps' = Equal(ty, trm, Inj(lbl, None)) :: hyps
	    in let (assrs, trm') = floatAssure univ hyps' trm
	    in (assrs, (lbl, None, trm'))
	| (lbl, Some (nm,ty), trm) ->
	    let (assrs1, ty') = floatAssureSet univ hyps ty
	    in let univ' = (nm, ty') :: univ
	    in let hyps' = 
	      Equal( ty, trm, Inj(lbl, Some (Var(longname_of_name nm))) ) :: hyps
	    in let (assrs2, trm') = floatAssure univ' hyps' trm
	    in (assrs1 @ assrs2, (lbl, Some (nm, ty'), trm'))
      in let (assrs5s, arms') = List.split (List.map floatArm arms)
      in let assrs5 = List.flatten assrs5s
      in (assrs3 @ assrs4 @ assrs5, Case(trm', ty', arms'))

  | RzQuot trm ->
      let (assrs, trm') = floatAssure univ hyps trm
      in ( assrs, RzQuot trm')
  | RzChoose ((nm1,Rz ty2), trm3, trm4, ty5) ->
      let    (assrs2, ty2') = floatAssureSet univ hyps ty2
      in let (assrs3, trm3') = floatAssure univ hyps trm3
      in let univ' = (nm1,ty2') :: univ
      in let hyps' = 
	Equal(ty2, RzQuot (Var(longname_of_name nm1)), trm3) :: hyps
      in let (assrs4, trm4') = floatAssure univ' hyps' trm4
      in let (assrs5, ty5') = floatAssureSet univ hyps ty5
      in (assrs2 @ assrs3 @ assrs4 @ assrs5, 
	 RzChoose((nm1,ty2'), trm3', trm4', ty5') )
  | RzChoose _ -> failwith "Impossible: floatAssure"
  | Quot(trm, prp) ->
      let    (assrs1, trm') = floatAssure univ hyps trm
      in let (assrs2, prp') = floatAssureProp univ hyps prp
      in ( assrs1 @ assrs2, Quot(trm', prp'))
  | Choose((nm1,ty2), pred3, trm4, trm5, ty6) ->
      let    (assrs2, ty2' ) = floatAssureSet univ hyps ty2
      in let (assrs3, pred3') = floatAssureProp univ hyps pred3
      in let (assrs4, trm4') = floatAssure univ hyps trm4
      in let univ' = (nm1,ty2') :: univ
      in let hyps' = 
	Equal(Quotient(ty2, pred3),
	      Quot(Var(longname_of_name nm1),pred3'), trm4) :: hyps
      in let (assrs5, trm5') = floatAssure univ' hyps' trm5
      in let (assrs6, ty6' ) = floatAssureSet univ hyps ty6
      in ( assrs2 @ assrs3 @ assrs4 @ assrs5 @ assrs6, 
	   Choose((nm1,ty2'), pred3', trm4', trm5', ty6') )
  | Let((nm1,ty2), trm3, trm4, ty5) ->
      let    (assrs2, ty2' ) = floatAssureSet univ hyps ty2
      in let (assrs3, trm3') = floatAssure univ hyps trm3
      in let univ' = (nm1,ty2') :: univ
      in let hyps' = Equal(ty2, Var(longname_of_name nm1), trm3) :: hyps
      in let (assrs4, trm4') = floatAssure univ' hyps' trm4
      in let (assrs5, ty5' ) = floatAssureSet univ hyps ty5
      in (assrs2 @ assrs3 @ assrs4 @ assrs5, 
	 RzChoose((nm1,ty2'), trm3', trm4', ty5') )
  | Subin(trm, ty) ->
      let    (assums1, trm') = floatAssure univ hyps trm
      in let (assums2, ty' ) = floatAssureSet univ hyps ty
      in (assums1 @ assums2, 
	  Subin(trm', ty') )
  | Subout(trm, ty) ->
      let    (assums1, trm') = floatAssure univ hyps trm
      in let (assums2, ty' ) = floatAssureSet univ hyps ty
      in (assums1 @ assums2, 
	  Subout(trm', ty') )

and floatAssureProp univ hyps = function
    (False | True | Atomic _) as prp -> ([], prp)
  | PAssure (None, prp1, prp2) ->
      let    (assrs1, prp1') = floatAssureProp univ hyps prp1
      in let (assrs2, prp2') = floatAssureProp univ hyps prp2
      in let assr = (None, foldForall (List.rev univ) 
	                     (foldImply hyps prp1) )
      in 
	   ( assrs1 @ [assr] @ assrs2, prp2' )
  | PAssure (Some (nm, ty), prp1, prp2) ->
      (* Assrs0 and assrs1 can't refer to the variable being assured. *)
      let    (assrs0, ty') = floatAssureSet univ hyps ty
      in let (assrs1, prp1') = floatAssureProp univ hyps prp1
	(* Assrs2 can, and these references shouldn't be univ. quantified.
	   We also don't have to add this assertion as a new hypothesis
	   for assrs2, since this assertion will appear first. *)
      in let (assrs2, prp2') = floatAssureProp univ hyps prp2
      in let assr = (Some (nm, ty'), foldForall (List.rev univ)
 	                                (foldImply hyps prp1) )
      in 
	   ( assrs0 @ assrs1 @ [assr] @ assrs2, prp2' )

  | And prps ->
      let (assrs, prps') = floatList (floatAssureProp univ hyps) prps
      in (assrs, And prps')

  | Or prps ->
      let (assrs, prps') = floatList (floatAssureProp univ hyps) prps
      in (assrs, Or prps')

  | Imply(prp1, prp2) ->
      let    (assrs1, prp1') = floatAssureProp univ hyps prp1
      in let (assrs2, prp2') = floatAssureProp univ hyps prp2
      in ( assrs1 @ assrs2, Imply(prp1',prp2') )

  | Iff(prp1, prp2) ->
      let    (assrs1, prp1') = floatAssureProp univ hyps prp1
      in let (assrs2, prp2') = floatAssureProp univ hyps prp2
      in ( assrs1 @ assrs2, Iff(prp1',prp2') )

  | Forall((nm,ty), prp) ->
      let    (assrs1, ty') = floatAssureSet univ hyps ty
      in let univ' = (nm,ty') :: univ
      in let (assrs2, prp') = floatAssureProp univ' hyps prp
      in ( assrs1 @ assrs2, Forall((nm,ty'), prp') )

  | Exists((nm,ty), prp) ->
      (** XXX NO ! *)
      let    (assrs1, ty') = floatAssureSet univ hyps ty
      in let univ' = (nm,ty') :: univ
      in let (assrs2, prp') = floatAssureProp univ' hyps prp
      in ( assrs1 @ assrs2, Exists((nm,ty'), prp') )

      
  | _ -> failwith "unimplemented"

and floatAssureSet univ hyps = function 
    (Empty | Unit | Basic _) as st -> ([], st)
(*
  | Product bnds ->
      let rec fun processBnds univ = function
	  [] -> ([], [])
	| (nm,st)::rest ->
	    let (st',
*)
  | _ -> failwith "unimplemented"

(**************************************)
(** {3 Type and Theory Normalization} *)
(**************************************)

(** Head-normalization of a theory: replacing theory names by
    definitions, and reducing top-level lambda applications.

    Postcondition:  The returned theory is neither a variable nor
    an application (since we don't have abstract theory variables).
*)
let rec hnfTheory cntxt = function
    TheoryName nm ->
      begin
	match lookupId cntxt nm with
	    Some(DeclTheory (thry, _)) -> hnfTheory cntxt thry
	  | _ -> failwith "Impossible: Logicrules.hnfTheory 1"
      end
  | TheoryApp (thry, mdl) ->
      begin
	match hnfTheory cntxt thry with
	    TheoryLambda((nm,_), thry2) ->
	      let subst = insertModelvar emptysubst nm mdl
	      in hnfTheory cntxt (substTheory subst thry2)
	  | _ -> failwith "Impossible: Logicrules.hnfTheory 2"
      end
  | thry -> thry

(* cntxt -> model -> theory *)
(** Assumes that the given model is well-formed.
*)
let rec theoryOf cntxt = function
    ModelName nm ->
      begin
	match (lookupId cntxt nm) with
	    Some(DeclModel thry) -> thry
	  | _ -> failwith "Impossible: Logicrules.theoryOf 1"
      end
  | ModelProj (mdl, nm) -> 
      begin
	match hnfTheory cntxt (theoryOf cntxt mdl) with
	    Theory elems ->
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclModel thry) -> thry
		  | _ -> failwith "Impossible: Logicrules.theoryOf 2"
	      end
	  | _ -> failwith "Impossible: Logicrules.theoryOf 3"
      end
  | ModelApp (mdl1, mdl2) ->
      begin
	match hnfTheory cntxt (theoryOf cntxt mdl1) with
	    TheoryArrow((nm, thry1), thry2) ->
	      let subst = insertModelvar emptysubst nm mdl2
	      in substTheory subst thry2
	  | _ -> failwith "Impossible: Logicrules.theoryOf 4"
      end
	

(** Expand out any top-level definitions or function
    applications for a (well-formed) set 
  *)
let rec hnfSet cntxt = function
    Basic (SLN ( None, stnm ), _) as orig_set ->
      begin
	match (lookupId cntxt stnm) with
            Some(DeclSet(Some st, _)) -> hnfSet cntxt st
	  | Some(DeclSet(None, _))    -> orig_set
	  | _ -> failwith "Impossible: hnfSet 1"
      end

  | Basic (SLN ( Some mdl, nm), _) as orig_set -> 
      begin
	match hnfTheory cntxt (theoryOf cntxt mdl) with
	    Theory elems -> 
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclSet(Some st, _)) -> hnfSet cntxt st
		  | Some (DeclSet(None, _))    -> orig_set
		  | _ -> failwith "Impossible: hnfSet 2"
	      end
	  | _ -> failwith "Impossible: hnfSet 3"
      end

  | SApp(st1,trm2) -> 
      begin
	match (hnfSet cntxt st1) with
	    SLambda((nm,_),st1body) ->
	      let sub = insertTermvar emptysubst nm trm2
	      in
		hnfSet cntxt (substSet sub st1body)
	  | st1' -> SApp(st1', trm2)
      end

  | st -> st


(** Expand out any top-level definitions or function
    applications for a (well-formed) proposition or predicate
  *)
let rec hnfTerm cntxt = function
    Var (LN ( None, nm )) as orig_term ->
      begin
	match (lookupId cntxt nm) with
            Some(DeclTerm(Some trm, _)) -> hnfTerm cntxt trm
	  | Some(DeclTerm(None, _))    -> orig_term
	  | _ -> failwith "Impossible: Logicrules.hnfTerm 1"
      end

  | Var (LN ( Some mdl, nm)) as orig_term -> 
      begin
	match hnfTheory cntxt (theoryOf cntxt mdl) with
	    Theory elems -> 
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclTerm(Some trm, _)) -> hnfTerm cntxt trm
		  | Some (DeclTerm(None, _))    -> orig_term
		  | _ -> failwith "Impossible: Logicrules.hnfTerm 2"
	      end
	  | _ -> failwith "Impossible: Logicrules.hnfTerm 3"
      end

  | App(trm1,trm2) -> 
      begin
	match (hnfTerm cntxt trm1) with
	    Lambda((nm,_),trm1body) ->
	      let sub = insertTermvar emptysubst nm trm2
	      in
		hnfTerm cntxt (subst sub trm1body)
	  | trm1' -> App(trm1', trm2)
      end

  | Case(trm1, ty, arms) ->
      begin
	match (hnfTerm cntxt trm1) with
	    Inj(lbl, None) ->
	      begin
		match (List.find (fun (l,_,_) -> l = lbl) arms) with
		    (_, None, trm2) -> hnfTerm cntxt trm2
		  | _ -> failwith "Impossible: Logicrules.hnfTerm 4"
	      end
	  | Inj(lbl, Some trm1') ->
	      begin
		match (List.find (fun (l,_,_) -> l = lbl) arms) with
		    (_, Some (nm,_), trm2) -> 
		      let sub = insertTermvar emptysubst nm trm1'
		      in
			hnfTerm cntxt (subst sub trm2)
		  | _ -> failwith "Impossible: Logicrules.hnfTerm 5"
	      end
	  | trm1' -> Case(trm1', ty, arms)
      end

  | Proj(n1, trm2) ->
      begin
	match (hnfTerm cntxt trm2) with
	    Tuple trms -> hnfTerm cntxt (List.nth trms n1)
	  | trm2' -> Proj(n1, trm2')
      end
	      
  | Let((nm,_),trm1,trm2,_) ->
      let sub = insertTermvar emptysubst nm trm1
      in
	hnfTerm cntxt (subst sub trm2)

  | Assure (None, _, trm) ->
      (** Since hnfTerm is only applied to well-formed terms, the
          assure must be true. More importantly, since we can't
          _actually_ check that the proposition is true, hnfTerm is
          only used in deciding term equivalence, where assures
          are irrelevant.  [The _optimizer_ on the other hand, 
          should not be throwing away assures!] *)
      hnfTerm cntxt trm

  | trm -> trm

(** Expand out any top-level definitions or function
    applications for a (well-formed) proposition or predicate
  *)
let rec hnfProp cntxt = function
    Atomic (LN ( None, nm ), _) as orig_prop ->
      begin
	match (lookupId cntxt nm) with
            Some (DeclProp(Some prp, _)) -> hnfProp cntxt prp
	  | Some (DeclProp(None, _))    -> orig_prop
	  | _ -> failwith "Impossible: Logicrules.hnfProp 1"
      end

  | Atomic (LN ( Some mdl, nm), _) as orig_prop -> 
      begin
	match hnfTheory cntxt (theoryOf cntxt mdl) with
	    Theory elems -> 
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclProp(Some prp, _)) -> hnfProp cntxt prp
		  | Some (DeclProp(None, _))    -> orig_prop
		  | _ -> failwith "Impossible: Logicrules.hnfProp 2"
	      end
	  | _ -> failwith "Impossible: Logicrules.hnfProp 3"
      end

  | PApp(prp1,trm2) -> 
      begin
	match (hnfProp cntxt prp1) with
	    PLambda((nm,_),prp1body) ->
	      let sub = insertTermvar emptysubst nm trm2
	      in
		hnfProp cntxt (substProp sub prp1body)
	  | prp1' -> PApp(prp1', trm2)
      end

  | PCase(trm1, ty, arms) ->
      begin
	match (hnfTerm cntxt trm1) with
	    Inj(lbl, None) ->
	      begin
		match (List.find (fun (l,_,_) -> l = lbl) arms) with
		    (_, None, prp1') -> hnfProp cntxt prp1'
		  | _ -> failwith "Impossible: Logicrules.hnfProp 4"
	      end
	  | Inj(lbl, Some trm1') ->
	      begin
		match (List.find (fun (l,_,_) -> l = lbl) arms) with
		    (_, Some (nm,_), prp2) -> 
		      let sub = insertTermvar emptysubst nm trm1'
		      in
			hnfProp cntxt (substProp sub prp2)
		  | _ -> failwith "Impossible: Logicrules.hnfProp 5"
	      end
	  | trm1' -> PCase(trm1', ty, arms)
      end

  | PAssure (None, _, prp) ->
      (** See the Assure comment in hnfTerm above *)
      hnfProp cntxt prp

  | prp -> prp



(**********************************************)
(** {2 Equivalence, Subtyping, and Coercions} *)
(**********************************************)

(****************************************)
(** {4 Sets: equivalence and subtyping} *)
(****************************************)

let eqArms cntxt substFn eqFn eqSetFn arms1 arms2 =
  let rec loop = function
      ([], []) -> true
    | ((lbl1, None, val1)::rest1, (lbl2, None, val2)::rest2) ->
	lbl1 = lbl2  && 
          eqFn cntxt val1 val2 && 
	  loop (rest1, rest2)
    | ((lbl1, Some (nm1,st1), val1) :: rest1, 
      (lbl2, Some (nm2,st2), val2) :: rest2 ) ->
	lbl1 = lbl2 &&
          eqSetFn cntxt st1 st2 &&
	  (let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	    in let val1' = substFn sub1 val1
	    in let val2' = substFn sub2 val2
	    in let cntxt' = insertTermVariable cntxt nm1 st1 None
	    in 
		 eqFn cntxt' val1' val2') &&
                   loop(rest1, rest2)
    | _ -> false
  in let order (lbl1, _, _) (lbl2, _, _) = compare lbl1 lbl2
  in let arms1' = List.sort order arms1
  in let arms2' = List.sort order arms2
  in 
       loop (arms1', arms2')


(* eqSet': bool -> cntxt -> set -> set -> bool *)
(**
      Precondition:  The two sets are fully-annotated
                     and proper (first-order, i.e., KindSet) sets.

      Postcondition:  Whether the two sets are equal (or implicitly-
                      convertible, if the boolean is true) in the 
                      given context.  Equality defined as alpha-equivalence,
                      commutivity of sums, and definition expansion.

                      Implicit convertability is especially important
                      as a way of addressing defects in type inference, since
                      we don't want to have to annotate each injection
                      with the corresponding sum type.
                      
                      Implicit conversion used to just be generated
                      by conversion of sum types in strictly positive
                      positions.   Now it does more, but this might
                      be a bug. XXX
  *)
let rec eqSet' do_subset cntxt = 
   let rec cmp (s1 : set) (s2 : set) = 
      (** Short circuting for (we hope) the common case *)
      (s1 = s2)
      (** Head-normalize the two sets *)
      || let    s1' = hnfSet cntxt s1
         in let s2' = hnfSet cntxt s2

         in (s1' = s2') 
            || (match (s1',s2') with
                 ( Empty, Empty ) -> true       (** Redundant *)

               | ( Unit, Unit )   -> true       (** Redundant *) 

               | ( Basic (SLN(mdlopt1, nm1), _),
		   Basic (SLN(mdlopt2, nm2), _) ) -> 
                    (** Neither has a definition *)
                    eqModelOpt cntxt mdlopt1 mdlopt2 
                    && (nm1 = nm2) 

 	       | ( Product ss1, Product ss2 ) -> 
                    cmpProducts cntxt (ss1,ss2)

               | ( Sum lsos1, Sum lsos2 )     -> 
	            subSum do_subset cntxt (lsos1, lsos2) 
                    && (do_subset || subSum false cntxt (lsos2, lsos1))


               | ( Exp( nm1, st3, st4 ), Exp ( nm2, st5, st6 ) ) ->
		   (** Domains are now compared contravariantly. *)
		   cmp st5 st3 &&
		     let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	             in let st4' = substSet sub1 st4
	             in let st6' = substSet sub2 st6
		     in let cntxt' = insertTermVariable cntxt nm st5 None
	             in 
			  eqSet' do_subset cntxt' st4' st6'

	       | ( Subset( (nm1,st1),  p1 ), 
		   Subset( (nm2,st2), p2 ) )->
		   cmp st1 st2 &&
	            (** Alpha-vary the propositions so that they're using the
                        same (fresh) variable name *)
                       let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	               in let p1' = substProp sub1 p1
	               in let p2' = substProp sub2 p2
		       in let cntxt' = insertTermVariable cntxt nm st1 None
	               in 
                          eqProp cntxt' p1' p2'  

               | ( Quotient ( st3, eqvlnce3 ), 
		   Quotient ( st4, eqvlnce4 ) ) -> 
                    cmp st3 st4  
                    && eqProp cntxt eqvlnce3 eqvlnce4

               | ( SApp (st3, trm3), SApp (st4, trm4) ) ->
		   (* XXX: this is a place where we would presumably
		      emit an obligation *)
		    eqSet cntxt st3 st4
		    && eqTerm cntxt trm3 trm4

               | ( Rz st3, Rz st4 ) -> 
                    (** RZ seems like it should be invariant.  *)
		    (** XXX Is it? *)
                    eqSet cntxt st3 st4  

               | (_,_) -> false )

      and cmpProducts' cntxt subst1 subst2 = function
          ( [] , [] ) -> true

	| ( (nm1, s1) :: s1s, (nm2, s2) :: s2s) -> 
	    begin
	      let s1' = substSet subst1 s1
	      in let s2' = substSet subst2 s2
	      in 
		   eqSet' do_subset cntxt s1' s2'
	    end &&
	      begin
		let (nm, subst1', subst2') = 
		  jointNameSubsts' nm1 nm2 subst1 subst2
		in let cntxt' = insertTermVariable cntxt nm s1 None
		in 
		     cmpProducts' cntxt' subst1' subst2' (s1s,s2s)
	      end

        | (_,_) -> false

   and cmpProducts cntxt lst = cmpProducts' cntxt emptysubst emptysubst lst
     
   and subSum do_subset cntxt = function
       ( [], _ ) -> true
     | ((l1,None   )::s1s, s2s) ->
	 (try
	     match (List.assoc l1 s2s) with
		 None -> subSum do_subset cntxt (s1s, s2s)
	       | _ -> false 
	   with 
	       Not_found -> false)
     | ((l1,Some s1)::s1s, s2s) -> 
	 (try
	     match (List.assoc l1 s2s) with
		 Some s2 -> eqSet' do_subset cntxt s1 s2  && 
                   subSum do_subset cntxt (s1s,s2s)
	       |  _ -> false 
	   with
	       Not_found -> false)
	   
   in cmp

and equivToArrow ty =
  PropArrow(wildName(), ty, PropArrow(wildName(), ty, StableProp))

and eqPropType' do_subset cntxt = 
   let rec cmp (pt1 : proptype) (pt2 : proptype) = 
     begin
       (** Short circuting for (we hope) the common case *)
       (pt1 = pt2) ||
         match (pt1, pt2) with
           | ( StableProp, Prop ) -> true
	       
           | ( EquivProp st1, EquivProp st2) -> 
	       eqSet' do_subset cntxt st2 st1
	       
           | ( EquivProp st1, _ ) ->
		 do_subset &&
		   eqPropType' true cntxt (equivToArrow st1) pt2
		 
           | ( PropArrow( nm1, st1, pt1 ), PropArrow ( nm2, st2, pt2 ) ) ->
	       let (_, sub1, sub2) = jointNameSubsts nm1 nm2
	       in let pt1' = substProptype sub1 pt1
	       in let pt2' = substProptype sub2 pt2
	           in 
		    (* Domains are now compared contravariantly. *)
                    subSet cntxt st2 st1 
                    && cmp pt1' pt2'

	   | _ -> false
     end
   in cmp

and subPropType cntxt pt1 pt2 = eqPropType' true cntxt pt1 pt2

and eqPropType cntxt pt1 pt2 = eqPropType' false cntxt pt1 pt2

and eqKind' do_subset cntxt = 
   let rec cmp (k1 : setkind) (k2 : setkind) = 
     begin
       (** Short circuting for (we hope) the common case *)
       (k1 = k2) ||
         match (k1, k2) with
             ( KindArrow( nm1, st1, kk1 ), KindArrow ( nm2, st2, kk2 ) ) ->
	       let (_, sub1, sub2) = jointNameSubsts nm1 nm2
	       in let kk1' = substSetkind sub1 kk1
	       in let kk2' = substSetkind sub2 kk2
	           in 
		    (* Domains are now compared contravariantly. *)
                    subSet cntxt st2 st1 
                    && cmp kk1' kk2'

	   | _ -> false
     end
   in cmp

and subKind cntxt k1 k2 = eqKind' true cntxt k1 k2

and eqKind cntxt k1 k2 = eqKind' false cntxt k1 k2

(** IMPORTANT: two provably equivalent propositions are NOT
    necessarily interchangeable because they may have realizers
    of different types.  They are interchangeable if:
      0) They are identical modulo set and term equivalence.
      1) They are alpha, beta, and delta equivalent modulo sets/terms
          [current implementation]
      2) Or, they are provably equivalent and stable.
      3) Or, when reduced to normal form (exists r:t, phi)
         they have the same realizer types t and provably
         equivalent classical parts (phi's).
*)
and eqProp cntxt prp1 prp2 = 
  (prp1 = prp2) (* short-circuiting *) ||
    match (hnfProp cntxt prp1, hnfProp cntxt prp2) with
	(False, False) -> true    (* Redundant *)
      | (True, True) -> true      (* Redundant *)
      | (Atomic(LN(Some mdl1, nm1), _), 
	 Atomic(LN(Some mdl2, nm2), _)) ->
	  eqModel cntxt mdl1 mdl2 && nm1 = nm2
	    && nm1 = nm2
      | (Atomic(LN(None, nm1), _), Atomic(LN(None, nm2), _) ) -> 
	  nm1 = nm2
      | (And prps1, And prps2) 
      | (Or prps1, Or prps2 )->
	  eqProps cntxt prps1 prps2
      | (Imply(prp1a, prp1b), Imply(prp2a, prp2b)) 
      | (Iff(prp1a, prp1b), Iff(prp2a, prp2b)) ->
	  eqProp cntxt prp1a prp2a &&
	    eqProp cntxt prp1b prp2b
      | (Forall((nm1,st1), prp1), Forall((nm2,st2), prp2)) 
      | (Exists((nm1,st1), prp1), Exists((nm2,st2), prp2)) 
      | (Unique((nm1,st1), prp1), Unique((nm2,st2), prp2)) 
      | (PLambda((nm1,st1), prp1), PLambda((nm2,st2), prp2)) ->
	  eqSet cntxt st1 st2 &&
	    let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	    in let prp1' = substProp sub1 prp1
	    in let prp2' = substProp sub2 prp2
	    in let cntxt' = insertTermVariable cntxt nm1 st1 None
	    in eqProp cntxt' prp1' prp2'
      | (Not prp1, Not prp2) ->
	  eqProp cntxt prp1 prp2
      | (Equal(ty1, trm1a, trm1b), Equal(ty2, trm2a, trm2b)) ->
	  eqSet cntxt ty1 ty2 &&
	    eqTerm cntxt trm1a trm2a &&
	    eqTerm cntxt trm1b trm2b
      | (PApp(prp1, trm1), PApp(prp2, trm2)) ->
	  eqProp cntxt prp1 prp2 &&
	    eqTerm cntxt trm1 trm2
      | (IsEquiv(prp1,st1), IsEquiv(prp2,st2)) ->
	  eqProp cntxt prp1 prp2 &&
	    eqSet cntxt st1 st2 
      | (PCase(trm1, ty1, arms1), PCase(trm2, ty2, arms2)) ->
	  eqTerm cntxt trm1 trm2 &&
	    eqSet cntxt ty1 ty2 &&
	    eqArms cntxt substProp eqProp eqSet arms1 arms2
      | _ -> false
	    
and eqProps cntxt prps1 prps2 = 
  try  List.for_all2 (eqProp cntxt) prps1 prps2  with
      Invalid_argument _ -> false
	                             

and eqTerm cntxt trm1 trm2 = 
  (trm1 = trm2) ||
    match (hnfTerm cntxt trm1, hnfTerm cntxt trm2) with
	(EmptyTuple, EmptyTuple) -> true   (* Redundant *)
      | (Var(LN(Some mdl1, nm1)), Var(LN(Some mdl2, nm2))) ->
	  eqModel cntxt mdl1 mdl2 && nm1 = nm2
      | (Var(LN(None, nm1)), Var(LN(None, nm2))) ->
	  nm1 = nm2
      | (Tuple trms1, Tuple trms2) -> 
	  eqTerms cntxt trms1 trms2
      | (Proj(n1, trm1), Proj(n2, trm2)) ->
	  n1 = n2 && eqTerm cntxt trm1 trm2

      | (App(trm1a, trm1b), App(trm2a, trm2b)) ->
	  eqTerm cntxt trm1a trm2a &&
	    eqTerm cntxt trm1b trm2b

      | (Lambda((nm1,ty1),trm1), Lambda((nm2,ty2),trm2)) ->
	    let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	    in let trm1' = subst sub1 trm1
	    in let trm2' = subst sub2 trm2
	    in let cntxt' = insertTermVariable cntxt nm1 ty1 None
	    in 
		 eqSet cntxt ty1 ty2 &&
		   eqTerm cntxt' trm1' trm2'

      | (The((nm1,ty1),prp1), The((nm2,ty2),prp2)) ->
	  eqSet cntxt ty1 ty2 &&
	    let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	    in let prp1' = substProp sub1 prp1
	    in let prp2' = substProp sub2 prp2
	    in let cntxt' = insertTermVariable cntxt nm1 ty1 None
	    in eqProp cntxt' prp1' prp2'

      | (Inj(lbl1, None), Inj(lbl2, None)) ->
	  lbl1 = lbl2
      | (Inj(lbl1, Some trm1), Inj(lbl2, Some trm2)) ->
	  lbl1 = lbl2 && eqTerm cntxt trm1 trm2

      | (Case(trm1, ty1, arms1), Case(trm2, ty2, arms2)) ->
	  eqTerm cntxt trm1 trm2 &&
	    eqSet cntxt ty1 ty2 &&
	    eqArms cntxt subst eqTerm eqSet arms1 arms2

      | (RzQuot trm1, RzQuot trm2) ->
	  eqTerm cntxt trm1 trm2

      | (RzChoose((nm1, ty1a), trm1a, trm1b, ty1b), 
	 RzChoose((nm2, ty2a), trm2a, trm2b, ty2b))
      | (Let     ((nm1, ty1a), trm1a, trm1b, ty1b), 
	 Let     ((nm2, ty2a), trm2a, trm2b, ty2b)) ->
	    let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	    in let trm1b' = subst sub1 trm1b
	    in let trm2b' = subst sub2 trm2b
	    in let cntxt' = insertTermVariable cntxt nm1 ty1a None
	    in 
		 eqSet cntxt ty1a ty2a &&
		   eqTerm cntxt trm1a trm2a &&
		   eqTerm cntxt' trm1b' trm2b' &&
		   eqSet cntxt ty1b ty2b

      | (Quot(trm1,prp1), Quot(trm2,prp2)) ->
	  eqTerm cntxt trm1 trm2 &&
	    eqProp cntxt prp1 prp2

      | (Choose((nm1,ty1a),prp1,trm1a,trm1b,ty1b),
	 Choose((nm2,ty2a),prp2,trm2a,trm2b,ty2b)) ->
	    let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	    in let trm1b' = subst sub1 trm1b
	    in let trm2b' = subst sub2 trm2b
	    in let cntxt' = insertTermVariable cntxt nm1 ty1a None
	    in 
		 eqSet cntxt ty1a ty2a &&
		   eqProp cntxt prp1 prp2 &&
		   eqTerm cntxt trm1a trm2a &&
		   eqTerm cntxt' trm1b' trm2b' &&
		   eqSet cntxt ty1b ty2b

      | (Subin (trm1,st1), Subin (trm2,st2))
      | (Subout(trm1,st1), Subout(trm2,st2)) ->
	  eqTerm cntxt trm1 trm2 &&
	    eqSet cntxt st1 st2

      | _ -> false
	 
and eqTerms cntxt trms1 trms2 = 
  try  List.for_all2 (eqTerm cntxt) trms1 trms2  with
      Invalid_argument _ -> false

and eqModel ctx mdl1 mdl2 = (mdl1 = mdl2)

and eqModelOpt ctx mdlopt1 mdlopt2 = (mdlopt1 = mdlopt2)

and eqSet cntxt st1 st2 = eqSet' false cntxt st1 st2

and subSet cntxt st1 st2 = eqSet' true cntxt st1 st2


(** Computes the join of the two sets s1 and s2.  Like subtSet (and
    unlike Coerce), join does *not* do/include/permit implicit
    conversions *)
let rec joinType cntxt s1 s2 : set possibility = 
  if (s1 = s2) then
    (* Short circuit *)
      definitely s1
   else
      let    s1' = hnfSet cntxt s1
      in let s2' = hnfSet cntxt s2

      (* Assumes arms of the two types are merged and sorted *)
      in let rec joinSums = function 
	  ([], sumA, reqA) -> YesIf(Sum sumA, reqA)

	| ([last], sumA, reqA) -> joinSums([], last :: sumA, reqA)

	| ( ((l1,_) as first) :: (((l2,_) :: _) as rest), sumA, reqA) 
	    when l1 <> l2 ->
	    (* First two labels in the list are unequal *)
	    joinSums(rest, first :: sumA, reqA)

	| ( ((l1,None) as first) :: (_,None) :: rest, sumA, reqA) ->
	    (* If we got this far, the two labels are equal *)
	    (* Both agree that l1 (== l2) tags no value. *)
	    joinSums(rest, first :: sumA, reqA)

	| ( (l1,Some ty1) :: (_, Some ty2) :: rest, sumA, reqA ) ->
	    (* If we got this far, the two labels are equal *)
	    (* Both agree that l1 (== l2) tags carry a value. *)
	    begin
	      match joinType cntxt ty1 ty2 with
		  YesIf(ty, reqs) -> 
		    joinSums(rest, (l1, Some ty)::sumA, reqs @ reqA)
		| NoBecause reasons -> 
		    NoBecause
		      (("The label " ^ string_of_label l1 ^ 
			   "tags inconsistent types " ^ string_of_set ty1 ^
		           " and " ^ string_of_set ty2) :: reasons)
	    end

	| ( (l1, _) :: (l2, _) :: _, _, _) ->
	    definitelyNot
	      ("Disagreement as to whether " ^ l1 ^
		  " stands alone or tags a value")

      in let result =
	match (s1',s2') with
            (Sum lsos1, Sum lsos2) -> 
	      let order (lbl1, _) (lbl2, _) = compare lbl1 lbl2
	      in let lsos' = List.sort order (lsos1 @ lsos2)
	      in 
		   joinSums (lsos', [], []) 
          | _ -> 
	      begin
(*
		match (eqSet cntxt s1 s2) with
	            YesIf (_,reqs) -> YesIf(s1, reqs)
		  | NoBecause _ as ans -> ans
*)
		if (eqSet cntxt s1 s2) then
		  YesIf(s1, [])
		else
		  NoBecause []
	      end

      in 
	   possCase result
	     (fun yes -> yes)
	     (fun rsns -> 
	       ("The types " ^ string_of_set s1 ^ " and " ^ 
		   string_of_set s2 ^ " have no join") :: rsns)

let joinTypes cntxt =
  let rec loop = function
      [] -> definitely Unit
    | [s] -> definitely s
    | s::ss -> 
	possCase' (loop ss)
	  (fun (join_ss, reqs) -> addReqs (joinType cntxt s join_ss) reqs)
	  (fun rsns            -> NoBecause rsns)
  in
    loop

let joinProperPropType p1 p2 = 
  begin
    match (p1,p2) with
	(StableProp, StableProp) -> StableProp
      | ((Prop | StableProp), (Prop | StableProp)) -> Prop
      | _ -> failwith "joinProperPropType only allows Prop and StableProp!"
  end

let joinProperPropTypes lst = 
  List.fold_left joinProperPropType StableProp lst



let rec joinPropType cntxt pt1 pt2 = 
  let ptposs = 
    match (pt1,pt2) with
	(StableProp, StableProp) ->
	  definitely StableProp
      | ((Prop | StableProp), (Prop | StableProp)) -> 
	  definitely Prop
      | (EquivProp ty1, EquivProp ty2) -> 
	  modifyIfYes fEquivProp (joinType cntxt ty1 ty2)
      | (EquivProp ty1, _ ) -> 
	  joinPropType cntxt (equivToArrow ty1) pt2
      | (_, EquivProp ty2) -> 
	  joinPropType cntxt pt1 (equivToArrow ty2)
      | (PropArrow(nm3, st3, pt3), PropArrow(nm4, st4, pt4)) ->
	  let (nm, sub3, sub4) = jointNameSubsts nm3 nm4
	  in let pt3' = substProptype sub3 pt3
	  in let pt4' = substProptype sub4 pt4
	  in let cntxt' = insertTermVariable cntxt nm st3 None
	  in 
	       if (eqSet cntxt st3 st4) then
		 modifyIfYes (fun pt -> PropArrow(nm, st3, pt))  
		   (joinPropType cntxt' pt3' pt4') 
	       else
		 definitelyNot ("The domain types " ^ string_of_set st3 ^ 
				   " and " ^ string_of_set st4 ^ 
				   " have no join")
		   
      | _ -> NoBecause []
  in
    
    ifNotWhyNot ptposs 
      ("The propositional types " ^ string_of_proptype pt1 ^ 
	  " and " ^ string_of_proptype pt2 ^ " have no join")
      

let joinPropTypes cntxt =
  let rec loop = function
      []      -> definitelyNot "No join for zero propositional types"
    | [pt]    -> definitely pt
    | pt::pts -> 
	possCase' (loop pts)
	  (fun (join_pt, reqs) -> addReqs (joinPropType cntxt pt join_pt) reqs)
	  (fun rsns            -> NoBecause rsns)
  in
    loop


let rec eqMbnd cntxt subst1 subst2 (nm1, thry1) (nm2, thry2) =
  let (nm, subst1', subst2') = jointModelNameSubsts' nm1 nm2 subst1 subst2
  in let thry1' = substTheory subst1 thry1
  in let thry2' = substTheory subst2 thry2
  in let cntxt' = insertModelVariable cntxt nm thry1'
  in 
       if (eqTheory cntxt thry1' thry2') then
	 Some (cntxt', subst1', subst2')
       else
	 None


and eqMbnds' cntxt subst1 subst2 mbnds1 mbnds2 =
  match (mbnds1, mbnds2) with
      ([], []) -> Some (cntxt, subst1, subst2)
    | (mbnd1::rest1, mbnd2::rest2) ->
	begin
	  match eqMbnd cntxt subst1 subst2 mbnd1 mbnd2 with
	      Some (cntxt', subst1', subst2') -> 
		eqMbnds' cntxt' subst1' subst2' rest1 rest2
	    | None -> None
	end
    | _ -> None

and eqMbnds cntxt mbnds1 mbnds2 =
  eqMbnds' cntxt emptysubst emptysubst mbnds1 mbnds2

and eqTheory cntxt thry1 thry2 =
  (thry1 = thry2) || 
    begin
      match (hnfTheory cntxt thry1, hnfTheory cntxt thry2) with
	  (TheoryLambda(mbnd1, thry1b), 
	   TheoryLambda(mbnd2, thry2b)) ->
	    begin
	      match eqMbnd cntxt emptysubst emptysubst mbnd1 mbnd2 with
		  Some (cntxt', subst1, subst2) ->
		    let    thry1b' = substTheory subst1 thry1b
		    in let thry2b' = substTheory subst2 thry2b
		    in  eqTheory cntxt' thry1b' thry2b'
		| None -> false
	    end
		      
	| (TheoryLambda _, _ ) -> false
	| (_, TheoryLambda _) -> false

	| (thry1', thry2') ->
	    (* If we get this far, the two theories have
	       theorykind ModelTheoryKind, so we can reduce the
	       question to uses of checkModelConstraint.

	       T1 == T2 iff  ( X:T1 |- X : T2  &&  X:T2 |- X : T1 )
	    *)
	    let nm = wildModelName()
	    in let cntxt1 = insertModelVariable cntxt nm thry1'
	    in let cntxt2 = insertModelVariable cntxt nm thry1'
	    in let mdl = ModelName nm
	    in checkModelConstraint cntxt1 mdl thry1' thry2' &&
	      checkModelConstraint cntxt2 mdl thry2' thry1'
    end

(* Inputs must be a well-formed logical model, its inferred theory, and
   some other theory *)
and checkModelConstraint cntxt mdl1 thry1 thry2 = 
  match (hnfTheory cntxt thry1, hnfTheory cntxt thry2) with
      (TheoryArrow ((nm1, thry1a), thry1b), 
       TheoryArrow ((nm2, thry2a), thry2b)) ->
	let (nm, sub1, subs) = jointModelNameSubsts nm1 nm2
	in let thry1b' = substTheory sub1 thry1b
	in let thry2b' = substTheory sub1 thry1b
	in let cntxt' = insertModelVariable cntxt nm thry2a
	in 
	     (* contravariant domain *)
	     checkModelConstraint cntxt (ModelName nm) thry2a thry1a &&
	       (* covariant codomain *)
	       checkModelConstraint cntxt' (ModelApp(mdl1, ModelName nm)) 
	          thry1b' thry2b'

    | (Theory elems1, Theory elems2) ->
	let weakEq eqFun left = function
	    (** Checks for equality iff an optional value is given *)
	    None -> true
	  | Some right -> eqFun left right
	in let rec loop cntxt = function
	    [] -> true
	  | Declaration(nm, DeclSet(st2opt, knd2)) :: rest ->
	      begin
		match searchElems cntxt nm mdl1 elems1 with
		    Some (DeclSet (_,knd1)) -> 
		      let projAsSet = Basic(SLN(Some mdl1, nm), knd1)
		      in
			subKind cntxt knd1 knd2 &&
			  (* st2 might be "mdl1.nm", even if mdl1.nm doesn't
			     have a definition, so we want to compare it to
			     mdl1.nm and not to mdl1.nm's definition (if any) *)
			  weakEq (eqSet cntxt) projAsSet st2opt &&
			  let cntxt' = 
			    insertSetVariable cntxt nm knd1 (Some projAsSet)
			  in loop cntxt' rest
		  | _ -> false
	      end    
	  | Declaration(nm, DeclProp(prpopt2, pt2)) :: rest ->
	      begin
		match searchElems cntxt nm mdl1 elems1 with
		    Some (DeclProp(_, pt1)) ->
		      let projAsProp = Atomic(LN(Some mdl1, nm), pt1)
		      in
			subPropType cntxt pt1 pt2 &&
			  weakEq (eqProp cntxt) projAsProp prpopt2 &&
			  let cntxt' = 
			    insertPropVariable cntxt nm pt1 (Some projAsProp)
			  in loop cntxt' rest
		  | _ -> false
	      end

	  | Declaration(nm, DeclTerm(trmopt2, st2)) :: rest ->
	      begin
		match searchElems cntxt nm mdl1 elems1 with
		    Some (DeclTerm(_, st1)) ->
		      let projAsTerm = Var(LN(Some mdl1, nm))
		      in
			subSet cntxt st1 st2 &&
			  weakEq (eqTerm cntxt) projAsTerm trmopt2 &&
			  let cntxt' = 
			    insertTermVariable cntxt nm st1 (Some projAsTerm)
			  in loop cntxt' rest
		  | _ -> false
	      end

          | Declaration(nm, DeclModel(thry2)) :: rest ->
	      begin
		match searchElems cntxt nm mdl1 elems1 with
		    Some (DeclModel thry1) ->
		      let projAsModel = ModelProj(mdl1, nm)
		      in
			(checkModelConstraint cntxt projAsModel thry1 thry2 &&
			    let cntxt' = 
			      insertModelVariable cntxt nm thry1
			    in loop cntxt' rest)
		  | _ -> false
	      end
		
	  | Comment _ :: rest -> loop cntxt rest

          | Declaration(nm, DeclSentence (mbnds2, prp2)) :: rest ->
	      begin
		match searchElems cntxt nm mdl1 elems1 with
		    Some (DeclSentence(mbnds1, prp1)) ->
		      begin
			match eqMbnds cntxt mbnds1 mbnds2 with
			    Some (cntxt'', subst1, subst2) -> 
			      let prp1' = substProp subst1 prp1
			      in let prp2' = substProp subst2 prp2
			      in
				   eqProp cntxt'' prp1' prp2' && 
				     loop cntxt rest
			  | _ -> false
		      end
		  | _ -> false
	      end

	  | Declaration(nm, DeclTheory _) :: rest ->
	      E.noNestedTheoriesError nm

	in loop cntxt elems2

    | _ -> false (* No abstract Theory variables *)

(* coerce: cntxt -> term -> set -> set -> trm option *)
(**
     coerce trm st1 st2 coerces trm from the set st1 to the set st2
       using subin and subout.
     Preconditions: trm is in st1 and all arguments are fully-annotated.
     Returns:  None       if trm cannot be turned into a value in set st2.
               Some trm'  if we can obtain the term trm'
*)
let rec coerce cntxt trm st1 st2 = 
   if (subSet cntxt st1 st2) then
      (** Short circuting, since the identity coercion is (we hope)
          the common case *)
      Some trm
   else
      let    st1' = hnfSet cntxt st1
      in let st2' = hnfSet cntxt st2
   
      in match (trm, st1', st2') with
	| ( _, Subset ( ( _, st1'1 ) , _ ),
               Subset ( ( _, st2'1 ) , _ ) ) -> 

	    (** Try an implicit out-of-subset conversion *)
           (match ( coerce cntxt ( Subout(trm,st1) ) st1'1 st2 ) with
              Some trm' -> Some trm'
            | None -> (** That didn't work, so try an implicit 
                          into-subset conversion *)
                      (match (coerce cntxt trm st1 st2'1) with
                        Some trm' -> Some ( Subin ( trm', st2 ) )
                      | None      -> None ) )

        | ( _, Subset( ( _, st1'1 ), _ ), _ ) -> 
	    (** Try an implicit out-of-subset conversion *)
            coerce cntxt ( Subout(trm,st2) ) st1'1 st2 

        | ( _, _, Subset( ( _, st2'1 ), _ ) ) -> 
	    (** Try an implicit into-subset conversion *)
            ( match (coerce cntxt trm st1 st2'1) with
                Some trm' -> Some ( Subin ( trm', st2 ))
              | None      -> None )

        | ( Tuple trms, Product sts1, Product sts2 ) ->
            let rec loop subst2 = function 
                ([], [], []) -> Some []
              | ([], _, _)   -> None
              | (trm::trms, (nm1, st1)::sts1, (nm2, st2)::sts2) ->
		  if (isWild nm1) then
		    let st2' = substSet subst2 st2
		    in let subst2' = insertTermvar subst2 nm2 trm
                    in (match (coerce cntxt trm st1 st2', 
			      loop subst2' (trms,sts1,sts2)) with
			(Some trm', Some trms') -> Some (trm'::trms')
                      | _ -> None )
		  else
		    (* This case shouldn't ever arise; tuples naturally
		       yield non-dependent product types.  
		       But just in case, ...*)
		    (E.tyGenericWarning
			("coerce: dependent->? case for products arose. " ^
			    "Maybe it should be implemented after all");
		     None)
	      | _ -> failwith "Impossible: Logicrules.coerce 1"
            in (match (loop emptysubst (trms, sts1, sts2)) with
                  Some trms' -> Some (Tuple trms')
                | None -> None)

        | _ -> None

let rec coerceFromSubset cntxt trm st = 
   match (hnfSet cntxt st) with
      Subset( ( _, st1 ), _ ) -> 
         coerceFromSubset cntxt (Subout(trm, st)) st1
    | st' -> (trm, st')

(*
 Never mind.  We're not doing automatic EquivCoerce insertion...yet.

let rec coerceProp cntxt prp pt1 pt2 =
   if (subPropType cntxt pt1 pt2) then
      (** Short circuting, since the identity coercion is (we hope)
          the common case *)
      Some trm
   else
     match (prp, pt1, pt2) with
	 (_, PropArrow(s1a, PropArrow(s1b, StableProp), EquivProp s2))
*)
