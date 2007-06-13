open Name
open Logic
module E = Error

exception TooFast

(*****************)
(** {2 Contexts} *)
(*****************)

(*******************)
(** {3 Definition} *)
(*******************)

(* A context contains three components:
     1) The traditional typing context, containing mappings from bound
        variables to their sorts (and, optionally a value for this variable.)
        We also keep a timestamp recording when each variable entered
        the context; see below for more information.
     2) Implicit type (or, more generally, kind/theory/etc.) information
        declared by the user.  If a bound variable is introduced without
        an explicit classifier or definition, we look here to see if the
        variable name was previously declared to range over a certain sort.
        (For convenience, we use the same datatype, but in
        these we know there will never be a value specified for the variable.)
     3) A renaming mapping variables to variables.  The typechecker removes
        shadowing whenever possible by renaming bound variables, and this
        mapping keeps track of what renamings are currently being done.
        If a bound variable is not in the domain of this mapping, it is not
        being renamed.
*)
type timestamp = int

type context = {bindings : (declaration * timestamp) NameMap.t;
		            implicits : declaration NameMap.t;
	              renaming  : name NameMap.t;
	              lastthy : timestamp}

let emptyContext = {bindings = NameMap.empty; 
                    implicits = NameMap.empty;
		                renaming = NameMap.empty;
		                lastthy = max_int}

let displayContext cntxt = 
  NameMap.iter 
    (fun n (decl,_) -> 
        print_endline(string_of_theory_element(Declaration(n,decl))))
    cntxt.bindings

(**************)
(* {3 Lookup} *)
(**************)

let lookupImplicit cntxt nm = 
  try Some (NameMap.find nm cntxt.implicits) with
      Not_found -> None

let lookupId cntxt nm =
  try Some (fst (NameMap.find nm cntxt.bindings)) with
      Not_found -> None

let lookupTimestamp cntxt nm =
  snd (NameMap.find nm cntxt.bindings)

let isUnbound cntxt nm =
  not (NameMap.mem nm cntxt.bindings)

let lookupLastThy cntxt = cntxt.lastthy

(*****************)
(* {3 Insertion} *)
(*****************)


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
let timestamp_counter = ref 0

let doInsert validator idString cntxt nm info =
  if validator nm then
    if isUnbound cntxt nm then
      (timestamp_counter := !timestamp_counter + 1;
	     {cntxt with 
	        bindings = NameMap.add nm (info, !timestamp_counter) cntxt.bindings})
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

let insertSentenceVariable cntxt nm mbnds prp =
  doInsert validSentenceName "sentence" cntxt nm (DeclSentence(mbnds,prp))

let markThy cntxt =
  {cntxt with lastthy = !timestamp_counter}

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
  let nm' = refresh nm in 
    ({cntxt with renaming = NameMap.add nm nm' cntxt.renaming}, nm')

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

(* the primed version takes in an initial substitution and extends
   in as it goes along, and also returns the final substitution at
   the point where the desired element occurs.  The idea is that we
   can stop the search when we find one element, and then restart
   a new search (with the right substitution) right after that point.
   
   If you just want to search once, from the beginning, call the
   unprimed version   
*)

let rec searchElems' subst0 cntxt nm' mdl = 
  let rec loop subst = function 
      [] -> subst, None
    | elem :: rest ->
	match substTheoryElt subst elem with
	  | Declaration(nm, (DeclSet(_,knd) as decl)) ->
	      if (nm = nm') then
		     subst, Some decl (** XXX Or selfify? *)
	      else 
		loop (insertSetvar subst nm 
			 (Basic(SLN(Some mdl, nm), knd)))
		  rest
	  | Declaration(nm, (DeclProp(_,pt) as decl)) ->
	      if (nm = nm') then
		     subst, Some decl
	      else 
		loop (insertPropvar subst nm 
			 (Atomic(LN(Some mdl, nm), pt)))
		  rest
	  | Declaration(nm, (DeclTerm _ as decl))  -> 
	      if (nm = nm') then
		     subst, Some decl
	      else 
		loop (insertTermvar subst nm (Var(LN(Some mdl, nm))))
		  rest
	  | Declaration(nm, (DeclModel _ as decl) ) ->
	      if (nm = nm') then
		     subst, Some decl
	      else 
		loop (insertModelvar subst nm (ModelProj(mdl, nm))) 
		  rest
	  | Declaration(nm, (DeclSentence _ as decl)) ->
	      if (nm = nm') then
		     subst, Some decl
	      else 
		loop subst rest
	  | Declaration(nm, (DeclTheory _ as decl)) ->
	      if (nm = nm') then
		     subst, Some decl
	      else 
		loop (insertTheoryvar subst nm (TheoryProj(mdl,nm)))
		  rest
	  | Comment _  -> 
	      (** Comments cannot be searched for, currently *)
	      loop subst rest
  in
    loop subst0
    
let searchElems cntxt nm' mdl elems = 
    let (_, answer) = searchElems' emptysubst cntxt nm' mdl elems
    in answer

(**************************************)
(** {3 Type and Theory Normalization} *)
(**************************************)

(** Head-normalization of a theory: replacing theory names by
    definitions, and reducing top-level lambda applications.

    Postcondition:  The returned theory is neither a variable nor
    an application (since we don't have abstract theory variables).
*)
(*
    let rec hnfTheory cntxt = function
    TheoryName nm ->
      begin
	match lookupId cntxt nm with
	    Some(DeclTheory (thry, _)) -> hnfTheory cntxt thry
	  | Some _ -> failwith ("hnfTheory 1a " ^ string_of_name nm)
	  | None -> failwith ("hnfTheory 1b " ^ string_of_name nm)
      end
  | TheoryApp (thry, mdl) ->
      begin
	match hnfTheory cntxt thry with
	    TheoryLambda((nm,_), thry2) ->
	      let subst = insertModelvar emptysubst nm mdl
	      in hnfTheory cntxt (substTheory subst thry2)
	  | _ -> failwith "hnfTheory 2"
      end
  | TheoryProj(mdl, nm) ->
      begin
	match hnfTheory cntxt (modelToTheory cntxt mdl) with
	    Theory elems ->
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclTheory (thry,_)) -> thry
		  | _ -> failwith "hnfTheory 3"
	      end
	  | _ -> failwith "hnfTheory 4"
      end
  | thry -> thry
*)

let rec hnfTheory cntxt thry =
    begin
        match hnfTheory1 cntxt thry with
            Some thry' -> hnfTheory cntxt thry'
          | None -> thry
    end 

and hnfTheory1 cntxt = function
      TheoryName nm ->
        begin
  	match lookupId cntxt nm with
  	    Some(DeclTheory (thry, _)) ->  Some thry
  	  | Some _ -> failwith ("hnfTheory1 1a " ^ string_of_name nm)
  	  | None -> failwith ("hnfTheory1 1b " ^ string_of_name nm)
        end
    | TheoryApp (thry, mdl) ->
        begin
  	        match (hnfTheory1 cntxt thry, thry) with
  	        (Some thry',_) -> Some (TheoryApp(thry', mdl))
  	        | (None, TheoryLambda((nm,_), thry2)) ->
  	            let subst = insertModelvar emptysubst nm mdl
  	        in Some (substTheory subst thry2)
  	        | _ -> failwith "hnfTheory1 2"
        end
    | TheoryProj(mdl, nm) ->
        begin
  	        match hnfTheory cntxt (modelToTheory cntxt mdl) with
  	        Theory elems ->
  	            begin
  		            match searchElems cntxt nm mdl elems with
  		            Some (DeclTheory (thry,_)) -> Some thry
  		            | _ -> failwith "hnfTheory1 3"
  	            end
  	        | _ -> failwith "hnfTheory1 4"
        end
    | thry -> None
    
(* cntxt -> model -> theory *)
(** Assumes that the given model is well-formed.
*)
and modelToTheory cntxt = function
    ModelName nm ->
      begin
	match (lookupId cntxt nm) with
	    Some(DeclModel thry) -> thry
	  | _ -> failwith "modelToTheory 1"
      end
  | ModelProj (mdl, nm) -> 
      begin
	match hnfTheory cntxt (modelToTheory cntxt mdl) with
	    Theory elems ->
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclModel thry) -> thry
		  | _ -> failwith "modelToTheory 2"
	      end
	  | _ -> failwith "modelToTheory 3"
      end
  | ModelApp (mdl1, mdl2) ->
      begin
	match hnfTheory cntxt (modelToTheory cntxt mdl1) with
	    TheoryArrow((nm, thry1), thry2) ->
	      let subst = insertModelvar emptysubst nm mdl2
	      in substTheory subst thry2
	  | _ -> failwith "modelToTheory 4"
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
	  | _ -> failwith "hnfSet 1"
      end

  | Basic (SLN ( Some mdl, nm), _) as orig_set -> 
      begin
        (** XXX: Shouldn't modelToTheory be applying the context renaming
	    if this is a model variable? *)
	match hnfTheory cntxt (modelToTheory cntxt mdl) with
	    Theory elems -> 
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclSet(Some st, _)) -> hnfSet cntxt st
		  | Some (DeclSet(None, _))    -> orig_set
		  | _ -> failwith "hnfSet 2"
	      end
	  | _ -> failwith "hnfSet 3"
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
	  | _ -> failwith "hnfTerm 1"
      end

  | Var (LN ( Some mdl, nm)) as orig_term -> 
      begin
	match hnfTheory cntxt (modelToTheory cntxt mdl) with
	    Theory elems -> 
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclTerm(Some trm, _)) -> hnfTerm cntxt trm
		  | Some (DeclTerm(None, _))    -> orig_term
		  | _ -> failwith "hnfTerm 2"
	      end
	  | _ -> failwith "hnfTerm 3"
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

  | Case(trm1, ty, arms, ty2) ->
      begin
	match (hnfTerm cntxt trm1) with
	    Inj(lbl, None) ->
	      begin
		match (List.find (fun (l,_,_) -> l = lbl) arms) with
		    (_, None, trm2) -> hnfTerm cntxt trm2
		  | _ -> failwith "hnfTerm 4"
	      end
	  | Inj(lbl, Some trm1') ->
	      begin
		match (List.find (fun (l,_,_) -> l = lbl) arms) with
		    (_, Some (nm,_), trm2) -> 
		      let sub = insertTermvar emptysubst nm trm1'
		      in
			hnfTerm cntxt (subst sub trm2)
		  | _ -> failwith "hnfTerm 5"
	      end
	  | trm1' -> Case(trm1', ty, arms, ty2)
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

  | Assure(_,_,trm,_) -> hnfTerm cntxt trm

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
	  | _ -> failwith "hnfProp 1"
      end

  | Atomic (LN ( Some mdl, nm), _) as orig_prop -> 
      begin
	match hnfTheory cntxt (modelToTheory cntxt mdl) with
	    Theory elems -> 
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclProp(Some prp, _)) -> hnfProp cntxt prp
		  | Some (DeclProp(None, _))    -> orig_prop
		  | _ -> failwith "hnfProp 2"
	      end
	  | _ -> failwith "hnfProp 3"
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
		  | _ -> failwith "hnfProp 4"
	      end
	  | Inj(lbl, Some trm1') ->
	      begin
		match (List.find (fun (l,_,_) -> l = lbl) arms) with
		    (_, Some (nm,_), prp2) -> 
		      let sub = insertTermvar emptysubst nm trm1'
		      in
			hnfProp cntxt (substProp sub prp2)
		  | _ -> failwith "hnfProp 5"
	      end
	  | trm1' -> PCase(trm1', ty, arms)
      end

  | PLet((nm,_),trm1,prp2) ->
          let sub = insertTermvar emptysubst nm trm1
          in
    	hnfProp cntxt (substProp sub prp2)
    	
  | PAssure(_, _, prp) -> hnfProp cntxt prp

  | prp -> prp

(***************)
(** {2 Typeof} *)
(***************)

(** See also modelToTheory above *)

let typeOfProj cntxt bnds trm n =
  let rec loop k subst = function
      [] -> raise Impossible
    | (nm,ty) :: rest ->
	if (k = n) then
	  Some (substSet subst ty)
	else
	  loop (k+1) ( insertTermvar subst nm (Proj(k,trm)) ) rest
  in let len = List.length bnds
  in 
       if ( (n < 0) || (n >= len) ) then
	 None
       else 
	 loop 0 emptysubst bnds
  

let rec typeOf cntxt trm = 
  match trm with
    | EmptyTuple -> Unit

    | BTrue | BFalse -> Bool
	
    | Var (LN ( None, nm )) ->
	begin
	  match (lookupId cntxt nm) with
	      Some (DeclTerm(_, ty)) -> ty
	    | _ -> failwith ("typeOf 1: " ^ string_of_name nm)
	end

    | Var (LN ( Some mdl, nm)) -> 
      begin
	match hnfTheory cntxt (modelToTheory cntxt mdl) with
	    Theory elems -> 
	      begin
		match searchElems cntxt nm mdl elems with
		    Some (DeclTerm(_, ty)) -> ty
		  | _ -> failwith "typeOf 2"
	      end
	  | _ -> failwith "typeOf 3"
      end

    | Tuple trms ->
	Product (List.map (fun t -> (wildName(), typeOf cntxt t)) trms)

    | Proj (n, trm) ->
	begin
	  match hnfSet cntxt (typeOf cntxt trm) with
	      Product bnds -> 
		begin
		  match (typeOfProj cntxt bnds trm n) with
		      Some ty -> ty
		    | None -> failwith "typeOf 4"
		end
	    | _ -> failwith "typeOf 5"
	end
	  
    | App (trm1, trm2) ->
	begin
	  match hnfSet cntxt (typeOf cntxt trm1) with
	      Exp(nm,_,ty) ->
		let subst = insertTermvar emptysubst nm trm2
		in substSet subst ty
	    | _ -> failwith "typeOf 6"
	end

    | Lambda((nm1,ty2),trm3) ->
	let cntxt' = insertTermVariable cntxt nm1 ty2 None
	in let ty3 = typeOf cntxt' trm3
	in Exp(nm1, ty2, ty3)

    | The((_,ty),_) -> ty

    | Inj(lbl, None) -> Sum [(lbl,None)]

    | Inj(lbl, Some trm) -> Sum [(lbl, Some (typeOf cntxt trm))]


    | RzQuot trm -> 
	begin
	  match  hnfSet cntxt (typeOf cntxt trm) with
	      Rz ty -> ty
	    | _ -> failwith "typeOf 7"
	end

    | Quot (trm, prp) -> Quotient(typeOf cntxt trm, prp)

    | Subin (_, bnd, prp) -> Subset(bnd,prp)

    | Case(_, _, _, ty) -> ty
    | RzChoose (_, _, _, ty) -> ty
    | Choose (_, _, _, _, ty) -> ty
    | Let (_, _, _, ty) -> ty
    | Subout(_, ty) -> ty
    | Assure(_, _, _, ty) -> ty


(**********************************************)
(** {2 Equivalence, Subtyping, and Coercions} *)
(**********************************************)

(****************************************)
(** {4 Sets: equivalence and subtyping} *)
(****************************************)

let eqArms cntxt substFn eqFn eqSetFn arms1 arms2 =
  let rec loop = function
      ([], []) -> []

    | ((lbl1, None, val1)::rest1, (lbl2, None, val2)::rest2) when lbl1 = lbl2 ->
        eqFn cntxt val1 val2 @ loop (rest1, rest2)

    | ((lbl1, Some (nm1,st1), val1) :: rest1, 
       (lbl2, Some (nm2,st2), val2) :: rest2 ) when lbl1 = lbl2 ->
        let reqs1 = eqSetFn cntxt st1 st2
	in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	in let val1' = substFn sub1 val1
	in let val2' = substFn sub2 val2
	in let cntxt' = insertTermVariable cntxt nm1 st1 None
	in let prereqs2 = eqFn cntxt' val1' val2'
	in let reqs2 = List.map (fForall (nm,st1)) prereqs2
	in let reqs3 = loop(rest1, rest2)
	in reqs1 @ reqs2 @ reqs3

    | _ -> raise (E.TypeError ["Different numbers of arms"])

  in let order (lbl1, _, _) (lbl2, _, _) = compare lbl1 lbl2
  in let arms1' = List.sort order arms1
  in let arms2' = List.sort order arms2
  in 
       loop (arms1', arms2')


(* eqSet': bool -> cntxt -> set -> set ->  *)
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
     try
       (** Short circuting for (we hope) the common case *)
       if (s1 = s2) then
	 []
       else
	 (** Head-normalize the two sets *)
	 let    s1' = hnfSet cntxt s1
         in let s2' = hnfSet cntxt s2
	   
         in if (s1' = s2')  then
	     []
	   else
             (match (s1',s2') with
         (Empty, _) when do_subset -> 
             (* The empty set is a subset of every other set  *)
                []
		   | ( Basic (SLN(mdlopt1, nm1), _),
		 Basic (SLN(mdlopt2, nm2), _) ) when (nm1 = nm2) -> 
                   (** Neither has a definition *)
		   eqModelOpt cntxt mdlopt1 mdlopt2 
		     
 	       | ( Product ss1, Product ss2 ) -> 
                   cmpProducts cntxt (ss1,ss2)
		   
             | ( Sum lsos1, Sum lsos2 )     -> 
	         let reqs1 = subSum do_subset cntxt (lsos1, lsos2) 
		 in let reqs2 = 
		   if do_subset then [] else subSum false cntxt (lsos2, lsos1)
		 in reqs1 @ reqs2
		   
             | ( Exp( nm1, st3, st4 ), Exp ( nm2, st5, st6 ) ) ->
		 (** Domains are now compared contravariantly. *)
		 let reqs1 = cmp st5 st3
		 in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	         in let st4' = substSet sub1 st4
	         in let st6' = substSet sub2 st6
		 in let cntxt' = insertTermVariable cntxt nm st5 None
	         in let prereqs2 = eqSet' do_subset cntxt' st4' st6'
		 in let reqs2 = List.map (fForall (nm,st3)) prereqs2
		 in reqs1 @ reqs2
			  
	     | ( Subset( (nm1,st1),  p1 ), 
	       Subset( (nm2,st2), p2 ) )->
		 let reqs1 = cmp st1 st2
	           (** Alpha-vary the propositions so that they're using the
                       same (fresh) variable name *)
		 in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	         in let p1' = substProp sub1 p1
	         in let p2' = substProp sub2 p2
		 in let cntxt' = insertTermVariable cntxt nm st1 None
	         in let prereqs2 = eqProp cntxt' p1' p2'  
		 in let reqs2 = List.map (fForall (nm,st1)) prereqs2
		 in reqs1 @ reqs2
			  
             | ( Quotient ( st3, eqvlnce3 ), 
	       Quotient ( st4, eqvlnce4 ) ) -> 
                 (** Quotient is invariant *)
                 let reqs1 = eqSet cntxt st3 st4  
		 in let reqs2 = eqProp cntxt eqvlnce3 eqvlnce4
		 in reqs1 @ reqs2
		   
             | ( SApp (st3, trm3), SApp (st4, trm4) ) ->
		 (* XXX: this is a place where we would presumably
		    emit an obligation.  The way I'll implement this
		    is for eqTerm to always succeed, but possibly
		    return the obligation that trm3 = trm4, if it's
		    not immediately provable. *)
		 let reqs1 = eqSet cntxt st3 st4
		 in let reqs2 = eqTerm cntxt trm3 trm4 
		 in reqs1 @ reqs2
		   
             | ( Rz st3, Rz st4 ) -> 
                 (** RZ seems like it should be invariant.  *)
		 (** XXX Is it? *)
                 eqSet cntxt st3 st4  
		   
             | (_,_) -> raise (E.TypeError ["Incompatible sets"]) )

     with
	 E.TypeError msgs -> 
	   E.generalizeError msgs 
	     ("...in comparing sets " ^ string_of_set s1 ^ " and " ^
		 string_of_set s2)
	     
	   
      and cmpProducts' cntxt subst1 subst2 = function
       ( [] , [] ) -> []
	 
     | ( (nm1, s1) :: s1s, (nm2, s2) :: s2s) -> 
	 let s1' = substSet subst1 s1
	 in let s2' = substSet subst2 s2
	 in let reqs1 = eqSet' do_subset cntxt s1' s2'
	 in let (nm, subst1', subst2') = 
	   jointNameSubsts' nm1 nm2 subst1 subst2
	 in let cntxt' = insertTermVariable cntxt nm s1 None
	 in let prereqs2 = cmpProducts' cntxt' subst1' subst2' (s1s,s2s)
	 in let reqs2 = List.map (fForall (nm,s1')) prereqs2
	 in  reqs1 @ reqs2
	     
     | (_,_) -> raise (E.TypeError ["Products have different lengths"])
	 
   and cmpProducts cntxt lst = cmpProducts' cntxt emptysubst emptysubst lst
     
   and subSum do_subset cntxt = function
       ( [], _ ) -> []
     | ((l1,None   )::s1s, s2s) ->
	 begin
	   try
	     match (List.assoc l1 s2s) with
		 None -> subSum do_subset cntxt (s1s, s2s)
	       | _ -> raise (E.TypeError ["Disagreement whether " ^ 
					   string_of_label l1 ^ 
					   "carries a value."])
					   
	   with 
	       Not_found ->
		 raise (E.TypeError ["Missing " ^ string_of_label l1 ^
				      " component of sum"]) 
	 end
     | ((l1,Some s1)::s1s, s2s) -> 
	 begin
	   try
	     match (List.assoc l1 s2s) with
		 Some s2 -> 
		   ( eqSet' do_subset cntxt s1 s2 ) 
                   @ ( subSum do_subset cntxt (s1s,s2s) )
	       |  _ -> raise (E.TypeError ["Disagreement whether " ^ 
					    string_of_label l1 ^ 
					    "carries a value."])
	   with
	       Not_found ->
		 raise (E.TypeError ["Missing " ^ string_of_label l1 ^
				      " component of sum"]) 
	 end
   in cmp

and equivToArrow ty =
  PropArrow(wildName(), ty, PropArrow(wildName(), ty, StableProp))

and eqPropType' do_subset cntxt pt1 pt2 = 
  try
    (** Short circuting for (we hope) the common case *)
    if (pt1 = pt2) then
      []
    else
      match (pt1, pt2) with
        | ( StableProp, Prop ) -> []
	    
        | ( EquivProp st1, EquivProp st2) -> 
	    eqSet' do_subset cntxt st2 st1
	      
        | ( EquivProp st1, _ ) when do_subset ->
	    eqPropType' true cntxt (equivToArrow st1) pt2
	      
        | ( PropArrow( nm1, st1, pt1 ), PropArrow ( nm2, st2, pt2 ) ) ->
	    let reqs1 = eqSet' do_subset cntxt st2 st1
	    in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	    in let pt1' = substProptype sub1 pt1
	    in let pt2' = substProptype sub2 pt2
	    in let cntxt' = insertTermVariable cntxt nm st1 None
	    in let prereqs2 = eqPropType' do_subset cntxt' pt1' pt2'
	    in let reqs2 = List.map (fForall (nm,st1)) prereqs2
	    in reqs1 @ reqs2
	      
	| _ -> raise (E.TypeError ["Incompatible proposition types"])
  with
      E.TypeError msgs -> 
	E.generalizeError msgs
	  ("...in comparison of " ^ string_of_proptype pt1 ^ " and " ^
	      string_of_proptype pt2)

and subPropType cntxt pt1 pt2 = eqPropType' true cntxt pt1 pt2

and eqPropType cntxt pt1 pt2 = eqPropType' false cntxt pt1 pt2

and eqKind' do_subset cntxt k1 k2 = 
  try
    if (k1 = k2) then
    (** Short circuting for (we hope) the common case *)
      []
    else
      match (k1, k2) with
          ( KindArrow( nm1, st1, kk1 ), KindArrow ( nm2, st2, kk2 ) ) ->
	    let reqs1 = eqSet' do_subset cntxt st2 st1 
	    in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	    in let kk1' = substSetkind sub1 kk1
	    in let kk2' = substSetkind sub2 kk2
	    in let prereqs2 = eqKind' do_subset cntxt kk1' kk2'
	    in let reqs2 = List.map (fForall (nm,st1)) prereqs2
	    in reqs1 @ reqs2
		   
	| _ -> E.tyGenericError "Incompatible kinds"
  with 
      E.TypeError msgs -> 
	E.generalizeError msgs
	  ("...in comparing kinds " ^ string_of_kind k1 ^ 
	       " and " ^ string_of_kind k2)

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
  try
    if (prp1 = prp2) then
      (* short-circuiting *)
      []
    else
      match (hnfProp cntxt prp1, hnfProp cntxt prp2) with
	  (False, False) -> []
	| (True, True) -> []

	| (Atomic(LN(None, nm1), _), Atomic(LN(None, nm2), _) ) when nm1=nm2 -> 
	    []

	| (Atomic(LN(Some mdl1, nm1), _), 
	  Atomic(LN(Some mdl2, nm2), _)) when nm1 = nm2 ->
	    eqModel cntxt mdl1 mdl2
	      
	| (And prps1, And prps2) -> eqProps cntxt prps1 prps2

	| (Or prps1, Or prps2 )-> eqDisjuncts cntxt prps1 prps2
	      
	| (Imply(prp1a, prp1b), Imply(prp2a, prp2b)) 
	| (Iff(prp1a, prp1b), Iff(prp2a, prp2b)) ->
	    eqProp cntxt prp1a prp2a @ 
	      eqProp cntxt prp1b prp2b
	      
	| (Forall((nm1,st1), prp1), Forall((nm2,st2), prp2)) 
	| (Exists((nm1,st1), prp1), Exists((nm2,st2), prp2)) 
	| (Unique((nm1,st1), prp1), Unique((nm2,st2), prp2)) 
	| (PLambda((nm1,st1), prp1), PLambda((nm2,st2), prp2)) ->
	    let reqs1 = eqSet cntxt st1 st2
	    in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	    in let prp1' = substProp sub1 prp1
	    in let prp2' = substProp sub2 prp2
	    in let cntxt' = insertTermVariable cntxt nm st1 None
	    in let prereqs2 = eqProp cntxt' prp1' prp2'
	    in let reqs2 = List.map (fForall (nm,st1)) prereqs2
	    in reqs1 @ reqs2
	      
	| (Not prp1, Not prp2) ->
	    eqProp cntxt prp1 prp2
	      
	| (Equal(ty1, trm1a, trm1b), Equal(ty2, trm2a, trm2b)) ->
	    eqSet cntxt ty1 ty2 @
	      eqTerm cntxt trm1a trm2a @
	      eqTerm cntxt trm1b trm2b

	| (PApp(prp1, trm1), PApp(prp2, trm2)) ->
	    eqProp cntxt prp1 prp2 @
	      eqTerm cntxt trm1 trm2

	| (IsEquiv(prp1,st1), IsEquiv(prp2,st2)) ->
	    eqProp cntxt prp1 prp2 @
	      eqSet cntxt st1 st2 

	| (PCase(trm1, ty1, arms1), PCase(trm2, ty2, arms2)) ->
	    eqTerm cntxt trm1 trm2 @
	      eqSet cntxt ty1 ty2 @
	      eqArms cntxt substProp eqProp eqSet arms1 arms2
	      
	(* 
	   hnfProp removes PAssures
	   
        | (PAssure(Some (nm1, st1), prp1a, prp1b), 
	   PAssure(Some (nm2, st2), prp2a, prp2b)) ->
	  let reqs1 = eqSet cntxt st1 st2
	  in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	  in let prp1a' = substProp sub1 prp1a
	  in let prp2a' = substProp sub2 prp2a
	  in let prp1b' = substProp sub1 prp1b
	  in let prp2b' = substProp sub2 prp2b
	  in let cntxt' = insertTermVariable cntxt nm st1 None
	  in 
	       eqProp cntxt' prp1a' prp2a' &&
		 eqProp cntxt' prp1b' prp2b' 

        | (PAssure(None, prp1a, prp1b),
  	   PAssure(None, prp2a, prp2b)) ->
	   eqProp cntxt prp1a prp2a &&
	   eqProp cntxt prp2a prp2b
	*)

      | _ -> raise (E.TypeError ["Incompatible propositions"]) 
  with
      E.TypeError msgs -> 
	E.generalizeError msgs 
	  ("...in comparison of propositions " ^ string_of_prop prp1 ^
	       " and " ^ string_of_prop prp2) 	    

and eqProps cntxt prps1 prps2 = 
  try  
    List.flatten (List.map2 (eqProp cntxt) prps1 prps2)  
  with
      Invalid_argument _ -> 
	raise (E.TypeError ["Different numbers of propositions"])

and eqPropOpt cntxt prpopt1 prpopt2 =
  match prpopt1, prpopt2 with
  | None, None -> []
  | Some prp1, Some prp2 -> eqProp cntxt prp1 prp2
  | _ -> raise (E.TypeError [])

and eqDisjunct cntxt (lbl1, prp1) (lbl2, prp2) =
  if lbl2 = lbl2 then
    eqProp cntxt prp1 prp2
  else
    raise (E.TypeError ["Incompatible labels on disjuncts"])
	                             
and eqDisjuncts cntxt disj1 disj2 = 
  let disj1 = List.sort (fun (lbl1, _) (lbl2, _) -> compare lbl1 lbl2) disj1 in
  let disj2 = List.sort (fun (lbl1, _) (lbl2, _) -> compare lbl1 lbl2) disj2 in
    try  
      List.flatten (List.map2 (eqDisjunct cntxt) disj1 disj2)
    with
	Invalid_argument _ -> 
	  raise (E.TypeError ["Different numbers of disjuncts"])
	                             
and eqTerm cntxt trm1 trm2 = 
  if (trm1 = trm2) then
    []
  else
    match (hnfTerm cntxt trm1, hnfTerm cntxt trm2) with
	(EmptyTuple, EmptyTuple) -> []
      | (Var(LN(None, nm1)), Var(LN(None, nm2))) when nm1 = nm2 -> []
      | (Inj(lbl1, None), Inj(lbl2, None)) when lbl1 = lbl2  -> []
      | (Var(LN(Some mdl1, nm1)), Var(LN(Some mdl2, nm2)))  when nm1 = nm2 ->
	  eqModel cntxt mdl1 mdl2
	    
      | (Tuple trms1, Tuple trms2) -> 
	  eqTerms cntxt trms1 trms2
	    
      | (Proj(n1, trm1), Proj(n2, trm2)) when n1 = n2 ->
	  eqTerm cntxt trm1 trm2
	    
      | (App(trm1a, trm1b), App(trm2a, trm2b)) ->
	  eqTerm cntxt trm1a trm2a @
	    eqTerm cntxt trm1b trm2b
	    
      | (Lambda((nm1,ty1),trm1), Lambda((nm2,ty2),trm2)) ->
	  let reqs1 = eqSet cntxt ty1 ty2 
	  in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	  in let trm1' = subst sub1 trm1
	  in let trm2' = subst sub2 trm2
	  in let cntxt' = insertTermVariable cntxt nm ty1 None
	  in let prereqs2 = eqTerm cntxt' trm1' trm2'
	  in let reqs2 = List.map (fForall (nm,ty1)) prereqs2 
	  in reqs1 @ reqs2

      | (The((nm1,ty1),prp1), The((nm2,ty2),prp2)) ->
	  let reqs1 = eqSet cntxt ty1 ty2
	  in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	  in let prp1' = substProp sub1 prp1
	  in let prp2' = substProp sub2 prp2
	  in let cntxt' = insertTermVariable cntxt nm ty1 None
	  in let prereqs2 = eqProp cntxt' prp1' prp2'
	  in let reqs2 = List.map (fForall (nm,ty1)) prereqs2
	  in reqs1 @ reqs2

      | (Inj(lbl1, Some trm1), Inj(lbl2, Some trm2)) when lbl1 = lbl2 ->
	  eqTerm cntxt trm1 trm2

      | (Case(trm1, ty1, arms1, ty3), Case(trm2, ty2, arms2, ty4)) ->
	  eqTerm cntxt trm1 trm2 @
	    eqSet cntxt ty1 ty2 @
	    eqArms cntxt subst eqTerm eqSet arms1 arms2 @
	    eqSet cntxt ty3 ty4

      | (RzQuot trm1, RzQuot trm2) ->
	  eqTerm cntxt trm1 trm2

(* hnfTerm removes lets
      | (Let     ((nm1, ty1a), trm1a, trm1b, ty1b), 
	 Let     ((nm2, ty2a), trm2a, trm2b, ty2b))  *)
      | (RzChoose((nm1, ty1a), trm1a, trm1b, ty1b), 
	 RzChoose((nm2, ty2a), trm2a, trm2b, ty2b)) ->
	  let reqs1 = eqSet cntxt ty1a ty2a 
	  in let reqs2 = eqTerm cntxt trm1a trm2a
	  in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	  in let trm1b' = subst sub1 trm1b
	  in let trm2b' = subst sub2 trm2b
	  in let cntxt' = insertTermVariable cntxt nm ty1a None
	  in let prereqs3 = eqTerm cntxt' trm1b' trm2b'
	  in let reqs3 = List.map (fForall (nm, ty1a)) prereqs3
	  in let reqs4 = eqSet cntxt ty1b ty2b
	  in reqs1 @ reqs2 @ reqs3 @ reqs4

      | (Quot(trm1,prp1), Quot(trm2,prp2)) ->
	  eqTerm cntxt trm1 trm2 @
	    eqProp cntxt prp1 prp2

      | (Choose((nm1,ty1a),prp1,trm1a,trm1b,ty1b),
	 Choose((nm2,ty2a),prp2,trm2a,trm2b,ty2b)) ->
	  let reqs1 = eqSet cntxt ty1a ty2a 
	  in let reqs2 = eqProp cntxt prp1 prp2
	  in let reqs3 = eqTerm cntxt trm1a trm2a 
	  in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2 
	  in let trm1b' = subst sub1 trm1b
	  in let trm2b' = subst sub2 trm2b
	  in let cntxt' = insertTermVariable cntxt nm ty1a None
	  in let prereqs4 = eqTerm cntxt' trm1b' trm2b' 
	  in let reqs4 = List.map (fForall (nm,ty1a)) prereqs4
	  in let reqs5 = eqSet cntxt ty1b ty2b
	  in reqs1 @ reqs2 @ reqs3 @ reqs4 @ reqs5

      | (Subin (trm1,(nm1,ty1),prp1), Subin (trm2,(nm2,ty2),prp2)) ->
	  let reqs1 = eqTerm cntxt trm1 trm2
	  in let reqs2 = eqSet cntxt ty1 ty2
	  in let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	  in let prp1' = substProp sub1 prp1
	  in let prp2' = substProp sub2 prp2
	  in let cntxt' = insertTermVariable cntxt nm ty1 None
	  in let reqs3 = eqProp cntxt' prp1' prp2'
	  in reqs1 @ reqs2 @ reqs3

      | (Subout(trm1,st1), Subout(trm2,st2)) ->
	  eqTerm cntxt trm1 trm2 @
	    eqSet cntxt st1 st2

(* hnfTerm removed Assures 

      | (Assure(Some(nm1, st1), prp1, trm1), 
	 Assure(Some(nm2, st2), prp2, trm2)) ->
	  eqSet cntxt st1 st2 &&
	    let (nm, sub1, sub2) = jointNameSubsts nm1 nm2
	    in let prp1' = substProp sub1 prp1
	    in let prp2' = substProp sub2 prp2
	    in let trm1' = subst sub1 trm1
	    in let trm2' = subst sub2 trm2
	    in let cntxt' = insertTermVariable cntxt nm st1 None
	    in 
		 eqProp cntxt' prp1' prp2' &&
		   eqTerm cntxt' trm1' trm2'

      | (Assure(None, prp1, trm1), 
	 Assure(None, prp2, trm2)) ->
	  eqProp cntxt prp1 prp2 &&
	    eqTerm cntxt trm1 trm2
*)
      | _ -> 
	  let ty1 = typeOf cntxt trm1
	  in let ty2 = typeOf cntxt trm2
	  in let (ty,reqs) = joinType cntxt ty1 ty2
	  in reqs @ [Equal(ty, trm1, trm2)]
	 
and eqTerms cntxt trms1 trms2 = 
  try  
    List.flatten (List.map2 (eqTerm cntxt) trms1 trms2)  
  with
      Invalid_argument _ -> 
	E.tyGenericError "Different numbers of terms"

and eqTermOpt cntxt trmopt1 trmopt2 =
  match trmopt1, trmopt2 with
  | None, None -> []
  | Some trm1, Some trm2 -> eqTerm cntxt trm1 trm2
  | _ -> raise (E.TypeError [])

and eqModel ctx mdl1 mdl2 = 
  if (mdl1 = mdl2) then
    []
  else
    E.tyGenericError ("Incompatible models " ^ string_of_model mdl1 ^ " and " ^
		       string_of_model mdl2)

and eqModelOpt ctx mdlopt1 mdlopt2 = 
  if (mdlopt1 = mdlopt2) then
    []
  else
    raise (E.TypeError[])

and eqSet cntxt st1 st2 = eqSet' false cntxt st1 st2

and subSet cntxt st1 st2 = eqSet' true cntxt st1 st2

and eqSetOpt cntxt stopt1 stopt2 =
  match stopt1, stopt2 with
  | Some st1, Some st2 -> eqSet cntxt st1 st2
  | None, None -> []
  | _ -> raise (E.TypeError[])

(** Computes the join of the two sets s1 and s2.
    Like subtSet (and unlike Coerce), 
    join does *not* do implicit conversions *)
and joinType cntxt s1 s2 = 
   if (s1 = s2) then
      (* Short circuit *)
      (s1, [])
   else
      let    s1' = hnfSet cntxt s1
      in let s2' = hnfSet cntxt s2

(*** XXX if t1 <> t2 have a join, then   a:t1   and   a:t2  
     ought to have a join as well. *)

      in let rec joinSums = function 
	  ([], s2s) -> (s2s, [])
        | ((l1,None)::s1s, s2s) ->
	    if (List.mem_assoc l1 s2s) then
	      (match (List.assoc l1 s2s) with
	          None   -> joinSums(s1s, s2s)
		| Some _ -> 
		    E.tyGenericError ("Disagreement whether " ^ l1 ^
					 " stands alone or tags a value"))
	    else let (arms, reqs) = joinSums(s1s, s2s)
	         in ((l1,None) :: arms, reqs)

        | ((l1,Some s1)::s1s, s2s) ->
	    if (List.mem_assoc l1 s2s) then
	      (match (List.assoc l1 s2s) with
		  Some s2 -> 
		    let reqs1 = 
		      (try eqSet cntxt s1 s2 with
			  E.TypeError _ -> 
			    E.tyGenericError
			      ("Disagreement on what type of value " ^ 
                                  l1 ^ " should tag") )
		    in let (arms, reqs2) = joinSums(s1s, s2s)
		    in (arms, reqs1 @ reqs2)
		| None -> E.tyGenericError("Disagreement whether " ^ l1 ^
					 " tags a value or stands alone"))
	    else 
		let (arms, reqs) = joinSums(s1s, s2s)
		in ((l1,Some s1) :: arms, reqs)

      in match (s1',s2') with
        | (Sum lsos1, Sum lsos2) -> 
	    let (arms, reqs) = joinSums (lsos1, lsos2)
	    in (Sum arms, reqs)
        | _ -> 
	    let reqs = 
	      try eqSet cntxt s1 s2 with 
                  E.TypeError _ -> E.tyJoinError s1 s2
	    in
	      (s1, reqs)

 

let rec joinTypes cntxt = function
      [] -> (Unit, [])
    | [s] -> (s, [])
    | s::ss -> 
	let (ty1, reqs1) = joinTypes cntxt ss
	in let (ty2, reqs2) = joinType cntxt s ty1
	in (ty2, reqs1 @ reqs2)

let joinProperPropType p1 p2 = 
  begin
    match (p1,p2) with
	(StableProp, StableProp) -> StableProp
      | ((Prop | StableProp), (Prop | StableProp)) -> Prop
      | _ -> failwith "joinProperPropType only allows Prop and StableProp!"
  end

let joinProperPropTypes lst = List.fold_left joinProperPropType StableProp lst



let rec joinPropType cntxt pt1 pt2 = 
  begin
    match (pt1,pt2) with
	(StableProp, StableProp) -> (StableProp, [])
      | ((Prop | StableProp), (Prop | StableProp)) -> (Prop, [])
      | (EquivProp ty1, EquivProp ty2) -> 
	  let (ty, reqs) = joinType cntxt ty1 ty2
	  in (EquivProp ty, reqs)
      | (EquivProp ty1, _ ) -> 
	  joinPropType cntxt (equivToArrow ty1) pt2
      | (_, EquivProp ty2) -> 
	  joinPropType cntxt pt1 (equivToArrow ty2)
      | (PropArrow(nm3, st3, pt3), PropArrow(nm4, st4, pt4)) ->
	  let (nm, sub3, sub4) = jointNameSubsts nm3 nm4
	  in let pt3' = substProptype sub3 pt3
	  in let pt4' = substProptype sub4 pt4
	  in let cntxt' = insertTermVariable cntxt nm st3 None
	  in let reqs1 = 
	    try eqSet cntxt st3 st4 with
		E.TypeError _ -> E.tyPTJoinError pt1 pt2
	  in let (pt, reqs2) = joinPropType cntxt' pt3' pt4'
	  in 
	       (PropArrow(nm, st3, pt), reqs1 @ reqs2)
      | _ -> E.tyPTJoinError pt1 pt2
  end

let rec joinPropTypes cntxt = function
      [] -> failwith "joinPropTypes"
    | [pt] -> (pt, [])
    | pt::pts -> 
	let (pt1, reqs1) = joinPropTypes cntxt pts
	in let (pt2, reqs2) = joinPropType cntxt pt pt1
	in (pt2, reqs1 @ reqs2)

let rec eqMbnd cntxt subst1 subst2 (nm1, thry1) (nm2, thry2) =
  let (nm, subst1', subst2') = jointModelNameSubsts' nm1 nm2 subst1 subst2
  in let thry1' = substTheory subst1 thry1
  in let thry2' = substTheory subst2 thry2
  in let cntxt' = insertModelVariable cntxt nm thry1'
  in let prereqs = eqTheory cntxt thry1' thry2'
  in if (prereqs <> []) then
      E.tyGenericError "UNIMPLEMENTED: eqMbnd"
    else 
      (cntxt', subst1', subst2')


and eqMbnds' cntxt subst1 subst2 mbnds1 mbnds2 =
  match (mbnds1, mbnds2) with
      ([], []) -> (cntxt, subst1, subst2)
    | (mbnd1::rest1, mbnd2::rest2) ->
	let (cntxt', subst1', subst2') =  eqMbnd cntxt subst1 subst2 mbnd1 mbnd2
	in 
	  eqMbnds' cntxt' subst1' subst2' rest1 rest2
    | _ -> E.tyGenericError "Different numbers of model bindings"

and eqMbnds cntxt mbnds1 mbnds2 =
  eqMbnds' cntxt emptysubst emptysubst mbnds1 mbnds2

and eqTheory cntxt thry1 thry2 =
  try
    if (thry1 = thry2) then
      []
    else
      match (hnfTheory cntxt thry1, hnfTheory cntxt thry2) with
	  (TheoryLambda(mbnd1, thry1b), 
	   TheoryLambda(mbnd2, thry2b)) ->
	    let (cntxt', subst1, subst2) = 
	      eqMbnd cntxt emptysubst emptysubst mbnd1 mbnd2 
	    in let    thry1b' = substTheory subst1 thry1b
	    in let thry2b' = substTheory subst2 thry2b
	    in  eqTheory cntxt' thry1b' thry2b'
		      
	| (TheoryLambda _, _ ) -> E.tyGenericError "Unequal theories"
	| (_, TheoryLambda _) -> E.tyGenericError "Unequal theories"

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
	    in let prereqs1 = checkModelConstraint cntxt1 mdl thry1' thry2'
	    in let prereqs2 = checkModelConstraint cntxt2 mdl thry2' thry1'
	    in if (prereqs1 <> []) || (prereqs2 <> []) then
		E.tyGenericError "UNIMPLEMENTED: eqTheory 1"
	      else
		[]
  with
      E.TypeError msgs ->
	E.generalizeError msgs
	    ("...in comparing theories " ^ string_of_theory thry1 ^ "\nand " ^
		string_of_theory thry2)

and theoryToTimestamp cntxt = function
  | TheoryName nm -> lookupTimestamp cntxt nm
  | TheoryApp (thry, _) -> theoryToTimestamp cntxt thry
  | TheoryProj(mdl, _) -> modelToTimestamp cntxt mdl
  | TheoryLambda((nm,thry'), thry'') ->
      (* We add one so that the application
            (LAMBDA X. FOO(X))(Y)
         ends up with a later timestamp than
            FOO(Y),
         instead of the two being equal.   This is a hack, but
         the whole timestamp thing is just a heuristic anyway. *)
      theoryToTimestamp (insertModelVariable cntxt nm thry') thry'' + 1
  | _ -> -1
   
and modelToTimestamp cntxt = function
  | ModelName nm -> lookupTimestamp cntxt nm
  | ModelProj (mdl, _) -> modelToTimestamp cntxt mdl
  | ModelApp (mdl, _) -> modelToTimestamp cntxt mdl

(* Sound but not complete --- might return "false" if the
   answer is really "true".
   
   Uses an ad-hoc method to try to avoid fully expanding out
   all definitions.  E.g., if we have
      X = ...something big...
      Z = X
   it's faster to reduce Z to X, rather than reducing both
   X and Z to something big, and then comparing the big things.
   
   The idea is that to keep track of a "timestamp" describing when
   each variable entered the context.  A variable with a later timestamp
   might be an abbreviation for something with an earlier timestamp,
   so we try expanding later-timestamp theories first. 
   
   Note that this optimization doesn't help when comparing
      FOO (X)
   vs 
      FOO (Y);
   when FOO has a definition, we still end up expanding out
   both copies, rather than comparing X and Y.  Future work, I guess. *)
and quickEqTheory cntxt thry1 thry2 =
  if (thry1 = thry2) then
      true
  else
    let ts1 = theoryToTimestamp cntxt thry1
    in let ts2 = theoryToTimestamp cntxt thry2
    in if ts1 < ts2 then
        match (hnfTheory1 cntxt thry2) with
           None -> false
        |  Some thry2' -> quickEqTheory cntxt thry1 thry2'
    else 
        match (hnfTheory1 cntxt thry1) with
           None -> false
        |  Some thry1' -> quickEqTheory cntxt thry1' thry2
   
           
(* Inputs must be a well-formed logical model, its inferred theory, and
   some other theory *)
and checkModelConstraint cntxt mdl1 thry1 thry2 = 
  if quickEqTheory cntxt thry1 thry2 then
    []
  else
  (
  try
    match (hnfTheory cntxt thry1, hnfTheory cntxt thry2) with
	(TheoryArrow ((nm1, thry1a), thry1b), 
	TheoryArrow ((nm2, thry2a), thry2b)) ->
	  let (nm, sub1, sub2) = jointModelNameSubsts nm1 nm2
	  in let cntxt' = insertModelVariable cntxt nm thry2a
	  in let prereqs1 = 
	    (* contravariant domain *)
	    checkModelConstraint cntxt' (ModelName nm) thry2a thry1a
	  in let thry1b' = substTheory sub1 thry1b
	  in let thry2b' = substTheory sub2 thry2b
	  in let prereqs2 =  
	    (* covariant codomain *)
	    checkModelConstraint cntxt' (ModelApp(mdl1, ModelName nm)) 
	      thry1b' thry2b'
	  in if (prereqs1 <> []) || (prereqs2 <> []) then
	      (* We can't say "forall models", so we just give up.
		 It's unlikely this case will arise in practice.
	      *)
	      failwith "Unimplemented: checkModelConstraint1"
            else
	      []
		

      | (Theory elems1, Theory elems2) ->
	  let weakEq eqFun left = function
	      (** Checks for equality iff an optional value is given *)
	      None -> []
	    | Some right -> eqFun left right
	    
	  in let compareDeclSet cntxt (nm, st2opt, knd2, knd1) =
			let projAsSet = Basic(SLN(Some mdl1, nm), knd1)
			in let reqs1 = subKind cntxt knd1 knd2
			in let reqs2 = weakEq (eqSet cntxt) projAsSet st2opt
			in let cntxt' = 
			  insertSetVariable cntxt nm knd1 (Some projAsSet)
			in let subst = insertSetvar emptysubst nm projAsSet
			in (cntxt', reqs1 @ reqs2, subst)
	          
	  in let compareDeclProp cntxt (nm, prpopt2, pt2, pt1) =
			let projAsProp = Atomic(LN(Some mdl1, nm), pt1)
			in let reqs1 = subPropType cntxt pt1 pt2
			in let reqs2 = weakEq (eqProp cntxt) projAsProp prpopt2
			in let cntxt' = 
			  insertPropVariable cntxt nm pt1 (Some projAsProp)
			in let subst = insertPropvar emptysubst nm projAsProp
	        in (cntxt', reqs1 @ reqs2, subst) 
	      	    
	  in let compareDeclTerm cntxt (nm, trmopt2, st2, st1) =
			let projAsTerm = Var(LN(Some mdl1, nm))
			in let reqs1 = subSet cntxt st1 st2 
			in let reqs2 = weakEq (eqTerm cntxt) projAsTerm trmopt2
			in let cntxt' = 
			  insertTermVariable cntxt nm st1 (Some projAsTerm)
			in let subst = insertTermvar emptysubst nm projAsTerm
			in (cntxt', reqs1 @ reqs2, subst)	      
	      
	  in let compareDeclModel cntxt (nm, thry2, thry1) =
			let projAsModel = ModelProj(mdl1, nm)
			in let reqs1 = 
			  checkModelConstraint cntxt projAsModel thry1 thry2
			in let cntxt' = 
			  insertModelVariable cntxt nm thry1
			in let subst = insertModelvar emptysubst nm projAsModel
		    in (cntxt', reqs1, subst) 
			
	  in let compareDeclSentence cntxt (nm, mbnds2, prp2, mbnds1, prp1) =
		  let (cntxt'', subst1, subst2) = 
		    eqMbnds cntxt mbnds1 mbnds2 
		  in let prp1' = substProp subst1 prp1
		  in let prp2' = substProp subst2 prp2
		  in let prereqs1 = eqProp cntxt'' prp1' prp2'
		  in let reqs1 = if (prereqs1 <> []) then
		      (* We can't wrap with "forall mbnds1" *)
		      E.tyGenericError "UNIMPLEMENTED: CheckModelConstraint/Declaration"
		    else 
		      []
     	  in (cntxt, reqs1, emptysubst)
     	  
	  in let rec slowLoop cntxt = function
	      [] -> []
	    | decl :: rest ->
	        let (cntxt', reqs12, subst) =
              match decl with
	          | Declaration(nm, DeclSet(st2opt, knd2)) ->
 		        begin
          		  match searchElems cntxt nm mdl1 elems1 with
  		            Some (DeclSet (_,knd1)) -> 
		              compareDeclSet cntxt (nm, st2opt, knd2, knd1)
		          | _ -> 
			        E.tyGenericError ("Missing set component " ^ 
					     string_of_name nm)
		        end    
	          | Declaration(nm, DeclProp(prpopt2, pt2)) ->
		        begin
		          match searchElems cntxt nm mdl1 elems1 with
		            Some (DeclProp(_, pt1)) ->
		              compareDeclProp cntxt (nm, prpopt2, pt2, pt1)
		          | _ -> 
			        E.tyGenericError ("Missing proposition component " ^ 
					     string_of_name nm)
		        end
	          | Declaration(nm, DeclTerm(trmopt2, st2)) ->
		        begin
		          match searchElems cntxt nm mdl1 elems1 with
		            Some (DeclTerm(_, st1)) ->
		              compareDeclTerm cntxt (nm, trmopt2, st2, st1)
		          | _ -> 
			          E.tyGenericError ("Missing term component " ^ 
					     string_of_name nm)
		        end
              | Declaration(nm, DeclModel(thry2)) ->
		        begin
		          match searchElems cntxt nm mdl1 elems1 with
		            Some (DeclModel thry1) ->
			          compareDeclModel cntxt (nm, thry2, thry1) 
		          | _ -> 
			        E.tyGenericError ("Missing model component " ^ 
					     string_of_name nm)
		        end
	         | Comment _ ->
	             (cntxt, [], emptysubst)
        
	         | Declaration(nm, DeclSentence (mbnds2, prp2)) ->
		       begin
		         match searchElems cntxt nm mdl1 elems1 with
		           Some (DeclSentence(mbnds1, prp1)) ->
			         compareDeclSentence cntxt (nm, mbnds2, prp2, mbnds1, prp1)
 		         | _ -> 
			       E.tyGenericError ("Missing axiom " ^ 
					     string_of_name nm)
		       end

	         | Declaration(nm, DeclTheory _) ->
		        E.noNestedTheoriesError nm
       in let prereqs3 = slowLoop cntxt' rest
       in let reqs3 = List.map (substProp subst) prereqs3
       in reqs12 @ reqs3       

      (* fastLoop tries to compute the same answer as slowLoop above,
         but tries to speed things up (linear rather than quadratic)
         by walking through both lists of declarations in parallel,
         rather than walking through one and doing searches in the
         other.  If anything seems wrong, we punt back to the
         more general case to either succeed or report the error. *)

	  in let rec fastLoop cntxt subst1 = function
	      (_,[]) -> []
	    | ([],_) -> raise TooFast (* Punt to the general case *)
	    | (((_ :: rest1) as elems1), decl2 :: rest2) ->
	        let (subst1', (cntxt', reqs12, subst)) =
           match decl2 with
	          | Declaration(nm, DeclSet(st2opt, knd2)) ->
		        begin
       		      match searchElems' subst1 cntxt nm mdl1 elems1 with
		            (subst1', Some (DeclSet (_,knd1))) ->
		              (subst1',  
		               compareDeclSet cntxt (nm, st2opt, knd2, knd1))
		          | _ -> 
		            raise TooFast
		        end    
	          | Declaration(nm, DeclProp(prpopt2, pt2)) ->
		        begin
		          match searchElems' subst1 cntxt nm mdl1 elems1 with
		            (subst1', Some (DeclProp(_, pt1))) ->
		              (subst1', compareDeclProp cntxt (nm, prpopt2, pt2, pt1))
		          | _ -> 
		            raise TooFast
		        end
	          | Declaration(nm, DeclTerm(trmopt2, st2)) ->
		        begin
		          match searchElems' subst1 cntxt nm mdl1 elems1 with
		            (subst1', Some (DeclTerm(_, st1))) ->
		              (subst1', compareDeclTerm cntxt (nm, trmopt2, st2, st1))
		          | _ -> 
			          raise TooFast
		        end
              | Declaration(nm, DeclModel(thry2)) ->
		        begin
		          match searchElems' subst1 cntxt nm mdl1 elems1 with
		            (subst1', Some (DeclModel thry1)) ->
			          (subst1', compareDeclModel cntxt (nm, thry2, thry1))
		          | _ -> 
					raise TooFast
		        end
	         | Comment _ ->
	             (subst1, (cntxt, [], emptysubst))
     
	         | Declaration(nm, DeclSentence (mbnds2, prp2)) ->
		       begin
		         match searchElems' subst1 cntxt nm mdl1 elems1 with
		           (subst1', Some (DeclSentence(mbnds1, prp1))) ->
			         (subst1',
			          compareDeclSentence cntxt (nm, mbnds2, prp2, mbnds1, prp1))
		         | _ -> 
				   raise TooFast
		       end

	         | Declaration(nm, DeclTheory _) ->
		        E.noNestedTheoriesError nm
		        
    in let prereqs3 = fastLoop cntxt' subst1' (rest1, rest2)
    in let reqs3 = List.map (substProp subst) prereqs3
    in reqs12 @ reqs3       

	  in 
	     (try
	        fastLoop cntxt emptysubst (elems1, elems2)
	     with 
        TooFast -> slowLoop cntxt elems2)

    | _ -> E.tyGenericError "Incompatible theories"

  with
      E.TypeError msgs -> 
	E.generalizeError msgs
	  ("...in comparing theories " ^ string_of_theory thry1 ^
	      "\nand " ^ string_of_theory thry2)
	)  
(* coerce: cntxt -> term -> set -> set -> trm option *)
(**
     coerce trm st1 st2 coerces trm from the set st1 to the set st2
       using subin and subout.
     Preconditions: trm is in st1 and all arguments are fully-annotated.
     Returns:  None       if trm cannot be turned into a value in set st2.
               Some trm'  if we can obtain the term trm'
*)
let rec coerce cntxt trm st1 st2 = 
  try
    (** Short circuting, since the identity coercion is (we hope)
        the common case *)
    let reqs = subSet cntxt st1 st2 
    in 
      maybeAssure reqs trm st2
  with E.TypeError _ ->
    (** Just because the identity coercion won't work doesn't
        mean it's time to give up! *)
    let    st1' = hnfSet cntxt st1
    in let st2' = hnfSet cntxt st2
    in try       
	match (trm, st1', st2') with
	  | ( _, Subset ( ( _, st1'1 ) , _ ),
            Subset ( ( _, st2'1 ) as bnd2', prp2'2 ) ) -> 
	      begin
		(** Try an implicit out-of-subset conversion *)
		try
		  coerce cntxt ( Subout(trm,st1) ) st1'1 st2 
		with E.TypeError _ -> 
		  (** That didn't work, so try an implicit 
		      into-subset conversion *)
		  (* XXX Eventually we may add an assure here for the subin *)
		  let trm' = coerce cntxt trm st1 st2'1
		  in  Subin ( trm', bnd2', prp2'2 )
	      end
		
	  | ( _, Subset( ( _, st1'1 ), _ ), _ ) -> 
	      (** Try an implicit out-of-subset conversion *)
	      (* XXX Eventually we may add an assure here for the subin *)
	      coerce cntxt ( Subout(trm,st2) ) st1'1 st2 
		
	  | ( _, _, Subset( ( _, st2'1 ) as bnd2', prp2'2 ) ) -> 
	      (** Try an implicit into-subset conversion *)
	      let trm' = coerce cntxt trm st1 st2'1
	      in  Subin ( trm', bnd2', prp2'2 )
		
	  | ( Tuple trms, Product sts1, Product sts2 ) ->
	      let rec loop subst2 = function 
		  ([], [], []) -> []
		| ([], _, _)   -> failwith "Impossible: coerce 1" 
		| (trm::trms, (nm1, st1)::sts1, (nm2, st2)::sts2) ->
		    if (isWild nm1) then
		      let st2' = substSet subst2 st2
		      in let subst2' = insertTermvar subst2 nm2 trm
		      in (coerce cntxt trm st1 st2') ::
		         (loop subst2' (trms,sts1,sts2))
		    else
		      (* This case shouldn't ever arise; tuples naturally
			 yield non-dependent product types.  
			 But just in case, ...*)
		      (failwith
			  ("coerce: dependent->? case for products arose. " ^
			      "Maybe it should be implemented after all"))
		| _ -> raise Impossible
              in let trms' = loop emptysubst (trms, sts1, sts2)
	      in Tuple trms'

          | _ -> E.tyGenericErrors []
      with
	  E.TypeError _ -> 
	    (* Provide a less confusing error message, since some of
	       the things we tried may have made no sense. *)
	    E.tyGenericError ("No implicit coercion from  type " ^ 
				 string_of_set st1 ^ 
			         (if st1 = st1' then "" else
                                     "=" ^ string_of_set st1') ^
			         " to type " ^ 
			         string_of_set st2 ^ 
			         (if st2 = st2' then "" else
                                     "=" ^ string_of_set st2'))

(* XXX Should this be accumulating and returning assurances? *)
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

(* Wrapper for equality-testing functions: returns a bool, rather than
     a list or an exception.
   Tells us whether the equivalence holds *without assumptions* or not.
   Never raises the TypeError exception.
*)
let reallyEq f x y z = 
  try
     f x y z = []
  with
     E.TypeError _ -> false

(* New idea:  we can ignore/drop a theory element if it is identical
   (say, up to equivalence, for generality) to a previous declaration
  in the *same* thy...end group.  
 *)
let declaredInSameThy cntxt nm =
  try
    lookupTimestamp cntxt nm >= lookupLastThy cntxt
  with
    Not_found -> false

let ignorableElem cntxt elem =
  match elem with
    Comment _ -> false
  | Declaration(nm, decl) ->
      try
        begin
        declaredInSameThy cntxt nm &&
        match decl, lookupId cntxt nm with
        | DeclSet(stopt, knd), Some(DeclSet(stopt', knd'))  ->
            reallyEq eqKind cntxt knd knd' &&
              reallyEq eqSetOpt cntxt stopt stopt'
        | DeclProp(prpopt, pt), Some(DeclProp(prpopt', pt')) -> 
            reallyEq eqPropType cntxt pt pt' &&
              reallyEq eqPropOpt cntxt prpopt prpopt'
        | DeclTerm(trmopt, ty), Some(DeclTerm(trmopt', ty')) -> 
            reallyEq eqSet cntxt ty ty' &&
              reallyEq eqTermOpt cntxt trmopt trmopt'
        | DeclModel thry, Some(DeclModel thry') -> 
            reallyEq eqTheory cntxt thry thry'
        | DeclTheory(thry,tknd), Some(DeclTheory(thry',tknd')) ->
            (tknd = tknd') &&
              reallyEq eqTheory cntxt thry thry'
        | DeclSentence([],prp), Some(DeclSentence([],prp')) ->
            reallyEq eqProp cntxt prp prp'
        | DeclSentence _, Some(DeclSentence _) ->
            (* XXX *)
            failwith "Unimplemented: ignoreableElem/DeclSentence"
        | _ -> false
        end
      with
        E.TypeError _ -> false

let rec updateContextForElems cntxt = function
  | [] -> cntxt, []
  | elem :: elems -> 
      if (ignorableElem cntxt elem) then
        updateContextForElems cntxt elems
      else 
        let cntxt' = 
          match elem with
          | Declaration(nm, DeclSet(stopt, knd)) ->
              insertSetVariable  cntxt nm knd stopt
          | Declaration(nm, DeclProp(prpopt, pt)) -> 
              insertPropVariable cntxt nm pt prpopt
          | Declaration(nm, DeclTerm(trmopt, ty)) -> 
              insertTermVariable cntxt nm ty trmopt
          | Declaration(nm, DeclModel(thry)) -> 
              insertModelVariable cntxt nm thry
          | Declaration(nm, DeclTheory(thry,tknd)) ->
              insertTheoryVariable cntxt nm thry tknd
          | Declaration(nm, DeclSentence(mbnds,prp)) ->
              insertSentenceVariable cntxt nm mbnds prp
          | Comment _   -> cntxt  in
        let cntxt'', elems' = updateContextForElems cntxt' elems  in
        cntxt'', elem :: elems'



let rec renameElem nm1 nm2 = function
  | [] -> []
  | Declaration(nm, decl) :: rest when nm = nm1 ->
      let sub = 
        match decl with
        | DeclProp(_,pt) -> insertPropvar emptysubst nm (prop_of_name nm2 pt)
        | DeclSet(_,knd) -> insertSetvar emptysubst nm (set_of_name nm2 knd)
        | DeclTerm _ -> insertTermvar emptysubst nm (term_of_name nm2)
        | DeclModel _ -> insertModelvar emptysubst nm (model_of_name nm2)
        | DeclTheory _ -> insertTheoryvar emptysubst nm (theory_of_name nm2)
        | DeclSentence _ -> emptysubst    in
      Declaration(nm2, decl) :: substTheoryElts sub rest
   | elem :: rest -> elem :: renameElem nm1 nm2 rest
   
(* Unfortunately, if you rename all the sentences then you've
   changed the theory:  a functor expecting a Group, for example, doesn't
   get a model with the right axiom names. 

let rec renameSentences = function
  | [] -> []
  | Declaration(nm, (DeclSentence _ as decl)) :: rest ->
      Declaration(refresh nm, decl) :: renameSentences rest
  | elem :: rest ->   elem :: renameSentences rest
*)