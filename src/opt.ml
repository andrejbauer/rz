(** XXX: Can we avoid expanding out all the type definitions? *)

(********************************************************************)
(** {1 Simplification}                                              *)
(**                                                                 *)
(** Precondition:  TopTy and Dagger have been completely eliminated *)
(**   EXCEPT that Dagger may appear as the realizer for a named     *)
(**   proposition.                                                  *)
(********************************************************************)

open Name
open Outsyn

exception Unimplemented
exception Impossible of string



(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)

(** Context carried around by the type reconstruction algorithm.
 *)
type ctx = {types      : ty NameMap.t;
               (** Typing context; types for names in scope. *)
            tydefs     : ty NameMap.t;
               (** Definitions of type variables in scope. *)
            moduli     : sig_summary NameMap.t;
	    termdefs   : term NameMap.t;
           }

and sig_summary = 
    Summary_Struct  of ctx
  | Summary_Functor of modul_name * sig_summary

let occurs ctx nm =
  NameMap.mem nm ctx.types  ||
  NameMap.mem nm ctx.tydefs ||
  NameMap.mem nm ctx.moduli ||
  NameMap.mem nm ctx.termdefs 

(* lookupModul : cntxt -> modul_name -> sig_summary
 *)
let lookupModul ctx nm = 
  NameMap.find nm ctx.moduli
       
(* lookupModulLong : ctx -> sig_summary * subst

   Despite the name, does more than lookup; figures out the
   signature of the 
 *)
let rec lookupModulLong ctx = function
    ModulName mdlnm        -> ( lookupModul ctx mdlnm, emptysubst )
  | ModulProj (mdl, mdlnm) ->
       begin
	 match ( lookupModulLong ctx mdl ) with
           ( Summary_Struct ctx', sub ) -> ( lookupModul ctx' mdlnm, sub )
	 | _ -> raise (Impossible "lookupModulLong")
       end
  | ModulApp (mdl1, mdl2)  -> 
      (match lookupModulLong ctx mdl1 with
	  Summary_Functor ( mdlnm, summary11 ), sub -> (summary11, insertModulvar sub mdlnm mdl2)
	| Summary_Struct _, _ -> raise (Impossible "lookupModulLong, app")
      )


let lookupType  ctx   nm = 
   try (NameMap.find nm ctx.types) with 
      Not_found -> ( print_string ( "Opt: Unbound name: " ^ Name.string_of_name nm ^ "\n");
                     raise Not_found )

let lookupTypeLong  ctx = function
    LN(None, nm)     ->  lookupType ctx nm
  | LN(Some mdl, nm) ->
       begin
	 match (lookupModulLong ctx mdl) with
           ( Summary_Struct ctx', sub ) -> substTy sub (lookupType ctx' nm)
	 | _                -> raise (Impossible "lookupTypeLong")
       end


let peekTydef ctx tynm = 
   try  Some (NameMap.find tynm ctx.tydefs)  with 
      Not_found -> None

let peekTydefLong ctx = function
    LN(None, nm)     ->  peekTydef ctx nm
  | LN(Some mdl, nm) ->
       begin
	 match (lookupModulLong ctx mdl) with
           ( Summary_Struct ctx', sub ) -> substTyOption sub (peekTydef ctx' nm)
	 | _                -> raise (Impossible "peekTydefLong")
       end

let peekTermdef ctx nm = 
   try  Some (NameMap.find nm ctx.termdefs)  with 
      Not_found -> None

let insertTermdef ({termdefs=termdefs} as ctx) nm trm =
  { ctx with termdefs = NameMap.add nm trm termdefs }

let insertType ({types=types} as ctx) nm ty = 
       {ctx with types = NameMap.add nm ty types}

(* insertBnds : ty NameMap.t -> (name * ty) list -> ty NameMap.t
 *)
let rec insertBnds types = function
    [] -> types
  | (nm,ty)::bnds -> insertBnds (NameMap.add nm ty types) bnds

(* insertTypeBnds : ctx -> (name * ty) list -> ctx
 *)
let insertTypeBnds ({types=types} as ctx) bnds = 
       { ctx  with  types = insertBnds types bnds }

let insertTydef ({tydefs=tydefs} as ctx) tynm ty = 
       { ctx with tydefs = NameMap.add tynm ty tydefs }

let insertModul ({moduli=moduli} as ctx) nm sg = 
       { ctx with moduli = NameMap.add nm sg moduli }

let emptyCtx = {types = NameMap.empty; tydefs = NameMap.empty; 
		termdefs = NameMap.empty; moduli = NameMap.empty}


(*******************)
(** Set operations *)
(*******************)


(** Expand out any top-level definitions for a set *)
let rec hnfTy ctx = function
    NamedTy tynm ->
      (match (peekTydefLong ctx tynm) with
      | None -> NamedTy tynm
      | Some s' -> hnfTy ctx s')
  | s -> s


let joinTy ctx s1 s2 = 
   if (s1 = s2) then
      (* Short circuting *)
      s1
   else
      let    s1' = hnfTy ctx s1
      in let s2' = hnfTy ctx s2

      in let rec joinSums = function 
	  ([], s2s) -> s2s
	| ((l1,t)::s1s, s2s) ->
	    if List.mem_assoc l1 s2s then
	      joinSums (s1s, s2s)
	    else
	      (l1,t) :: (joinSums (s1s, s2s))

      in match (s1',s2') with
        | (SumTy lsos1, SumTy lsos2) -> SumTy (joinSums (lsos1, lsos2))
        | _ -> s1' (** We're assuming the input to the optimizer
                       typechecks! *)

(*********************)
(** Helper functions *)
(*********************)

let findEq nm orig_prop =
  match orig_prop with
      Equal(Id(LN(None,nm')), trm) 
        when nm = nm' and not(List.mem nm (fvTerm trm)) ->
	    
      True
    | False
    |  -> 

(***************************)
(** Optimization functions *)
(***************************)



(* optTy : ty -> ty
    
   Since types don't contain terms or propositions or type-applications,
   there's really nothing to make simpler.  [Recall that thinning has
   already occurred.]
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
	Id n -> let ty = lookupTypeLong ctx n
          in  (ty, Id n)
      | EmptyTuple -> (UnitTy, EmptyTuple)
      | Dagger -> 
	  (print_string "Is this a Dagger which I see before me?\n";
	   raise (Impossible "Dagger found after thinning"))
      | App(e1,e2) -> 
	  begin
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
	  let    ty1' = optTy ctx ty1
	  in let ctx' = insertType ctx nm1 ty1
	  in let (ty2', trm2') = optTerm ctx' trm2
	  in let ty = ArrowTy(ty1',ty2')
	  in 
	       (ty,  optReduce ctx (Lambda((nm1,ty1'),trm2')))
      | Tuple es -> 
	  let (ts, es') = optTerms ctx es
	  in (TupleTy ts, Tuple es')
      | Proj (n,e) ->
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
      | Inj (lbl, None) -> (SumTy [(lbl,None)], Inj(lbl, None))
      | Inj (lbl, Some e) ->
	  let (ty, e') = optTerm ctx e in
	    (SumTy [(lbl,Some ty)], Inj(lbl, Some e'))
      | Case (e, arms) ->
	  let (ty, e') = optTerm ctx e
	  in let doArm = function
	      (lbl, Some (name2,ty2),  e3) -> 
		let ty2' = optTy ctx ty2 
		in let ctx' = insertType ctx name2 ty
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
	  (* Phase 1: Basic Optimization *)
	  let    (ty1, term1') = optTerm ctx term1
	  in let ctx' = insertTermdef (insertType ctx name1 ty1) name1 term1'
	  in let (ty2, term2') = optTerm ctx' term2
	  in let trm' = optReduce ctx (Let(name1, term1', term2'))
	  in let trm'' =
	    match trm' with
		(* Turn a let of a tuple into a sequence of lets, if
		   the tuple is never referred to as a whole *)
		Let(name1, Tuple trms, term2) when opTerm name1 term2 ->
		  let good = List.map (fun _ -> [name1]) trms
		  in let nms = freshNameList good [] (occurs ctx) 
		  in let trm'' = nested_let nms trms term2
		  in optReduce ctx trm''
	      | _ -> trm'
	  in (ty2, trm'')

      | Obligation(bnds, prop, trm) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (optTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let ctx' = List.fold_left2 insertType ctx names tys
	  in let prop' = optProp ctx' prop
	  in let ty2, trm' = optTerm ctx' trm
	  in begin
	      match (bnds', prop') with
		  ([], True) -> (ty2, trm')
		| _ -> (ty2, Obligation(bnds', prop', trm'))
	    end
  with e ->
    (print_endline ("\n\n...in " ^
		       string_of_term orig_term);
     raise e)

and optReduce ctx trm =
  try
    let trm' = reduce trm
    in 
      if trm <> trm' then
	let (_,trm'') = optTerm ctx trm' in trm''
      else
	trm'
  with e ->
    (print_endline ("\n\n...in " ^
		       string_of_term trm);
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
    (print_endline ("\n\n...in " ^
		       string_of_proposition prp);
     raise e)
	  
and optTerms ctx = function 
    [] -> ([], [])   
  | e::es -> let (ty, e') = optTerm ctx e
    in let (tys, es') = optTerms ctx es
    in (match (hnfTy ctx ty) with
        TopTy -> (ty :: tys, es')
      | _ -> (ty :: tys, e'::es'))
      

and optTerm' ctx e =
  let (_,e') = optTerm ctx e 
  in e'      

and optTerms' ctx lst =
  let (_, es) = optTerms ctx lst in es

and optProp ctx orig_prp = 
  try
    match orig_prp with
	True                    -> True
      | False                   -> False
      | IsPer (nm, lst)         -> IsPer (nm, optTerms' ctx lst)
      | IsPredicate (nm, ty, lst) ->
	  IsPredicate (nm, optTyOption ctx ty, List.map (fun (nm, ms) -> (nm, optModest ctx ms)) lst)
      | IsEquiv (p, ms)         -> IsEquiv (optProp ctx p, optModest ctx ms)
      | NamedTotal (n, lst)     -> NamedTotal (n, optTerms' ctx lst)
      | NamedPer (n, lst)       -> NamedPer (n, optTerms' ctx lst)
      | NamedProp (n, Dagger, lst) -> NamedProp(n, Dagger, optTerms' ctx lst)
      | NamedProp (n, t, lst)   -> NamedProp (n, optTerm' ctx t, optTerms' ctx lst)
      | Equal(e1, e2) -> 
	  begin
	    let (ty1,e1') = optTerm ctx e1
	    in let e2' = optTerm' ctx e2
	    in
		 match (hnfTy ctx ty1) with
	             VoidTy -> True
		   | UnitTy -> True
		   | SumTy _ ->
		       begin
			 match e1', e2' with
			     Inj (lbl1, None), Inj (lbl2, None) ->
			       if lbl1 = lbl2 then True else False
			   | Inj (lbl1, Some t1), Inj (lbl2, Some t2) ->
			       if lbl1 = lbl2 then
				 Equal (t1, t2)
				   (* optProp ctx (Equal (t1, t2)) *)
			       else
				 False
			   | Inj (_, None), Inj (_, Some _)
			   | Inj (_, Some _), Inj (_, None) -> False
			   | _ -> Equal (e1', e2')
		       end
		   | _ -> Equal(e1',e2') 
	  end
      | And ps ->
	  let rec loop = function
            | ([], []) -> True
	    |  ([], raccum) -> And (List.rev raccum)
	    | (p::ps, raccum) -> 
		(match optProp ctx p with
		    True -> loop(ps,raccum)
		  | False -> False
		  | p' -> loop(ps, p' :: raccum))
	  in loop(ps,[])
      | Cor ps ->
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
	  (match (optProp ctx p1, optProp ctx p2) with
	      (p1',   p2'  ) when p1' = p2' -> True
	    | (True,  p2'  ) -> p2'
	    | (False, _    ) -> True
	    | (_,     True ) -> True
	    | (p1',   False) -> Not p1'
	    | (p1',   p2'  ) -> Imply(p1', p2'))

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
	  let p' = optProp (insertType ctx n ty) p
	  in (match (optTy ctx ty, p') with
              (_, True) -> True
	    | (UnitTy, _) -> optReduceProp ctx (PLet(n,EmptyTuple,p'))
	    | (VoidTy, _) -> True
	    | (NamedTy n1, Imply (PApp (NamedTotal (n2, []), Id n3), p'')) ->
		if (LN(None,n) = n3) && (n1 = n2) then
		  ForallTotal((n, NamedTy n1), p'')
		else
		  Forall((n,NamedTy n1),p')
	    | (ty',_) -> Forall((n,ty'), p'))
	    
      | ForallTotal((n,ty),p) ->
	  let p' = optProp (insertType ctx n ty) p
	  in ForallTotal((n,optTy ctx ty), p')
	    
      | Cexists ((n, ty), p) ->
	  let p' = optProp (insertType ctx n ty) p in
	    (match optTy ctx ty, p' with
		(_, False) -> False
	      | (VoidTy, _) -> False
	      | (UnitTy, _) -> optReduceProp ctx (PLet(n,EmptyTuple,p'))
	      | (ty', _) -> Cexists((n, ty'), p'))

      | PObligation (bnds, p, q) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (optTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let ctx' = List.fold_left2 insertType ctx names tys
	  in let p' = optProp ctx' p
	  in let q' = optProp ctx' q
	  in 
	       begin
		 match (bnds', p') with
		     ([], True) -> q'
		   | _ -> PObligation(bnds', p', q')
	       end

      | PMLambda ((n, ms), p) ->
	  let ms' = optModest ctx ms in
	  let p' = optProp (insertType ctx n ms.ty) p
	  in let pre = (PMLambda ((n,ms'), p'))
	  in optReduceProp ctx pre
	    
      | PMApp (p, t) -> 
	  optReduceProp ctx (PMApp (optProp ctx p, optTerm' ctx t))

      | PLambda ((n,ty), p) ->
	  let p' = optProp (insertType ctx n ty) p
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
		let ty' = optTy ctx ty
		in 
		  (Some (nm, ty'), insertType ctx0 nm ty)
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
	  let    (ty1, trm1') = optTerm ctx trm1
	  in let ctx' = insertType ctx nm ty1
	  in let prp2' = optProp ctx' prp2
	  in let prp' = optReduceProp ctx (PLet(nm, trm1', prp2'))
	  in let prp'' = 
	    match prp' with
		(* Turn a let of a tuple into a sequence of lets, if
		   the tuple is never referred to as a whole *)
		PLet(name1, Tuple trms, prp2) when opProp name1 prp2 ->
		  let good = List.map (fun _ -> [name1]) trms
		  in let nms = freshNameList good [] (occurs ctx) 
		  in let subst = 
		    insertTermvar emptysubst name1 (Tuple (List.map id nms))
		  in let prp2' = substProp subst prp2
		  in let prp'' = nested_plet nms trms prp2'
		  in optProp ctx prp''
	      | _ -> prp'
	  in 
	       prp''   
  with e ->
    (print_endline ("\n\n...in " ^
		       string_of_proposition orig_prp);
     raise e)

	  and optAssertion ctx (name, prop) = 
	    let prop' = optProp ctx prop
	    in 

	    let prop'' = if (!Flags.do_hoist) then
		let (obs, prp') = hoistProp prop' in
		  optProp ctx (foldPObligation obs prp') 
	      else
		prop'
	    in
	      (name, prop'')

	  and optModest ctx {ty=t; tot=p; per=q} =
	    {ty = optTy ctx t;
	     tot = optProp ctx p;
	     per = optProp ctx q}

	  and optElems ctx orig_elems = 
	    try
	      match orig_elems with
		  [] -> [], emptyCtx
		|  ValSpec(name, ty, assertions) :: rest ->
		     let ty'  = optTy ctx ty in
		     let ctx' = insertType ctx name ty in
		     let assertions' = List.map (optAssertion ctx') assertions
		     in let (rest', ctx'') = optElems (insertType ctx name ty) rest in
			  (ValSpec (name, ty', assertions') :: rest', 
			  insertType ctx'' name ty')
			    
		|  AssertionSpec assertion  ::  rest ->
		     let assertion' = optAssertion ctx assertion in
		     let (rest', ctx') = optElems ctx rest in
		       (AssertionSpec assertion' :: rest'), ctx'

		|  ModulSpec (name,signat) :: rest -> 
		     let (signat',summary) = optSignat ctx signat
		     in let ctx'' = insertModul ctx name summary
		     in let (rest', ctx''') = optElems ctx'' rest 
		     in (ModulSpec (name, signat') :: rest',
			ctx''')

		|  TySpec(nm, None, assertions) :: rest -> 
		     (** We don't add nm to the input context of optAssertion
			 because we never need to know whether something is a type or
			 not; we're assuming that the input was well-formed *)
		     let assertions' = List.map (optAssertion ctx) assertions in
		     let rest', ctx'' = optElems ctx rest in
		       (TySpec (nm, None, assertions') :: rest'), ctx''

		|  TySpec(nm, Some ty, assertions) :: rest ->
		     let ty' = optTy ctx ty in
		       (** We might care about expanding a definition for nm, though *)
		     let ctx' = insertTydef ctx nm ty  in
		     let assertions' = List.map (optAssertion ctx') assertions in
		     let rest', ctx'' = optElems ctx'  rest in
		       TySpec(nm, Some ty',assertions') :: rest', (insertTydef ctx'' nm ty')

		|  Comment cmmnt :: rest -> 
		     let rest', ctx' = optElems ctx rest in
		       (Comment cmmnt :: rest', ctx')
	    with e ->
	      (print_endline ("\n\n...in " ^
				 (String.concat "\n" (List.map string_of_spec orig_elems)));
	       raise e)


	  and optSignat ctx = function
	      SignatName s ->
		( SignatName s, lookupModul ctx s )
	    | Signat body -> 
		let body', ctx' = optElems ctx body in
		  ( Signat body', Summary_Struct ctx' )
	    | SignatFunctor(arg, body) ->
		let    ( (mdlnm, _) as arg', ctx'  ) = optStructBinding ctx arg
		in let ( body', summary ) = optSignat ctx' body
		in ( SignatFunctor ( arg', body' ), 
		   Summary_Functor (mdlnm, summary) )
	    | SignatApp(sgnt1,mdl,sgnt2) ->
		let sgnt2', smmry = optSignat ctx sgnt2 in
		  SignatApp(fst (optSignat ctx sgnt1), mdl, sgnt2'),
		smmry
		  
	  and optStructBinding ctx (m, signat) =
	    let signat', summary = optSignat ctx signat in
	      ( (m, signat'),
	      insertModul ctx m summary )

	  and optStructBindings ctx = function
	      [] -> [], ctx
	    | (m, signat) :: bnd ->
		let signat', summary = optSignat ctx signat in
		let bnd', ctx'' = optStructBindings ctx bnd in
		  ( (m, signat') :: bnd',
		  insertModul ctx'' m summary )

let optToplevel ctx = function
    (Signatdef (s, signat)) ->
      let signat', summary' = optSignat ctx signat in
	( Signatdef (s, signat'), 
          insertModul ctx s summary' )

  | TopComment cmmnt -> (TopComment cmmnt, ctx)

  | TopModul (mdlnm, signat) ->
      let (signat', summary') = optSignat ctx signat in
	( TopModul(mdlnm, signat'), 
	  insertModul ctx mdlnm summary' )

let rec optToplevels' ctx = function
    [] -> ([], ctx)
  | sg :: lst ->
      let sg', ctx' = optToplevel ctx sg in
      let lst', ctx'' = optToplevels' ctx' lst in
	(sg'::lst', ctx'')

let optToplevels ctx sigs =
  if !Flags.do_thin && !Flags.do_opt then 
    optToplevels' ctx sigs 
  else 
    (if !Flags.do_opt then
	(print_endline "WARNING:  ";
	 print_endline "Optimization skipped (it requires thinning)");
    (sigs,ctx))
   
