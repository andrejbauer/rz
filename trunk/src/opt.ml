(** XXX: Can we avoid expanding out all the type definitions? *)

(*******************************************************************)
(** {1 TopTy Elimination}                                          *)
(**                                                                *)
(** For now we assume that                                         *)
(** all bound variables are annotated, either when declared        *)
(** or through a prior "implicit" statement.                       *)
(*******************************************************************)

open Outsyn

exception Unimplemented
exception Impossible

(** XXX:  Shouldn't cut-and-paste from infer.ml!!! *)


(*************************************)
(** {2 Lookup Tables (Environments)} *)
(*************************************)

let emptyenv = []
let insert (x,s,env) = (x,s)::env

exception NotFound
let rec lookup = function
      (y,[]) -> (raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookup(y,rest)


let rec peek = function
      (y,[]) -> None
    | (y,(k,v)::rest) -> if (y=k) then Some v else peek(y,rest)

let rec lookupName = function
      (y,[]) -> (print_string ("Unbound name: " ^ Syntax.string_of_name y ^ "\n");
                 raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookupName(y,rest)

(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)



(** Context carried around by the type reconstruction algorithm.
 *)
type ctx = {types      : ty NameMap.t;
               (** Typing context; types for names in scope *)
            tydefs     : ty TyNameMap.t;
               (** Definitions of type/set variables in scope *)
            moduli     : (string*ctx) list
           }

(* Unused and out-of-date
let rec string_of_ctx {types=types; tydefs=tydefs; moduli=moduli} =
  "{ types = [" ^ (String.concat "," (List.map (fun (n,t) ->
				       (Syntax.string_of_name n) ^ ":" ^ (string_of_ty t)) types)) ^ "],\n" ^
  "  tydefs = [" ^ (String.concat "," (List.map (fun (n,t) -> n ^ ":" ^ (string_of_ty t)) tydefs)) ^ "],\n" ^
  "  moduli = [" ^ (String.concat "," (List.map (fun (n,t) -> n ^ ":" ^ (string_of_ctx t)) moduli)) ^ "],\n" ^
 "}"
*)

let lookupType  ctx   nm = 
   try (NameMap.find nm ctx.types) with 
      Not_found -> ( print_string ( "Unbound name: " ^ string_of_name nm ^ 
				    "\n");
                     raise Not_found )

let peekTydef ctx  tynm = 
   try  Some (TyNameMap.find tynm ctx.tydefs)  with 
      Not_found -> None

let lookupModul    ctx str = lookup (str, ctx.moduli)

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
       { ctx with tydefs = TyNameMap.add tynm ty tydefs }

let insertModul ({moduli=moduli} as ctx) str ctx' = 
       {ctx with moduli = insert(str,ctx',moduli)}

let emptyCtx = {types = NameMap.empty; tydefs = TyNameMap.empty; moduli = []}

(* lookupModulLong : ctx -> ctx
 *)
let rec lookupModulLong ctx = function
    ModulName mdlnm -> lookupModul ctx mdlnm
  | ModulProj (mdl, mdlnm) ->
       let ctx' = lookupModulLong ctx mdl
       in lookupModul ctx' mdlnm
  | ModulApp (mdl1, mdl2) ->
       raise Impossible   (** Modul application not implemented yet *)

let rec peekLong peeker ctx = function
    LN(None, nm)     ->  peeker ctx nm
  | LN(Some mdl, nm) ->
       let ctx' = lookupModulLong ctx mdl
       in peeker ctx' nm

let rec peekTyLong peeker ctx = function
    TLN(None, nm)     ->  peeker ctx nm
  | TLN(Some mdl, nm) ->
       let ctx' = lookupModulLong ctx mdl
       in peeker ctx' nm
 
(** Expand out any top-level definitions for a set *)
let rec hnfTy ctx = function
    NamedTy tynm ->
      (match (peekTyLong peekTydef ctx tynm) with
        Some s' -> hnfTy ctx s'
      | None -> NamedTy tynm)
  | s -> s


(*******************)

let notTopTy = function
      TopTy -> false
    | _ -> true

let topTyize = function
      TupleTy [] -> TopTy
    | TupleTy [ty] -> ty
    | ty -> ty

let joinTy ctx s1 s2 = 
   if (s1 = s2) then
      (* Short circuting *)
      s1
   else
      let    s1' = hnfTy ctx s1
      in let s2' = hnfTy ctx s2

      in let rec joinSums = function 
	  ([], s2s) -> s2s
        | ((l1,None)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let None = List.assoc l1 s2s
		in (l1,None) :: joinSums(s1s, s2s)
              with _ -> raise Impossible
	    else (l1,None) :: joinSums(s1s, s2s))
        | ((l1,Some s1)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let Some s2 = List.assoc l1 s2s
		in (** Assume input to optimizer typechecks *)
		   (l1,None) :: joinSums(s1s, s2s)
              with _ -> raise Impossible
	    else (l1,None) :: joinSums(s1s, s2s))


      in match (s1',s2') with
        | (SumTy lsos1, SumTy lsos2) -> SumTy (joinSums (lsos1, lsos2))
        | _ -> s1' (** We're assuming the input to the optimizer
                       typechecks! *)


(* optTy : ty -> ty

     Never returns TupleTy []
 *)
let rec optTy ctx ty = 
  let ans = match (hnfTy ctx ty) with
    ArrowTy (ty1, ty2) -> 
      (match (optTy ctx ty1, optTy ctx ty2) with
        (TopTy, ty2') -> ty2'
      | (_, TopTy)    -> TopTy
      | (ty1', ty2')   -> ArrowTy(ty1', ty2'))
  | TupleTy tys -> topTyize
        (TupleTy (List.filter notTopTy
                    (List.map (optTy ctx) tys)))
  | SumTy lst ->
      SumTy (List.map (function
			 (lb, None) -> (lb,None)
		       | (lb, Some ty) ->
			   (lb, 
			    match optTy ctx ty with
				TopTy -> None
			      | ty' -> Some ty')) lst)
  | nonunit_ty -> nonunit_ty
  in
    hnfTy ctx ans

let rec optBinds ctx = function
    [] -> []
  | (n,ty)::bnds ->
      (match optTy ctx ty with
	   TopTy -> optBinds ctx bnds
	 | ty' -> (n,ty')::(optBinds ctx bnds))

let simpleTerm = function
    Id _ -> true
  | Star -> true
  | Dagger -> true
  | _ -> false

let rec betaReduce = function
    App(Lambda ((nm, _), trm1), trm2) as trm ->
      if (simpleTerm trm2) then
         betaReduce (substTerm [] [(nm, trm2)] trm1)
      else
         trm
  | Proj(n, Tuple(trms)) ->
      betaReduce (List.nth trms n)
  | trm -> trm
    

(* optTerm ctx e = (t, e', t')
      where t  is the original type of e under ctx
            e' is the optimized version of e
            t' is the optimized type (i.e., the type of e')

      Never returns Tuple []
*)       
let rec optTerm ctx = function
   Id n -> (let oldty = peekLong lookupType ctx n
            in  match (optTy ctx oldty) with
                   TopTy -> (oldty, Dagger, TopTy)
                 | nonunit_ty -> (oldty, Id n, nonunit_ty))
 | Star -> (UnitTy, Star, UnitTy)
 | Dagger -> (print_string "Is this a Dagger which I see before me?\n";
	      (UnitTy, Dagger, UnitTy))
 | App(e1,e2) -> 
     let    (ArrowTy(ty2, oldty), e1', ty1') = optTerm ctx e1
     in let (_, e2', ty2') = optTerm ctx e2
     in let ty' = optTy ctx oldty
     in (match (ty', hnfTy ctx ty2') with
           (TopTy, _) -> (* Application can be eliminated entirely *)
                            ((oldty, Dagger, TopTy))
         | (_, TopTy) -> (* Argument is dagger and can be eliminated *)
                            ((oldty, e1', ty1'))
         | (ty', _)    -> (* Both parts matter.
                             Eliminate trivial beta-redices, though. *)
                            ((oldty, betaReduce (App(e1', e2')), ty')))
 | Lambda((name1, ty1), term2) ->
    (let    ty1' = optTy ctx ty1
     in let ctx' = insertType ctx name1 ty1
     in let (ty2, term2', ty2') = optTerm ctx' term2
     in let oldty = ArrowTy(ty1,ty2)
     in match (hnfTy ctx ty1', hnfTy ctx ty2') with
       (_,TopTy) -> (oldty, Dagger, TopTy)
     | (TopTy,_) -> (oldty, term2', ty2')
     | (_,_)     -> (oldty, Lambda((name1,ty1'),term2'), ArrowTy(ty1',ty2')))
 | Tuple es -> 
     let (ts, es', ts') = optTerms ctx es
     in (TupleTy ts, Tuple es', topTyize (TupleTy ts'))
 | Proj (n,e) ->
     let (ty, e', _) = optTerm ctx e
     in let tys = 
               match  hnfTy ctx ty with
		 TupleTy tys -> tys
	       |  ty_bad -> (print_string (Outsyn.string_of_ty ty ^ "\n");
			     print_string (Outsyn.string_of_ty ty_bad ^ "\n");
			     raise Impossible)
     in let rec loop = function
         (ty::tys, TopTy::tys', nonunits, index) ->
         if index == n then
           (* The projection is unit-like and can be eliminated entirely *)
           (ty, Dagger, TopTy)
	 else
	   loop(tys, tys', nonunits, index+1)
       | (ty::tys, ty'::tys', nonunits, index) ->
	 if index = n then
           (* The projection returns some interesting value.
              Check if it's the only interesting value in the tuple. *)
           if (nonunits = 0 && List.length(List.filter notTopTy tys')=0) then
              (* Yes; there were no non-unit types before or after. *)
	     (ty, e', ty')
           else
              (* Nope; there are multiple values so the tuple is 
                 still a tuple and this projection is still a projection *)
	     (ty, betaReduce (Proj(nonunits, e')), ty')
	 else
	   loop(tys, tys', nonunits+1, index+1)
       | (tys,tys',_,index) -> (print_string (string_of_int (List.length tys));
			    print_string (string_of_int (List.length tys'));
			    print_string (string_of_int n);
			    print_string (string_of_int index);
			    raise Impossible)
     in 
        loop (tys, List.map (optTy ctx) tys, 0, 0) 
 | Inj (lbl, None) -> (SumTy [(lbl,None)], Inj(lbl, None), SumTy [(lbl,None)])
 | Inj (lbl, Some e) ->
     let (ty, e', ty') = optTerm ctx e in
       if ty' = TopTy then
	 (SumTy [(lbl,Some ty)], Inj (lbl, None), SumTy[(lbl, None)])
       else
	 (SumTy [(lbl,Some ty)], Inj(lbl, Some e'), SumTy[(lbl, Some ty')])
 | Case (e, arms) ->
     let (ty, e', ty') = optTerm ctx e
     in let doArm = function
	 (lbl, Some (name2,ty2),  e3) -> 
	   let ty2' = optTy ctx ty2 
	   in let ctx' = insertType ctx name2 ty
	   in let (ty3, e3', ty3') = optTerm ctx' e3
	   in (ty3, (lbl, Some (name2, ty2'), e3'), ty3')
       | (lbl, None,  e3) -> 
	   let (ty3, e3', ty3') = optTerm ctx e3
	   in (ty3, (lbl, None, e3'), ty3')
     in let rec doArms = function
	 [] -> raise Impossible
       | [arm] -> let (tyarm, arm', tyarm') = doArm arm
	          in (tyarm, [arm'], tyarm')
       | arm::arms -> let (tyarm, arm', tyarm') = doArm arm
                      in let (tyarms, arms', tyarms') = doArms arms
		      in (joinTy ctx tyarm tyarms,
			  arm' :: arms',
			  (* XXX: doublecheck invariant that the 
			     thinned type never has a toplevel defn. *)
			  joinTy emptyCtx tyarm' tyarms')
     in let (tyarms, arms', tyarms') = doArms arms
     in (tyarms, Case(e',arms'), tyarms')

 | Let(name1, term1, term2) ->
     let    (ty1, term1', ty1') = optTerm ctx term1
     in let ctx' = insertType ctx name1 ty1
     in let (ty2, term2', ty2') = optTerm ctx' term2
     in (ty2, Let(name1, term1', term2'), ty2')

 | Obligation((name,ty), prop, trm) ->
     let    ty'  = optTy ctx ty
     in let ctx' = insertType ctx name ty
     in let prop' = optProp ctx' prop
     in let ty2', trm', ty2 = optTerm ctx' trm
     (** XXX: Is this the right typing rule for obligations? *)
     in (ty2', Obligation((name,ty'), prop', trm'), ty2)



and optTerms ctx = function 
    [] -> ([], [], [])   
  | e::es -> let (ty, e', ty') = optTerm ctx e
	     in let (tys, es', tys') = optTerms ctx es
             in (match (hnfTy ctx ty') with
               TopTy -> (ty :: tys, es', tys')
             | _ -> (ty :: tys, e'::es', ty'::tys'))
           

and optTerm' ctx e =
   let (_,e',_) = optTerm ctx e 
   in e'      

and optProp ctx = function
    True                    -> True
  | False                   -> False
  | IsPer nm                -> IsPer nm
  | IsPredicate nm          -> IsPredicate nm
  | NamedTotal(str, e)      -> 
      NamedTotal(str, optTerm' ctx e)
  | NamedPer(str, e1, e2)   -> 
      NamedPer (str, optTerm' ctx e1, optTerm' ctx e2)
  | NamedProp(str, e1, es2) -> 
      NamedProp(str, optTerm' ctx e1, List.map (optTerm' ctx) es2)
  | Equal(e1, e2) -> 
      let (_,e1',ty1') = optTerm ctx e1
      in let e2' = optTerm' ctx e2
      in (match (hnfTy ctx ty1') with
            TopTy -> True
(* AB:          | UnitTy -> True *)
	  | VoidTy -> True
          | _ -> Equal(e1',e2'))
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
        (True,  p2'  ) -> p2'
      | (False, _    ) -> True
      | (_,     True ) -> True
      | (p1',   False) -> Not p1'
      | (p1',   p2'  ) -> Imply(p1', p2'))

  | Iff (p1, p2) -> 
      (match (optProp ctx p1, optProp ctx p2) with
        (True,  p2'  ) -> p2'
      | (False, p2'  ) -> Not p2'
      | (p1',   True ) -> p1'
      | (p1',   False) -> Not p1'
      | (p1',   p2'  ) -> Iff(p1', p2'))

  | Not p -> (match optProp ctx p with
      True  -> False
    | False -> True
    | p'    -> Not p')

  | Forall((n,ty), p) ->
      let p' = optProp (insertType ctx n ty) p
      in (match (optTy ctx ty, p') with
        (_, True) -> True
      | (TopTy,_) -> p'
      | (NamedTy n1,Imply(NamedTotal (n2,Id n3),p'')) ->
	  if (LN(None,n) = n3) && (n1 = n2) then
	    ForallTotal((n,NamedTy n1), p'')
	  else
	    Forall((n,NamedTy n1),p')
      | (ty',_) -> Forall((n,ty'), p'))
 
  | ForallTotal((n,ty),p) ->
      let p' = optProp (insertType ctx n ty) p
      in Forall((n,optTy ctx ty), p')
 
  | Cexists ((n, ty), p) ->
      let p' = optProp (insertType ctx n ty) p in
	(match optTy ctx ty, p with
	     (_, False) -> False
	   | (TopTy, _) -> p'
	   | (ty', _) -> Cexists((n, ty'), p'))

and optAssertion ctx (name, bnds, prop) =
      let ctx' = insertTypeBnds ctx bnds in
      let bnds' = optBinds ctx bnds in
      let prop' = optProp ctx' prop
      in
	(name, bnds', prop')


and optElems ctx = function
    [] -> [], emptyCtx
  |  ValSpec(name, ty, assertions) :: rest ->
      let ty'  = optTy ctx ty in
      let ctx' = insertType ctx name ty in
      let assertions' = List.map (optAssertion ctx') assertions
      in let (rest', ctx'') = optElems (insertType ctx name ty) rest in
	(match ty' with
  	     TopTy -> 
	       (** Keep the (non-computational) assertions even if the 
		 computational part is elided for being trivial *)
	       (List.map (fun a -> AssertionSpec a) assertions' @ rest', ctx'')
	   | ty' ->
	       (ValSpec (name, ty', assertions') :: rest', 
		insertType ctx'' name ty'))
	
  |  AssertionSpec assertion  ::  rest ->
       let assertion' = optAssertion ctx assertion in
       let (rest', ctx') = optElems ctx rest in
	 (AssertionSpec assertion' :: rest'), ctx'

  | ModulSpec (name,signat) :: rest -> 
      let (signat',ctxopt') = optSignat ctx signat
      in let ctx'' = (match ctxopt' with
	                 Some ctx' -> insertModul ctx name ctx'
                       | None -> ctx)
      in let (rest', ctx''') = optElems ctx'' rest 
      in (ModulSpec (name, signat') :: rest',
	  ctx''')

  |  TySpec(nm, None, assertions) :: rest -> 
       (** We don't add nm to the input context of optAssertion
       because we never need to know whether something is a type or
       not; we're assuming that the input was well-formed *)
       let assertions' = List.map (optAssertion ctx) assertions in
       let rest', ctx'' = optElems ctx rest in
	 (TySpec (nm, None, assertions') :: rest'), insertTydef ctx'' nm TYPE

  |  TySpec(nm, Some ty, assertions) :: rest ->
       let ty' = optTy ctx ty in
	 (** We might care about expanding a definition for nm, though *)
       let ctx' = insertTydef ctx nm ty'  in
       let assertions' = List.map (optAssertion ctx') assertions in
       let rest', ctx'' = optElems ctx'  rest in
	 TySpec(nm, Some ty',assertions') :: rest', (insertTydef ctx'' nm ty')

  |  Comment cmmnt :: rest -> 
       let rest', ctx' = optElems ctx rest in
	 (Comment cmmnt :: rest', ctx')


and optSignat ctx = function
    SignatName s ->
      ( SignatName s, Some ( lookupModul ctx s ) )
  | Signat body -> 
      let body', ctx' = optElems ctx body in
      ( Signat body', Some ctx' )
  | SignatFunctor(args, body) ->
      let    ( args', ctx'  ) = optStructBindings ctx args
      in let ( body', ctx'' ) = optSignat ctx' body
      in ( SignatFunctor ( args', body' ), None )
      (* XXX:  We are failing to put any information into the context
         for functors, since the context doesn't support them yet *)


and optStructBindings ctx = function
    [] -> [], ctx
  | (m, signat) :: bnd ->
      let signat', ctxopt' = optSignat ctx signat in
      let bnd', ctx'' = optStructBindings ctx bnd in
	( (m, signat') :: bnd',
	  (match ctxopt' with
             Some ctx' -> insertModul ctx'' m ctx'
           | None      -> ctx'') )
        (* XXX: Again, ignoring functor variables ! *)

let optToplevel ctx = function
    (Signatdef (s, signat)) ->
      let signat', ctxopt' = optSignat ctx signat in
	( Signatdef (s, signat'), 
	  ( match ctxopt' with
              Some ctx' -> insertModul ctx s ctx'
            | None      -> ctx                   ) )
          (* XXX: Again, ignoring functor variables ! *)
  | TopComment cmmnt -> (TopComment cmmnt, ctx)
  | TopModul (mdlnm, signat) ->
      let (signat', ctxopt') = optSignat ctx signat in
	(TopModul(mdlnm, signat'), 
	  ( match ctxopt' with
              Some ctx' -> insertModul ctx mdlnm ctx'
            | None      -> ctx                   ) )
          (* XXX: Again, ignoring functor variables ! *)

let rec optToplevels' ctx = function
    [] -> ([], ctx)
  | sg :: lst ->
      let sg', ctx' = optToplevel ctx sg in
      let lst', ctx'' = optToplevels' ctx' lst in
	(sg'::lst', ctx'')

let optToplevels ctx sigs =
  if !Flags.do_opt then optToplevels' ctx sigs else (sigs,ctx)
