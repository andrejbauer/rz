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
let insertbnds (bnds, env) = bnds @ env
exception NotFound
let rec lookup = function
      (y,[]) -> (raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookup(y,rest)


let rec peek = function
      (y,[]) -> None
    | (y,(k,v)::rest) -> if (y=k) then Some v else peek(y,rest)

let rec lookupName = function
      (y,[]) -> (print_string ("Unbound name: " ^ string_of_name y ^ "\n");
                 raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookupName(y,rest)

(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)

(** Context carried around by the type reconstruction algorithm.
 *)
type ctx = {types      : (name*ty) list;
               (** Typing context; types for names in scope *)
            tydefs     : (string*ty) list;
               (** Definitions of type/set variables in scope *)
            models     : (string*ctx) list
           }

let rec string_of_ctx {types=types; tydefs=tydefs; models=models} =
  "{ types = [" ^ (String.concat "," (List.map (fun (n,t) -> (string_of_name n) ^ ":" ^ (string_of_ty t)) types)) ^ "],\n" ^
  "  tydefs = [" ^ (String.concat "," (List.map (fun (n,t) -> n ^ ":" ^ (string_of_ty t)) tydefs)) ^ "],\n" ^
  "  models = [" ^ (String.concat "," (List.map (fun (n,t) -> n ^ ":" ^ (string_of_ctx t)) models)) ^ "],\n" ^
 "}"

(** Determines whether a variable has an implicitly declared type.
     @param ctx  The type reconstruction context
     @param str  The (string) name of the variable.
  *)
let lookupType     ctx   n = lookupName (n, ctx.types)
let lookupTydef    ctx str = lookup (str, ctx.tydefs)
let lookupModel    ctx str = lookup (str, ctx.models)
let peekTydef ctx s = peek(s, ctx.tydefs)

let insertType ({types=types} as ctx) n ty = 
       {ctx with types = insert(n,ty,types)}
let insertTypeBnds ({types=types} as ctx) bnds = 
       {ctx with types = insertbnds(bnds,types)}
let insertTydef ({tydefs=tydefs} as ctx) str ty = 
       {ctx with tydefs = insert(str,ty,tydefs)}
let insertModel ({models=models} as ctx) str ctx' = 
       {ctx with models = insert(str,ctx',models)}

let emptyCtx = {types = []; tydefs = []; models = []}

let rec peekLong peeker ctx = function
    (Syntax.LN(str, [], namesort) as lname) -> 
       peeker ctx (Syntax.N(str,namesort))
  | (Syntax.LN(str, label::labels, namesort) as lname) ->
       let ctx' = lookupModel ctx str in
	 peekLong peeker ctx' (Syntax.LN(label,labels,namesort))

(** Expand out any top-level definitions for a set *)
let rec hnfTy ctx = function
    NamedTy n ->
      (match (peekTydef ctx (string_of_longname n)) with
        Some s' -> hnfTy ctx s'
      | None -> NamedTy n)
  | s -> s


(*******************)

let notTopTy = function
      TopTy -> false
    | _ -> true

let topTyize = function
      TupleTy [] -> TopTy
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
         | (ty', _)    -> (* Both parts matter *)
                            ((oldty, App(e1', e2'), ty')))
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
     in (topTyize (TupleTy ts), Tuple es', topTyize (TupleTy ts'))
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
	     (ty, Proj(nonunits, e'), ty')
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

 | Obligation((name,ty), prop) ->
     let    ty'  = optTy ctx ty
     in let ctx' = insertType ctx name ty
     in let prop' = optProp ctx' prop
     (** XXX: Is this the right typing rule for obligations? *)
     in (ty, Obligation((name,ty'), prop'), ty')



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
    True -> True
  | False -> False
  | NamedTotal(str, e) -> NamedTotal(str, optTerm' ctx e)
  | NamedPer(str, e1, e2) -> NamedPer(str, optTerm' ctx e1, optTerm' ctx e2)
  | NamedProp(str, e1, e2) -> NamedProp(str, optTerm' ctx e1, optTerm' ctx e2)
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
      True -> False
    | False -> True
    | p' -> Not p')

  | Forall((n,ty), p) ->
      let p' = optProp (insertType ctx n ty) p
      in (match (optTy ctx ty, p') with
        (_, True) -> True
      | (TopTy,_) -> p'
      | (ty',_) -> Forall((n,ty'), p'))

  | Cexists ((n, ty), p) ->
      let p' = optProp (insertType ctx n ty) p in
	(match optTy ctx ty, p with
	     (_, False) -> False
	   | (TopTy, _) -> p'
	   | (ty', _) -> Cexists((n, ty'), p'))

      
and optElems ctx = function
    [] -> [], emptyCtx
  |  ValSpec(name, ty) :: rest ->
      let    ty'   = optTy ctx ty
      in let rest', ctx' = optElems (insertType ctx name ty) rest in
	(match ty' with
  	     TopTy -> 
	       rest', ctx'
	   | ty' ->
	       ValSpec (name, ty') :: rest', (insertType ctx' name ty'))
	
  |  AssertionSpec(name, bnds, prop) :: rest ->
       let ctx' = insertTypeBnds ctx bnds in
       let bnds' = optBinds ctx bnds in
       let rest', ctx'' = optElems ctx rest in
	 (AssertionSpec (name, bnds', optProp ctx' prop) :: rest'), ctx''

  |  TySpec(Syntax.N(str,_) as n, None) :: rest -> 
       let rest', ctx' = optElems ctx rest in
	 (TySpec (n, None) :: rest'), insertTydef ctx' str TYPE

  |  TySpec(Syntax.N(str,_) as n, Some ty) :: rest ->
       let ty' = optTy ctx ty in
       let rest', ctx' = optElems (insertTydef ctx str ty') rest in
	 TySpec(n, Some ty') :: rest', (insertTydef ctx' str ty')

let optSignat ctx = function
    SignatID s ->
      SignatID s, lookupModel ctx s
  | Signat body -> 
      let body', ctx' = optElems ctx body in
	Signat body', ctx'

let rec optStructBinding ctx = function
    [] -> [], ctx
  | (m, signat) :: bnd ->
      let signat', ctx' = optSignat ctx signat in
      let bnd', ctx'' = optStructBinding ctx bnd in
	(m, signat') :: bnd',
	insertModel ctx'' m ctx'

let optSignatdef ctx (Signatdef (s, args, signat)) =
  let args', ctx' = optStructBinding ctx args in
  let signat', ctx'' = optSignat ctx' signat in
    Signatdef (s, args', signat'), ctx''
    
let rec optSignatdefs ctx = function
    [] -> []
  | (Signatdef (s, args, signat) as sg) :: lst ->
      let sg', ctx' = optSignatdef ctx sg in
	sg' :: (optSignatdefs (insertModel ctx s ctx') lst)
