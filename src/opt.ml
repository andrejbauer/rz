(** XXX: Can we avoid expanding out all the type definitions? *)

(*******************************************************************)
(** {1 TopTy Elimination}                                          *)
(**                                                                *)
(** For now we assume that                                         *)
(** all bound variables are annotated, either when declared        *)
(** or through a prior "implicit" statement.                       *)
(*******************************************************************)

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
               (** Typing context; types for names in scope.
		   Records the UNoptimized type. *)
            tydefs     : ty NameMap.t;
               (** Definitions of type variables in scope.
                   Records the UNoptimized type definition *)
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


let nonTopTy = function
      TopTy -> false
    | _ -> true

let topTyize = function
      TupleTy [] -> TopTy
    | TupleTy [ty] -> ty
    | ty -> ty

 
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


(***************************)
(** Optimization functions *)
(***************************)



(* optTy : ty -> ty

     Never returns TupleTy [] or TupleTy[_]
 *)
let rec optTy ctx ty = 
  let ans = match (hnfTy ctx ty) with
    ArrowTy (ty1, ty2) -> 
      (match (optTy ctx ty1, optTy ctx ty2) with
        (TopTy, ty2')  -> ty2'
      | (_,     TopTy) -> TopTy
      | (ty1',  ty2')  -> ArrowTy(ty1', ty2'))

    | TupleTy tys -> 
	let tys' = List.filter nonTopTy (List.map (optTy ctx) tys)
	in topTyize (TupleTy tys')
	  
    | SumTy lst ->
	SumTy (List.map (function
	 		 (lbl, None) ->    (lbl, None)
		       | (lbl, Some ty) -> (lbl, match optTy ctx ty with
			                           TopTy -> None
 			                         | ty' -> Some ty')) 
                      lst)

    | nonunit_ty -> nonunit_ty
  in
    hnfTy ctx ans

let rec optTyOption ctx = function
    None    -> None
  | Some ty -> Some (optTy ctx ty)

(** optBinds: ctx -> binding list -> binding list

    Thins all the types in the binding, and removes any bindings
    of variables to TopTy.
*)
let rec optBinds ctx = function
    [] -> []
  | (n,ty) :: bnds ->
      (match optTy ctx ty with
	   TopTy -> optBinds ctx bnds
	 | ty' -> (n,ty')::(optBinds ctx bnds))

(* optTerm ctx e = (t, e', t')
      where t  is the original type of e under ctx
            e' is the optimized version of e
            t' is the optimized type (i.e., the type of e')

      Never returns Tuple [] or Tuple [x]
*)       
let rec optTerm ctx = function
   Id n -> (let oldty = lookupTypeLong ctx n
            in  match (optTy ctx oldty) with
                   TopTy -> (oldty, Dagger, TopTy)
                 | nonunit_ty -> (oldty, Id n, nonunit_ty))
 | EmptyTuple -> (UnitTy, EmptyTuple, UnitTy)
 | Dagger -> ((* print_string "Is this a Dagger which I see before me?\n"; *)
	      (TopTy, Dagger, TopTy))
 | App(e1,e2) -> 
     begin
       match optTerm ctx e1 with
         (ArrowTy(ty2, oldty), e1', ty1') ->
	 let (_, e2', ty2') = optTerm ctx e2
	 in let ty' = optTy ctx oldty
	 in (match (ty', hnfTy ctx ty2') with
		   (TopTy, _) -> (* Application can be eliminated entirely *)
		   ((oldty, Dagger, TopTy))
		   | (_, TopTy) -> (* Argument is dagger and can be eliminated *)
                            ((oldty, e1', ty1'))
         | (ty', _)    -> (* Both parts matter.
                             Eliminate trivial beta-redices, though. *)
	 ((oldty, optReduce ctx (App(e1', e2')), ty')))
      | (t1, _, _) -> (print_string "In application ";
                       print_string (Outsyn.string_of_term (App(e1,e2)));
                       print_string " the operator has type ";
                       print_endline (Outsyn.string_of_ty t1);
                       raise (Impossible "App"))
    end
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
     in let e' = 
       (match es' with
	   [] -> Dagger
	 | [e] -> e
	 | _ -> Tuple es')
     in (TupleTy ts, e', topTyize (TupleTy ts'))
 | Proj (n,e) as proj_code ->
     let (ty, e', _) = optTerm ctx e
     in let tys = 
               match  hnfTy ctx ty with
		 TupleTy tys -> tys
	       | ty_bad -> (print_string (Outsyn.string_of_ty ty ^ "\n");
			    print_string (Outsyn.string_of_ty ty_bad ^ "\n");
			    print_endline (Outsyn.string_of_term proj_code);
			    raise (Impossible "Proj"))
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
           if (nonunits = 0 && List.length(List.filter nonTopTy tys')=0) then
              (* Yes; there were no non-unit types before or after. *)
	     (ty, e', ty')
           else
              (* Nope; there are multiple values so the tuple is 
                 still a tuple and this projection is still a projection *)
	     (ty, optReduce ctx (Proj(nonunits, e')), ty')
	 else
	   loop(tys, tys', nonunits+1, index+1)
       | (tys,tys',_,index) -> (print_string (string_of_int (List.length tys));
			    print_string (string_of_int (List.length tys'));
			    print_string (string_of_int n);
			    print_string (string_of_int index);
			    raise (Impossible "deep inside"))
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
	 [] -> raise (Impossible "Case")
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
     in (tyarms, optReduce ctx (Case(e',arms')), tyarms')

 | Let(name1, term1, term2) ->
     (* Phase 1: Basic Optimization *)
     let    (ty1, term1', ty1') = optTerm ctx term1
     in let ctx' = insertTermdef (insertType ctx name1 ty1) name1 term1'
     in let (ty2, term2', ty2') = optTerm ctx' term2
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
     in (ty2, trm'', ty2')

 | Obligation(bnds, prop, trm) ->
     let (names,tys) = List.split bnds
     in let tys'  = List.map (optTy ctx) tys
     in let bnds' = List.combine names tys'
     in let bnds'' = List.filter (fun (n,t) -> t <> TopTy) bnds'
     in let ctx' = List.fold_left2 insertType ctx names tys
     in let prop' = optProp ctx' prop
     in let ty2', trm', ty2 = optTerm ctx' trm
     in begin
	 match (bnds'', prop') with
	     ([], True) -> (ty2', trm', ty2)
	   | _ -> (ty2', Obligation(bnds'', prop', trm'), ty2)
       end


and optReduce ctx trm =
  let trm' = reduce trm
  in 
    if trm <> trm' then
      let (_,trm'',_) = optTerm ctx trm' in trm''
    else
      trm'

and optReduceProp ctx prp =
  let prp' = reduceProp prp
  in 
    if prp <> prp' then
      optProp ctx prp'
    else
      prp'

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

and optTerms' ctx lst =
  let (_, es, _) = optTerms ctx lst in es

and optProp ctx prp = 
  match prp with
    True                    -> True
  | False                   -> False
  | IsPer (nm, lst)         -> IsPer (nm, optTerms' ctx lst)
  | IsPredicate (nm, ty, lst) ->
      IsPredicate (nm, optTyOption ctx ty, List.map (fun (nm, ms) -> (nm, optModest ctx ms)) lst)
  | IsEquiv (p, ms)         -> IsEquiv (optProp ctx p, optModest ctx ms)
  | NamedTotal (n, lst)     -> NamedTotal (n, optTerms' ctx lst)
  | NamedPer (n, lst)       -> NamedPer (n, optTerms' ctx lst)
  | NamedProp (n, t, lst)   -> NamedProp (n, optTerm' ctx t, optTerms' ctx lst)
  | Equal(e1, e2) -> 
      let (_,e1',ty1') = optTerm ctx e1
      in let e2' = optTerm' ctx e2
      in

(* (match (hnfTy ctx ty1') with
            TopTy -> True
	  | VoidTy -> True
	  | SumTy _ ->
	      (match e1', e2' with
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
	      )
          | _ ->*) Equal(e1',e2') (* )  *)
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
    | Not (Not p') -> Not p'
    | p'    -> Not p')

  | Forall((n,ty), p) ->
      let p' = optProp (insertType ctx n ty) p
      in (match (optTy ctx ty, p') with
        (_, True) -> True
      | (TopTy,_) -> p'
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
	   | (TopTy, _) -> p'
	   | (ty', _) -> Cexists((n, ty'), p'))

  | PObligation (bnds, p, q) ->
     let (names,tys) = List.split bnds
     in let tys'  = List.map (optTy ctx) tys
     in let bnds' = List.combine names tys'
     in let bnds'' = List.filter (fun (n,t) -> t <> TopTy) bnds'
     in let ctx' = List.fold_left2 insertType ctx names tys
     in let p' = optProp ctx' p
     in let q' = optProp ctx' q
     in 
	  begin
	    match (bnds'', p') with
		([], True) -> q'
	      | _ -> PObligation(bnds'', p', q')
	  end

  | PMLambda ((n, ms), p) ->
      let ms' = optModest ctx ms in
      let p' = optProp (insertType ctx n ms.ty) p
      in let pre = (PMLambda ((n,ms'), p'))
      in optReduceProp ctx pre

  | PMApp (p, t) -> optReduceProp ctx (PMApp (optProp ctx p, optTerm' ctx t))

  | PLambda ((n,ty), p) ->
      begin
	let p' = optProp (insertType ctx n ty) p
	in let ty' = optTy ctx ty
	in 
	     match ty' with
		 TopTy -> p'
	       | _ -> optReduceProp ctx (PLambda((n,ty'), p'))
      end

  | PApp (p, t) -> 
      begin
	let p' = optProp ctx p
	in let (_,t',ty') = optTerm ctx t
	in 
	     match ty' with
		 TopTy -> p'
	       | _ -> optReduceProp ctx (PApp(p', t'))
      end

  | PCase (e1, e2, arms) ->
      let doBind ctx0 = function
	  None -> None, ctx0
	| Some (nm, ty) ->
	    (match optTy ctx ty with
		TopTy -> None, ctx0
	      | ty' -> Some (nm, ty'), insertType ctx0 nm ty)
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
      let    (ty1, trm1', ty1') = optTerm ctx trm1
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
  if !Flags.do_opt then optToplevels' ctx sigs else (sigs,ctx)
