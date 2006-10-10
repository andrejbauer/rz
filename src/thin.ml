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
open Outsynrules

exception Unimplemented
exception Impossible of string


(**************************)
(** {2: Thinning Context} *)
(**************************)

(** As originally written, this code maintained a single typing
    context --- tracking only the *unthinned*
    types/signatures/definitions of variables.  Then, if the thinned
    type/signature/definition of a variable were needed, we'd just
    rerun thinning on that definition.

    Unfortunately, this turned out not to work completely.  In the
    presence of dependencies and type definitions we must avoid
    shadowing, and if you have a model whose signature declares a type
    n, and then later you have a local variable "n", and then still
    later you use that model, re-running thinning on the signature at
    that point, which now already contains the local n, is treated as
    un-avoidable shadowing and the code aborts.

    So, we give in, and maintain two contexts: the unthinned context and
    the thinned context.

    We only use the renamings in the first (unthinned) context!

*)

module OR = Outsynrules

(** Unthinned and thinned contexts *)
type context = OR.context * OR.context

let emptyContext = (OR.emptyContext, OR.emptyContext)

let wrapLookup lookupFn (ctx,tctx) nm = 
  (lookupFn ctx nm, lookupFn tctx nm)

let lookupTermVariable = wrapLookup OR.lookupTermVariable
let lookupTypeVariable = wrapLookup OR.lookupTypeVariable
let lookupModulVariable = wrapLookup OR.lookupModulVariable
let lookupSignatVariable = wrapLookup OR.lookupSignatVariable

let wrapInsert insertFn (ctx,tctx) nm (ty,tty) =
  (insertFn ctx nm ty, insertFn tctx nm tty)

let insertTermVariable = wrapInsert OR.insertTermVariable
let insertTypeVariable = wrapInsert OR.insertTypeVariable
let insertModulVariable = wrapInsert OR.insertModulVariable
let insertSignatVariable = wrapInsert OR.insertSignatVariable

let hnfSignats (ctx, tctx) (sg,sg') =
  (hnfSignat ctx sg, hnfSignat tctx sg')

let hnfSignat(ctx, _) = hnfSignat ctx
let hnfTy (ctx, _)    = OR.hnfTy ctx
let hnfTy' (_, tctx)  = OR.hnfTy tctx


let wrapRename renameFn ((ctx, tctx):context) (nm:name) =
  let (ctx', nm') = renameFn ctx nm
  in ((ctx', tctx), nm')

let renameBoundTermVar  = wrapRename OR.renameBoundTermVar
let renameBoundTypeVar  = wrapRename OR.renameBoundTypeVar
let renameBoundModulVar = wrapRename OR.renameBoundModulVar

(* We completely re-do this one function, rather than wrap
   OR.renameTermBindings, because we need to make sure that the
   bindings are added to *both* contexts *)
let rec renameTermBindings cntxt bnds bnds' = 
  match (bnds, bnds') with
      ([],[]) -> (cntxt, [])
    | ((nm,ty)::bnds, (nm',ty')::bnds') when nm = nm' -> 
	let (cntxt', nm') = renameBoundTermVar cntxt nm
	in let cntxt'' = insertTermVariable cntxt' nm' (ty,ty')
	in let (cntxt''', bnds') = renameTermBindings cntxt'' bnds bnds'
	in (cntxt''', (nm',ty')::bnds')
    | _ -> failwith "Thin.renameTermBindings"
	    
let wrapApply applyFn ((ctx, _):context) (nm:name) =
  applyFn ctx nm

let applyTermRenaming  = wrapApply OR.applyTermRenaming 
let applyTypeRenaming  = wrapApply OR.applyTypeRenaming 
let applyModulRenaming = wrapApply OR.applyModulRenaming

let joinTy (ctx,_)    = OR.joinTy ctx 
let joinTy' (_, tctx) = OR.joinTy tctx 

  
(*******************)
(** Set operations *)
(*******************)


let nonTopTy ctx ty =
  match hnfTy' ctx ty with
    TopTy -> false
  | _     -> true

let toptyize ctx orig_type = 
  match hnfTy ctx orig_type with
      TupleTy []            -> TopTy
    | TupleTy [ty]          -> ty
    | SumTy   []            -> VoidTy
    | _                     -> orig_type
 


(***************************)
(** Thinimization functions *)
(***************************)



(* thinTy : ty -> ty

     Never returns 
       TupleTy []
       TupleTy[_]
       SumTy   []

     And, never returns anything equivalent to TopTy except
     TopTy itself.

 *)
let rec thinTy (ctx: context) orig_type = 
  match orig_type with
    ArrowTy (ty1, ty2) -> 
      let ty1' = thinTy ctx ty1
      in let ty2' = thinTy ctx ty2
      in
      (match (ty1', ty2') with
        (TopTy, _)     -> ty2'
      | (_,     TopTy) -> TopTy
      | _              -> ArrowTy(ty1', ty2'))

    | TupleTy tys -> 
	let tys' = List.filter (nonTopTy ctx) (List.map (thinTy ctx) tys)
	in toptyize ctx (TupleTy tys')
	  
    | SumTy lst ->
	let rec filterArms = function
	    [] -> []
	  | (lbl,None) :: rest -> (lbl,None) :: filterArms rest
	  | (lbl, Some ty) :: rest ->
	      let ty' = thinTy ctx ty
	      in match ty' with
	      | TopTy  -> (lbl, None) :: filterArms rest
	      | _      -> (lbl, Some ty') :: filterArms rest
	in
	   toptyize ctx (SumTy (filterArms lst))

    | NamedTy _ ->
	(** Normally when the input is a type abbreviation with a
	definition , then we can just return that type abbreviation
	unchanged because its definition would have been thinned.
	However, if a type is just an abbreviation for top it might
	disappear completely, in which case we should return TopTy
	instead. *)
	(match hnfTy ctx orig_type with
	  TopTy -> TopTy
	| _ -> orig_type)

    | _ -> orig_type


let rec thinTyOption ctx = function
    None    -> None
  | Some ty -> Some (thinTy ctx ty)

(** thinBinds: ctx -> binding list -> binding list

    Thins all the types in the binding, and removes any bindings
    of variables to TopTy.
*)
let rec thinBinds ctx = function
    [] -> []
  | (n,ty) :: bnds ->
      let ty' = thinTy ctx ty
      in match ty' with
	TopTy -> thinBinds ctx bnds
      | _     -> (n,ty')::(thinBinds ctx bnds)

let wrapObsTerm disappearingTerm wrapee =
  let (obs, _) = hoist disappearingTerm
  in foldObligation obs wrapee

let wrapObsProp disappearingTerm wrapee =
  let (obs, _) = hoist disappearingTerm
  in foldPObligation obs wrapee

let wrapPObsProp disappearingProp wrapee =
  let (obs, _) = hoistProp disappearingProp
  in foldPObligation obs wrapee

(* thinTerm ctx e = (t, e', t')
      where t  is the original type of e under ctx
            e' is the thinimized version of e
            t' is the thinimized type (i.e., the type of e')

      Never returns Tuple [] or Tuple [x] or an injection into a
      single-element sum.
*)       
let rec thinTerm (ctx : context) orig_term = 
  try
    match orig_term with
	Id (LN(None,nm)) ->
	  begin
	    let nm = applyTermRenaming ctx nm
	    in let (oldty, newty) = lookupTermVariable ctx nm
            in  match newty with
		TopTy -> (oldty, wrapObsTerm orig_term Dagger, TopTy)
              | _     -> (oldty, Id(LN(None,nm)), newty)
	  end
      | Id (LN(Some mdl, nm)) ->
	  begin
	    let (sg, mdl', sg') = thinModul ctx mdl
	    in let (oldty,newty) = 
	      match hnfSignats ctx (sg,sg') with
		  (Signat elems, Signat elems') -> 
		    (findTermvarInElems elems mdl nm,
		     findTermvarInElems elems' mdl' nm)
		| _ -> failwith "Thin.thinTerm: invalid path"
	    in match newty with
		TopTy -> (oldty, wrapObsTerm orig_term Dagger, TopTy)
	      | _     -> (oldty, Id(LN(Some mdl',nm)), newty)
	  end

      | EmptyTuple -> (UnitTy, EmptyTuple, UnitTy)

      | Dagger -> (TopTy, Dagger, TopTy)

      | App(e1,e2) -> 
	  begin
	    match thinTerm ctx e1 with
		(ArrowTy(ty2, oldty), e1', ty1') ->
		  let (_, e2', ty2') = thinTerm ctx e2
		  in let ty' = thinTy ctx oldty
		  in let trm' = App(e1', e2')
		  in (match (ty', ty2') with
		      (TopTy, _) -> 
                        (* Application can be eliminated entirely *)
			((oldty, wrapObsTerm trm' Dagger, TopTy))
		    | (_, TopTy) -> 
                        (* Argument is dagger and can be eliminated *)
                        ((oldty, wrapObsTerm e2' e1', ty1'))
		    | (ty', _)    -> 
                        (* Both parts matter. *)
			((oldty, (App(e1', e2')), ty')))
	      | (t1, _, _) -> (print_string "In application ";
			       print_string (Outsyn.string_of_term (App(e1,e2)));
			       print_string " the operator has type ";
			       print_endline (Outsyn.string_of_ty t1);
			       raise (Impossible "App"))
	  end
      | Lambda((name1, ty1), term2) ->
	  (let    ty1' = thinTy ctx ty1
	    in let (ctx,name1) = renameBoundTermVar ctx name1
	    in let ctx' = insertTermVariable ctx name1 (ty1,ty1')
	    in let (ty2, term2', ty2') = thinTerm ctx' term2
	    in let oldty = ArrowTy(ty1,ty2)
	    in let trm' = Lambda((name1,ty1'),term2')
	    in match (ty1', ty2') with
	      | (TopTy, TopTy) -> (oldty, wrapObsTerm term2' Dagger, TopTy)
	      | (_,     TopTy) -> (oldty, wrapObsTerm trm' Dagger, TopTy)
	      | (TopTy, _    ) -> (oldty, term2', ty2')
	      | (_,     _    ) -> (oldty, trm', ArrowTy(ty1',ty2')))
      | Tuple es -> 
	  let (ts, es', obs, ts') = thinTerms ctx es
	  in let e' = 
	    foldObligation obs
	      (match es' with
		  [] -> Dagger
		| [e] -> e
		| _ -> Tuple es')
	  in (TupleTy ts, e', toptyize ctx (TupleTy ts'))
      | Proj (n,e) as proj_code ->
	  let (ty, e', ty') = thinTerm ctx e
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
		  (ty, wrapObsTerm e' Dagger, TopTy)
		else
		  loop(tys, tys', nonunits, index+1)
	    | (ty::tys, ty'::tys', nonunits, index) ->
		if index = n then
		  (* The projection returns some interesting value.
		     Check if it's the only interesting value in the tuple. *)
		  if (nonunits = 0 && 
		      List.length(List.filter (nonTopTy ctx) tys')=0) then
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
				     raise (Impossible "deep inside"))
	  in 
               loop (tys, List.map (thinTy ctx) tys, 0, 0) 
      | Inj (lbl, None) -> 
	  (SumTy [(lbl,None)], Inj(lbl, None), SumTy [(lbl,None)])
      | Inj (lbl, Some e) ->
	  begin
	    let (ty, e', ty') = thinTerm ctx e
	    in match ty' with
	      TopTy -> 
		(SumTy [(lbl,Some ty)], 
		 wrapObsTerm e' (Inj (lbl, None)), 
		 SumTy[(lbl, None)])
	    | _ -> 
		(SumTy [(lbl,Some ty)], 
		 Inj(lbl, Some e'), 
		 SumTy[(lbl, Some ty')])
	  end
      | Case (e, arms) ->
	  let (ty, e', ty') = thinTerm ctx e
	  in let doArm = function
	      (lbl, Some (name2,ty2),  e3) -> 
		let ty2' = thinTy ctx ty2 
		in let (ctx,name2) = renameBoundTermVar ctx name2
		in let ctx' = insertTermVariable ctx name2 (ty,ty')
		in let (ty3, e3', ty3') = thinTerm ctx' e3
		in (ty3, (lbl, Some (name2, ty2'), e3'), ty3')
	    | (lbl, None,  e3) -> 
		let (ty3, e3', ty3') = thinTerm ctx e3
		in (ty3, (lbl, None, e3'), ty3')
	  in let rec doArms = function
	      [] -> raise (Impossible "Case")
	    | [arm] -> let (tyarm, arm', tyarm') = doArm arm
	      in (tyarm, [arm'], tyarm')
	    | arm::arms -> let (tyarm, arm', tyarm') = doArm arm
              in let (tyarms, arms', tyarms') = doArms arms
	      in (joinTy ctx tyarm tyarms,
		 arm' :: arms',
		 joinTy' ctx tyarm' tyarms')
	  in let (tyarms, arms', tyarms') = doArms arms
	  in (tyarms, Case(e',arms'), tyarms')

      | Let(name1, term1, term2) ->
	  begin
	    let    (ty1, term1', ty1') = thinTerm ctx term1
	    in let (ctx,name1) = renameBoundTermVar ctx name1
	    in let ctx' = insertTermVariable ctx name1 (ty1,ty1')
	    in let (ty2, term2', ty2') = thinTerm ctx' term2
	    in match ty1' with
		TopTy -> (ty2, wrapObsTerm term1' term2', ty2')
	      | _ -> (ty2, Let(name1, term1', term2'), ty2')
	  end

      | Obligation(bnds, prop, trm) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (thinTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = renameTermBindings ctx bnds bnds'
	  in let bnds''' = List.filter (fun (n,t) -> t <> TopTy) bnds''
	  in let prop' = thinProp ctx' prop
	  in let ty2, trm', ty2' = thinTerm ctx' trm
	  in (ty2, Obligation(bnds''', prop', trm'), ty2')

      | PolyInst _ ->
	  failwith "Thin.thinTerm:  unexpected PolyInst"

  with e ->
    (print_endline ("\n\n...in (thin term) " ^
		       string_of_term orig_term);
     raise e)

and thinTerms (ctx : context) = function 
    [] -> ([], [], [], [])   
  | e::es -> let (ty, e', ty') = thinTerm ctx e
    in let (tys, es', obss, tys') = thinTerms ctx es
    in (match (hnfTy ctx ty') with
        TopTy -> 
	  let (obs,_) = hoist e'
	  in (ty :: tys, es', obs@obss, tys')
      | _ -> (ty :: tys, e'::es', obss, ty'::tys'))
      

and thinTerm' (ctx: context) e =
  let (_,e',_) = thinTerm ctx e 
  in e'      

and thinTerms' (ctx: context) lst =
  let (_, es, obs, _) = thinTerms ctx lst in (obs, es)

and thinProp (ctx: context) orig_prp = 
  try
    match orig_prp with
	True                    -> True
      | False                   -> False
      | NamedTotal (n, lst)     -> 
	  let (obs, lst') = thinTerms' ctx lst
	  in foldPObligation obs (NamedTotal (n, lst'))
      | NamedPer (n, lst)       -> 
	  let (obs, lst') = thinTerms' ctx lst
	  in foldPObligation obs (NamedPer (n, lst'))
      | NamedProp (n, t, lst)   -> 
	  let (obs, lst') = thinTerms' ctx lst
	  in foldPObligation obs (NamedProp (n, thinTerm' ctx t, lst'))
      | Equal(e1, e2) -> 
	  let (_,e1',ty1') = thinTerm ctx e1
	  in let e2' = thinTerm' ctx e2
	  in Equal(e1',e2')
      | And ps -> And (List.map (thinProp ctx) ps)
      | Cor ps -> Cor (List.map (thinProp ctx) ps)
      | Imply (p1, p2) -> Imply(thinProp ctx p1, thinProp ctx p2)
      | Iff (p1, p2) -> Iff(thinProp ctx p1, thinProp ctx p2)
      | Not p -> Not (thinProp ctx p)

      | Forall((n,ty), p) ->
	  let ty' = thinTy ctx ty
	  in let (ctx,n) = renameBoundTermVar ctx n
	  in let p' = thinProp (insertTermVariable ctx n (ty,ty')) p
	  in (match ty' with
	    | TopTy -> p'
	    | _ -> Forall((n,ty'), p'))
	    
      | ForallTotal((n,ln),p) ->
	  let ty = NamedTy ln
	  in let ty' = thinTy ctx ty
	  in let (ctx,n) = renameBoundTermVar ctx n
	  in let p' = thinProp (insertTermVariable ctx n (ty,ty')) p
	  in ForallTotal((n,ln), p')
	    
      | Cexists ((n, ty), p) ->
	  let ty' = thinTy ctx ty
	  in let (ctx,n) = renameBoundTermVar ctx n
	  in let p' = thinProp (insertTermVariable ctx n (ty,ty')) p in
	    (match ty' with
	      | TopTy -> p'
	      | _ -> Cexists((n, ty'), p'))

      | PObligation (bnds, p, q) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (thinTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = renameTermBindings ctx bnds bnds'
	  in let bnds''' = List.filter (fun (n,t) -> t <> TopTy) bnds''
	  in let p' = thinProp ctx' p
	  in let q' = thinProp ctx' q
	  in 
	       PObligation(bnds''', p', q')


      | PMLambda ((n, ms), p) ->
	  let ms' = thinModest ctx ms
	  in let (ctx,n) = renameBoundTermVar ctx n
	  in let p' = thinProp (insertTermVariable ctx n (ms.ty,ms'.ty)) p
	  in 
	    PMLambda ((n,ms'), p')

      | PMApp (p, t) -> 
	  PMApp (thinProp ctx p, thinTerm' ctx t)

      | PLambda ((n,ty), p) ->
	  begin
	    let ty' = thinTy ctx ty
	    in let (ctx,n) = renameBoundTermVar ctx n
	    in let p' = thinProp (insertTermVariable ctx n (ty,ty')) p
	    in 
		 match ty' with
		     TopTy -> p'
		   | _     -> PLambda((n,ty'), p')
	  end
	    
      | PApp (p, t) -> 
	  begin
	    let p' = thinProp ctx p
	    in let (_,t',ty') = thinTerm ctx t
	    in 
		 match ty' with
		     TopTy -> wrapObsProp t p'
		   | _     -> PApp(p', t')
	  end

      | PCase (e1, e2, arms) ->
	  let doBind ctx0 = function
	      None -> None, ctx0
	    | Some (nm, ty) ->
		let ty' = thinTy ctx ty
		in let (ctx0, nm) = renameBoundTermVar ctx0 nm
		in 
		     (match ty' with
			 TopTy -> None, ctx0
		       | _ -> (Some (nm, ty'), 
			      insertTermVariable ctx0 nm (ty,ty')))
	  in let doArm (lbl, bnd1, bnd2, p) =
	    let bnd1', ctx1 = doBind ctx  bnd1 in
	    let bnd2', ctx2 = doBind ctx1 bnd2 in
	    let p' = thinProp ctx2 p in
	      (lbl, bnd1', bnd2', p')
	  in
	       PCase (thinTerm' ctx e1, thinTerm' ctx e2, List.map doArm arms)

      | PLet(nm, trm1, prp2) ->
	  begin
	    let    (ty1, trm1', ty1') = thinTerm ctx trm1
	    in let (ctx,nm) = renameBoundTermVar ctx nm
	    in let ctx' = insertTermVariable ctx nm (ty1,ty1')
	    in let prp2' = thinProp ctx' prp2
	    in match ty1' with
		TopTy -> wrapObsProp trm1' prp2'
	      | _     -> PLet(nm, trm1', prp2')
	  end
  with e ->
    (print_endline ("\n\n...in (thin) " ^
		       string_of_proposition orig_prp);
     raise e)
      
and thinAssertion ctx (name, annots, prop) = (name, annots, thinProp ctx prop)

and thinModest ctx {ty=t; tot=p; per=q} =
  {ty  = thinTy ctx t;
   tot = thinProp ctx p;
   per = thinProp ctx q}

and thinElems (ctx : context) orig_elems = 
  try
    match orig_elems with
	[] -> ([], ctx)
      | Spec(name, ValSpec (tyvars,ty), assertions) :: rest ->
	   let ty'  = thinTy ctx ty in
	   let ctx' = insertTermVariable ctx name (ty,ty') in
	   let assertions' = List.map (thinAssertion ctx') assertions
	   in let (rest',ctx'') = 
	     thinElems (insertTermVariable ctx name (ty,ty')) rest
	   in
		((match ty' with
  		    TopTy -> 
		      (** Keep the (non-computational) assertions even if the 
			  computational part is elided for being trivial *)
		      List.map (fun a -> Assertion a) assertions' @ rest'
		  | ty' ->
		      Spec(name, ValSpec (tyvars,ty'), assertions') :: rest'),
		ctx'')
		  
      |  Assertion assertion  ::  rest ->
	   let assertion' = thinAssertion ctx assertion 
	   in let (rest',ctx'') = thinElems ctx rest 
	   in 
		(Assertion assertion' :: rest', ctx'')

      |  Spec(name, ModulSpec signat, assertions) :: rest -> 
	   let signat' = thinSignat ctx signat
	   in let ctx' = insertModulVariable ctx name (signat,signat')
	   in let assertions' = List.map (thinAssertion ctx') assertions
	   in let (rest', ctx'') = thinElems ctx' rest 
	   in 
		(Spec(name, ModulSpec signat', assertions') :: rest', ctx'')

      |  Spec(name, SignatSpec signat, assertions) :: rest -> 
	   let signat' = thinSignat ctx signat
	   in let ctx' = insertSignatVariable ctx name (signat, signat')
	   in let assertions' = List.map (thinAssertion ctx') assertions
	   in let (rest', ctx'') = thinElems ctx' rest 
	   in 
		(Spec(name, SignatSpec signat', assertions') :: rest', ctx'')

      |  Spec(nm, TySpec None, assertions) :: rest -> 
	   let ctx' = insertTypeVariable ctx nm (None,None)
	   in let assertions' = List.map (thinAssertion ctx') assertions 
	   in let (rest', ctx'') = thinElems ctx' rest in
		(Spec(nm, TySpec None, assertions') :: rest', ctx'')

      |  Spec(nm, TySpec (Some ty), assertions) :: rest ->
	   let ty' = thinTy ctx ty 
	   in let ctx' = insertTypeVariable ctx nm (Some ty, Some ty')  
	   in let assertions' = List.map (thinAssertion ctx') assertions 
	   in let (rest', ctx'') = thinElems ctx'  rest 
	   in
		(Spec(nm, TySpec(Some ty'), assertions') :: rest', ctx'')

      |  Comment cmmnt :: rest -> 
	   let (rest', ctx'') = thinElems ctx rest in
	     (Comment cmmnt :: rest', ctx'')
  with e ->
    (print_endline ("\n\n...in (thin) " ^
		       (String.concat "\n" (List.map string_of_spec orig_elems)));
     raise e)


and thinSignat ctx = function
    SignatName s ->
      SignatName s
  | Signat body -> 
      let (body',_) = thinElems ctx body in
	Signat body'
  | SignatFunctor(arg, body) ->
      let    ( (mdlnm, _) as arg', ctx'  ) = thinStructBinding ctx arg
      in let body' = thinSignat ctx' body
      in SignatFunctor ( arg', body' )
  | SignatApp(sgnt1,mdl) ->
	SignatApp(thinSignat ctx sgnt1, 
		  thinModul' ctx mdl)
  | SignatProj(mdl, nm) ->
      SignatProj(thinModul' ctx mdl, nm)

(* XXX There should be some renaming here, and probably insertion
   of bound variables in the opposite order in thinStructBindings! *)
	
and thinStructBinding ctx (m, signat) =
  let signat' = thinSignat ctx signat in
    ( (m, signat'),
    insertModulVariable ctx m (signat,signat') )

and thinStructBindings ctx = function
    [] -> [], ctx
  | (m, signat) :: bnd ->
      let signat' = thinSignat ctx signat in
      let bnd', ctx'' = thinStructBindings ctx bnd in
	( (m, signat') :: bnd',
	insertModulVariable ctx'' m (signat,signat') )

(* For now, at least, moduls never disappear completely, even if 
   their contents are entirely thinned away. *)
and thinModul ctx orig_modul = 
  try
  match orig_modul with
      ModulName nm -> 
	let nm = applyModulRenaming ctx nm
	in let (sg,sg') = lookupModulVariable ctx nm
	in (sg, orig_modul, sg')
    | ModulProj (mdl1, nm) -> 
	begin
	  let (sg1,mdl1',sg1') = thinModul ctx mdl1
	  in match (hnfSignat ctx sg1, hnfSignat ctx sg1') with
	      (Signat elems, Signat elems') ->
		(findModulvarInElems elems mdl1 nm,
		mdl1',
		findModulvarInElems elems' mdl1' nm)
	    | _ -> failwith "Thin.thinModul 1"
	end
    | ModulApp (mdl1, mdl2) ->
	begin
	  let (sg1, mdl1', sg1') = thinModul ctx mdl1
	  in let (sg2, mdl2', sg2') = thinModul ctx mdl2
          in match (hnfSignat ctx sg1, hnfSignat ctx sg1') with
	      (SignatFunctor((nm,_),sg3), SignatFunctor((nm',_),sg3')) ->
		(substSignat (insertModulvar emptysubst nm mdl2) sg3,
		ModulApp(mdl1', mdl2'),
		substSignat (insertModulvar emptysubst nm' mdl2') sg3')
	    | _ -> failwith "Thin.thinModul 2"
	end
    | ModulStruct defs ->
	let (elems, defs', elems') = thinDefs ctx defs
	in (Signat elems, ModulStruct defs, Signat elems')
  with e ->
    (print_endline ("\n\n...in (thinModul) " ^
		       (string_of_modul orig_modul));
     raise e)
	  
and thinModul' ctx orig_modul =
  let (_, mdl, _) = thinModul ctx orig_modul
  in mdl

and thinDefs ctx = function
    [] -> ([], [], [])
  | DefType(nm,ty)::defs ->
      begin
	let spec = Spec(nm, TySpec (Some ty), [])
	in let ty' = thinTy ctx ty
	in let ctx' = insertTypeVariable ctx nm (Some ty, Some ty')
	in let (elems, defs', elems') = thinDefs ctx' defs
	in match ty' with
	    TopTy -> (spec::elems, defs', elems')
	  | _     -> (spec::elems, DefType(nm,ty')::defs',
		      Spec(nm, TySpec (Some ty'), [])::elems')
      end
  | DefTerm(nm,ty,trm)::defs ->
      begin
	let spec = Spec(nm, ValSpec ([],ty), [])
	in let ty' = thinTy ctx ty
	in let ctx' = insertTermVariable ctx nm (ty,ty')
	in let (elems, defs', elems') = thinDefs ctx' defs
	in let trm' = thinTerm' ctx trm
	in match ty' with
	    (* XXX: Possibility of losing assertions in trm' ! *)
	    TopTy -> (spec::elems, defs', elems')
	  | _     -> (spec::elems, DefTerm(nm,ty',trm')::defs',
		     Spec(nm, ValSpec ([],ty'), [])::elems')
      end
  | DefModul(nm,sg,mdl)::defs ->
      begin
	let spec = Spec(nm, ModulSpec sg, [])
	in let sg' = thinSignat ctx sg
	in let mdl' = thinModul' ctx mdl
	in let ctx' = insertModulVariable ctx nm (sg,sg')
	in let (elems, defs', elems') = thinDefs ctx' defs
	in 
	     (spec::elems, DefModul(nm,sg',mdl')::defs',
	     Spec(nm, ModulSpec sg', [])::elems')
      end
  | DefSignat(nm,sg)::defs ->
      begin
	let spec = Spec(nm, SignatSpec sg, [])
	in let sg' = thinSignat ctx sg
	in let ctx' = insertSignatVariable ctx nm (sg,sg')
	in let (elems, defs', elems') = thinDefs ctx' defs
	in 
	     (spec::elems, DefSignat(nm,sg')::defs',
		   Spec(nm, SignatSpec sg', [])::elems')
      end
	    


let rec thinToplevels' ctx elems = 
  thinElems ctx elems

let thinToplevels ctx elems =
  if !Flags.do_thin then 
    thinToplevels' ctx elems
  else 
    (elems,ctx)
