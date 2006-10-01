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

(*******************)
(** Set operations *)
(*******************)


let nonTopTy = function
      TopTy -> false
    | _ -> true

let toptyize = function
      TupleTy [] -> TopTy
    | TupleTy [ty] -> ty
    | ty -> ty

 


(***************************)
(** Thinimization functions *)
(***************************)



(* thinTy : ty -> ty

     Never returns TupleTy [] or TupleTy[_]
 *)
let rec thinTy ctx ty = 
  let ans = match (hnfTy ctx ty) with
    ArrowTy (ty1, ty2) -> 
      (match (thinTy ctx ty1, thinTy ctx ty2) with
        (TopTy, ty2')  -> ty2'
      | (_,     TopTy) -> TopTy
      | (ty1',  ty2')  -> ArrowTy(ty1', ty2'))

    | TupleTy tys -> 
	let tys' = List.filter nonTopTy (List.map (thinTy ctx) tys)
	in toptyize (TupleTy tys')
	  
    | SumTy lst ->
	SumTy (List.map (function
	 		 (lbl, None) ->    (lbl, None)
		       | (lbl, Some ty) -> (lbl, match thinTy ctx ty with
			                           TopTy -> None
 			                         | ty' -> Some ty')) 
                      lst)

    | nonunit_ty -> nonunit_ty
  in
    hnfTy ctx ans

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
      (match thinTy ctx ty with
	   TopTy -> thinBinds ctx bnds
	 | ty' -> (n,ty')::(thinBinds ctx bnds))

(* thinTerm ctx e = (t, e', t')
      where t  is the original type of e under ctx
            e' is the thinimized version of e
            t' is the thinimized type (i.e., the type of e')

      Never returns Tuple [] or Tuple [x]
*)       
let rec thinTerm ctx orig_term = 
  try
    match orig_term with
	Id (LN(None,nm)) ->
	  begin
	    let nm = applyTermRenaming ctx nm
	    in let oldty = lookupTermVariable ctx nm
            in  match (thinTy ctx oldty) with
		TopTy -> (oldty, Dagger, TopTy)
              | nonunit_ty -> (oldty, Id(LN(None,nm)), nonunit_ty)
	  end
      | Id (LN(Some mdl, nm)) ->
	  begin
	    let (sg, mdl', _) = thinModul ctx mdl
	    in let oldty = 
	      match hnfSignat ctx sg with
		  Signat elems -> findTermvarInElems elems mdl nm
		| _ -> failwith "Thin.thinTerm: invalid path"
	    in match (thinTy ctx oldty) with
		TopTy -> (oldty, Dagger, TopTy)
	      | newty -> (oldty, Id(LN(Some mdl',nm)), newty)
	  end

      | EmptyTuple -> (UnitTy, EmptyTuple, UnitTy)

      | Dagger -> (TopTy, Dagger, TopTy)

      | App(e1,e2) -> 
	  begin
	    match thinTerm ctx e1 with
		(ArrowTy(ty2, oldty), e1', ty1') ->
		  let (_, e2', ty2') = thinTerm ctx e2
		  in let ty' = thinTy ctx oldty
		  in (match (ty', hnfTy ctx ty2') with
		      (TopTy, _) -> (* Application can be eliminated entirely *)
			((oldty, Dagger, TopTy))
		    | (_, TopTy) -> (* Argument is dagger and can be eliminated *)
                        ((oldty, e1', ty1'))
		    | (ty', _)    -> (* Both parts matter.
					Eliminate trivial beta-redices, though. *)
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
	    in let ctx' = insertTermVariable ctx name1 ty1
	    in let (ty2, term2', ty2') = thinTerm ctx' term2
	    in let oldty = ArrowTy(ty1,ty2)
	    in match (hnfTy ctx ty1', hnfTy ctx ty2') with
		(_,TopTy) -> (oldty, Dagger, TopTy)
	      | (TopTy,_) -> (oldty, term2', ty2')
	      | (_,_)     -> (oldty, Lambda((name1,ty1'),term2'), ArrowTy(ty1',ty2')))
      | Tuple es -> 
	  let (ts, es', ts') = thinTerms ctx es
	  in let e' = 
	    (match es' with
		[] -> Dagger
	      | [e] -> e
	      | _ -> Tuple es')
	  in (TupleTy ts, e', toptyize (TupleTy ts'))
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
      | Inj (lbl, None) -> (SumTy [(lbl,None)], Inj(lbl, None), SumTy [(lbl,None)])
      | Inj (lbl, Some e) ->
	  let (ty, e', ty') = thinTerm ctx e in
	    if ty' = TopTy then
	      (SumTy [(lbl,Some ty)], Inj (lbl, None), SumTy[(lbl, None)])
	    else
	      (SumTy [(lbl,Some ty)], Inj(lbl, Some e'), SumTy[(lbl, Some ty')])
      | Case (e, arms) ->
	  let (ty, e', ty') = thinTerm ctx e
	  in let doArm = function
	      (lbl, Some (name2,ty2),  e3) -> 
		let ty2' = thinTy ctx ty2 
		in let (ctx,name2) = renameBoundTermVar ctx name2
		in let ctx' = insertTermVariable ctx name2 ty
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
		 (* XXX: doublecheck invariant that the 
		    thinned type never has a toplevel defn. *)
		 joinTy emptyContext tyarm' tyarms')
	  in let (tyarms, arms', tyarms') = doArms arms
	  in (tyarms, Case(e',arms'), tyarms')

      | Let(name1, term1, term2) ->
	  begin
	    let    (ty1, term1', ty1') = thinTerm ctx term1
	    in let (ctx,name1) = renameBoundTermVar ctx name1
	    in let ctx' = insertTermVariable ctx name1 ty1
	    in let (ty2, term2', ty2') = thinTerm ctx' term2
	    in match ty1' with
		TopTy -> (ty2, term2', ty2')
	      | _ -> (ty2, Let(name1, term1', term2'), ty2')
	  end

      | Obligation(bnds, prop, trm) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (thinTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = renameTermBindings ctx bnds'
	  in let bnds''' = List.filter (fun (n,t) -> t <> TopTy) bnds''
	  in let prop' = thinProp ctx' prop
	  in let ty2, trm', ty2' = thinTerm ctx' trm
	  in (ty2, Obligation(bnds''', prop', trm'), ty2')

  with e ->
    (print_endline ("\n\n...in (thin term) " ^
		       string_of_term orig_term);
     raise e)

and thinTerms ctx = function 
    [] -> ([], [], [])   
  | e::es -> let (ty, e', ty') = thinTerm ctx e
    in let (tys, es', tys') = thinTerms ctx es
    in (match (hnfTy ctx ty') with
        TopTy -> (ty :: tys, es', tys')
      | _ -> (ty :: tys, e'::es', ty'::tys'))
      

and thinTerm' ctx e =
  let (_,e',_) = thinTerm ctx e 
  in e'      

and thinTerms' ctx lst =
  let (_, es, _) = thinTerms ctx lst in es

and thinProp ctx orig_prp = 
  try
    match orig_prp with
	True                    -> True
      | False                   -> False
      | IsPer (nm, lst)         -> IsPer (nm, thinTerms' ctx lst)
      | IsPredicate (nm, ty, lst) ->
	  IsPredicate (nm, thinTyOption ctx ty, 
		      List.map (fun (nm, ms) -> (nm, thinModest ctx ms)) lst)
      | IsEquiv (p, ms)         -> IsEquiv (thinProp ctx p, thinModest ctx ms)
      | NamedTotal (n, lst)     -> NamedTotal (n, thinTerms' ctx lst)
      | NamedPer (n, lst)       -> NamedPer (n, thinTerms' ctx lst)
      | NamedProp (n, t, lst)   -> NamedProp (n, thinTerm' ctx t, thinTerms' ctx lst)
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
	  in let p' = thinProp (insertTermVariable ctx n ty) p
	  in (match ty' with
	    | TopTy -> p'
	    | _ -> Forall((n,ty'), p'))
	    
      | ForallTotal((n,ty),p) ->
	  let ty' = thinTy ctx ty
	  in let (ctx,n) = renameBoundTermVar ctx n
	  in let p' = thinProp (insertTermVariable ctx n ty) p
	  in ForallTotal((n,ty'), p')
	    
      | Cexists ((n, ty), p) ->
	  let ty' = thinTy ctx ty
	  in let (ctx,n) = renameBoundTermVar ctx n
	  in let p' = thinProp (insertTermVariable ctx n ty) p in
	    (match ty' with
	      | TopTy -> p'
	      | _ -> Cexists((n, ty'), p'))

      | PObligation (bnds, p, q) ->
	  let (names,tys) = List.split bnds
	  in let tys'  = List.map (thinTy ctx) tys
	  in let bnds' = List.combine names tys'
	  in let (ctx', bnds'') = renameTermBindings ctx bnds'
	  in let bnds''' = List.filter (fun (n,t) -> t <> TopTy) bnds''
	  in let p' = thinProp ctx' p
	  in let q' = thinProp ctx' q
	  in 
	       PObligation(bnds''', p', q')


      | PMLambda ((n, ms), p) ->
	  let ms' = thinModest ctx ms
	  in let (ctx,n) = renameBoundTermVar ctx n
	  in let p' = thinProp (insertTermVariable ctx n ms.ty) p
	  in 
	    PMLambda ((n,ms'), p')

      | PMApp (p, t) -> 
	  PMApp (thinProp ctx p, thinTerm' ctx t)

      | PLambda ((n,ty), p) ->
	  begin
	    let ty' = thinTy ctx ty
	    in let (ctx,n) = renameBoundTermVar ctx n
	    in let p' = thinProp (insertTermVariable ctx n ty) p
	    in 
		 match ty' with
		     TopTy -> p'
		   | _ -> PLambda((n,ty'), p')
	  end
	    
      | PApp (p, t) -> 
	  begin
	    let p' = thinProp ctx p
	    in let (_,t',ty') = thinTerm ctx t
	    in 
		 match ty' with
		     TopTy -> p'
		   | _ -> PApp(p', t')
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
		       | _ -> Some (nm, ty'), insertTermVariable ctx0 nm ty)
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
	    in let ctx' = insertTermVariable ctx nm ty1
	    in let prp2' = thinProp ctx' prp2
	    in match ty1' with
		TopTy -> prp2'
	      | _ -> PLet(nm, trm1', prp2')
	  end
  with e ->
    (print_endline ("\n\n...in (thin) " ^
		       string_of_proposition orig_prp);
     raise e)
      
and thinAssertion ctx (name, prop) = (name, thinProp ctx prop)

and thinModest ctx {ty=t; tot=p; per=q} =
  {ty = thinTy ctx t;
   tot = thinProp ctx p;
   per = thinProp ctx q}

and thinElems ctx orig_elems = 
  try
    match orig_elems with
	[] -> ([], ctx)
      | Spec(name, ValSpec (tyvars,ty), assertions) :: rest ->
	   let ty'  = thinTy ctx ty in
	   let ctx' = insertTermVariable ctx name ty in
	   let assertions' = List.map (thinAssertion ctx') assertions
	   in let (rest',ctx'') = thinElems (insertTermVariable ctx name ty) rest in
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
	   in let ctx' = insertModulVariable ctx name signat
	   in let assertions' = List.map (thinAssertion ctx') assertions
	   in let (rest', ctx'') = thinElems ctx' rest 
	   in 
		(Spec(name, ModulSpec signat', assertions') :: rest', ctx'')

      |  Spec(name, SignatSpec signat, assertions) :: rest -> 
	   let signat' = thinSignat ctx signat
	   in let ctx' = insertSignatVariable ctx name signat
	   in let assertions' = List.map (thinAssertion ctx') assertions
	   in let (rest', ctx'') = thinElems ctx' rest 
	   in 
		(Spec(name, SignatSpec signat', assertions') :: rest', ctx'')

      |  Spec(nm, TySpec None, assertions) :: rest -> 
	   let ctx' = insertTypeVariable ctx nm None
	   in let assertions' = List.map (thinAssertion ctx') assertions 
	   in let (rest', ctx'') = thinElems ctx' rest in
		(Spec(nm, TySpec None, assertions') :: rest', ctx'')

      |  Spec(nm, TySpec (Some ty), assertions) :: rest ->
	   let ty' = thinTy ctx ty 
	   in let ctx' = insertTypeVariable ctx nm (Some ty)  
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
    insertModulVariable ctx m signat )

and thinStructBindings ctx = function
    [] -> [], ctx
  | (m, signat) :: bnd ->
      let signat' = thinSignat ctx signat in
      let bnd', ctx'' = thinStructBindings ctx bnd in
	( (m, signat') :: bnd',
	insertModulVariable ctx'' m signat )

(* For now, at least, moduls never disappear completely, even if 
   their contents are entirely thinned away. *)
and thinModul ctx orig_modul = 
  match orig_modul with
      ModulName nm -> 
	let nm = applyModulRenaming ctx nm
	in let sg = lookupModulVariable ctx nm
	in let sg' = thinSignat ctx sg
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
	  
and thinModul' ctx orig_modul =
  let (_, mdl, _) = thinModul ctx orig_modul
  in mdl

and thinDefs ctx = function
    [] -> ([], [], [])
  | DefType(nm,ty)::defs ->
      begin
	let spec = Spec(nm, TySpec (Some ty), [])
	in let ctx' = insertTypeVariable ctx nm (Some ty)
	in let (elems, defs', elems') = thinDefs ctx' defs
	in match hnfTy ctx (thinTy ctx ty) with
	    TopTy -> (spec::elems, defs', elems')
	  | ty' -> (spec::elems, DefType(nm,ty')::defs',
		   Spec(nm, TySpec (Some ty'), [])::elems')
      end
  | DefTerm(nm,ty,trm)::defs ->
      begin
	let spec = Spec(nm, ValSpec ([],ty), [])
	in let ctx' = insertTermVariable ctx nm ty
	in let (elems, defs', elems') = thinDefs ctx' defs
	in let trm' = thinTerm' ctx trm
	in match hnfTy ctx (thinTy ctx ty) with
	    TopTy -> (spec::elems, defs', elems')
	  | ty' -> (spec::elems, DefTerm(nm,ty',trm')::defs',
		   Spec(nm, ValSpec ([],ty'), [])::elems')
      end
  | DefModul(nm,sg,mdl)::defs ->
      begin
	let spec = Spec(nm, ModulSpec sg, [])
	in let sg' = thinSignat ctx sg
	in let mdl' = thinModul' ctx mdl
	in let ctx' = insertModulVariable ctx nm sg
	in let (elems, defs', elems') = thinDefs ctx' defs
	in 
	     (spec::elems, DefModul(nm,sg',mdl')::defs',
		   Spec(nm, ModulSpec sg', [])::elems')
      end
  | DefSignat(nm,sg)::defs ->
      begin
	let spec = Spec(nm, SignatSpec sg, [])
	in let sg' = thinSignat ctx sg
	in let ctx' = insertSignatVariable ctx nm sg
	in let (elems, defs', elems') = thinDefs ctx' defs
	in 
	     (spec::elems, DefSignat(nm,sg')::defs',
		   Spec(nm, SignatSpec sg', [])::elems')
      end
	    


let rec thinToplevels' ctx elems = 
  thinElems ctx elems

let thinToplevels ctx elems =
  if !Flags.do_thin || !Flags.do_opt then 
    thinToplevels' ctx elems
  else 
    (elems,ctx)
