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
		   Records the UNthinimized type. *)
            tydefs     : ty NameMap.t;
               (** Definitions of type variables in scope.
                   Records the UNthinimized type definition *)
            moduli     : sig_summary NameMap.t;
           }

and sig_summary = 
    Summary_Struct  of ctx
  | Summary_Functor of modul_name * sig_summary

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
      Not_found -> ( print_string ( "Thin: Unbound name: " ^ Name.string_of_name nm ^ "\n");
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
		moduli = NameMap.empty}


(*******************)
(** Set operations *)
(*******************)


let nonTopTy = function
      TopTy -> false
    | _ -> true

let tthinyize = function
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
        | _ -> s1' (** We're assuming the input to the thinimizer
                       typechecks! *)


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
	in tthinyize (TupleTy tys')
	  
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
   Id n -> (let oldty = lookupTypeLong ctx n
            in  match (thinTy ctx oldty) with
                   TopTy -> (oldty, Dagger, TopTy)
                 | nonunit_ty -> (oldty, Id n, nonunit_ty))
 | EmptyTuple -> (UnitTy, EmptyTuple, UnitTy)
 | Dagger -> ((* print_string "Is this a Dagger which I see before me?\n"; *)
	      (TopTy, Dagger, TopTy))
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
     in let ctx' = insertType ctx name1 ty1
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
     in (TupleTy ts, e', tthinyize (TupleTy ts'))
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
	   in let ctx' = insertType ctx name2 ty
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
			  joinTy emptyCtx tyarm' tyarms')
     in let (tyarms, arms', tyarms') = doArms arms
     in (tyarms, Case(e',arms'), tyarms')

 | Let(name1, term1, term2) ->
     begin
       let    (ty1, term1', ty1') = thinTerm ctx term1
       in let ctx' = insertType ctx name1 ty1
       in let (ty2, term2', ty2') = thinTerm ctx' term2
       in match ty1' with
	   TopTy -> (ty2, term2', ty2')
	 | _ -> (ty2, Let(name1, term1', term2'), ty2')
     end

 | Obligation(bnds, prop, trm) ->
     let (names,tys) = List.split bnds
     in let tys'  = List.map (thinTy ctx) tys
     in let bnds' = List.combine names tys'
     in let bnds'' = List.filter (fun (n,t) -> t <> TopTy) bnds'
     in let ctx' = List.fold_left2 insertType ctx names tys
     in let prop' = thinProp ctx' prop
     in let ty2, trm', ty2' = thinTerm ctx' trm
     in (ty2, Obligation(bnds'', prop', trm'), ty2')

with e ->
  (print_endline ("\n\n...in " ^
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
      let p' = thinProp (insertType ctx n ty) p
      in (match (thinTy ctx ty) with
      | TopTy -> p'
      | ty' -> Forall((n,ty'), p'))
 
  | ForallTotal((n,ty),p) ->
      let p' = thinProp (insertType ctx n ty) p
      in ForallTotal((n,thinTy ctx ty), p')
 
  | Cexists ((n, ty), p) ->
      let p' = thinProp (insertType ctx n ty) p in
	(match thinTy ctx ty with
	   | TopTy -> p'
	   | ty' -> Cexists((n, ty'), p'))

  | PObligation (bnds, p, q) ->
     let (names,tys) = List.split bnds
     in let tys'  = List.map (thinTy ctx) tys
     in let bnds' = List.combine names tys'
     in let bnds'' = List.filter (fun (n,t) -> t <> TopTy) bnds'
     in let ctx' = List.fold_left2 insertType ctx names tys
     in let p' = thinProp ctx' p
     in let q' = thinProp ctx' q
     in 
	  PObligation(bnds'', p', q')


  | PMLambda ((n, ms), p) ->
      let ms' = thinModest ctx ms in
      let p' = thinProp (insertType ctx n ms.ty) p
      in 
	PMLambda ((n,ms'), p')

  | PMApp (p, t) -> 
      PMApp (thinProp ctx p, thinTerm' ctx t)

  | PLambda ((n,ty), p) ->
      begin
	let p' = thinProp (insertType ctx n ty) p
	in let ty' = thinTy ctx ty
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
	    (match thinTy ctx ty with
		TopTy -> None, ctx0
	      | ty' -> Some (nm, ty'), insertType ctx0 nm ty)
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
	in let ctx' = insertType ctx nm ty1
	in let prp2' = thinProp ctx' prp2
	in match ty1' with
	    TopTy -> prp2'
	  | _ -> PLet(nm, trm1', prp2')
      end
with e ->
  (print_endline ("\n\n...in " ^
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
    [] -> [], emptyCtx
  |  ValSpec(name, ty, assertions) :: rest ->
      let ty'  = thinTy ctx ty in
      let ctx' = insertType ctx name ty in
      let assertions' = List.map (thinAssertion ctx') assertions
      in let (rest', ctx'') = thinElems (insertType ctx name ty) rest in
	(match ty' with
  	     TopTy -> 
	       (** Keep the (non-computational) assertions even if the 
		 computational part is elided for being trivial *)
	       (List.map (fun a -> AssertionSpec a) assertions' @ rest', ctx'')
	   | ty' ->
	       (ValSpec (name, ty', assertions') :: rest', 
		insertType ctx'' name ty'))
	
  |  AssertionSpec assertion  ::  rest ->
       let assertion' = thinAssertion ctx assertion in
       let (rest', ctx') = thinElems ctx rest in
	 (AssertionSpec assertion' :: rest'), ctx'

  |  ModulSpec (name,signat) :: rest -> 
      let (signat',summary) = thinSignat ctx signat
      in let ctx'' = insertModul ctx name summary
      in let (rest', ctx''') = thinElems ctx'' rest 
      in (ModulSpec (name, signat') :: rest',
	  ctx''')

  |  TySpec(nm, None, assertions) :: rest -> 
       (** We don't add nm to the input context of thinAssertion
       because we never need to know whether something is a type or
       not; we're assuming that the input was well-formed *)
       let assertions' = List.map (thinAssertion ctx) assertions in
       let rest', ctx'' = thinElems ctx rest in
	 (TySpec (nm, None, assertions') :: rest'), ctx''

  |  TySpec(nm, Some ty, assertions) :: rest ->
       let ty' = thinTy ctx ty in
	 (** We might care about expanding a definition for nm, though *)
       let ctx' = insertTydef ctx nm ty  in
       let assertions' = List.map (thinAssertion ctx') assertions in
       let rest', ctx'' = thinElems ctx'  rest in
	 TySpec(nm, Some ty',assertions') :: rest', (insertTydef ctx'' nm ty')

  |  Comment cmmnt :: rest -> 
       let rest', ctx' = thinElems ctx rest in
	 (Comment cmmnt :: rest', ctx')
with e ->
  (print_endline ("\n\n...in " ^
      (String.concat "\n" (List.map string_of_spec orig_elems)));
   raise e)


and thinSignat ctx = function
    SignatName s ->
      ( SignatName s, lookupModul ctx s )
  | Signat body -> 
      let body', ctx' = thinElems ctx body in
      ( Signat body', Summary_Struct ctx' )
  | SignatFunctor(arg, body) ->
      let    ( (mdlnm, _) as arg', ctx'  ) = thinStructBinding ctx arg
      in let ( body', summary ) = thinSignat ctx' body
      in ( SignatFunctor ( arg', body' ), 
	   Summary_Functor (mdlnm, summary) )
  | SignatApp(sgnt1,mdl,sgnt2) ->
      let sgnt2', smmry = thinSignat ctx sgnt2 in
	SignatApp(fst (thinSignat ctx sgnt1), mdl, sgnt2'),
	smmry
      
and thinStructBinding ctx (m, signat) =
  let signat', summary = thinSignat ctx signat in
    ( (m, signat'),
      insertModul ctx m summary )

and thinStructBindings ctx = function
    [] -> [], ctx
  | (m, signat) :: bnd ->
      let signat', summary = thinSignat ctx signat in
      let bnd', ctx'' = thinStructBindings ctx bnd in
	( (m, signat') :: bnd',
	  insertModul ctx'' m summary )

let thinToplevel ctx = function
    (Signatdef (s, signat)) ->
      let signat', summary' = thinSignat ctx signat in
	( Signatdef (s, signat'), 
          insertModul ctx s summary' )

  | TopComment cmmnt -> (TopComment cmmnt, ctx)

  | TopModul (mdlnm, signat) ->
      let (signat', summary') = thinSignat ctx signat in
	( TopModul(mdlnm, signat'), 
	  insertModul ctx mdlnm summary' )

let rec thinToplevels' ctx = function
    [] -> ([], ctx)
  | sg :: lst ->
      let sg', ctx' = thinToplevel ctx sg in
      let lst', ctx'' = thinToplevels' ctx' lst in
	(sg'::lst', ctx'')

let thinToplevels ctx sigs =
  if !Flags.do_thin || !Flags.do_opt then thinToplevels' ctx sigs else (sigs,ctx)
