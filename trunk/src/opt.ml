(*******************************************************************)
(** {1 Type Reconstruction}                                        *)
(**                                                                *)
(** For now we assume that                                         *)
(** all bound variables are annotated, either when declared        *)
(** or through a prior "implicit" statement.                       *)
(*******************************************************************)

open Outsyn

exception Unimplemented
exception Impossible

(*************************************)
(** {2 Lookup Tables (Environments)} *)
(*************************************)

let emptyenv = []
let insert (x,s,env) = (x,s)::env
let insertbnds (bnds, env) = bnds @ env
exception NotFound
let rec lookup = function
      (y,[]) -> (print_string ("Unbound name: " ^ y ^ "\n");
                 raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookup(y,rest)

let rec lookupName = function
      (y,[]) -> (print_string ("Unbound name: " ^ (fst y) ^ "\n");
                 raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookupName(y,rest)

(*******************)

let notUnitTy = function
      UnitTy -> false
    | _ -> true

let unitTyize = function
      TupleTy [] -> UnitTy
    | ty -> ty

(* optTy : ty -> ty

     Never returns TupleTy []
 *)
let rec optTy = function
   ArrowTy (ty1, ty2) -> 
     (match (optTy ty1, optTy ty2) with
        (UnitTy, ty2') -> ty2'
      | (_, UnitTy)    -> UnitTy
      | (ty1', ty2')   -> ArrowTy(ty1', ty2'))
 | TupleTy tys -> unitTyize
                    (TupleTy (List.filter notUnitTy
                              (List.map optTy tys)))
 | nonunit_ty -> nonunit_ty


(* optTerm ctx e = (t, e', t')
      where e' is the optimized version of e
            t  is the original type of e under ctx
            t' is the optimized type (i.e., the type of e')

      Never returns Tuple []
*)       
let rec optTerm ctx = function
   Id n -> (let oldty = lookupName (n, ctx)
            in  match (optTy oldty) with
                   UnitTy -> (oldty, Star, UnitTy)
                 | nonunit_ty -> (oldty, Id n, nonunit_ty))
 | Star -> (UnitTy, Star, UnitTy)
 | App(e1,e2) -> 
     let    (ArrowTy(ty2, oldty), e1', ty1') = optTerm ctx e1
     in let (_, e2', ty2') = optTerm ctx e2
     in (match (optTy oldty, ty2') with
           (UnitTy, _) -> (* Application can be eliminated entirely *)
                            (oldty, Star, UnitTy)
         | (_, UnitTy) -> (* Argument is unit and can be eliminated *)
                            (oldty, e1', ty1')
         | (ty', _)    -> (* Both parts matter *)
                            (oldty, App(e1', e2'), ty'))
 | Tuple es -> 
     let (ts, es', ts') = optTerms ctx es
     in (unitTyize (TupleTy ts), Tuple es', unitTyize (TupleTy ts'))
 | Proj (n,e) ->
     let (TupleTy tys, e', _) = optTerm ctx e
     in let rec loop = function
         (ty::tys, UnitTy::tys', nonunits, index) ->
         if index == n then
           (* Projection is unit-like and can be eliminated entirely *)
           (ty, Star, UnitTy)
	 else
	   loop(tys, tys', nonunits, index+1)
       | (ty::tys, ty'::tys', nonunits, index) ->
	 if index = n then
           (* Projection returns some interesting value.
              Check if it's the only interesting value in the tuple. *)
           if (nonunits = 0 && List.length(List.filter notUnitTy tys')=0) then
              (* Yes; there were no non-unit types before or after. *)
	     (ty, e, ty')
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
        loop (tys, List.map optTy tys, 0, 0) 
 | e -> (** XXX: Way wrong! *)
        (NamedTy "unknown", e, NamedTy "unknown")


and optTerms ctx = function 
    [] -> ([], [], [])   
  | e::es -> let (ty, e', ty') = optTerm ctx e
	     in let (tys, es', tys') = optTerms ctx es
             in (match ty' with
               UnitTy -> (ty :: tys, es', tys')
             | _ -> (ty :: tys, e'::es', ty'::tys'))
           

and optTerm' ctx e =
   let (_,e',_) = optTerm ctx e 
   in e'      

and optProp ctx = function
    NamedTotal(str, e) -> NamedTotal(str, optTerm' ctx e)
  | NamedPer(str, e1, e2) -> NamedPer(str, optTerm' ctx e1, optTerm' ctx e2)
  | NamedProp(str, e1, e2) -> NamedProp(str, optTerm' ctx e1, optTerm' ctx e2)
  | Equal(e1, e2) -> 
      let (_,e1',ty1') = optTerm ctx e1
      in let e2' = optTerm' ctx e2
      in (match ty1' with
            UnitTy -> True
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

    (** XXX: Further simplifications possible *)
  | Imply (p1, p2) -> Imply(optProp ctx p1, optProp ctx p2)
  | Iff (p1, p2) -> Iff(optProp ctx p1, optProp ctx p2)

  | Not p -> (match optProp ctx p with
      True -> False
    | False -> True
    | p' -> Not p')

  | Forall((n,ty), p) ->
      let p' = optProp (insert(n,ty,ctx)) p
      in (match optTy ty with
        UnitTy -> p'
      | ty' -> Forall((n,ty'), p'))

      
and optElems ctx = function
    [] -> []
  |  ValSpec(name, ty) :: rest ->
      ValSpec(name, optTy ty) ::
      optElems (insert(name, ty, ctx)) rest
  |  AssertionSpec(bnds, prop) :: rest ->
      (** XXX Eliminate unit bindings? *)
      let ctx' = insertbnds(bnds,ctx)
      in AssertionSpec(bnds, optProp ctx' prop) :: optElems ctx rest
  |  TySpec(str, None) :: rest -> 
      TySpec(str, None) :: optElems ctx rest
  |  TySpec(str, Some ty) :: rest ->
      (** XXX Need to add the definition into the context *)
      TySpec(str, Some (optTy ty)) :: optElems ctx rest

 
(** XXX needs a context; body needs context from args *)
let optSignat {s_name = n; s_arg = a; s_body = b} = 
   {s_name = n;
    s_arg = (match a with
              None -> None
            | Some elts -> Some (optElems [] elts));
    s_body = optElems [] b}
