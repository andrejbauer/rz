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
      (y,[]) -> (print_string ("Unbound name: " ^ (fst y) ^ "\n");
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
           }

(** Determines whether a variable has an implicitly declared type.
     @param ctx  The type reconstruction context
     @param str  The (string) name of the variable.
  *)
let lookupType     ctx   n = lookupName (n, ctx.types)
let lookupTydef    ctx str = lookup (str, ctx.tydefs)
let peekTydef ctx s = peek(s, ctx.tydefs)

let insertType ({types=types} as ctx) n ty = 
       {ctx with types = insert(n,ty,types)}
let insertTypeBnds ({types=types} as ctx) bnds = 
       {ctx with types = insertbnds(bnds,types)}
let insertTydef ({tydefs=tydefs} as ctx) str ty = 
       {ctx with tydefs = insert(str,ty,tydefs)}

let emptyCtx = {types = []; tydefs = []}


(** Expand out any top-level definitions for a set *)
let rec hnfTy ctx = function
    NamedTy n ->
      (match (peekTydef ctx n) with
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
  | nonunit_ty -> nonunit_ty
  in
    hnfTy ctx ans

(* optTerm ctx e = (t, e', t')
      where e' is the optimized version of e
            t  is the original type of e under ctx
            t' is the optimized type (i.e., the type of e')

      Never returns Tuple []
*)       
let rec optTerm ctx = function
   Id n -> (let oldty = lookupType ctx n
            in  match (optTy ctx oldty) with
                   TopTy -> (oldty, Star, TopTy)
                 | nonunit_ty -> (oldty, Id n, nonunit_ty))
 | Star -> (UnitTy, Star, UnitTy)
 | App(e1,e2) -> 
     let    (ArrowTy(ty2, oldty), e1', ty1') = optTerm ctx e1
     in let (_, e2', ty2') = optTerm ctx e2
     in (match (optTy ctx oldty, hnfTy ctx ty2') with
           (TopTy, _) -> (* Application can be eliminated entirely *)
                            (oldty, Star, TopTy)
         | (_, TopTy) -> (* Argument is unit and can be eliminated *)
                            (oldty, e1', ty1')
         | (ty', _)    -> (* Both parts matter *)
                            (oldty, App(e1', e2'), ty'))
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
           (* Projection is unit-like and can be eliminated entirely *)
           (ty, Star, TopTy)
	 else
	   loop(tys, tys', nonunits, index+1)
       | (ty::tys, ty'::tys', nonunits, index) ->
	 if index = n then
           (* Projection returns some interesting value.
              Check if it's the only interesting value in the tuple. *)
           if (nonunits = 0 && List.length(List.filter notTopTy tys')=0) then
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
        loop (tys, List.map (optTy ctx) tys, 0, 0) 
 | e -> (** XXX: Way wrong! *)
        (NamedTy "unknown", e, NamedTy "unknown")


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
    NamedTotal(str, e) -> NamedTotal(str, optTerm' ctx e)
  | NamedPer(str, e1, e2) -> NamedPer(str, optTerm' ctx e1, optTerm' ctx e2)
  | NamedProp(str, e1, e2) -> NamedProp(str, optTerm' ctx e1, optTerm' ctx e2)
  | Equal(e1, e2) -> 
      let (_,e1',ty1') = optTerm ctx e1
      in let e2' = optTerm' ctx e2
      in (match (hnfTy ctx ty1') with
            TopTy -> True
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
      let p' = optProp (insertType ctx n ty) p
      in (match optTy ctx ty with
        TopTy -> p'
      | ty' -> Forall((n,ty'), p'))

      
and optElems ctx = function
    [] -> []
  |  ValSpec(name, ty) :: rest ->
      let    ty'   = optTy ctx ty
      in let rest' = optElems (insertType ctx name ty) rest
      in (match ty' with
  	TopTy -> rest'
      |	ty' ->   ValSpec(name, ty') :: rest')

  |  AssertionSpec(bnds, prop) :: rest ->
      (** XXX Eliminate unit bindings? *)
      let ctx' = insertTypeBnds ctx bnds
      in AssertionSpec(bnds, optProp ctx' prop) :: optElems ctx rest
  |  TySpec(n, None) :: rest -> 
      TySpec(n, None) :: optElems ctx rest
  |  TySpec((str,_) as n, Some ty) :: rest ->
      (** XXX Need to add the definition into the context *)
      TySpec(n, Some (optTy ctx ty)) :: 
      optElems (insertTydef ctx str ty) rest

 
(** XXX needs a context; body needs context from args *)
let optSignat {s_name = n; s_arg = a; s_body = b} = 
   {s_name = n;
    s_arg = (match a with
              None -> None
            | Some elts -> Some (optElems emptyCtx elts));
    s_body = optElems emptyCtx b}
