(*******************************************************************)
(** {1 Type Reconstruction}                                        *)
(**                                                                *)
(** For now we assume that                                         *)
(** all bound variables are annotated, either when declared        *)
(** or through a prior "implicit" statement.                       *)
(*******************************************************************)

open Syntax

exception Unimplemented
exception Impossible

(*************************************)
(** {2 Lookup Tables (Environments)} *)
(*************************************)

let emptyenv = []
let insert (x,s,env) = (x,s)::env
exception NotFound
let rec lookup = function
      (y,[]) -> (print_string ("Unbound name: " ^ y ^ "\n");
                 raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookup(y,rest)

let rec lookupName = function
      (y,[]) -> (print_string ("Unbound name: " ^ (fst y) ^ "\n");
                 raise NotFound)
    | (y,(k,v)::rest) -> if (y=k) then v else lookupName(y,rest)



(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)

(** Context carried around by the type reconstruction algorithm.
 *)
type ctx = {implicits  : (string*set) list;  
               (** Implicit types for given variable names *)
            types      : (name*set) list;
               (** Typing context; types for names in scope *)
            tydefs     : (set_name*set) list;
               (** Definitions of type/set variables in scope *)
            sets       : set_name list ;
               (** Abstract (undefined) type/set variables in scope *)
           }

(** Determines whether a variable has an implicitly declared type.
     @param ctx  The type reconstruction context
     @param str  The (string) name of the variable.
  *)
let lookupImplicit ctx str = lookup (str, ctx.implicits)

let lookupType     ctx   n = lookupName (n, ctx.types)
let lookupTydef    ctx str = lookup (str, ctx.tydefs)
let lookupSet      ctx str = if (List.mem str ctx.sets) then
                                   ()
                             else raise NotFound

let peekTydef ctx s = try Some(lookupTydef ctx s) with
                        NotFound -> None

let insertImplicit ({implicits=implicits} as ctx) str ty = 
       {ctx with implicits = insert(str,ty,implicits)}
let insertType ({types=types} as ctx) n ty = 
       {ctx with types = insert(n,ty,types)}
let insertTydef ({tydefs=tydefs} as ctx) str ty = 
       {ctx with tydefs = insert(str,ty,tydefs)}
let insertSet ({sets=sets} as ctx) str =
       {ctx with sets = str::sets}

let emptyCtx = {implicits = []; types = [];
                tydefs = []; sets = []}

(**********************************)
(** {2 Set Comparison Operations} *)
(**********************************)

exception TypeError
let tyError s = (print_string ("TYPE ERROR: " ^ s ^ "\n");
                 raise TypeError)


(** Expand out any top-level definitions for a set *)
let rec hnfSet ctx = function
    Set_name n ->
      (match (peekTydef ctx n) with
        Some s' -> hnfSet ctx s'
      | None -> Set_name n)
  | s -> s

let eqSet   ctx s1 s2 = 
   if (s1 = s2) then
      (* Short circuting for common case *)
      true
   else
      let    s1' = hnfSet ctx s1
      in let s2' = hnfSet ctx s2
   
      in let rec cmp = function
          (Empty, Empty) -> true
        | (Unit, Unit) -> true
	| (Bool, Bool) -> true       (* Bool <> Sum() for now *)
        | (Set_name n1, Set_name n2) -> (n1 = n2)
	| (Product ss1, Product ss2) -> cmps (ss1,ss2)
        | (Sum lsos1, Sum lsos2) -> cmpsum (lsos1, lsos2)
        | (Exp(s3,s4), Exp(s5,s6)) -> cmp (s3,s5) && cmp (s4,s6)
	| (Subset(b1,p1), Subset(b2,p2)) -> 
            cmpbnd(b1,b2) && if (p1=p2) then
                                true 
		             else
                                (print_string 
		                   ("WARNING: not guaranteeing " ^ 
                                    "proposition equality\n");
				 true)
        | (Quotient(s3,t3), Quotient(s4,t4)) ->
            cmp(s3,s4) && if (t3=t4) then
                                true 
		             else
                                (print_string 
		                   ("WARNING: not guaranteeing " ^ 
                                    "equivalence-relation equality\n");
				 true)
        | (RZ s3, RZ s4) -> cmp(s3, s4)
        | (Prop,Prop) -> raise Unimplemented (* Shouldn't occur without HOL *)
        | (_,_) -> false
      and cmps = function
          ([], []) -> true
	| (s1::s1s, s2::s2s) -> cmp(s1,s2) && cmps(s1s,s2s)
        | (_,_) -> false
      and cmpsum = function
          ([], []) -> true
	| ((l1,None)::s1s, (l2,None)::s2s) -> (l1=l2) && cmpsum(s1s,s2s)
	| ((l1,Some s1)::s1s, (l2,Some s2)::s2s) -> 
                                (l1=l2) && cmp(s1,s2) && cmpsum(s1s,s2s)
        | (_,_) -> false
      and cmpbnd = function
	  (* Since we're not verifying equivalence of propositions,
	     we don't have to worry about the bound variable *)
          ((_, None),(_,None)) -> true
        | ((_, Some s1), (_,Some s2)) -> cmp(s1,s2)
        | (_,_) -> false

      in cmp(s1', s2')

let subSet  ctx s1 s2 =
  (s1 = s2) || (match (hnfSet ctx s1) with
		    Subset ((_, Some t), _) -> eqSet ctx t s2
		  | _ -> false)
			
let joinSet ctx s1 s2 = if (eqSet ctx s1 s2) then s1 else (tyError "No Join")

(* toProduct : ctx -> Syntax.set -> Syntax.set
     Supposed to return the "least supertype" of the given set
     that is a tuple type.  Currently only tries to expand
     definitions.
*)
let rec toProduct ctx = function
   Set_name s -> 
     let s' = (try lookupTydef ctx s with
                 NotFound -> 
                   tyError ("Cannot project from term of abstract type " ^ s))
     in toProduct ctx s'                    
 | Product ss -> Product ss
 | Subset (_,_) -> tyError "toProduct not defined for Subsets"
 | Quotient (_,_) -> tyError "toProduct not defined for Quotients"
 | _ -> tyError "bad projection; projectee is not a product"

(* toExp : ctx -> Syntax.set -> Syntax.set
     Supposed to return the "least supertype" of the given set
     that is a function type.  Currently only tries to expand
     definitions.
*)
let rec toExp ctx = function
   Set_name s -> 
     let s' = (try lookupTydef ctx s with
                NotFound -> 
                   tyError ("Cannot apply term of abstract type " ^ s))
     in toExp ctx s'
 | Exp (ty1,ty2) -> Exp (ty1, ty2)
 | Subset (_,_) -> tyError "toProduct not defined for Subsets"
 | Quotient (_,_) -> tyError "toProduct not defined for Quotients"
 | _ -> tyError "bad application; operand is not a function"


(*****************************************)
(** {2 Typechecking/Type Reconstruction} *)
(*****************************************)

let rec annotateSet ctx = 
    (let rec ann = function
          Product ss -> Product (List.map ann ss)
        | Sum lsos   -> Sum (List.map (function (l,sopt) -> 
                                         (l,annotateSetOpt ctx sopt))
                                      lsos)

        | Exp(s1,s2) -> Exp(ann s1, ann s2)

        | Subset(bnd, p) -> 
             let (bnd',ctx') = annotateBinding ctx bnd
             in let p' = annotateProp ctx' p
             in Subset(bnd', p')
        | Quotient(s, t) -> 
             (* What is the type of an equivalence relation? *)
             raise Unimplemented
(*             Quotient(ann s, annotateTerm ctx t) *)
        | RZ s -> RZ (ann s)
        | Set_name str ->
             ((try ignore(lookupSet ctx str) with
                _ -> ignore(lookupTydef ctx str));
              Set_name str)
        | s -> s
     in
        ann)

and annotateSetOpt ctx =
    (let ann = function
          Some s -> Some (annotateSet ctx s)
        | None -> None
     in
       ann)

and annotateProp ctx =
    (let rec ann = function
          False -> False
        | True -> True
        | And ps -> And (List.map ann ps)
        | Or ps -> Or (List.map ann ps)
        | Imply (p1, p2) -> Imply (ann p1, ann p2)
        | Iff (p1, p2) -> Iff (ann p1, ann p2)
        | Not p -> Not (ann p)
        | Equal (None, t1, t2) ->
            let    (t1', ty1) = annotateTerm ctx t1
            in let (t2', ty2) = annotateTerm ctx t2
            in let ty = joinSet ctx ty1 ty2
            in Equal(Some ty, t1', t2')
        | Equal (Some s, t1, t2) ->
            let    ty = annotateSet ctx s
            in let (t1', ty1) = annotateTerm ctx t1
            in let (t2', ty2) = annotateTerm ctx t2
            in if (eqSet ctx ty1 ty) then
                Equal(Some ty, t1', t2')
              else
                tyError "Operands of equality don't match constraint"
        | Forall(bnd, p) ->
            let (bnd',ctx') = annotateBinding ctx bnd
            in Forall(bnd', annotateProp ctx' p)
        | Exists(bnd, p) ->
            let (bnd',ctx') = annotateBinding ctx bnd
            in Exists(bnd', annotateProp ctx' p)
        | t -> (match annotateTerm ctx t with
                 (t', Prop) -> t'
                | _ -> tyError "Term found where a proposition was expected")
    in ann)
           
and annotateBinding ctx = function
      ((str,_) as x,sopt) -> 
         let s' = (match sopt with
                     Some s -> annotateSet ctx s
                   | None   -> (try (lookupImplicit ctx str) with
                                  NotFound -> 
                                   (tyError ("Bound variable not annotated " ^
                                             "explicitly or implicitly."))))
         in let ctx' = insertType ctx x s'
         in ((x, Some s'), ctx')

 (* Mildly bogus:  allows the types to refer to variables bound
    earlier in the sequence. *)
and annotateBindings ctx = function
      [] -> ([], ctx)
    | (bnd::bnds) -> 
         let    (bnd',ctx') = annotateBinding ctx bnd
         in let (bnds', ctx'') = annotateBindings ctx' bnds
         in (bnd'::bnds', ctx'')

and annotateTerm ctx = 
    (let rec ann = function 
       Var n -> (Var n, lookupType ctx n)
     | Constraint(t,s) ->
        let    (t',ty) = ann t
        in let s' = annotateSet ctx s
        in if eqSet ctx ty s' then
              (Constraint(t',s'), s')
           else
              tyError "Invalid constraint"
     | Star -> (Star, Unit)
     | Tuple ts ->
        let (ts', tys) = List.split (List.map ann ts)
        in (Tuple ts', Product tys)
     | Proj (n, t) -> 
        let    (t', tuplety) = ann t
        in let Product tys = toProduct ctx tuplety
        in if (n >= 1 && n <= List.length tys) then
              (Proj(n,t'), List.nth tys (n+1))
           else
              tyError ("Projection " ^ string_of_int n ^ " out of bounds")
     | App (t1, t2) ->
        let    (t1', ty1) = ann t1
        in let (t2', ty2) = ann t2
        in let Exp(ty3,ty4) = toExp ctx ty1
        in if (eqSet ctx ty2 ty3) then
              (App (t1', t2'), ty4)
           else
              tyError "Application has invalid argument"

     | Inj(_,_) -> 
         (print_string "Cannot typecheck Injections until they're annotated";
          raise Unimplemented)

     | Case(_,_) -> 
         (print_string "No point in implementing Case until we have Inj";
          raise Unimplemented)

     | Quot(_,_) -> 
         (print_string "What is the type of an equivalence relation?";
          raise Unimplemented)
 
     | Choose(_,_,_) ->
         (print_string "No point in implementing Choose until we have Quot";
          raise Unimplemented)
        
     | Let(bnd,t1,t2) ->
         let    (t1', ty1) = ann t1
         in let (bnd',ctx') = annotateBinding ctx bnd
         in let (t2', ty2) = annotateTerm ctx' t2
         in ((try (ignore(annotateSet ctx ty2)) with
               _ -> tyError ("Inferred let-body type depends on local " ^ 
                            "defns; maybe add a constraint?"));
             (Let(bnd',t1',t2'), ty2))

     | Lambda(bnd,t) ->
         let    ((_,Some ty1) as bnd', ctx') = annotateBinding ctx bnd
         in let (t', ty2) = annotateTerm ctx' t
         in (Lambda(bnd',t'), Exp(ty1, ty2))

     | Subin (t, s) ->
	 let s' = annotateSet ctx s in
	 let (t', ty) = annotateTerm ctx t in
	   if subSet ctx s' ty then
	     (Subin (t', s'), s')
	   else tyError("Subset mismatch :>")

     | Subout (t, s) ->
	 let s' = annotateSet ctx s in
	 let (t', ty) = annotateTerm ctx t in
	   if subSet ctx ty s' then
	     (Subout (t', s'), s')
	   else tyError ("Subset mismatch :<")


     | _ -> tyError "Proposition found where a term was expected"
   in ann)

and annotateTheoryElem ctx = 
    let rec ann = function
         Set(str, None) -> (Set(str, None), insertSet ctx str)
       | Set(str, Some s) -> 
           let ty = annotateSet ctx s
           in (Set(str, Some ty), insertTydef ctx str ty)
       | Value(n,s) ->
           let ((_,Some ty1), ctx') = annotateBinding ctx (n, Some s)
           in (Value(n,ty1), ctx')
       | Let_term(bnd,t) ->
           let    (t', ty1) = annotateTerm ctx t
           in let ((_,Some ty2) as bnd', ctx') = annotateBinding ctx bnd
           in if (eqSet ctx ty1 ty2) then
                (Let_term(bnd',t'), ctx')
              else
                tyError "Term definition doesn't match constraint"
       | Sentence(sort, n, bnds, p) ->
           let    (bnds',ctx') = annotateBindings ctx bnds
           in let p' = annotateProp ctx' p
           in (Sentence(sort, n, bnds', p'),
               ctx)   (* XXX:  Cannot refer to previous axioms!? *)
       | Predicate ((_, (Infix0|Infix1|Infix3|Infix4)) as n, stab, s) ->
	   begin
	     match toProduct ctx s with
		 Product [s1; s2] ->
		   (Predicate (n, stab, s),
		    insertType ctx n (Exp (s1, Exp (s2, Prop))))
	       | _ -> tyError "Infix names can only be used for binary relations"
	   end
       | Predicate (n, stab, s) ->
           let s' = annotateSet ctx s
           in
	     (Predicate (n, stab, s'),
              insertType ctx n (Exp (s', Prop)))
       | Implicit(_,_) -> raise Impossible (* see below *)
    in
      ann

and annotateTheoryElems ctx = function
      [] -> ([], ctx)
  
    | (Implicit(strs, s)::tes) ->    (* Eliminated during inference *)
           let    s' = annotateSet ctx s
           in let ctx' = List.fold_left 
                            (fun ctx -> fun str -> insertImplicit ctx str s') 
                            ctx strs
           in annotateTheoryElems ctx' tes

    | te::tes -> let (te', ctx') = annotateTheoryElem ctx te
                 in let (tes', ctx'') = annotateTheoryElems ctx' tes
                 in (te'::tes', ctx'')

(* XXX Does not return context or handle TheoryID's*)
and annotateTheory ctx = function
      Theory tes -> Theory(fst(annotateTheoryElems ctx tes))
   
and annotateTheorySpec ctx = function
      {t_arg = None; t_name = n; t_body = thr} ->
           {t_arg = None; t_name = n; t_body = annotateTheory ctx thr}
 
                    
      
