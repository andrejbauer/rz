(*******************************************************************)
(** {1 Type Reconstruction and Checking}                           *)
(**                                                                *)
(** For now we assume that                                         *)
(** all bound variables are annotated, either when declared        *)
(** or through a prior "implicit" statement.                       *)
(*******************************************************************)

open Syntax

exception Unimplemented
exception Impossible

(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)

(** Context carried around by the type reconstruction algorithm.
 *)
type ctx = {implicits  : set NameMap.t;  
               (** Implicit types for variables *)
            types      : set NameMap.t;
               (** Typing context; types for names in scope,
                   including sentences and terms *)
            tydefs     : set NameMap.t;
               (** Definitions of type/set variables in scope *)
            sets       : NameSet.t ;
               (** Abstract (undefined) type/set variables in scope *)
           }

(** Determines whether a variable has an implicitly declared type.
     @param ctx   The type reconstruction context
     @param name  The name of the variable.

     @raise Not_Found when the name isn't in the map.
  *)
let lookupImplicit ctx name = NameMap.find name ctx.implicits

let lookupType     ctx name = NameMap.find name ctx.types
let lookupTydef    ctx name = NameMap.find name ctx.tydefs


let peekSet ctx str = NameSet.mem str ctx.sets

let peekTydef ctx name = 
       if (NameMap.mem name ctx.tydefs) then
           Some (NameMap.find name ctx.tydefs)
       else None

let insertImplicit ctx name ty = 
       {ctx with implicits = NameMap.add name ty ctx.implicits}
let insertType ctx name ty = 
       {ctx with types = NameMap.add name ty ctx.types}
let insertTydef ctx name ty = 
       {ctx with tydefs = NameMap.add name ty ctx.tydefs}
let insertSet ctx name =
       {ctx with sets = NameSet.add name ctx.sets}

let emptyCtx = {implicits = NameMap.empty; 
                types     = NameMap.empty;
                tydefs    = NameMap.empty; 
                sets = NameSet.empty}

(**********************************)
(** {2 Set Comparison Operations} *)
(**********************************)

exception TypeError
let tyError s = (print_string ("TYPE ERROR: " ^ s ^ "\n");
                 raise TypeError)


(** Expand out any top-level definitions for a set *)
let rec hnfSet ctx = function
    Set_name name ->
      (match (peekTydef ctx name) with
        Some set -> hnfSet ctx set
      | None -> Set_name name)
  | set -> set

let eqSet' do_subtyping ctx s1 s2 = 
   if (s1 = s2) then
      (* Short circuting for common case *)
      true
   else
      let    s1' = hnfSet ctx s1
      in let s2' = hnfSet ctx s2
   
      in let rec cmp = function
          (Empty, Empty) -> true
        | (Unit, Unit)   -> true
	| (Bool, Bool)   -> true       (* Bool <> Sum() for now *)
        | (Set_name n1, Set_name n2) -> (n1 = n2)
	| (Product ss1, Product ss2) -> cmps (ss1,ss2)
        | (Sum lsos1, Sum lsos2)     -> subsum (lsos1, lsos2) &&
                                        (do_subtyping || subsum (lsos2, lsos1))
        | (Exp(s3,s4), Exp(s5,s6))   -> cmp (s3,s5) && cmp (s4,s6)
	| (Subset(b1,p1), Subset(b2,p2)) -> 
            cmpbnd(b1,b2) && if (p1=p2) then
                                true 
		             else
                                (print_string 
		                   ("WARNING: cannot confirm " ^ 
                                    "proposition equality\n");
				 true)
        | (Quotient(s3,x3,y3,t3), Quotient(s4,x4,y4,t4)) ->
            cmp(s3,s4) && if x3=y3 && y3=y4 && t3=t4 then
                                true 
		             else
                                (print_string 
		                   ("WARNING: cannot confirm " ^ 
                                    "equivalence-relation equality\n");
				 true)
        | (RZ s3, RZ s4) -> cmp(s3, s4)

        | (Prop,Prop) -> raise Impossible (** Shouldn't occur without HOL *)

        | (StableProp,StableProp) -> raise Impossible (** Shouldn't occur without HOL *)

        | (_,_) -> false

      and cmps = function
          ([], []) -> true
	| (s1::s1s, s2::s2s) -> cmp(s1,s2) && cmps(s1s,s2s)
        | (_,_) -> false

      and subsum = function
          ([], _) -> true
       | ((l1,None   )::s1s, s2s) ->
	     (try (let None = (List.assoc l1 s2s)
                   in subsum(s1s, s2s))
	      with _ -> tyError "Mismatch in sum types")
       | ((l1,Some s1)::s1s, s2s) -> 
	     (try (let Some s2 = (List.assoc l1 s2s)
                   in cmp(s1,s2) && subsum(s1s,s2s))
	      with _ -> tyError "Mismatch in sum types")

      and cmpsum = function
          ([], []) -> true
	| ((l1,None   )::s1s, (l2,None   )::s2s) -> (l1=l2) && cmpsum(s1s,s2s)
	| ((l1,Some s1)::s1s, (l2,Some s2)::s2s) -> 
                                (l1=l2) && cmp(s1,s2) && cmpsum(s1s,s2s)
        | (_,_) -> false

      and cmpbnd = function
	  (* Since we're not verifying equivalence of propositions,
	     we don't have to worry about the bound variable *)
          ((_, None), (_,None)) -> true
        | ((_, Some s1), (_,Some s2)) -> cmp(s1,s2)
        | (_,_) -> false

      in cmp(s1', s2')

let eqSet  = eqSet' false
let subSet = eqSet' true

let joinSet ctx s1 s2 = 
   if (s1 = s2) then
      (* Short circuting *)
      s1
   else
      let    s1' = hnfSet ctx s1
      in let s2' = hnfSet ctx s2

      in let rec joinSums = function 
	  ([], s2s) -> s2s
        | ((l1,None)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let None = List.assoc l1 s2s
		in (l1,None) :: joinSums(s1s, s2s)
              with _ -> tyError "Mismatch in sums [None/Some]"
	    else (l1,None) :: joinSums(s1s, s2s))
        | ((l1,Some s1)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let Some s2 = List.assoc l1 s2s
		in if eqSet ctx s1 s2 then
		      (l1,None) :: joinSums(s1s, s2s)
		else
		    tyError "Mismatch in sums [Some/Some]"
              with _ -> tyError "Mismatch in sums [Some/None]"
	    else (l1,None) :: joinSums(s1s, s2s))


      in match (s1',s2') with
        | (Sum lsos1, Sum lsos2) -> Sum (joinSums (lsos1, lsos2))
        | _ -> if eqSet ctx s1 s2 then
                  s1
       	       else
	          tyError "Sets don't have a join"
 

let joinSets ctx =
  let rec loop = function
      [] -> Unit
    | [s] -> s
    | s::ss -> joinSet ctx s (loop ss)
  in
    loop

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
        | Quotient(s, x, y, eq) -> 
	    let (_, ctx') = annotateBinding ctx (x, Some s) in
	    let (_, ctx'') = annotateBinding ctx' (y, Some s) in
	    let eq' = annotateProp ctx'' eq in
	      Quotient (ann s, x, y, eq')
        | RZ s -> RZ (ann s)
        | Set_name name ->
             (if peekSet ctx name then
		 Set_name name
	      else match peekTydef ctx name with
                     Some _ -> Set_name name
                   | None -> tyError ("Unknown set " ^ (fst name)))
        | s -> s
     in
        ann)

and annotateSetOpt ctx = function
      Some s -> Some (annotateSet ctx s)
    | None -> None

and annotateProp ctx =
    (let rec ann = function
          False  -> False
        | True   -> True
        | And ps -> And (List.map ann ps)
        | Or  ps -> Or  (List.map ann ps)
        | Imply (p1, p2) -> Imply (ann p1, ann p2)
        | Iff (p1, p2)   -> Iff (ann p1, ann p2)
        | Not p  -> Not (ann p)
        | Equal (None, t1, t2) ->
            let    (t1', ty1) = annotateTerm ctx t1
            in let (t2', ty2) = annotateTerm ctx t2
            in let ty3 = joinSet ctx ty1 ty2
            in Equal(Some ty3, t1', t2')
        | Equal (Some s, t1, t2) ->
            let    ty = annotateSet ctx s
            in let (t1', ty1) = annotateTerm ctx t1
            in let (t2', ty2) = annotateTerm ctx t2
            in if (subSet ctx ty1 ty) && (subSet ctx ty2 ty) then
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
                  | (t', StableProp) -> t'
                  | _ -> tyError "Term found where a proposition was expected")
    in ann)
           
and annotateBinding ctx = function
      (x,sopt) -> 
         let s' = (match sopt with
                     Some s -> annotateSet ctx s
                   | None   -> (try (lookupImplicit ctx x) with
                                  Not_found -> 
                                   (tyError ("Bound variable not annotated " ^
                                             "explicitly or implicitly."))))
         in let ctx' = insertType ctx x s'
         in ((x, Some s'), ctx')

 (** XXX  Mildly bogus?:  allows the types to refer to variables bound
    earlier in the sequence. *)
and annotateBindings ctx = function
      [] -> ([], ctx)
    | (bnd::bnds) -> 
         let    (bnd',  ctx') = annotateBinding ctx bnd
         in let (bnds', ctx'') = annotateBindings ctx' bnds
         in (bnd'::bnds', ctx'')

and annotateTerm ctx = 
    (let rec ann = function 
       Var n -> (Var n, lookupType ctx n)
     | Constraint(t,s) ->
        let    (t',ty) = ann t
        in let s' = annotateSet ctx s
        in if subSet ctx ty s' then
              (Constraint(t',s'), s')
           else
              tyError "Invalid constraint"
     | Star -> (Star, Unit)
     | Tuple ts ->
        let (ts', tys) = List.split (List.map ann ts)
        in (Tuple ts', Product tys)
     | Proj (n, t) -> 
        let    (t', tuplety) = ann t
        in let Product tys = hnfSet ctx tuplety
        in if (n >= 0 && n < List.length tys) then
              ((Proj(n,t'), List.nth tys n))
           else
              tyError ("Projection " ^ string_of_int n ^ " out of bounds")
     | App (t1, t2) ->
        let    (t1', ty1) = ann t1
        in let (t2', ty2) = ann t2
        in let Exp(ty3,ty4) = hnfSet ctx ty1
        in if (subSet ctx ty2 ty3) then
              (App (t1', t2'), ty4)
           else
              tyError "Application has invalid argument"

     | Inj(l,e) -> 
        let (e', ty)= ann e
        in (Inj(l,e'), Sum [(l, Some ty)])

     | Case(e,arms) -> 
	 let (e', ty) = ann e

	 in let annArm = function
             (l, None, e) -> 
                let (e', ty2) = ann e
		in ((l, None, e'), (l, None), ty2)
           | (l, Some bnd, e) ->
                let    ((_,Some ty1) as bnd', ctx') = annotateBinding ctx bnd
		in let (e', ty2) = annotateTerm ctx' e
		in ((l, Some bnd', e'), (l, Some ty1), ty2)
         in let getArm = fun (arm,_,_) -> arm
         in let getSumPart = fun (_,sp,_) -> sp
         in let getReturn = fun (_,_,ret) -> ret
	 in let l = List.map annArm arms
	 in let newcase = Case(e', List.map getArm l)
         in let sum_set = Sum (List.map getSumPart l)
         in let return_set = joinSets ctx (List.map getReturn l)
	 in
	    if (subSet ctx sum_set ty) then
	      (newcase, return_set)
	    else
	      tyError "patterns don't agree with type of matched value."

     | Quot(t, r) -> 
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
	   (match hnfSet ctx s' with
	     Subset ((_, Some t), _) -> 
	       if (subSet ctx ty t) then
		 (Subin (t', s'), s')
	       else
		 tyError("Subset mismatch :>")
	   | _ -> tyError("Subset mismatch :>"))

     | Subout (t, s) ->
	 let s' = annotateSet ctx s in
	 let (t', ty) = annotateTerm ctx t in
	   (match hnfSet ctx ty with
	     Subset ((_, Some t), _) -> 
	       if (subSet ctx t s') then
		 (Subout (t', s'), s')
	       else
		 tyError("Subset mismatch :<")
	   | _ -> tyError("Subset mismatch :<"))

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
           in if (subSet ctx ty1 ty2) then
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
	     match hnfSet ctx s with
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
       |  Let_predicate(n, bnds, p) ->
	   let    (bnds', ctx') = annotateBindings ctx bnds
	   in let tys = List.map (function (_,Some ty) -> ty) bnds'
	   in let p' = annotateProp ctx' p
	   in
	     (Let_predicate(n, bnds', p'),
	      insertType ctx n (List.fold_right 
				  (fun x y -> Exp(x,y)) tys Prop))
       | Implicit(_,_) -> raise Impossible (* see below *)
    in
      ann

and annotateTheoryElems ctx = function
      [] -> ([], ctx)
  
    | (Implicit(strs, s)::tes) ->    (** Eliminated during inference *)
           let    s' = annotateSet ctx s
           in let ctx' = List.fold_left 
                            (fun ctx str -> insertImplicit ctx (str,Word) s') 
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
 
                    
      
