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

(************************)
(** {2 Error Reporting} *)
(************************)

exception TypeError
exception SumError

let tyGenericError msg = (print_string ("\nTYPE ERROR: " ^ msg ^ "\n\n");
                 raise TypeError)

let tyMismatchError expr expected found =
    (print_string "\nTYPE ERROR:  the expression ";
     print_string (string_of_term expr);
     print_string "\nWas expected to have type: ";
     print_string (string_of_set expected);
     print_string "\nbut it actually has type: ";
     print_string (string_of_set found);
     print_string "\n\n";
     raise TypeError)

let tyJoinError ty1 ty2 =
    (print_string "\nTYPE ERROR:  the types ";
     print_string (string_of_set ty1);
     print_string " and ";
     print_string (string_of_set ty2);
     print_string " are incompatible\n\n";
     raise TypeError)


let tyCaseError expr term ty1 ty2 =
    (print_string "\nTYPE ERROR:  The value ";
     print_string (string_of_term term);
     print_string " being analyzed has type  ";
     print_string (string_of_set ty1);
     print_string "\n but the patterns are expecting a value of type  ";
     print_string (string_of_set ty2);
     print_string "\n\n";
     raise TypeError)

(*
let tyCondError expr ty1 ty2 =
    (print_string "Type error in conditional expression: ";
     print_string (string_of_term expr);
     print_string "\nThe first branch has type: ";
     print_string (string_of_set ty1);
     print_string "\nand the second branch has type: ";
     print_string (string_of_set ty2);
     print_string "\n\n";
     raise TypeError)
*)

let tyWrongSortError expr sort ty =
    (print_string "\nTYPE ERROR: ";
     print_string (string_of_term expr);
     print_string " is used as if it had a";
     print_string sort;
     print_string " type,\nbut it actually has type ";
     print_string (string_of_set ty);
     print_string "\n\n";
     raise TypeError)

let tyUnboundError lname =
    (print_string "\nTYPE ERROR:  Unbound variable ";
     print_string (string_of_longname lname);
     print_string "\n\n";
     raise TypeError)

(**************************)
(** {2 Utility Functions} *)
(**************************)


let mkProp = function
    Unstable -> Prop
  | Equivalence -> EquivProp
  | Stable -> StableProp



(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)

type ctx = theory_element list

let emptyCtx = []



let peekImplicit (ctx : ctx) (N(namestring, fixity) : name) = 
   let rec loop = function
       [] -> None
     | Implicit (strings, set)::rest -> 
         if List.mem namestring strings
            then Some set
            else loop rest
     | _::rest -> loop rest
   in
      loop ctx

(* For simplicity, at the moment does not descend into models,
   hence does not require substitutions *)
let peekTheory (ctx : ctx) namestring =
   let rec loop = function
       [] -> None
     | Subtheory (thisstring, theory)::rest -> 
         if thisstring = namestring 
            then Some theory
            else loop rest
     | _::rest -> loop rest
   in
      loop ctx

let rec expandTheory ctx = function
    Theory {t_arg = []; t_body = elems} -> elems
  | Theory _ -> []
  | TheoryID theoryid -> 
     (match (peekTheory ctx theoryid) with
        Some theory -> expandTheory ctx theory
      | None -> tyGenericError ("Undefined theory " ^ theoryid))
          

let addToSubst (substitution : renamingsubst) (N(namestring,fixity)) = function
    [] -> substitution
  | model::models  -> (N(namestring,fixity),
                       LN(model, models@[namestring], fixity)) ::
                             substitution

(** All these routines need cleaning up.
  
    The Basic idea is to maintain two things:  
     (1) where we are in reference to the top level
         (a list of model names representing the start of a path)
     (2) a substitution mapping all theory-component names in scope to the
         paths that would be used to access these values from
         the top-level.  so, e.g., if we had

           thy
              set s
              model M : thy
                           set t
                           model N : thy
                                        set u
                                        const x : u
                                     end
                        end

           end
      
         assuming we're looking for M::N::x, by the time we
         get there the substitution contains
             s -> s
             t -> M::t
             u -> M::N::u
         and the "where am I" list would be [M ; N].


    Warning:  references to TheoryID's from inside a 
     strict subtheory are likely to fail.  (The problem is
     that the "top-level" context that is passed to peekTypeof'
     gets lost on the recursive call, when we descend into
     a specific sub-model 
 *)

let rec peekTypeof' subst0 ctx pathtohere = function
    LN(namestring, strs, fixity) as lname ->
      let rec loop substitution = function
       [] -> None
        | Set(sname, sopt) :: rest ->
	    ((* let _ = print_string ("Found the set " ^ (string_of_name sname) ^ " when pathtohere = ")
	    in let _ = List.iter print_string 
		          (pathtohere @ ["\n"])
	    in *)
              loop (addToSubst substitution sname pathtohere) rest)
	| Predicate(pname, pkind, domain) :: rest ->
            if lname = toLN pname then
              Some (substSet substitution (Exp(domain, mkProp pkind)))
            else 
              loop (addToSubst substitution pname pathtohere) rest
	| Let_predicate(pname, pkind, bnds, _) :: rest ->
            if lname = toLN pname then
	      let    tys = List.map (function (_, Some ty) -> ty) bnds
              in let ty = List.fold_right (fun x y -> Exp(x,y)) tys (mkProp pkind)
              in     Some (substSet substitution ty)
            else 
              loop (addToSubst substitution pname pathtohere) rest
	| Let_term((tname, Some set), _) :: rest ->
	    if lname = toLN tname then 
                (let answer = substSet substitution set
                 in (* let _ = print_string ("answer= " ^ string_of_set answer ^ "\n")
                 in *)Some answer)
            else 
	    (loop (addToSubst substitution tname pathtohere) rest)
	| Value(vname, set) :: rest ->
	    if lname = toLN vname then 
                (let answer = substSet substitution set
		in (* let _ = print_string (string_of_int (List.length substitution))
                 in let _ = print_string ("answer= " ^ string_of_set answer ^ "\n")
                 in *) Some answer)
            else 
	    (loop (addToSubst substitution vname pathtohere) rest)

	| Variable(vname, set) :: rest ->
	    if lname = toLN vname then (Some (substSet substitution set)) else
	    (loop (addToSubst substitution vname pathtohere) rest)
        | Model (modelstr, theory) :: rest ->
	    (match strs with
	      [] -> (* We're looking for a variable in the current
                       so don't descend into searching this model *)
                loop (addToSubst substitution (N(modelstr,Word)) pathtohere) 
                     rest
            | str1::str1s -> 
		if (namestring = modelstr) then
                  peekTypeof' substitution
                    (expandTheory ctx theory) 
                    (pathtohere @ [namestring])
                    (LN(str1,str1s,fixity))
		else 
		  (* Wrong model; don't descend *)
                     loop (addToSubst substitution (N(modelstr,Word)) 
			     pathtohere) 
                          rest)
                                          
	| _ ::rest -> loop substitution rest
      in loop subst0 ctx 

let peekTypeof ctx lname = peekTypeof' [] ctx [] lname

let rec peekTydef' subst0 ctx pathtohere = function
    LN(namestring, strs, fixity) as lname ->
      let rec loop substitution = function
       [] -> None
        | Set(sname, sopt) :: rest -> 
	    if lname = toLN sname then
	      substSetOption substitution sopt
	    else
	      loop (addToSubst substitution sname pathtohere) rest
	| Predicate(pname, pkind, domain) :: rest ->
              loop (addToSubst substitution pname pathtohere) rest
	| Let_predicate(pname, pkind, bnds, _) :: rest ->
              loop (addToSubst substitution pname pathtohere) rest
	| Let_term((tname, Some set), _) :: rest ->
	    (loop (addToSubst substitution tname pathtohere) rest)
	| Value(vname, set) :: rest ->
	    (loop (addToSubst substitution vname pathtohere) rest)
	| Variable(vname, set) :: rest ->
	    (loop (addToSubst substitution vname pathtohere) rest)
        | Model (modelstr, theory) :: rest ->
	    (match strs with
	      [] -> (* We're looking for a variable in the current
                       so don't descend into searching this model *)
                loop (addToSubst substitution (N(modelstr,Word)) pathtohere) 
                     rest
            | str1::str1s -> 
		if (namestring = modelstr) then
                  peekTydef' substitution
                    (expandTheory ctx theory) 
                    (pathtohere @ [namestring])
                    (LN(str1,str1s,fixity))
		else 
		  (* Wrong model; don't descend *)
                     loop (addToSubst substitution (N(modelstr,Word)) 
			     pathtohere) 
                          rest)
                                          
	| _ ::rest -> loop substitution rest
      in loop subst0 ctx 

let peekTydef ctx lname = peekTydef' [] ctx [] lname


(* Simpler than peekTydef and peekTypeof because we are just
   returning a boolean, so there's no need to maintain the substitution.
   More complex than peekImplicit because the argument might be a
   general path. *)
let rec peekSet ctx = function
    LN(namestring, strs, fixity) as lname ->
      (* let _ = print_string ("looking for " ^ namestring ^ "\n")
      in *) let rec loop = function
       [] -> false
        | Set(sname, sopt) :: rest -> 
	    if lname = toLN sname then
	      true
	    else
	      loop rest
        | Model (modelstr, theory) :: rest ->
	    ((* print_string ("found the model" ^ modelstr ^ "\n"); *)
	     match strs with
	      [] -> (* We're looking for a variable in the current
                       so don't descend into searching this model *)
                loop rest
            | str1::str1s -> 
                if (namestring = modelstr) then
                  ((* print_string "it's what we're looking for\n"; *)
                   peekSet (expandTheory ctx theory) (LN(str1,str1s,fixity)))
		else 
		  (* Wrong model; don't descend *)
                     loop rest)
	| _ ::rest -> loop rest
      in loop ctx 



(** XXX should check for [and reject as erroneous] shadowing! *)
let insertModel ctx modelstring theory = (Model(modelstring,theory)::ctx)
let insertSet ctx name = (Set(name, None) :: ctx)
let insertTydef ctx name set = (Set(name,Some set) :: ctx)
let insertType ctx name set = (Value(name,set) :: ctx)
let insertImplicits ctx namestrings set = (Implicit(namestrings,set) :: ctx)
let insertTheory ctx thrstring thr = (Subtheory(thrstring, thr)::ctx)



(**********************************)
(** {2 Set Comparison Operations} *)
(**********************************)

(** Expand out any top-level definitions for a set 
  *)
let rec hnfSet ctx = function
    Set_name (lname) ->
      (match (peekTydef ctx lname) with
        Some set -> hnfSet ctx set
      | None -> Set_name lname)
  | set -> set

(** Compare two sets.  If do_subtyping is true, we're doing subtyping
    (which currently is generated by width-subtyping on sums).  If it's
    false, we're doing equivalence.
  *)
let eqSet' do_subtyping ctx s1 s2 = 
   if (s1 = s2) then
      (** Short circuting for common case *)
      true
   else
      let    s1' = hnfSet ctx s1
      in let s2' = hnfSet ctx s2
   
      in let rec cmp = function
          (Empty, Empty) -> true
        | (Unit, Unit)   -> true
	| (Bool, Bool)   -> true       (** Bool <> Sum() for now *)
        | (Set_name n1, Set_name n2) -> (n1 = n2)
	| (Product ss1, Product ss2) -> cmps (ss1,ss2)
        | (Sum lsos1, Sum lsos2)     -> 
	      subsum (lsos1, lsos2) &&
              (do_subtyping || subsum (lsos2, lsos1))
        | (Exp(s3,s4), Exp(s5,s6))   -> cmp (s5,s3) && cmp (s4,s6)
	| (Subset(b1,p1), Subset(b2,p2)) -> 
            cmpbnd(b1,b2) && if (p1=p2) then
                                true 
		             else
                                (print_string 
		                   ("WARNING: cannot confirm " ^ 
                                    "proposition equality\n");
				 true)
        | (Quotient(s3,r3), Quotient(s4,r4)) -> r3 = r4 && cmp(s3,s4)
        | (Rz s3, Rz s4) -> cmp(s3, s4)

        | (Prop,Prop) -> raise Impossible (** Shouldn't occur without HOL *)

        | (StableProp,StableProp) -> raise Impossible (** Shouldn't occur without HOL *)

        | (EquivProp,EquivProp) -> raise Impossible (** Shouldn't occur without HOL *)

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
	      with _ -> false)
       | ((l1,Some s1)::s1s, s2s) -> 
	     (try (let Some s2 = (List.assoc l1 s2s)
                   in cmp(s1,s2) && subsum(s1s,s2s))
	      with _ -> false)

      and cmpbnd = function
	  (* Since we're not verifying equivalence of propositions,
	     we don't have to worry about the bound variable *)
          ((_, None),    (_,None)   ) -> true
        | ((_, Some s1), (_,Some s2)) -> cmp(s1,s2)
        | ( _,           _          ) -> false

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
              with _ -> tyGenericError ("Disagreement whether " ^ l1 ^
                         " stands alone or tags a value")
	    else (l1,None) :: joinSums(s1s, s2s))
        | ((l1,Some s1)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let Some s2 = List.assoc l1 s2s
		in if eqSet ctx s1 s2 then
		      (l1,None) :: joinSums(s1s, s2s)
		else
		    tyGenericError ("Disagreement whether " ^ l1 ^
                                    " tags a value or stands alone")
              with _ -> tyGenericError("Disagreement on what type of value " ^ 
                                        l1 ^ " should tag")
	    else (l1,None) :: joinSums(s1s, s2s))


      in match (s1',s2') with
        | (Sum lsos1, Sum lsos2) -> Sum (joinSums (lsos1, lsos2))
        | _ -> if eqSet ctx s1 s2 then
                  s1
       	       else
	          tyJoinError s1 s2
 

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

let isEquivalence ctx s r =
    match peekTypeof ctx r with
	Some (Exp (u, Exp (v, EquivProp)))
      | Some (Exp (Product [u; v], EquivProp)) ->
	  (eqSet ctx s u) && (eqSet ctx s v)
      | _ -> false

let rec isSet = function
    Empty | Unit | Bool | Set_name _ -> true
  | Product lst -> List.for_all isSet lst
  | Sum lst -> List.for_all (function (_, None) -> true | (_, Some s) -> isSet s) lst
  | Subset ((_, Some s), _) -> isSet s
  | Subset _ -> true
  | Rz s -> isSet s
  | Quotient (s,_) -> isSet s
  | Exp (s, t) -> isSet s && isSet t
  | Prop -> false
  | StableProp -> false
  | EquivProp -> false

and isProp = function
    Empty | Unit | Bool | Set_name _ | Product _
  | Sum _ | Subset _ | Rz _ | Quotient _ -> false
  | Prop -> true
  | StableProp -> true
  | EquivProp -> true
  | Exp (s, t) -> isSet s && isProp t

let rec propKind = function
    Prop -> Unstable
  | StableProp -> Stable
  | EquivProp -> Equivalence
  | Exp (s, t) -> propKind t
  | t -> failwith ("propKind of a non-proposition: " ^ (string_of_set t))


let isInfix = function
    N(_, (Infix0|Infix1|Infix2|Infix3|Infix4)) -> true
  | _ -> false

let makeBinaryCurried = function
    Exp (s1, Exp (s2, ((Prop|StableProp|EquivProp) as p)))
  | Exp (Product [s1; s2], ((Prop|StableProp|EquivProp) as p)) ->
      Exp (s1, Exp (s2, p))
  | _ -> failwith "Invalid type of infix binary relation"

let rec makeProp n prp s =
  if isSet s then
    Exp (s, prp)
  else if isProp s then
    s
  else
    tyGenericError ("Invalid type for predicate " ^ (string_of_name n))
    
let rec makeStable = function
    Prop | StableProp -> StableProp
  | EquivProp -> EquivProp
  | Exp (s, t) -> Exp (s, makeStable t)
  | _ -> failwith "Internal error: cannot make a non-predicate stable"

let rec makeEquivalence n ctx = function
    Exp (Product [s1; s2], (Prop|StableProp|EquivProp)) ->
      if eqSet ctx s1 s2 then
	Exp (Product [s1; s2], EquivProp)
      else
	tyGenericError ("Ill-typed equivalence " ^ (string_of_name n))
  | Exp (s1, Exp (s2, (Prop|StableProp|EquivProp))) ->
      if eqSet ctx s1 s2 then
	Exp (s1, Exp (s2, EquivProp))
      else
	tyGenericError ("Ill-typed equivalence " ^ (string_of_name n))

(** ------------------- *)

let rec annotateSet ctx = 
    (let rec ann = function
          Product ss -> Product (List.map ann ss)
        | Sum lsos   -> Sum (List.map (function (l,sopt) -> 
                                         (l,annotateSetOpt ctx sopt))
                                      lsos)

        | Exp(s1,s2) -> Exp (ann s1, ann s2)

        | Subset(bnd, p) -> 
             let (bnd',ctx') = annotateBinding ctx bnd
             in let p',_ = annotateProp ctx' p
             in Subset(bnd', p')
        | Quotient(s, r) ->
	    let s' = ann s in
	      if isEquivalence ctx s' r then
		Quotient (s', r)
	      else
		failwith "only quotients by stable binary relations exist"
        | Rz s -> Rz (ann s)
        | Set_name lname ->
             (if peekSet ctx lname then
		 Set_name lname
	      else match peekTydef ctx lname with
                     Some _ -> Set_name lname
                   | None -> tyGenericError ("Unknown set " ^ 
                                             string_of_longname lname))
        | s -> s
     in
        ann)

and annotateSetOpt ctx = function
      Some s -> Some (annotateSet ctx s)
    | None -> None

and annotateProp ctx =
    (let rec ann = function
          False  -> False, Stable
        | True   -> True, Stable
        | And ps ->
	    let lst = List.map ann ps in
	      And (List.map fst lst),
	      (if List.for_all (fun (_, s) -> s = Stable) lst then Stable else Unstable)
        | Or ps ->
	    let lst = List.map ann ps in
	      Or (List.map fst lst),
	      (match lst with [] -> Stable | [_,s] -> s | _ -> Unstable)

        | Imply (p1, p2) ->
	    let p1', _ = ann p1 in
	    let p2', stb2 = ann p2 in	      
	      Imply (p1', p2'), stb2

        | Iff (p1, p2) ->
	    let p1', stb1 = ann p1 in
	    let p2', stb2 = ann p2 in	      
	      Iff (p1', p2'),
	      (if stb1 = Stable && stb2 = Stable then Stable else Unstable)

        | Not p  -> Not (fst (ann p)), Stable

        | Equal (None, t1, t2) ->
            let    (t1', ty1) = annotateTerm ctx t1
            in let (t2', ty2) = annotateTerm ctx t2
            in let ty3 = joinSet ctx ty1 ty2
            in
	      Equal(Some ty3, t1', t2'), Stable

        | Equal (Some s, t1, t2) ->
            let    ty = annotateSet ctx s
            in let (t1', ty1) = annotateTerm ctx t1
            in let (t2', ty2) = annotateTerm ctx t2
            in if (subSet ctx ty1 ty) && (subSet ctx ty2 ty) then
                Equal (Some ty, t1', t2'), Stable
              else
                tyGenericError "Operands of equality don't match constraint"
        | Forall(bnd, p) ->
            let (bnd',ctx') = annotateBinding ctx bnd in
            let (p', stb) = annotateProp ctx' p
	    in
	      Forall(bnd', p'), stb

        | Exists(bnd, p) ->
            let (bnd',ctx') = annotateBinding ctx bnd
            in
	      Exists (bnd', fst (annotateProp ctx' p)), Unstable

        | ForallModels (str, thr, p) ->
	    let thr' = annotateTheory ctx thr
	    in let ctx' = insertModel ctx str thr'
	    in let (p',stb) = annotateProp ctx' p
            in (ForallModels(str,thr',p'), stb) (** XXX Correct stability? *)

	| Case(e, arms) -> 
	    let (e', ty) = annotateTerm ctx e

	    in let annArm = function
		(l, None, prop) -> 
                  let prop', stab = ann prop
		  in ((l, None, prop'), stab, (l, None))
              | (l, Some bnd, prop) ->
                  let    ((_,Some ty1) as bnd', ctx') = annotateBinding ctx bnd
		  in let prop', stab = annotateProp ctx' prop
		  in ((l, Some bnd', prop'), stab, (l, Some ty1))
	    in let l = List.map annArm arms
	    in let newcase = Case (e', List.map (fun (a,_,_) -> a) l)
            in let sum_set = Sum (List.map (fun (_,_,s) -> s) l)
	    in
	    if (eqSet ctx sum_set ty) then
	      newcase,
	      (match l with [] -> Stable | [_,s,_] -> s | _ -> Unstable)
	    else
	      tyCaseError ctx e ty sum_set

        | t -> (match annotateTerm ctx t with
                    (t', Prop) -> (t', Unstable)
                  | (t', StableProp) -> (t', Stable)
                  | (t', EquivProp) -> (t', Equivalence)
                  | _ -> tyGenericError (
		      "Term " ^ string_of_term t ^ 
		      " found where a proposition was expected"))
    in ann)
           
and annotateBinding ctx = function
      (x,sopt) -> 
         let s' = (match sopt with
                     Some s -> annotateSet ctx s
                   | None   -> (match (peekImplicit ctx x) with
                                  Some s -> s
                                | None -> 
                                   (tyGenericError ("Bound variable " ^ 
						    string_of_name x ^ 
						    " not annotated " ^
                                             "explicitly or implicitly."))))
         in let ctx' = insertType ctx x s'
         in ((x, Some s'), ctx')

and annotateBindingWithDefault ctx defaultset = function
      (x,sopt) -> 
         let s' = (match sopt with
                     Some s -> annotateSet ctx s
                   | None   -> defaultset)
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

and addBindings ctx = function
      [] -> ctx
    | ((n,Some t)::bnds) -> 
         let    ctx' = insertType ctx n t
         in let ctx'' = addBindings ctx' bnds
         in ctx''

and annotateTerm ctx = 
    (let rec ann = function 
       Var lname -> 
	 (match (peekTypeof ctx lname) with
	   Some ty -> (Var lname, ty)
	 | None -> tyUnboundError lname)
     | Constraint(t,s) ->
        let    (t',ty) = ann t
        in let s' = annotateSet ctx s
        in if subSet ctx ty s' then
              (Constraint(t',s'), s')
           else
              tyMismatchError t s' ty
     | Star -> (Star, Unit)
     | Tuple ts ->
        let (ts', tys) = List.split (List.map ann ts)
        in (Tuple ts', Product tys)
     | Proj (n, t) -> 
        let    (t', tuplety) = ann t
        in let tys = (match (hnfSet ctx tuplety) with
	                      Product tys -> tys
	                    | _ -> tyWrongSortError t " tuple" tuplety)
        in if (n >= 0 && n < List.length tys) then
              ((Proj(n,t'), List.nth tys n))
           else
              tyGenericError ("Projection " ^ string_of_int n ^ " out of bounds")
     | App (t1, t2) ->
        let    (t1', ty1) = ann t1
        in let (t2', ty2) = ann t2
        in let (ty3,ty4) = (match (hnfSet ctx ty1) with
	                      Exp(ty3,ty4) -> (ty3,ty4)
	                    | _ -> tyWrongSortError t1 " function" ty1)
        in if (subSet ctx ty2 ty3) then
              (App (t1', t2'), ty4)
           else
              tyMismatchError t2 ty3 ty2

     | Inj (l, None) ->
	 (Inj (l, None), Sum [(l, None)])

     | Inj(l, Some e) -> 
        let (e', ty)= ann e
        in (Inj(l, Some e'), Sum [(l, Some ty)])

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
	    if (eqSet ctx sum_set ty) then
	      (newcase, return_set)
	    else
	      tyCaseError ctx e ty sum_set

     | Quot(t, r) -> 
	 let t', ty = ann t in
	   if isEquivalence ctx ty r then
	     Quot (t', r), Quotient (ty, r)
	   else
	     failwith (string_of_longname r ^ " is not an equivalence")
	 
     | RzQuot t ->
	 let (t', ty) = ann t in
	   (match hnfSet ctx ty with
		Rz ty' -> RzQuot t', ty'
	      | _ -> tyWrongSortError t "n RZ" ty)

     | RzChoose (bnd, t1, t2) ->
	 let (t1', ty1) = ann t1 in
	 let ((_, Some ty) as bnd', ctx') = annotateBinding ctx bnd in
	 let (t2', ty2) = annotateTerm ctx' t2 in
	   (match hnfSet ctx ty with
		Rz ty' ->
		  if eqSet ctx ty1 ty' then
		    RzChoose(bnd', t1', t2')
		  else
		    failwith "type mismatch in let [...] = "
	      | _ -> failwith "type mismatch in let [...] = "),
	   ty2

     | Choose (bnd, r, t1, t2) ->
	 let (t1', ty1) = ann t1 in
	 let ((_, Some ty) as bnd', ctx') = annotateBinding ctx bnd in
	 let (t2', ty2) = annotateTerm ctx' t2 in
	   (if eqSet ctx (hnfSet ctx ty1) (Quotient (ty, r)) then
	     Choose (bnd', r, t1', t2')
	   else
	     failwith "type mismatch in let % = "),
	   ty2	 
        
     | Let(bnd,t1,t2) ->
         let    (t1', ty1) = ann t1
         in let (bnd',ctx') = annotateBindingWithDefault ctx ty1 bnd
         in let (t2', ty2) = annotateTerm ctx' t2
         in ((try (ignore(annotateSet ctx ty2)) with
               _ -> tyGenericError ("Inferred let-body type depends on local " ^ 
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
	     Subset ((_, Some ty'), _) -> 
	       if (subSet ctx ty ty') then
		 (Subin (t', s'), s')
	       else
		 tyMismatchError t ty' ty
	   | _ -> tyGenericError "<: with a non-subset-type")

     | Subout (t, s) ->
	 let s' = annotateSet ctx s in
	 let (t', ty) = annotateTerm ctx t in
	   (match hnfSet ctx ty with
	     Subset ((_, Some ty'), _) -> 
	       if (subSet ctx ty' s') then
		 (Subout (t', s'), s')
	       else
		 tyGenericError("Subset mismatch :<")
	   | _ -> tyGenericError("Subset mismatch :<"))

     | _ -> tyGenericError "Proposition found where a term was expected"
   in ann)

and annotateTheoryElems ctx raccum ctx0 = function

         [] -> (List.rev raccum, ctx0, ctx)

       | Set(str, None)::rest -> 
           annotateTheoryElems (insertSet ctx str) 
                               (Set(str, None)::raccum) (insertSet ctx0 str) rest

       | Set(str, Some s)::rest -> 
           let ty = annotateSet ctx s
           in annotateTheoryElems (insertTydef ctx str ty)
                                  (Set(str, Some ty)::raccum)
                                  (insertTydef ctx0 str ty)
                                  rest

       | Value(n,s)::rest ->
           let ((_,Some ty1) as bnd', ctx') = annotateBinding ctx (n, Some s)
	   in let ctx0' = addBindings ctx0 [bnd']
           in annotateTheoryElems ctx' (Value(n,ty1)::raccum) ctx0' rest

       | Let_term(bnd,t)::rest ->
           let    (t', ty1) = annotateTerm ctx t
           in let ((_,Some ty2) as bnd', ctx') = 
	                 annotateBindingWithDefault ctx ty1 bnd
           in let ctx0' = addBindings ctx0 [bnd']
           in if (subSet ctx ty1 ty2) then
                annotateTheoryElems ctx' (Let_term(bnd',t')::raccum) ctx0' rest
              else
                tyGenericError "Term definition doesn't match constraint"

       | Sentence(sort, n, bnds, p)::rest ->
           let    (bnds',ctx') = annotateBindings ctx bnds
           in let (p',_) = annotateProp ctx' p
           in annotateTheoryElems ctx (Sentence(sort, n, bnds', p')::raccum) 
                                  ctx0 rest
                    (** XXX:  Cannot refer to previous axioms!? *)

       | Predicate (n, stab, s)::rest ->
	   let s1 = makeProp n (mkProp stab) (annotateSet ctx s) in
	   let s2 = (if isInfix n then makeBinaryCurried s1 else s1) in
	   let s3 = (if stab = Equivalence then makeEquivalence n ctx s2 else s2) in
	   let s4 = (if stab = Stable then makeStable s3 else s3) in
	   let ctx' = insertType ctx n s4 in
           let ctx0' = insertType ctx0 n s4 in
	     annotateTheoryElems ctx' (Predicate (n, (if propKind s4 = Stable then Stable else stab), s4)::raccum) ctx0' rest

       | Let_predicate (n, stab, bnds, p)::rest ->
	   let    (bnds', ctx') = annotateBindings ctx bnds
	   in let tys = List.map (function (_, Some ty) -> ty) bnds'
	   in let (p', stab') = annotateProp ctx' p
           in let ty = List.fold_right (fun x y -> Exp(x,y)) tys (mkProp stab')
           in let ctx' = insertType ctx n ty
           in let ctx0' = insertType ctx0 n ty
	   in
	     if stab = Unstable or stab' = Stable then
	       annotateTheoryElems ctx' (Let_predicate (n, stab, bnds', p')::raccum)
                                   ctx0' rest
	     else
	       failwith ("Could not determine that " ^ (string_of_name n) ^ " is stable")

       | Implicit(strs, s)::rest ->    (** Eliminated during inference *)
           let    s' = annotateSet ctx s
           in let ctx' = insertImplicits ctx strs s'
           in annotateTheoryElems ctx' raccum ctx0 rest

       | Model (str,thr) :: rest ->
           let thr' = annotateTheory ctx thr
           in let ctx' = insertModel ctx str thr'
           in let ctx0' = insertModel ctx str thr'
           in 
              annotateTheoryElems ctx' (Model(str,thr')::raccum) ctx0' rest
(*
       | Subtheory (str, thr)::rest ->
            raise Unimplemented
*)

(* XXX Does not return context or handle TheoryID's*)
and annotateTheory ctx = function
  | Theory {t_arg = []; t_body = tesb } ->
	let (tesb', ctx_thr, _) = annotateTheoryElems ctx [] emptyCtx tesb
        in Theory {t_arg=[]; t_body = tesb'}

  |  Theory {t_arg = tesa; t_body = tesb} -> 
	let (tesa', _, ctx') = annotateTheoryElems ctx [] emptyCtx tesa
	in let (tesb', ctx_thr, _) = annotateTheoryElems ctx' [] emptyCtx tesb
        in Theory {t_arg=tesa'; t_body = tesb'}
    | TheoryID str -> (match peekTheory ctx str with
			 Some thr -> TheoryID str
		       | None -> tyGenericError ("Unknown Theory " ^ str))
			    


and annotateTheoryDef ctx = function
      TheoryDef(str, thr) -> 
	let thr' = annotateTheory ctx thr
	in (TheoryDef(str, thr'),
	    insertTheory ctx str thr')

and annotateTheoryDefs ctx = function
    [] -> []
  | td::tds -> let (td', ctx') = annotateTheoryDef ctx td
               in let tds' = annotateTheoryDefs ctx' tds 
               in td'::tds'


