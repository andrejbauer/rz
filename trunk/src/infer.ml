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

let tyGenericError mssg = (print_string ("\nTYPE ERROR: " ^ mssg ^ "\n\n");
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

let tyUnboundError trm =
    (print_string "\nTYPE ERROR:  Unbound name ";
     print_string (string_of_term trm);
     print_string "\n\n";
     raise TypeError)

(**************************)
(** {2 Utility Functions} *)
(**************************)

let mkKind = function
    Unstable    -> Prop
  | Equivalence -> EquivProp
  | Stable      -> StableProp


(** XXX:   Several of the following utility functions are not
    really specific to infer.ml and might better belong
    in the Syntax file itself. *)

(** Determines whether the given "set" is a true set in
    first-order logic.
 *)
let rec isSet = function
    Empty | Unit | Bool | Set_name _ -> true

  | Product lst -> List.for_all isSet lst
  | Sum     lst -> List.for_all (function (_, None) -> true | 
                                          (_, Some s) -> isSet s) lst
  | Subset   ((_, Some st), _) -> isSet st
  | Subset   _          -> true
  | Rz       st         -> isSet st
  | Quotient (st,_)     -> isSet st
  | Exp      (st1, st2) -> isSet st1 && isSet st2

  | Prop       -> false
  | StableProp -> false
  | EquivProp  -> false

(** Determines whether the given "set" is a well-formed 
    either a proposition or (despite the name) a predicate.

    This isn't just the negation of isSet because a pair containing,
    say, a boolean and a proposition is neither a proper set nor a
    proper logical entity. 
*)
and isProp = function
    Empty | Unit | Bool | Set_name _ | Product _
  | Sum _ | Subset _ | Rz _ | Quotient _ -> false

  | Prop       -> true
  | StableProp -> true
  | EquivProp  -> true

  | Exp (s, t) -> isSet s && isProp t

let rec propKind = function
    Prop -> Unstable
  | StableProp -> Stable
  | EquivProp -> Equivalence
  | Exp (s, t) -> propKind t
  | t -> failwith ("propKind of a non-proposition: " ^ (string_of_set t))

(** Determines whether a name is infix. 
 *)
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

(** ------------------- *)


(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)

type theory_summary = 
    TermSpec of name * set 
  | SetSpec  of set_name * set option
  | ModelSpec  of model_name * theory_summary list  (** pre-expanded *)
     (* We can't apply a theory with arguments, so we don't even bother
        remembering such theories exist.  Technically, this means
        we don't detect shadowing *)
  | SentenceSpec

type cntxt = {implicits: set StringMap.t;
	      theories : ((model_name * theory) list * 
			  theory_summary list) StringMap.t;
              items    : theory_summary list}

let emptyCtx : cntxt = {implicits = StringMap.empty; 
			theories = StringMap.empty;
			items = []}

(** Check for an implicit declaration for the given name.
*)
let peekImplicit (cntxt : cntxt) (N(namestring, _)) = 
   if StringMap.mem namestring cntxt.implicits then
      Some (StringMap.find namestring cntxt.implicits)
   else 
      None

(** Searches the specs so far for the definition of a theory
    named by the given string.  Takes the whole context
    (unlike some of the other peek functions) because theories
    can be defined only at top level; we're never searching
    inside a model.
*)
let peekTheory (cntxt : cntxt) desired_thrynm =
   if StringMap.mem desired_thrynm cntxt.theories then
      Some (StringMap.find desired_thrynm cntxt.theories)
   else 
      None


(** Helper functions converting a list of model names to and from
    the corresponding (model) path.
*)

let toModel mdlnms = 
  let rec loop = function
      [] -> raise Impossible
    | [strng]       -> ModelName strng
    | strng::strngs -> ModelProj(loop strngs, strng)
  in loop (List.rev mdlnms)

let rec fmModel = function
    ModelName mdlnm -> [mdlnm]
  | ModelProj(mdl, lbl) -> fmModel mdl @ [lbl]


(** Given a substitution, a set name, and the sequence of models 
    inside which the set name occurs, extends the substitution to
    replace all references to the name by the appropriate projection
    from models.  Of course if the set name is declared at top-level,
    the substitution would be a no-op and so we don't bother to extend the
    substitution.

    The following two functions work similarly, but are given a model name
    or a term name respectively.
 *)
let addSetToSubst (substitution : subst) (nm : set_name) = function
    [] -> substitution
  | mdls  -> Syntax.insertSetvar substitution nm (Set_mproj(toModel mdls, nm))

let addModelToSubst (substitution : subst) mdlnm = function
    [] -> substitution
  | mdls  -> Syntax.insertModelvar substitution mdlnm 
      (ModelProj(toModel mdls, mdlnm))

let addTermToSubst (substitution : subst) (N(strng,fxty) as nm) = function
    [] -> substitution
  | mdls  -> Syntax.insertTermvar substitution nm 
      (MProj(toModel mdls, strng, fxty))


(** Given a theory (explicitly or by name), returns the specifications
    it contains.  

    XXX Doesn't really belong with the context functions, though.
*)
(*
let rec expandTheory cntxt = function
    Theory elems -> elems
  | TheoryID thrynm -> 
      (match (peekTheory cntxt thrynm) with
           Some ([],elems) -> elems
         | Some (_,_) -> tyGenericError ("Expanding a theory with args")
	 | None -> tyGenericError ("Undefined theory " ^ thrynm))
*)

(** It would be preferable if the following routines shared more code.
  
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
    get to x the substitution contains
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


(* Given the guts of a context and a desired set name, determine
   whether a set of that name exists (with or without a definition).

   Simpler than peekTydef and peekTypeof because we are just
   returning a boolean, so there's no need to maintain the substitution.

   This function takes the items, rather than a whole context,
   because this will also be used to search inside a model,
   where there are no implicits around.
 *)
let rec peekSet' items desired_stnm =
      (* let _ = print_string ("looking for " ^ stnm ^ "\n")
      in *) 
  let rec loop = function
      [] -> false
    | SetSpec(this_stnm, _) :: rest -> 
	(this_stnm = desired_stnm) || (loop rest)
    | _ ::rest -> loop rest
  in loop items
       
let peekSet cntxt desired_stnm = peekSet' cntxt.items desired_stnm

let addToSubst substitution pathtohere = function
    TermSpec(nm,_) -> addTermToSubst substitution nm pathtohere
  | SetSpec(stnm,_) -> addSetToSubst substitution stnm pathtohere
  | ModelSpec(mdlnm,_) -> addModelToSubst substitution mdlnm pathtohere
  | SentenceSpec      -> substitution (** Never referenced in a theory  *)

(** Given the guts of a context and a desired set name, determine
    whether a set of that name exists (with or without a definition).

    Simpler than peekTydef and peekTypeof because we are just
    returning a boolean, so there's no need to maintain the substitution.

    This function takes the items, rather than a whole context,
    because this will also be used to search inside a model,
    where there are no implicits around.
 *)
let rec peekTydef' subst0 cntxt pathtohere desired_stnm = 
  let rec loop substitution = function
      [] -> None
    | SetSpec (stnm, sopt) :: rest -> 
	if stnm = desired_stnm then
	  substSetOption substitution sopt
	else
	  loop (addSetToSubst substitution stnm pathtohere) rest
    | spc :: rest -> loop (addToSubst substitution pathtohere spc) rest
  in loop subst0 cntxt 
       
let peekTydef cntxt desired_stnm = 
  peekTydef' emptysubst cntxt.items [] desired_stnm

(* Rather than apply the substitution to the returned list of
   specs (describing the model's contents), we simply return
   the specs and the substitution separately.  If we go on
   to search inside the model, we can then pass in this
   substitution for the subst0 parameter.
*)
let rec peekTheoryof' subst0 cntxt pathtohere desired_mdlnm = 
  let rec loop substitution = function
      [] -> None
    | ModelSpec (mdlnm, theory) :: rest ->
        if mdlnm = desired_mdlnm then
          Some (theory, substitution)
        else
          loop (addModelToSubst substitution mdlnm pathtohere) rest
  in loop subst0 cntxt

let peekTheoryof cntxt desired_mdlnm = 
  peekTheoryof' emptysubst cntxt.items [] desired_mdlnm


let rec peekTypeof' subst0 items pathtohere desired_nm = 
  let rec loop substitution = function
      [] -> None
    | TermSpec(nm, set) :: rest ->
	if nm = desired_nm then 
          (let answer = substSet substitution set
	   in (* let _ = print_string (string_of_int (List.length substitution))
                 in let _ = print_string ("answer= " ^ string_of_set answer ^ "\n")
                 in *) Some answer)
        else 
	  (loop (addTermToSubst substitution nm pathtohere) rest)
    | spc :: rest -> loop (addToSubst substitution pathtohere spc) rest
  in loop subst0 items

let peekTypeof cntxt desired_nm = 
  peekTypeof' emptysubst cntxt.items [] desired_nm


(** XXX should check for [and reject as erroneous] shadowing! *)
let insertModel cntxt mdlnm thry = 
  (match peekTheoryof cntxt mdlnm with
       None -> {cntxt with items = ModelSpec(mdlnm,thry)::cntxt.items }
     | _ -> tyGenericError ("Shadowing of model name: " ^  mdlnm))

let insertSet   cntxt stnm = 
  if peekSet cntxt stnm then
    tyGenericError ("Shadowing of set name: " ^  stnm)
  else
    {cntxt with items = SetSpec(stnm, None) :: cntxt.items }
  
let insertTydef cntxt stnm st =
  if peekSet cntxt stnm then
    tyGenericError ("Shadowing of set name: " ^  stnm)
  else
    {cntxt with items = SetSpec(stnm, Some st) :: cntxt.items }

let insertVar  cntxt nm st = 
  (match peekTypeof cntxt nm with
       None -> {cntxt with items = TermSpec(nm,st) :: cntxt.items }
     | _ -> tyGenericError ("Shadowing of name: " ^  string_of_name nm))

let insertTheory cntxt thrynm args items =
  (match peekTheory cntxt thrynm with
       None -> {cntxt with theories = StringMap.add thrynm (args,items) 
					cntxt.theories}
     | _ -> tyGenericError ("Shadowing of theory name: " ^  thrynm))

let insertImplicits cntxt (namestrings : string list) st = 
  let rec loop = (* Add string/st pairs to the implicits mapping *)
    function 
      [] -> cntxt.implicits
    | strng::strngs -> StringMap.add strng st (loop strngs)
  in
    {cntxt with implicits = loop namestrings}


(**********************************)
(** {2 Set Comparison Operations} *)
(**********************************)


(** We also put in the annotateModel function here because it's
  used by hnfSet *)

(** Given a context and a model, returns 
     (a) the annotated model [currently this never changes, since
         models are just paths, with no place for sets to be inferred.]
     (b) the theory of the model 
     (c) A substitution that must be applied to the theory (b) in
         order for it to be well-formed
     (d) The list of model names in the model path.
*)
let rec annotateModel cntxt = function
    ModelName mdlnm ->
     (match (peekTheoryof cntxt mdlnm) with
	None -> tyGenericError ("Unknown Model " ^ mdlnm)
     | Some (thr,_) -> (ModelName mdlnm, thr, emptysubst, []))
  | ModelProj (mdl, lbl) as main_mdl ->
      let (mdl', thr', subst, pathtohere) = annotateModel cntxt mdl
      in (match (peekTheoryof' subst cntxt.items pathtohere lbl) with
	      None -> tyGenericError ("Unknown Model" ^ 
				      string_of_model main_mdl)
	    | Some (thr'',subst'') ->
		(ModelProj(mdl',lbl), thr'', subst'', pathtohere @ [lbl]))

(** Expand out any top-level definitions for a (well-formed) set 
  *)
let rec hnfSet cntxt = function
    Set_name stnm ->
      (match (peekTydef cntxt stnm) with
        Some st -> hnfSet cntxt st
      | None -> Set_name stnm)
  | Set_mproj (mdl, lbl) -> 
      let (_, thryspecs, subst, pathtohere) = annotateModel cntxt mdl
      in (match (peekTydef' subst thryspecs pathtohere lbl) with
		 None -> Set_mproj(mdl, lbl)
	       | Some st -> hnfSet cntxt st)
  | set -> set


(** Compare two sets.  If do_subtyping is true, we're doing subtyping
    (which currently is generated by width-subtyping on sums).  If it's
    false, we're doing equivalence.
  *)
let eqSet' do_subtyping cntxt s1 s2 = 
   if (s1 = s2) then
      (** Short circuting for (we hope) the common case *)
      true
   else
      let    s1' = hnfSet cntxt s1
      in let s2' = hnfSet cntxt s2
   
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

let joinSet cntxt s1 s2 = 
   if (s1 = s2) then
      (* Short circuting *)
      s1
   else
      let    s1' = hnfSet cntxt s1
      in let s2' = hnfSet cntxt s2

      in let rec joinSums = function 
	  ([], s2s) -> s2s
        | ((l1,None)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let None = List.assoc l1 s2s
		in (l1,None) :: joinSums(s1s, s2s)
              with _ -> tyGenericError ("Disagreement as to whether " ^ l1 ^
                         " stands alone or tags a value")
	    else (l1,None) :: joinSums(s1s, s2s))
        | ((l1,Some s1)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let Some s2 = List.assoc l1 s2s
		in if eqSet cntxt s1 s2 then
		      (l1,None) :: joinSums(s1s, s2s)
		else
		    tyGenericError ("Disagreement as to whether " ^ l1 ^
                                    " tags a value or stands alone")
              with _ -> tyGenericError("Disagreement on what type of value " ^ 
                                        l1 ^ " should tag")
	    else (l1,None) :: joinSums(s1s, s2s))


      in match (s1',s2') with
        | (Sum lsos1, Sum lsos2) -> Sum (joinSums (lsos1, lsos2))
        | _ -> if eqSet cntxt s1 s2 then
                  s1
       	       else
	          tyJoinError s1 s2
 

let joinSets cntxt =
  let rec loop = function
      [] -> Unit
    | [s] -> s
    | s::ss -> joinSet cntxt s (loop ss)
  in
    loop

(*****************************************)
(** {2 Typechecking/Type Reconstruction} *)
(*****************************************)


(** Given a context, a name, and a type, check this is the type of 
    some binary relation on some set and return the same type marked as an
    equivalence relation. 

    Raises an error if the type is not for a binary relation on a set. *)
let rec makeEquivalence cntxt nm = function
    Exp (Product [s1; s2], (Prop|StableProp|EquivProp)) ->
      if eqSet cntxt s1 s2 then
	Exp (Product [s1; s2], EquivProp)
      else
	tyGenericError ("Ill-typed equivalence " ^ (string_of_name nm))
  | Exp (s1, Exp (s2, (Prop|StableProp|EquivProp))) ->
      if eqSet cntxt s1 s2 then
	Exp (s1, Exp (s2, EquivProp))
      else
	tyGenericError ("Ill-typed equivalence " ^ (string_of_name nm))

(** Given a contxt and a set, return the annotated version of the set.

    Raises an error if the set is not well-formed.
*)
let rec annotateSet cntxt = 
    (let rec ann = function
          Product ss -> Product (List.map ann ss)
        | Sum lsos   -> Sum (List.map (function (l,sopt) -> 
                                         (l,annotateSetOpt cntxt sopt))
                                      lsos)

        | Exp(s1,s2) -> Exp (ann s1, ann s2)

        | Subset(bnd, p) -> 
             let (bnd',cntxt') = annotateBinding cntxt bnd
             in let p',_ = annotateProp cntxt' p
             in Subset(bnd', p')
        | Quotient(st, trm) ->
	    let    st' = ann st
	    in
	     (match equivalenceAt cntxt trm with
		  None -> tyGenericError 
		    ("Not an stable equivalence relation: " ^ 
		     string_of_term trm)
		| Some (domain_st, trm') -> 
		    if (eqSet cntxt st' domain_st) then
		      Quotient(st', trm')
		    else
		      tyGenericError
			("Wrong domain for equivalence relation in " ^
			 string_of_set (Quotient(st,trm))))
        | Rz st -> Rz (ann st)
        | Set_name stnm ->
             (if (peekSet cntxt stnm) then
		 Set_name stnm
	      else tyGenericError ("Set not found: " ^ stnm))
	| Set_mproj (mdl, lbl) as main_set -> 
	    let (mdl', thryspecs, _, _) = annotateModel cntxt mdl
	    in if (peekSet' thryspecs lbl) then
		Set_mproj(mdl',lbl)
	      else
		tyGenericError ("Unknown component " ^ string_of_set main_set)
        | s -> s
     in
        ann)

(** Same as annotateSet, but applies to set options *)
and annotateSetOpt cntxt = function
      Some s -> Some (annotateSet cntxt s)
    | None -> None

(** Given a context and a term denoting a logical proposition, return the
    annotated proposition and its stability.

    Raises an error if the given term is an ill-formed proposition
    or if it is a non-proposition term.
*)
and annotateProp cntxt =
    (let rec ann = function
          False  -> (False, Stable)
        | True   -> (True, Stable)
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
            let    (t1', ty1) = annotateTerm cntxt t1
            in let (t2', ty2) = annotateTerm cntxt t2
            in let ty3 = joinSet cntxt ty1 ty2
            in
	      Equal(Some ty3, t1', t2'), Stable

        | Equal (Some s, t1, t2) ->
            let    ty = annotateSet cntxt s
            in let (t1', ty1) = annotateTerm cntxt t1
            in let (t2', ty2) = annotateTerm cntxt t2
            in if (subSet cntxt ty1 ty) && (subSet cntxt ty2 ty) then
                Equal (Some ty, t1', t2'), Stable
              else
                tyGenericError "Operands of equality don't match constraint"
        | Forall(bnd, p) ->
            let (bnd',cntxt') = annotateBinding cntxt bnd in
            let (p', stb) = annotateProp cntxt' p
	    in
	      Forall(bnd', p'), stb

        | Exists(bnd, p) ->
            let (bnd',cntxt') = annotateBinding cntxt bnd
            in
	      Exists (bnd', fst (annotateProp cntxt' p)), Unstable

(*
        | ForallModels (str, thr, p) ->
	    let thr' = annotateTheory cntxt thr
	    in let cntxt' = insertModel cntxt str thr'
	    in let (p',stb) = annotateProp cntxt' p
            in (ForallModels(str,thr',p'), stb)
*)

	| Case(e, arms) -> 
	    let (e', ty) = annotateTerm cntxt e

	    in let annArm = function
		(l, None, prop) -> 
                  let prop', stab = ann prop
		  in ((l, None, prop'), stab, (l, None))
              | (l, Some bnd, prop) ->
                  let    ((_,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
		  in let prop', stab = annotateProp cntxt' prop
		  in ((l, Some bnd', prop'), stab, (l, Some ty1))
	    in let l = List.map annArm arms
	    in let newcase = Case (e', List.map (fun (a,_,_) -> a) l)
            in let sum_set = Sum (List.map (fun (_,_,s) -> s) l)
	    in
	    if (eqSet cntxt sum_set ty) then
	      newcase,
	      (match l with [] -> Stable | [_,s,_] -> s | _ -> Unstable)
	    else
	      tyCaseError cntxt e ty sum_set

        | t -> (match annotateTerm cntxt t with
                    (t', Prop) -> (t', Unstable)
                  | (t', StableProp) -> (t', Stable)
                  | (t', EquivProp) -> (t', Equivalence)
                  | _ -> tyGenericError (
		      "Term " ^ string_of_term t ^ 
		      " found where a proposition was expected"))
    in ann)

(** Given a context and a binding, returns the annotated binding
    and a copy of the context extended with this variable binding.

    Raises an error if there is no explicit or implicit set specified
    for the variable in the binding (or indirectly if a set in the
    binding is ill-formed).
*)
and annotateBinding cntxt = function
      (x,sopt) -> 
         let s' = (match sopt with
                     Some s -> annotateSet cntxt s
                   | None   -> (match (peekImplicit cntxt x) with
                                  Some s -> s
                                | None -> 
                                   (tyGenericError ("Bound variable " ^ 
						    string_of_name x ^ 
						    " not annotated " ^
                                             "explicitly or implicitly."))))
         in let cntxt' = insertVar cntxt x s'
         in ((x, Some s'), cntxt')

(** Like annotatebinding, but takes a (previously annotated) default set to
  be used if one is not implicitly specified in the binding or
  specified in an implicit declaration.

  Raises an error (indirectly) if the set in the binding is ill-formed.
*)
and annotateBindingWithDefault cntxt default_st = function
    (x,sopt) -> 
      let s' = (match sopt with
                    Some s -> annotateSet cntxt s
                  | None   -> (match (peekImplicit cntxt x) with
                                   Some s -> s
                                 | None -> default_st))
      in let cntxt' = insertVar cntxt x s'
      in ((x, Some s'), cntxt')
		 
		 
(**  Given a context and some bindings, annotate all the bindings.
     Returns the annotated bindings and a context with all the bindings 
     inserted.

     By design, does not allow sets in a binding to refer to earlier 
     bindings. 

     Raises an error (indirectly) if the bindings are not well-formed
     or if they create shadowing.
*)
and annotateBindings cntxt bnds = 
  let rec loop = function 
      [] -> []
    | (bnd::bnds) -> 
	let bnds' = loop bnds
	in let (bnd',_) = annotateBinding cntxt bnd
	in bnd' :: bnds'
  in let bnds' = loop bnds
  in (bnds', addBindings cntxt bnds')

(** Given a context and a list of pre-annotated bindings, returns
    a context with all the bound variables inserted.
*)
and addBindings cntxt = function
      [] -> cntxt
    | ((n,Some t)::bnds) -> 
         let    cntxt' = insertVar cntxt n t
         in let cntxt'' = addBindings cntxt' bnds
         in cntxt''
    | _ -> raise Impossible

(** Given a context and a list of pre-annotated model bindings, returns
    a context with all the bound variables inserted.
*)
(* Currently unused
and addMbindings cntxt = function
      [] -> cntxt
    | ((mdlnm,thry)::mbnds) -> 
         let    cntxt' = insertModel cntxt mdlnm thry
         in let cntxt'' = addMbindings cntxt' mbnds
         in cntxt''
*)

(** Given a context and a term, returns the corresponding annotated term
    and the set in which it lives.

    Raises an error if the term is ill-formed.
*)
and annotateTerm cntxt = 
  (let rec ann = function 
       Var nm -> 
	 (match (peekTypeof cntxt nm) with
	      Some ty -> (Var nm, ty)
	    | None -> tyUnboundError (Var nm))

     | MProj (mdl, lbl, fixity) as main_trm -> 
	 let (mdl', thryspecs, subst, pathtohere) = annotateModel cntxt mdl
	 in (match (peekTypeof' subst thryspecs pathtohere (N(lbl,fixity)))with
		 None -> tyGenericError ("Unknown component " ^
					 string_of_term main_trm)
	       | Some st -> (MProj(mdl,lbl,fixity), st))

     | Constraint(t,s) ->
         let    (t',ty) = ann t
         in let s' = annotateSet cntxt s
         in if subSet cntxt ty s' then
             (Constraint(t',s'), s')
           else
             tyMismatchError t s' ty

     | Star -> (Star, Unit)

     | Tuple ts ->
         let (ts', tys) = List.split (List.map ann ts)
         in (Tuple ts', Product tys)

     | Proj (n, t) -> 
         let    (t', tuplety) = ann t
        in let tys = (match (hnfSet cntxt tuplety) with
	                      Product tys -> tys
	                    | _ -> tyWrongSortError t " tuple" tuplety)
        in if (n >= 0 && n < List.length tys) then
              ((Proj(n,t'), List.nth tys n))
           else
              tyGenericError ("Projection " ^ string_of_int n ^ 
			      " out of bounds")
     | App (t1, t2) ->
        let (t1', ty1) = ann t1 in
        let (t2', ty2) = ann t2 in
        let (ty3,ty4) = (match (hnfSet cntxt ty1) with
	                      Exp(ty3,ty4) -> (ty3,ty4)
	                    | _ -> tyWrongSortError t1 " function" ty1)
        in
	  if (subSet cntxt ty2 ty3) then
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
               let    ((_,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
	       in let (e', ty2) = annotateTerm cntxt' e
	       in ((l, Some bnd', e'), (l, Some ty1), ty2)
         in let getArm = fun (arm,_,_) -> arm
         in let getSumPart = fun (_,sp,_) -> sp
         in let getReturn = fun (_,_,ret) -> ret
	 in let l = List.map annArm arms
	 in let newcase = Case(e', List.map getArm l)
         in let sum_set = Sum (List.map getSumPart l)
         in let return_set = joinSets cntxt (List.map getReturn l)
	 in
	   if (eqSet cntxt sum_set ty) then
	     (newcase, return_set)
	   else
	     tyCaseError cntxt e ty sum_set
	       
     | Quot(t, r) -> 
	 let t', ty = ann t in
	   (match equivalenceAt cntxt r with
		None -> 
		  failwith (string_of_term r ^ " is not a stable equivalence")
	      | Some(domain_st, r') ->
		  if eqSet cntxt domain_st ty then
		    (Quot(t',r'), Quotient(ty,r'))
		  else
		    tyGenericError
		      ("Term " ^ string_of_term t ^ " is in " ^
		       string_of_set ty ^ "\nbut " ^ string_of_term r ^
		       "is a relation on " ^ string_of_set domain_st))
	     
     | RzQuot t ->
	 let (t', ty) = ann t in
	   (match hnfSet cntxt ty with
		Rz ty' -> RzQuot t', ty'
	      | _ -> tyWrongSortError t "n RZ" ty)

     | RzChoose (bnd, t1, t2) ->
	 let (t1', ty1) = ann t1 in
	 let ((_, Some ty) as bnd', cntxt') = annotateBinding cntxt bnd in
	 let (t2', ty2) = annotateTerm cntxt' t2 in
	   (match hnfSet cntxt ty with
		Rz ty' ->
		  if eqSet cntxt ty1 ty' then
		    RzChoose(bnd', t1', t2')
		  else
		    failwith "type mismatch in let [...] = "
	      | _ -> failwith "type mismatch in let [...] = "),
	   ty2

     | Choose (bnd, r, t1, t2) ->
	 let (t1', ty1) = ann t1 in
	 let ((_, Some ty) as bnd', cntxt') = annotateBinding cntxt bnd in
	 let (t2', ty2) = annotateTerm cntxt' t2 in
	   (if eqSet cntxt (hnfSet cntxt ty1) (Quotient (ty, r)) then
	     Choose (bnd', r, t1', t2')
	   else
	     failwith "type mismatch in let % = "),
	   ty2	 
        
     | Let(bnd,t1,t2) ->
         let    (t1', ty1) = ann t1
         in let (bnd',cntxt') = annotateBindingWithDefault cntxt ty1 bnd
         in let (t2', ty2) = annotateTerm cntxt' t2
         in ((try (ignore(annotateSet cntxt ty2)) with
               _ -> tyGenericError ("Inferred let-body type depends on local " ^ 
                            "defns; maybe add a constraint?"));
             (Let(bnd',t1',t2'), ty2))

     | Lambda(bnd,t) ->
         let    ((_,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
         in let (t', ty2) = annotateTerm cntxt' t
         in (Lambda(bnd',t'), Exp(ty1, ty2))

     | Subin (t, s) ->
	 let s' = annotateSet cntxt s in
	 let (t', ty) = annotateTerm cntxt t in
	   (match hnfSet cntxt s' with
	     Subset ((_, Some ty'), _) -> 
	       if (subSet cntxt ty ty') then
		 (Subin (t', s'), s')
	       else
		 tyMismatchError t ty' ty
	   | _ -> tyGenericError "<: with a non-subset-type")

     | Subout (t, s) ->
	 let s' = annotateSet cntxt s in
	 let (t', ty) = annotateTerm cntxt t in
	   (match hnfSet cntxt ty with
	     Subset ((_, Some ty'), _) -> 
	       if (subSet cntxt ty' s') then
		 (Subout (t', s'), s')
	       else
		 tyGenericError("Subset mismatch :<")
	   | _ -> tyGenericError("Subset mismatch :<"))

     | prp -> tyGenericError ("Proposition " ^ 
			      string_of_term prp ^ 
			      " found where a term was expected")
   in ann)

(** Given a context and a term, determines whether the term is a
    (stable) equivalence relation.  If so, returns the domain set
    for this relation, and (for convenience) the annotated form
    of the term.
*)
and equivalenceAt cntxt trm =
   (match annotateTerm cntxt trm with  
	(trm', Exp (u, Exp (v, EquivProp))) |
        (trm', Exp (Product [u; v], EquivProp)) ->
	  if (eqSet cntxt u v) then
	    Some (u, trm')
	  else
	    None)



and annotateTheoryElem cntxt = function

    Set(stnm, None) -> 
      (insertSet cntxt stnm, Set(stnm, None), SetSpec(stnm, None))

  | Set(stnm, Some st) -> 
      let st' = annotateSet cntxt st
      in (insertTydef cntxt stnm st', 
	  Set(stnm, Some st'), 
	  SetSpec(stnm, Some st'))

  | Value(nm,st) ->
      let ((_,Some st') as bnd', cntxt') = annotateBinding cntxt (nm, Some st)
      in (cntxt', Value(nm,st'), TermSpec(nm,st'))

  | Let_term(bnd,trm) ->
      let   (trm', ty1) = annotateTerm cntxt trm
      in let ((nm,Some ty2) as bnd', cntxt') = 
	  annotateBindingWithDefault cntxt ty1 bnd
      in if (subSet cntxt ty1 ty2) then
          (cntxt', Let_term(bnd',trm'), TermSpec(nm,ty2))
        else
          tyGenericError ("Definition doesn't match constraint for " ^ 
			  string_of_bnd bnd)

  | Sentence(sort, sentence_nm, mbnds, bnds, p) ->
      let (mbnds', cntxt') = annotateModelBindings cntxt mbnds in
      let (bnds',cntxt'') = annotateBindings cntxt' bnds in
      let (p',_) = annotateProp cntxt'' p in
        (** Specs cannot refer to previous axioms, though 
	  the code matching this spec will. *)
        (cntxt, 
	 Sentence(sort, sentence_nm, mbnds', bnds', p'),
	 SentenceSpec)

  | Predicate (nm, stblty, st) ->
      (* XXX Code appears to be trying to allow user to explicitly say
	 the predicate is PROP/STABLEPROP (via makeProp), but I think
	 that annotateSet immediately reject these as non-sets.  *)
      let st' = annotateSet cntxt st in
      let st1 = makeProp nm (mkKind stblty) st' in
      let st2 = (if isInfix nm then makeBinaryCurried st1 else st1) in
      let st3 = (if stblty = Equivalence then makeEquivalence cntxt nm st2
		 else st2) in
      let st4 = (if stblty = Stable then makeStable st3 else st3) in
      let stblty' = (if propKind st4 = Stable then Stable else stblty) in
      let cntxt' = insertVar cntxt nm st4 in
	(cntxt',
	 Predicate (nm, stblty', st'), 
	 TermSpec(nm, st4))

  | Let_predicate (n, stab, bnds, p) ->
      let    (bnds', cntxt') = annotateBindings cntxt bnds
      in let tys = List.map (function (_, Some ty) -> ty) bnds'
      in let (p', stab') = annotateProp cntxt' p
      in let ty = List.fold_right (fun x y -> Exp(x,y)) tys (mkKind stab')
      in let cntxt' = insertVar cntxt n ty
      in
	if stab = Unstable or stab' = Stable then
	  (cntxt', 
	   (* XXX We could return stab' instead of stab...*)
	   Let_predicate (n, stab, bnds', p'),
	   TermSpec(n, ty))
	else
	  failwith ("Could not determine that " ^ 
		    (string_of_name n) ^ " is stable")

  | Model (mdlnm, thry) ->
      let (thry', contents) = annotateTheory cntxt thry
      in let cntxt' = insertModel cntxt mdlnm contents
      in 
        (cntxt', 
	 Model(mdlnm, thry'), 
	 ModelSpec(mdlnm, contents))

  | _ -> raise Impossible

and annotateTheoryElems cntxt = function
    [] -> ([], [])

  | Implicit(strs, s)::rest ->    (** Eliminated during inference *)
      let    s' = annotateSet cntxt s in
      let cntxt' = insertImplicits cntxt strs s' in
      let (rest_defs,rest_specs) = annotateTheoryElems cntxt' rest
      in (rest_defs, rest_specs)

  | thryelm::rest ->
      let (cntxt',def,spec) = annotateTheoryElem cntxt thryelm in
      let (rest_defs,rest_specs) = annotateTheoryElems cntxt' rest
      in (def::rest_defs, spec::rest_specs)

and annotateModelBindings cntxt = function
    [] -> [], cntxt
  | (m, th) :: bnd ->
      let (th',specs) = annotateTheory cntxt th in
      let bnd', cntxt' = annotateModelBindings cntxt bnd in
	((m, th') :: bnd', (insertModel cntxt' m specs))

and annotateTheory cntxt = function
  | Theory elems ->
	let (elems',specs) = annotateTheoryElems cntxt elems
        in (Theory elems', specs)

  | TheoryID str -> (match peekTheory cntxt str with
			 Some ([],specs) -> (TheoryID str, specs)
                       | Some (_,_) -> 
			   tyGenericError ("Use of parameterized theory: " ^
					   str)
		       | None -> tyGenericError ("Unknown theory: " ^ str))


and annotateTheoryDef cntxt = function
      Theorydef (str, args, thr) -> 
	let (args', cntxt') = annotateModelBindings cntxt args in
	let (thr', body_items) = annotateTheory cntxt' thr
	in (Theorydef (str, args', thr'), 
	    insertTheory cntxt str args body_items)

and annotateTheoryDefs cntxt = function
    [] -> []
  | td::tds -> let (td', cntxt') = annotateTheoryDef cntxt td
               in let tds' = annotateTheoryDefs cntxt' tds 
               in td'::tds'


