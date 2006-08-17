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

let tyGenericError mssg = 
  (print_string ("\nTYPE ERROR: " ^ mssg ^ "\n\n");
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

let tyWrongSortError expr sort ty =
    (print_string "\nTYPE ERROR: ";
     print_string (string_of_term expr);
     print_string " is used as if it had a";
     print_string sort;
     print_string " type,\nbut it actually has type ";
     print_string (string_of_set ty);
     print_string "\n\n";
     raise TypeError)

let notProperSetError ty in_string  =
	    (print_string "\nTYPE ERROR: ";
	     print_string (string_of_set ty);
	     print_string " is not a proper set in ";
	     print_string in_string;
	     print_string "\n\n";
	     raise TypeError)

(**************************)
(** {2 Utility Functions} *)
(**************************)

let mkPropSet = function
    Unstable    -> Prop
  | Equivalence -> EquivProp
  | Stable      -> StableProp

let meetPropKind k1 k2 = 
  (match (k1,k2) with
       (Unstable, _) -> Unstable
     | (_, Unstable) -> Unstable
     | (Stable, _) -> Stable
     | (_, Stable) -> Stable
     | _ -> Equivalence)

let meetPropKinds lst =
  List.fold_left meetPropKind Equivalence lst

let joinPropKind k1 k2 = 
  (match (k1,k2) with
       (Equivalence, _) -> Equivalence
     | (_, Equivalence) -> Equivalence
     | (Stable, _) -> Stable
     | (_, Stable) -> Stable
     | _ -> Unstable)

let joinPropKinds lst =
  List.fold_left joinPropKind Unstable lst


(** XXX:   Several of the following utility functions are not
    really specific to infer.ml and might better belong
    in the Syntax file itself. *)


(** propKind: set -> propKind

    Translates the type of a set satisfying isProp (the classifier
    of a predicate) into the sort of such predicates. 
 *)
let rec propKind = function
    Prop -> Unstable
  | StableProp -> Stable
  | EquivProp -> Equivalence
  | Exp (_, s, t) -> propKind t
  | t -> failwith ("propKind of a non-proposition: " ^ (string_of_set t))

(** isInfix : name -> bool
  
    Determines whether a name is infix. 
 *)
let isInfix = function
    N( _ , ( Infix0 | Infix1 | Infix2 | Infix3 | Infix4  ) )  -> true
  | _ -> false


(** makeStable : set -> set

    Translates a set classifying a relation into the corresponding
    set classifying a stable relation.
 *)
let rec makeStable = function
    Prop | StableProp -> StableProp
  | EquivProp -> EquivProp
  | Exp (nopt, s, t) -> Exp (nopt, s, makeStable t)
  | _ -> failwith "Internal error: cannot make a non-predicate stable"


(*********************************)
(** {2 The Typechecking Context} *)
(*********************************)

(********************************)
(** {3 Context Representation} **)
(********************************)

(** A summary of one item that might appear in a theory.
*)
type theory_summary_item = 
    TermSpec  of name * set                   (** Term and its type *)
  | SetSpec   of set_name * kind * set option (** Set and its definition *)
  | ModelSpec of model_name * theory_summary 
  | OtherSpec (** Some logical sentence or a comment; 
		  details aren't important *) 

and theory_summary =
     (** NB: The contents are stored with the
         first item in the list being the first item in the model! 
         This is BACKWARDS from the items list of a typing context,
         where the first item in the model becomes the last item of
         the list, but both make sense. *)
    Summary_Struct of theory * theory_summary_item list
  | Summary_Functor of (model_name * theory) * theory_summary

(** summaryTotheory : theory_summary -> theory 

    Each theory summary is easier to search for its components,
    but it also includes enough information to reconstruct the
    theory in its entirety.
 *)
let rec summaryToTheory = function
    Summary_Struct  ( thry, _ )      -> thry
  | Summary_Functor ( bnd, summary ) -> 
      TheoryFunctor ( bnd, summaryToTheory summary )

(** selfify : theory -> theory_summary -> theory_summary

    Replaces the theory contained in the theory summary.  For example,
    if we have
      theory N = thy ... end
    then the summary associated with the right-hand-side, when passed
    to summaryToTheory, returns the thy...end.  This function can be
    used to modify the summary so that summaryToTheory returns just N
    instead.
 *)
let rec selfify thry = function
    Summary_Struct ( _ , summary ) -> Summary_Struct ( thry , summary )
  | Summary_Functor ( (modnm,_) as bnd, summary ) ->
      Summary_Functor ( bnd , 
			selfify ( TheoryApp ( thry , ModelName modnm ) )
			        summary )

(** substSummary : Syntax.subst -> theory_summary -> theory_summary 

    XXX Not capture avoiding!
 *)
let rec substSummary sub = function
    Summary_Struct (thry, items) -> 
      Summary_Struct ( substTheory sub thry, 
		    substItems sub items )
  | Summary_Functor ( ( mdlnm, thry ), summary ) ->
      let    thry'    = substTheory sub thry
      in let sub'     = insertModelvar sub mdlnm ( ModelName mdlnm )
      in let summary' = substSummary sub' summary
      in Summary_Functor ( ( mdlnm, thry' ), summary' )

and substItems sub = function
    [] -> []
  | TermSpec ( nm, st ) :: rest -> 
      let st' = substSet sub st
      in let this' = TermSpec ( nm, st' )
      in let sub'  = insertTermvar sub nm ( Var ( None, nm ) )
      in let rest' = substItems sub' rest
      in this' :: rest'
  | SetSpec ( stnm, knd, stopt ) :: rest -> 
      let stopt' = substSetOption sub stopt
      in let knd'  = substKind sub knd
      in let this' = SetSpec ( stnm, knd', stopt' )
      in let sub'  = insertSetvar sub stnm ( Set_name ( None, stnm ) )
      in let rest' = substItems sub' rest
      in this' :: rest'
  | ModelSpec ( mdlnm, summary ) :: rest ->
      let summary' = substSummary sub summary
      in let this' = ModelSpec ( mdlnm, summary' )
      in let sub'  = insertModelvar sub mdlnm ( ModelName mdlnm ) 
      in let rest' = substItems sub' rest
      in this' :: rest'
  | OtherSpec :: rest ->
      OtherSpec :: ( substItems sub rest )
	  

(** Representation of the context itself.  The implicits and theories
    are stored separately, because they are not components of any model.
    (Theories can refer to top-level models defined previously, however.)

    Question:  Once theories can depend on models, is there any reason to
    forbid theories from being defined inside models?  Yes; ML doesn't
    permit signatures to be defined inside other signatures.
*)

type cntxt = { implicits: set StringMap.t;
	       theories : theory_summary StringMap.t;
               items    : theory_summary_item list    }

(** The empty context *)

let emptyCtx : cntxt = {implicits = StringMap.empty; 
			theories  = StringMap.empty;
			items     = []              }

(***************************)
(** {3 Lookup Functions } **)
(***************************)

(** peekImplicit: cntxt -> nm -> set option

    Returns any previous "implicit" declaration for a variable of
    the given name.
*)
let peekImplicit (cntxt : cntxt) (N(namestring, _)) = 
   if StringMap.mem namestring cntxt.implicits then
      Some (StringMap.find namestring cntxt.implicits)
   else 
      None

(** peekTheory: cntxt -> theory_name -> theory_summary option

    Searches the specs so far for the definition of a theory
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

(** addSetToSubst : subst -> set_name -> model -> subst

    Given a substitution, a set name, and the
    model directly containing that set name, extends the
    substitution to replace all direct references to the set by the
    appropriate projection from models.  Of course if the set name is
    declared at top-level, this would be an identity and so so we
    don't bother extending the substitution.

    The following two functions addModelToSubst and addTermToSubst work 
    similarly, but are given a model name or a term name respectively.
 *)
let addSetToSubst ( sub : subst ) ( stnm : set_name ) = function
    None      -> sub
  | Some mdl  -> Syntax.insertSetvar sub stnm 
                   ( Set_name ( Some mdl, stnm ) )

(** addModelToSubst : subst -> model_name -> model -> subst
  *)
let addModelToSubst (sub : subst) mdlnm = function
    None      -> sub
  | Some mdl  -> Syntax.insertModelvar sub mdlnm 
                   ( ModelProj ( mdl, mdlnm ) )

(** addTermToSubst : subst -> name -> model -> subst
  *)
let addTermToSubst (sub : subst) nm = function
    None      -> sub
  | Some mdl  -> Syntax.insertTermvar sub nm 
                   ( Var ( Some mdl, nm ) )

(** addToSubst : subst -> model -> theory_summary_item -> subst

    Generic function that updates a substitution as above to include the
    mapping for a single item in a theory. 
*)
let addToSubst sub whereami = function
    TermSpec ( nm   , _ ) -> addTermToSubst  sub nm    whereami
  | SetSpec  ( stnm , _, _ ) -> addSetToSubst   sub stnm  whereami
  | ModelSpec( mdlnm, _ ) -> addModelToSubst sub mdlnm whereami
  | OtherSpec             -> sub    (** Parts never referenced in a theory *)


(**  
    The key idea for lookup of long-names/module projections
    is to maintain two values as we go along:  
    (1) where we are in reference to the top level (a model path)
    (2) a substitution mapping all theory-component names in scope to the
        paths that would be used to access these values from
        the top-level.  So, e.g., if we had

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

    and assuming we're looking for M.N.x, by the time we
    get to x the substitution (2) contains
      s -> s
      t -> M.t
      u -> M.N.u
    and the "where am I" (1) would be M.N.

    The naming convention is that the primed functions take a list of
    (theory_summary) items (and in some cases an initial
    substitution), while the unprimed functions take the whole
    context and no substitution, and so should only be invoked on
    the "top-level" context.

    Also, "peek" functions never raise exceptions; they can be called
    whether or not the thing being searched for exists.
*)


(** peekSet' : Syntax.subst -> items -> model -> set_name -> kind option

    Given the items from a context and a desired set name, determine
    whether a set of that name exists, and if so, what it's kind is..

    An initial substitution is passed in.  This is updated (using the
    list of model_names, to tell us what model we are inside) as we enter
    the scope of more module components, and finally applied to the
    type being found (so that the type makes sense outside the enclosing 
    modules).

 *)
let rec peekSet' subst0 items whereami desired_stnm = 
  let rec loop substitution = function
      [] -> None
    | SetSpec (stnm, knd, sopt) :: rest -> 
	if stnm = desired_stnm then
	  Some (substKind substitution knd)
	else
	  loop (addSetToSubst substitution stnm whereami) rest
    | spc :: rest -> loop (addToSubst substitution whereami spc) rest
  in loop subst0 items

(** peekSet: cntxt -> set_name -> kind option 
  *)
let peekSet cntxt desired_stnm = 
  peekSet' emptysubst cntxt.items None desired_stnm


(** peekTydef' : Syntax.subst -> items -> model -> set_name -> set option

    Given the items from a context and a desired set name, determine
    whether a set of that name exists *with* a definition.

    An initial substitution is passed in.  This is updated (using the
    list of model_names, to tell us what model we are inside) as we enter
    the scope of more module components, and finally applied to the
    type being found (so that the type makes sense outside the enclosing 
    modules).

 *)
let rec peekTydef' subst0 items whereami desired_stnm = 
  let rec loop substitution = function
      [] -> None
    | SetSpec (stnm, _, sopt) :: rest -> 
	if stnm = desired_stnm then
	  substSetOption substitution sopt
	else
	  loop (addSetToSubst substitution stnm whereami) rest
    | spc :: rest -> loop (addToSubst substitution whereami spc) rest
  in loop subst0 items

(** peekTydef: cntxt -> set_name -> set option 
  *)
let peekTydef cntxt desired_stnm = 
  peekTydef' emptysubst cntxt.items None desired_stnm


(* peekTheoryof' : Syntax.subst -> items -> model_name list -> model_name 
                         -> (theory_summary * Syntax.subst) option

    Given the items from a context and a desired model_name, find the
    corresponding theory for that model in that context; returns None
    if the model doesn't exist.

    An initial substitution subst0 is passed in.  This is updated
    (using the list of model_names, to tell us what model we were
    searching to find these items came from) as we enter the scope of
    more module components, and finally applied to the theory being
    found (so that it makes sense outside the enclosing modules).

    Rather than apply the substitution to the returned list of
    specs (describing the model's contents), we simply return
    the specs and the substitution separately.  If we go on
    to search inside the model, we can then pass in this
    substitution for the subst0 parameter.
*)
let rec peekTheoryof' subst0 cntxt whereami desired_mdlnm = 
  let rec loop sub = function
      [] -> None
    | ModelSpec (mdlnm, summary) :: rest ->
        if mdlnm = desired_mdlnm then
          Some (summary, sub)
        else
          loop (addModelToSubst sub mdlnm whereami) rest
    | spc :: rest -> loop (addToSubst sub whereami spc) rest
  in loop subst0 cntxt

(** peekTheoryof : cntxt -> model_name
                         -> (theory_summary * Syntax.subst) option
 *)
let peekTheoryof cntxt desired_mdlnm = 
  peekTheoryof' emptysubst cntxt.items None desired_mdlnm


(** peekTypeof' : Syntax.subst -> items -> model_name list -> name 
                                                                 -> set option

    Given the items from a context and a name, determine the set
    containing the constant of that name, or None if no such
    constant exists.

    An initial substitution subst0 is passed in.  This is updated
    (using the list of model_names, to tell us what model we are
    inside) as we enter the scope of more module components, and
    finally applied to the type being found (so that the type makes
    sense outside the enclosing modules).
 *)
let rec peekTypeof' subst0 items whereami desired_nm = 
  let rec loop substitution = function
      [] -> None
    | TermSpec(nm, set) :: rest ->
	if nm = desired_nm then 
	   Some (substSet substitution set)
        else 
	  (loop (addTermToSubst substitution nm whereami) rest)
    | spc :: rest -> (loop (addToSubst substitution whereami spc) rest)
  in (loop subst0 items)

(** peekTypeof : context -> name -> set option
 *)
let peekTypeof cntxt desired_nm = 
  peekTypeof' emptysubst cntxt.items None desired_nm

(*****************************)
(** {3 Insertion Functions} **)
(*****************************)

(** Takes the context and adds a new model of the given name, with the
  given theory summary (represented as a list of theory_summary_item_item's *)
let insertModel cntxt mdlnm summary = 
  (match peekTheoryof cntxt mdlnm with
       None -> {cntxt with items = ModelSpec ( mdlnm, summary )
                                     :: cntxt.items }
     | _ -> tyGenericError ("Shadowing of model name: " ^  mdlnm))


(** Takes the context and adds an abstract set of the given name *)
let insertSet   cntxt stnm knd = 
  (match (peekSet cntxt stnm) with
      Some _ -> tyGenericError ("Shadowing of set name: " ^  stnm)
    | None   -> { cntxt with items = SetSpec(stnm, knd, None) :: cntxt.items } )
  
(** Takes the context and adds a new set of the given name, with the
  given set as its definition *)
let insertTydef cntxt stnm knd st =
  (match (peekSet cntxt stnm) with
      Some _ -> tyGenericError ("Shadowing of set name: " ^  stnm)
    | None -> {cntxt with items = SetSpec(stnm, knd, Some st) :: cntxt.items } )

(** Takes the context and adds a new term variable of the given name
  in the given set *)
let insertVar  cntxt nm st = 
  (match peekTypeof cntxt nm with
       None -> {cntxt with items = TermSpec(nm,st) :: cntxt.items }
     | _ -> tyGenericError ("Shadowing of name: " ^  string_of_name nm))

(** Takes the context and adds a new theory definition, with the
  given summary *)
let insertTheory cntxt thrynm summary =
  (match peekTheory cntxt thrynm with
       None -> { cntxt with theories = StringMap.add thrynm summary 
	                                             cntxt.theories }
     | _ -> tyGenericError ("Shadowing of theory name: " ^  thrynm) )

(** Takes the context and a list of strings and remembers these names
  as implicitly ranging over the given set, unless otherwise explicitly
  specified *)
let insertImplicits cntxt (namestrings : string list) (st : set) = 
  let rec loop = (* Add string/st pairs to the implicits mapping *)
    function 
      [] -> cntxt.implicits
    | strng::strngs -> StringMap.add strng st (loop strngs)
  in
    {cntxt with implicits = loop namestrings}

(**********************************)
(** {2 Set Comparison Operations} *)
(**********************************)

(** We put the annotateModel function here because it's
  used by hnfSet *)

(** Given a context and a model, returns 
     (a) the annotated model [currently this never changes, since
         models are just paths, with no place for sets to be inferred.]
     (b) A summary of the theory of the model 
     (c) A substitution that must be applied to (c) in
         order for it to be well-formed at top-level
*)
let rec annotateModel cntxt = function
    ModelName mdlnm ->
     (match (peekTheoryof cntxt mdlnm) with
	None                  -> tyGenericError ("Unknown Model " ^ mdlnm)
     |  Some (summary, subst) -> (ModelName mdlnm, summary, subst))

  | ModelProj (mdl, lbl) as main_mdl ->
      let ((mdl' as whereami), summary, subst) = annotateModel cntxt mdl
      in (match summary with
            Summary_Struct(_, items) ->
             (match (peekTheoryof' subst items (Some whereami) lbl) with
	       None -> tyGenericError ("Unknown Model" ^ 
				       string_of_model main_mdl)
	     | Some (summary'', subst'') ->
		 (ModelProj(mdl',lbl), summary'', subst''))
          | _ -> tyGenericError 
		   ( "Projection from parameterized model in\n  " ^
		      string_of_model main_mdl ) )

  | ModelApp (mdl1, mdl2) as main_mdl ->
     let    (mdl1', summary1, sub1) = annotateModel cntxt mdl1
     in let (mdl2', summary2, sub2) = annotateModel cntxt mdl2
     in match ( substSummary sub1 summary1 ) with
          Summary_Functor ( ( mdlnm, thry11 ), summary12 ) ->  
            if ( etaEquivTheories thry11 
		    (substTheory sub2 ( summaryToTheory summary2 ) ) ) then
	       let    newapp     = ModelApp (mdl1', mdl2')
               in let sub        = insertModelvar emptysubst mdlnm mdl2'
               in ( newapp, summary12, sub )
	    else
	      tyGenericError 
		( "Incompatible model argument in\n  " ^ 
		  string_of_model main_mdl ^ "\nExpected: " ^
		  string_of_theory thry11 ^ "\nFound   : " ^ 
		  string_of_theory ( substTheory sub2 ( summaryToTheory summary2 ) ) )

        | _ -> tyGenericError 
	         ( "Application of non-parameterized model in\n  " ^ 
		   string_of_model main_mdl )

(** Expand out any top-level definitions for a (well-formed) set 
  *)
let rec hnfSet cntxt = function
    Set_name ( None, stnm ) ->
      (match (peekTydef cntxt stnm) with
        Some st -> hnfSet cntxt st
      | None -> Set_name ( None, stnm ) )

  | Set_name ( Some mdl, stnm ) -> 
      let (whereami, summary, subst) = annotateModel cntxt mdl
      in ( match summary with
	     Summary_Struct ( _, items ) -> 
	       ( match (peekTydef' subst items (Some whereami) stnm) with
	           None    -> Set_name ( Some mdl, stnm ) 
	         | Some st -> hnfSet cntxt st )
           | _ -> raise Impossible )

  | st -> st


let rec freshNameSubsts' nm1 nm2 subst1 subst2 = 
  let freshname = N(Syntax.freshNameString(), Word)
  in let trm = Var(None, freshname)
  in let sub1 = insertTermvar subst1 nm1 trm
  in let sub2 = insertTermvar subst2 nm2 trm
  in (freshname, sub1, sub2)
    
let freshNameSubsts nm1 nm2 = 
  freshNameSubsts' nm1 nm2 emptysubst emptysubst


(** eqSet': bool -> cntxt -> set -> set -> bool
      Precondition:  The two sets are fully-annotated
                     and proper (first-order) sets.
      Postcondition:  Whether the two sets are equal (or implicitly-
                      convertible, if the boolean is true) in the 
                      given context.  Equality defined as alpha-equivalence,
                      commutivity of sums, and definition expansion.

                      Implicit convertability just involves subtyping
                      on sum types in positive positions.  It is here
                      merely to address defects in type inference, since
                      we don't want to have to annotate each injection
                      with the corresponding sum type.
  *)
let rec eqSet' do_subset cntxt = 
   let rec cmp (s1 : set) (s2 : set) = 
      (** Short circuting for (we hope) the common case *)
      (s1 = s2)
      (** Head-normalize the two sets *)
      || let    s1' = hnfSet cntxt s1
         in let s2' = hnfSet cntxt s2

         in (s1' = s2') 
            || (match (s1',s2') with
                 ( Empty, Empty ) -> true       (** Redundant *)

               | ( Unit, Unit )   -> true       (** Redundant *) 

               | ( Set_name (mdlopt1, nm1), Set_name (mdlopt2, nm2) )  -> 
                    (** Neither has a definition *)
                    eqModelOpt cntxt mdlopt1 mdlopt2 
                    && (nm1 = nm2) 

 	       | ( Product ss1, Product ss2 ) -> 
                    cmpProducts (ss1,ss2)

               | ( Sum lsos1, Sum lsos2 )     -> 
	            subSum do_subset cntxt (lsos1, lsos2) 
                    && (do_subset || subSum false cntxt (lsos2, lsos1))


               | ( Exp( None, st3, st4 ), Exp( None, st5, st6 ) )   -> 
                    (* The common case, so we treat it specially *)
		    (*** XXX.  Domains are not compared contravariantly.
			 Is this on purpose? *)
                    eqSet cntxt st5 st3 
                    && cmp st4 st6

               | ( Exp( Some nm1, st3, st4 ), Exp ( Some nm2, st5, st6 ) ) ->
		   let (_, sub1, sub2) = freshNameSubsts nm1 nm2
	           in let st4' = substSet sub1 st4
	           in let st6' = substSet sub2 st6
	           in 
		    (*** XXX.  Domains are not compared contravariantly.
			 Is this on purpose? *)
                    eqSet cntxt st5 st3 
                    && cmp st4' st6'

               | ( Exp( None, st3, st4), _ ) ->
		   (* If only one arrow has a variable, we add an unused
                      variable to the other.  They could still be equal,
                      if the one with the variable isn't really dependent. 

                      Even if one Exp has no variable and the other
                      "appears" to use its variable they might still
                      be equal, since that variable use' might disappear
                      once we expand substitutions and/or beta-reduce.
                   *)
		   let freshname =  N(Syntax.freshNameString(), Word)
		   in
		     cmp ( Exp (Some freshname, st3, st4) ) s2'

               | ( _, Exp( None, st3, st4) ) ->
		   let freshname =  N(Syntax.freshNameString(), Word)
		   in
		     cmp s1' ( Exp (Some freshname, st3, st4) )

	       | ( Subset( (nm1,_) as b1, p1 ), Subset( (nm2,_) as b2, p2 ) )->
                    cmpbnd(b1,b2)
	            (** Alpha-vary the propositions so that they're using the
                        same (fresh) variable name *)
                    && let (_, sub1, sub2) = freshNameSubsts nm1 nm2
	               in let p1' = subst sub1 p1
	               in let p2' = subst sub2 p2
	               in 
                          eqProp cntxt p1' p2'  

               | ( Quotient ( st3, eqvlnce3 ), Quotient ( st4, eqvlnce4 ) ) -> 
                    (** Quotient is invariant *)
                    eqSet cntxt st3 st4  
                    && eqTerm cntxt eqvlnce3 eqvlnce4

               | (SetApp (st3, trm3), SetApp (st4, trm4) ) ->
		    eqSet cntxt st3 st4
		    && eqTerm cntxt trm3 trm4

               | ( Rz st3, Rz st4 ) -> 
                    (** RZ seems like it should be invariant.  *)
		    (** XXX Is it? *)
                    eqSet cntxt st3 st4  

               | ( ( Prop | StableProp | EquivProp ), Prop ) -> 
                   true

               | ( ( StableProp | EquivProp ), StableProp ) -> 
		   true

	       | ( EquivProp, EquivProp ) ->
		   true

               | (_,_) -> false )

     and cmpbnd = function
	  (* Since we're not verifying equivalence of propositions,
	     we don't have to worry about the bound variable *)
          ((_, None),    (_,None)   ) -> true
        | ((_, Some s1), (_,Some s2)) -> cmp s1 s2
        | ( _,           _          ) -> false

      and cmpProducts' subst1 subst2 = function
          ( [] , [] ) -> true

	| ( (None, s1) :: s1s, (None, s2) :: s2s) -> 
	    (* The common case is non-dependent. *)
	    (cmp s1 s2 && cmpProducts' subst1 subst2 (s1s,s2s) )

	| ( (Some nm1, s1) :: s1s, (Some nm2, s2) :: s2s) -> 
	    let (_, subst1', subst2') = freshNameSubsts' nm1 nm2 subst1 subst2
	    in let s1' = substSet subst1 s1
	    in let s2' = substSet subst2 s2
	    in  (cmp s1' s2' && cmpProducts' subst1' subst2' (s1s,s2s) )
 
        | ( s1s, (None, s2) :: s2s ) ->
	    let freshname = N(Syntax.freshNameString(), Word)
	    in cmpProducts' subst1 subst2 
	          ( s1s, (Some freshname, s2) :: s2s )
	      

        | ( (None, s1) :: s1s, s2s ) ->
	    let freshname = N(Syntax.freshNameString(), Word)
	    in cmpProducts' subst1 subst2
	          ( (Some freshname, s1) :: s1s, s2s )

        | (_,_) -> false

   and cmpProducts lst = cmpProducts' emptysubst emptysubst lst

     and subSum do_subset cntxt = function
          ( [], _ ) -> true
       | ((l1,None   )::s1s, s2s) ->
	     (match (List.assoc l1 s2s) with
		 None -> subSum do_subset cntxt (s1s, s2s)
	       | _ -> false )
       | ((l1,Some s1)::s1s, s2s) -> 
	     (match (List.assoc l1 s2s) with
		 Some s2 -> eqSet' do_subset cntxt s1 s2  && 
                            subSum do_subset cntxt (s1s,s2s)
	       |  _ -> false )

      in cmp


and eqProp ctx prp1 prp2 = 
  (* XXX: Should allow alpha-equiv and set-equiv *)
  (print_string "WARNING: Fix eqProp!\n";
   prp1 = prp2)  

and eqTerm ctx trm1 trm2 = 
  (* XXX: Should allow alpha-equiv and set-equiv and beta *)
  (print_string "WARNING: Fix eqTerm!\n";
   trm1 = trm2)  


and eqModelOpt ctx mdlopt1 mdlopt2 = (mdlopt1 = mdlopt2)

and eqSet cntxt st1 st2 = eqSet' false cntxt st1 st2

and subSet cntxt st1 st2 = eqSet' true cntxt st1 st2

(* coerce: cntxt -> term -> set -> set -> trm option
     coerce trm st1 st2 coerces trm from the set st1 to the set st2
       using subin and subout.
     Preconditions: trm is in st1 and all arguments are fully-annotated.
     Returns:  None       if trm cannot be turned into a value in set st2.
               Some trm'  if we can obtain the term trm'
*)
let rec coerce cntxt trm st1 st2 = 
   if (subSet cntxt st1 st2) then
      (** Short circuting, since the identity coercion is (we hope)
          the common case *)
      Some trm
   else
      let    st1' = hnfSet cntxt st1
      in let st2' = hnfSet cntxt st2
   
      in match (trm, st1', st2') with
	| ( _, Subset ( ( _, Some st1'1 ) , _ ),
               Subset ( ( _, Some st2'1 ) , _ ) ) -> 

	    (** Try an implicit out-of-subset conversion *)
           (match ( coerce cntxt ( Subout(trm,st1) ) st1'1 st2 ) with
              Some trm' -> Some trm'
            | None -> (** That didn't work, so try an implicit 
                          into-subset conversion *)
                      (match (coerce cntxt trm st1 st2'1) with
                        Some trm' -> Some ( Subin ( trm', st2 ) )
                      | None      -> None ) )

        | ( _, Subset( ( _, Some st1'1 ), _ ), _ ) -> 
	    (** Try an implicit out-of-subset conversion *)
            coerce cntxt ( Subout(trm,st2) ) st1'1 st2 

        | ( _, _, Subset( ( _, Some st2'1 ), _ ) ) -> 
	    (** Try an implicit into-subset conversion *)
            ( match (coerce cntxt trm st1 st2'1) with
                Some trm' -> Some ( Subin ( trm', st2 ))
              | None      -> None )

        | ( Tuple trms, Product sts1, Product sts2 ) ->
            let rec loop subst2 = function 
                ([], [], []) -> Some []
              | ([], _, _)   -> None
              | (trm::trms, (None, st1)::sts1, (None, st2)::sts2) ->
		  let st2' = substSet subst2 st2
                  in (match (coerce cntxt trm st1 st2', 
			 loop subst2 (trms,sts1,sts2)) with
                     (Some trm', Some trms') -> Some (trm'::trms')
                   | _ -> None )
              | (trm::trms, (None, st1)::sts1, (Some nm2, st2)::sts2) ->
		  let st2' = substSet subst2 st2
		  in let subst2' = insertTermvar subst2 nm2 trm
                  in (match (coerce cntxt trm st1 st2', 
			 loop subst2' (trms,sts1,sts2)) with
                     (Some trm', Some trms') -> Some (trm'::trms')
                   | _ -> None )

              | (trm::trms, (Some _, _)::_, _) -> 
		  (* This case shouldn't ever arise; tuples naturally
		     yield non-dependent product types.  But just in case, ...*)
		  (print_string 
		      "WARNING: coerce: dependent->? case for products shouldn't arise!\n";
		   None)
	      | _ -> raise Impossible
            in (match (loop emptysubst (trms, sts1, sts2)) with
                  Some trms' -> Some (Tuple trms')
                | None -> None)

        | _ -> None

let rec coerceFromSubset cntxt trm st = 
   match (hnfSet cntxt st) with
      Subset( ( _, Some st1 ), _ ) -> 
         coerceFromSubset cntxt (Subout(trm, st)) st1
    | st' -> (trm, st')

(** Computes the join of the two sets s1 and s2.
   Unlike subtyping, join does *not* do implicit conversions
   for subsets.  *)
let joinSet cntxt s1 s2 = 
   if (s1 = s2) then
      (* Short circut *)
      s1
   else
      let    s1' = hnfSet cntxt s1
      in let s2' = hnfSet cntxt s2

      in let rec joinSums = function 
	  ([], s2s) -> s2s
        | ((l1,None)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      (match (List.assoc l1 s2s) with
	          None -> joinSums(s1s, s2s)
		| Some _ -> tyGenericError ("Disagreement as to whether " ^ l1 ^
                         " stands alone or tags a value"))
	    else (l1,None) :: joinSums(s1s, s2s))
        | ((l1,Some s1)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      (match (List.assoc l1 s2s) with
		  Some s2 -> 
		    if eqSet cntxt s1 s2 then
		      joinSums(s1s, s2s)
		    else
		      tyGenericError ("Disagreement on what type of value " ^ 
                                        l1 ^ " should tag")
		| None -> tyGenericError("Disagreement as to whether " ^ l1 ^
					 " tags a value or stands alone"))
	    else (l1,Some s1) :: joinSums(s1s, s2s))


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



let rec eqKind' do_subkind cntxt k1 k2 = 
  (** Short circuting for (we hope) the common case *)
  (k1 = k2)
  || (match (k1, k2) with
      ( KindArrow( None, st1, k3 ), KindArrow( None, st2, k4 ) )   -> 
	(* Contravariant domain *)
        eqSet' do_subkind cntxt st2 st1 
        && eqKind' do_subkind cntxt k3 k4

    | ( KindArrow( Some nm1, st1, k3 ), KindArrow ( Some nm2, st2, k4 ) ) ->
	let (_, sub1, sub2) = freshNameSubsts nm1 nm2
	in let k3' = substKind sub1 k3
	in let k4' = substKind sub2 k4
	in 
	     (* Contravariant domain *)
             eqSet' do_subkind cntxt st2 st1 
             && eqKind' do_subkind cntxt k3' k4'
	       
    | ( KindArrow( None, st2, k4), _ ) ->
	(* If only one arrow has a variable, we add an unused
           variable to the other.  They could still be equal,
           if the one with the variable isn't really dependent. 

           Even if one KindArrow has no variable and the other
           "appears" to use its variable they might still
           be equal, since that variable's use might disappear
           once we expand substitutions and/or beta-reduce.
        *)
	let freshname =  N(Syntax.freshNameString(), Word)
	in
	  eqKind' do_subkind cntxt ( KindArrow (Some freshname, st2, k4) ) k2
	    
    | ( _, KindArrow( None, st2, k4) ) ->
	let freshname =  N(Syntax.freshNameString(), Word)
	in
	  eqKind' do_subkind cntxt k1 ( KindArrow (Some freshname, st2, k4) ))

let subKind cntxt k1 k2 = eqKind' true  cntxt k1 k2
let eqKind  cntxt k1 k2 = eqKind' false cntxt k1 k2



(*****************************************)
(** {2 Typechecking/Type Reconstruction} *)
(*****************************************)


(** Given a context, a name, and a type, check this is the type of 
    some binary relation on some set and return the same type marked as an
    equivalence relation. 

    Raises an error if the type is not for a binary relation on a set. *)
let rec makeEquivalence cntxt nm = function
    Exp (_, Product [(None, s1); (_, s2)], (Prop|StableProp|EquivProp)) ->
      if eqSet cntxt s1 s2 then
	(* It's safe to ignore any bound variable in this function type; 
           if the codomain is xxxProp, then there can be no true dependency *)
	Exp (None, Product [(None, s1); (None, s2)], EquivProp)
      else
	tyGenericError ("Ill-typed equivalence " ^ (string_of_name nm))

  | Exp (_, Product [(Some nm1, s1); (_, s2)], (Prop|StableProp|EquivProp)) ->
      raise Unimplemented

  | Exp (None, s1, Exp (_, s2, (Prop|StableProp|EquivProp))) ->
      if eqSet cntxt s1 s2 then
	Exp (None, s1, Exp (None, s2, EquivProp))
      else
	tyGenericError ("Ill-typed equivalence " ^ (string_of_name nm))

  | Exp (Some nm1, s1, Exp (_, s2, (Prop|StableProp|EquivProp))) ->
      raise Unimplemented

  | st -> tyGenericError ("Cannot interpret " ^
			     (string_of_set st) ^
			     "as describing an equivalence relation" )

let checkNonParameterizedKind st in_st = function
    (KindArrow _) as k -> 
      tyGenericError ("The set " ^ (string_of_set st) ^
			 " in " ^ (string_of_set in_st) ^
			 " must not be parameterized, but has kind" ^
			 (string_of_kind k))
  | _ -> ()




(** Given a context and a term, determines whether the term is a
    (stable) equivalence relation.  If so, returns the domain set
    for this relation, and (for convenience) the annotated form
    of the term.
*)
let rec equivalenceAt cntxt trm =
(*  (match (annotateTerm cntxt trm : term * set) with
  
      (trm', Exp (None, u, Exp (None, v, EquivProp))) |
          (trm', Exp (_, Product [u; v], EquivProp)) ->

      (trm', u as v) ->
	    if (eqSet cntxt u v) then
              Some (u, trm')
	    else
              None
    | (_, Exp (Some _, _, Exp (_, _, EquivProp))) -> raise Unimplemented
    | _ -> None )
*)
  (* XXX *)
  None
      
    
(** Given a contxt and a set, return the annotated version of the set.

    Raises an informitive error if the set is not well-formed.
*)
and annotateSet cntxt = 
  (let rec ann orig_set = 
    match orig_set with
        Product nss -> annotateProduct cntxt nss

      | Sum lsos   -> annotateSum cntxt lsos

      | (Exp _) -> annotateExp cntxt orig_set

      | Subset(bnd, p) -> 
          let (bnd',cntxt') = annotateBinding cntxt bnd
          in let (p',_) = annotateProp cntxt' p
          in ( Subset(bnd', p'), KindSet )

      | SetApp(st, trm) ->
          let (st', k_st') = ann st
          in let (trm', st_trm') = annotateTerm cntxt trm 
          in (match k_st' with
              KindArrow( nmopt, st_k_st', k_k_st') ->
                if (subSet cntxt st_trm' st_k_st') then
                  let mySubst = 
		    (match nmopt with
			Some nm' -> insertTermvar emptysubst nm' trm'
		      | None -> emptysubst)
		  in (SetApp(st', trm'),
		      substKind mySubst k_k_st')
                else
                  tyGenericError
                    ("Term " ^ (string_of_term trm) ^ 
                        " is not a valid argument to " ^
                        (string_of_set st))
            | _ -> tyGenericError
                ((string_of_set st) ^ 
                    " does not take arguments; not even" ^
                    (string_of_term trm)) )

      | Quotient(st, trm) ->
	  let st' = annotateProperSet cntxt st (string_of_set orig_set) in
	    (match equivalenceAt cntxt trm with
		None -> tyGenericError 
		  ("Cannot quotient by the (non- stable equivalence) relation: " ^ 
		      string_of_term trm)
	      | Some (domain_st, trm') -> 
		  if (eqSet cntxt st' domain_st) then
		    (Quotient(st', trm'), KindSet)
		  else
		    tyGenericError
		      ("Wrong domain for equivalence relation in " ^
			  string_of_set (Quotient(st,trm))))
	      
      | (Rz st) -> ( Rz(annotateProperSet cntxt st (string_of_set orig_set)), KindSet )
	  
      | Set_name (None, stnm) ->
	  (match (peekSet cntxt stnm) with
	      Some knd -> (orig_set, knd)
	    | None     -> tyGenericError ("Set not found: " ^ stnm))
	    
      | Set_name (Some mdl, stnm) -> 
	  let (mdl', summary, _) = annotateModel cntxt mdl
	  in (match summary with
	      Summary_Struct(_, items) -> 
		(match (peekSet' emptysubst items (Some mdl') stnm) with
		    Some knd -> (Set_name(Some mdl', stnm), knd)
		  | None -> tyGenericError ( "Unknown component " ^ 
					       string_of_set orig_set ))
	    | _ -> tyGenericError 
                "Set projection from parameterized model")

      | Prop -> (Prop, KindProp Unstable)
      | StableProp -> (StableProp, KindProp Stable)
      | EquivProp -> (EquivProp, KindProp Equivalence)
      | (Bool | Unit | Empty) as st -> (st, KindSet)
 
      | SetLambda _ -> raise Unimplemented

      | Set -> raise Impossible

    in
     ann)

(** Same as annotateSet, but applies to set options *)
and annotateSetOpt cntxt = function
    Some s -> Some (annotateSet cntxt s)
  | None -> None

and annotateProperSet cntxt s in_string =
  let (s', k) = annotateSet cntxt s
  in (match k with
      KindSet -> s'
    | _ -> notProperSetError s in_string)

and annotateProduct cntxt nss = 
  (let rec ann cntxt = function
      [] -> []
    | (nopt, s) :: rest ->     
        let s' = annotateProperSet cntxt s (string_of_set (Product nss))
        in let cntxt' = match nopt with
            None -> cntxt
          | Some n -> insertVar cntxt n s'
        in (nopt, s') :: ann cntxt' rest
    in    
     (Product (ann cntxt nss), KindSet) )

and annotateSum cntxt lsos =
  (let rec ann lbls_used = function
      [] -> []

    | (l, sopt) :: rest ->
        if (not (List.mem l lbls_used)) then
          (match sopt with
              None -> (l, sopt) 
            | Some s -> 
		let s' = annotateProperSet cntxt s (string_of_set (Sum lsos))
		in (l, Some s')
          ) :: 
            ann (l :: lbls_used) rest
        else
          tyGenericError
            ("Duplicate label" ^
                (string_of_label l) ^
                "in the sum" ^
                (string_of_set (Sum lsos)))
            
    in ( Sum (ann [] lsos), KindSet ) )

and annotateExp cntxt = function
    (Exp(nopt,s1,s2)) as s ->
      let  s1' = annotateProperSet cntxt s1 (string_of_set s)
      in let cntxt' = (match nopt with
          None -> cntxt
        | Some n -> insertVar cntxt n s1')
      in let (s2',knd) = annotateSet cntxt' s2
      in let _ = checkNonParameterizedKind s2 s knd
      in ( Exp(nopt,s1',s2'), knd )
  | _ -> raise Impossible

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
        in let ty3 = try (joinSet cntxt ty1 ty2) with
            TypeError -> tyGenericError 
              ("Cannot compare " ^ string_of_term t1 ^ " and "
                ^ string_of_term t2 ^ " for equality")
              
        in
             Equal(Some ty3, t1', t2'), Stable

    | (Equal (Some s, t1, t2)) as t->
        let    ty = annotateProperSet cntxt s (string_of_term t)
        in let (t1', ty1) = annotateTerm cntxt t1
        in let (t2', ty2) = annotateTerm cntxt t2
        in if (subSet cntxt ty1 ty) && (subSet cntxt ty2 ty) then
            Equal (Some ty, t1', t2'), Stable
          else
            tyGenericError 
              ("Cannot compare " ^ string_of_term t1 ^ " and "
		^ string_of_term t2 ^ " for equality in set " ^
		string_of_set s)

    | Forall(bnd, p) ->
        let (bnd',cntxt') = annotateBinding cntxt bnd in
        let (p', stb) = annotateProp cntxt' p
        in
          Forall(bnd', p'), stb

    | Exists(bnd, p) ->
        let (bnd',cntxt') = annotateBinding cntxt bnd
        in
          Exists (bnd', fst (annotateProp cntxt' p)), Unstable

    | Unique(bnd, p) ->
        let (bnd',cntxt') = annotateBinding cntxt bnd
        in
          Unique (bnd', fst (annotateProp cntxt' p)), Unstable

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
	  Some s -> annotateProperSet cntxt s (string_of_bnd (x,sopt))
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
          Some s -> annotateProperSet cntxt s (string_of_bnd (x, sopt))
        | None   -> (match (peekImplicit cntxt x) with
              Some s -> s
            | None -> default_st))
      in let cntxt' = insertVar cntxt x s'
      in ((x, Some s'), cntxt')

and annotateBindingWithCheckedDefault cntxt default_st = function
    (x, None) -> 
      annotateBindingWithDefault cntxt default_st (x, None)

  | (x, Some s2) -> 
      let s2' = annotateProperSet cntxt s2 (string_of_bnd (x, Some s2)) in
	if (subSet cntxt default_st s2') then
          let cntxt' = insertVar cntxt x s2' in
            ((x, Some s2'), cntxt')
	else
          tyGenericError ( "Annotated Binding " ^ 
			     string_of_bnd (x, Some s2) ^
			     " doesn't match inferred set " ^ 
			     string_of_set default_st )
            
            
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
      Var (None, nm) as orig_trm -> 
	(match (peekTypeof cntxt nm) with
            Some ty -> (orig_trm, ty)
          | None -> tyUnboundError orig_trm)

    | Var (Some mdl, nm) as orig_trm -> 
	let (mdl' as whereami, summary, subst) = annotateModel cntxt mdl
	in ( match summary with
            Summary_Struct ( _ , items) ->
              (match (peekTypeof' subst items (Some whereami) nm)with
		  None -> tyGenericError ("Unknown component " ^
					     string_of_term orig_trm)
		| Some st -> ( Var ( Some mdl', nm ), st ) )
          | _ -> tyGenericError 
              ( "Term projection from parameterized model in:\n  " ^ 
		  string_of_term orig_trm ) )

    | Constraint(t,s) as orig_trm ->
        let (t',ty) = ann t  in
        let s'      = annotateProperSet cntxt s (string_of_term orig_trm) in
          begin
	    match (coerce cntxt t' ty s') with
		Some trm'' -> (Constraint(trm'',s'), s')
              | None       -> tyMismatchError t s' ty 
	  end
	    
    | Star -> (Star, Unit)

    | Tuple ts ->
        let (ts', tys) = List.split (List.map ann ts)
        in let noptss = List.map (function s -> (None, s)) tys
        in (Tuple ts', Product noptss)

    | Proj (n, t) -> 
        (* Projections are indexed starting with zero *)
        let    (trm', tuplety) = ann t
        in let (trm'', hnfty) = coerceFromSubset cntxt trm' tuplety
        in let tys = (match hnfty with
            Product tys -> tys
          | _ -> tyWrongSortError t " tuple" tuplety)
        in let rec loop i subst = function
	    [] -> raise Impossible
	  | (nopt, ty) :: tys ->
	      if (i == n) then
		substSet subst ty
	      else
		let subst' = 
		  (match nopt with
		      None -> subst
		    | Some nm -> insertTermvar subst nm (Proj(i,trm'')))
		in
		  loop (i+1) subst' tys
	     
	in if (n >= 0 && n < List.length tys) then
            ((Proj(n,trm''), loop 0 emptysubst tys))
          else
            tyGenericError ("Projection " ^ string_of_int n ^ 
			       " out of bounds")
    | App (t1, t2) ->
        let (t1', ty1) = ann t1 in
        let (t2', ty2) = ann t2 in
        let (t1'',nopt,ty3,ty4) = (match (coerceFromSubset cntxt t1' ty1) with
            (t1'', Exp(nopt,ty3,ty4)) -> (t1'',nopt,ty3,ty4)
          | _ -> tyWrongSortError t1 " function" ty1)
        in
          ( match (coerce cntxt t2' ty2 ty3) with
              Some trm2'' ->  
		let resultTy = 
		  (match nopt with
		      None -> ty4
		    | Some nm -> 
			(* Remove dependency *)
			substSet (insertTermvar emptysubst nm trm2'') ty4 )
		in 
		  (App (t1'', trm2''), resultTy)
            | None        ->  tyMismatchError t2 ty3 ty2 )
            
    | Inj (l, None) ->
	(Inj (l, None), Sum [(l, None)])

    | Inj(l, Some e) -> 
        let (e', ty)= ann e
        in (Inj(l, Some e'), Sum [(l, Some ty)])

    | Case(e,arms) -> 
	let (e', ty) = ann e
        in let (e'', hnfty) = coerceFromSubset cntxt e' ty
          
	in let annArm = function
            (l, None, e) -> 
              let (e', ty2) = ann e
              in ((l, None, e'), (l, None), ty2)
          | (l, Some bnd, e) ->
              let ((_,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
              in let (e', ty2) = annotateTerm cntxt' e
              in ((l, Some bnd', e'), (l, Some ty1), ty2)
        in let getArm     = fun (arm,_,_) -> arm
        in let getSumPart = fun (_,sp,_) -> sp
        in let getReturn  = fun (_,_,ret) -> ret
	in let l       = List.map annArm arms
	in let newcase = Case(e'', List.map getArm l)
        in let sum_set = Sum (List.map getSumPart l)
        in let return_set = joinSets cntxt (List.map getReturn l)
	in
	     if (eqSet cntxt sum_set hnfty) then
               (newcase, return_set)
	     else
               tyCaseError cntxt e ty sum_set
		 
    | Quot(t, r) -> 
	let (t', ty) = ann t in
	  begin
	    match equivalenceAt cntxt r with
		None -> 
		  failwith (string_of_term r ^ " is not a stable equivalence")
              | Some(domain_st, r') ->
		  if eqSet cntxt domain_st ty then
		    (Quot(t',r'), Quotient(ty,r'))
		  else
		    tyGenericError
		      ("Term " ^ string_of_term t ^ " is in " ^
			  string_of_set ty ^ "\nbut " ^ string_of_term r ^
			  " is a relation on " ^ string_of_set domain_st)
	  end
            
    | RzQuot t ->
	let (t', ty) = ann t in
	  (match hnfSet cntxt ty with
              Rz ty' -> RzQuot t', ty'
            | _ -> tyWrongSortError t "n RZ" ty)

    | RzChoose (bnd, t1, t2, body_ty_opt) as orig_term ->
	let (t1', ty1) = ann t1 in
	let ((nm, Some ty), cntxt') = annotateBindingWithCheckedDefault cntxt (Rz ty1) bnd in
	let (t2', ty2) = annotateTerm cntxt' t2 in
	  (begin
	      match hnfSet cntxt ty with
		  Rz ty' ->
		    if eqSet cntxt ty1 ty' then 
		      begin
			(try (ignore(annotateSet cntxt ty2)) with
			    _ -> tyGenericError ("Inferred let[]-body type depends on local " ^ 
						    "defns; maybe add a constraint?") ) ;
			( match body_ty_opt with
			    None -> ()
			  | Some body_ty -> if (eqSet cntxt' (annotateProperSet cntxt body_ty (string_of_term orig_term)) ty2 ) then
                                ()
                            else
                                tyGenericError ("Annotation of body in let[] is " ^ 
						   string_of_set body_ty ^ 
						   " but the body is really " ^
						   string_of_set ty2 ) ) ;
			RzChoose ((nm, Some (Rz ty')), t1', t2', Some ty2)
		      end
		    else
		      failwith "type mismatch in let [...] = "
		| _ -> failwith "type mismatch in let [...] = "
	    end,
	  ty2 )

    | Choose (bnd, r, t1, t2, body_ty_opt) as orig_term ->
        (* let  nm      % r = t1 in t2
           let (nm : s) % r = t1 in t2 
        *)
	let ( t1', typ_of_eqclass ) = ann t1 in
	  begin
            match ( hnfSet cntxt typ_of_eqclass ) with
		Quotient( ty_member, r' ) ->
		  if ( r = r' ) then
		    let ((nm, _) as bnd', cntxt') = 
		      annotateBindingWithCheckedDefault cntxt ty_member bnd in 
		    let ( t2', typ_of_body ) = annotateTerm cntxt' t2  in
		      begin
			( try  ( ignore ( annotateSet cntxt typ_of_body ) ) with
			    _ -> tyGenericError ("Inferred let%-body type " ^ 
						    string_of_set typ_of_body ^ 
						    "\ndepends on local defns; " ^
						    "maybe add a constraint?") ) ;
			( match body_ty_opt with
			    None -> ()
			  | Some body_ty -> if (eqSet cntxt' (annotateProperSet cntxt body_ty (string_of_term orig_term))
						   typ_of_body ) then
                                ()
                            else
                                tyGenericError ("Annotation of body in let% is " ^ 
						   string_of_set body_ty ^ 
						   " but the body is really " ^
						   string_of_set typ_of_body ) ) ;
			(Choose (bnd', r, t1', t2', Some typ_of_body), typ_of_body )
		      end
		  else
		    tyGenericError "Mismatch in let% equivalence relations"
	      | _ -> tyGenericError ("Bound value " ^ (string_of_term t1) ^ 
					"\nin let% inferred as " ^
					(string_of_set typ_of_eqclass) )
	  end
	    
            
    | Let (bnd, t1, t2, None) ->
        let    (t1', ty1) = ann t1
        in let (bnd',cntxt') = annotateBindingWithCheckedDefault cntxt ty1 bnd
        in let (t2', ty2) = annotateTerm cntxt' t2
        in ((try (ignore(annotateSet cntxt ty2)) with
            _ -> tyGenericError ("Inferred let-body type depends on local " ^ 
				    "defns; maybe add a constraint?"));
            (Let(bnd',t1',t2',Some ty2), ty2))

    | Let (bnd, t1, t2, Some st) as orig_term ->
        let    (t1', ty1) = ann t1
        in let (bnd',cntxt') = annotateBindingWithCheckedDefault cntxt ty1 bnd
        in let (t2', ty2) = annotateTerm cntxt' t2
	in let st' = annotateProperSet cntxt st (string_of_term orig_term)
        in if (subSet cntxt' ty2 st') then
            (Let(bnd',t1',t2',Some st'), st')
	  else
            tyGenericError ("Inferred let-body type does not match annotation")

    | Lambda (bnd,t) ->
        let    ((nm,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
        in let (t', ty2) = annotateTerm cntxt' t
	in let resultTy = 
	  if (NameSet.mem nm (fnSet ty2)) then
	    (print_string "INFO: Inferred a dependent Exp\n";
	     Exp(Some nm, ty1, ty2))
	  else
	    Exp(None, ty1, ty2)
        in (Lambda(bnd',t'), resultTy)

    | The (bnd,t) ->
        let    ((_,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
        in let (t', ty2) = annotateTerm cntxt' t
        in (The(bnd',t'), ty1)

    | Subin (t, s) as orig_term ->
	let s' = annotateProperSet cntxt s (string_of_term orig_term) in
	let (t', ty) = annotateTerm cntxt t in
	  (match hnfSet cntxt s' with
              Subset ((_,Some ty'), _) -> 
		if (subSet cntxt ty ty') then
		  (Subin (t', s'), s')
		else
		  tyMismatchError t ty' ty
	    | _ -> tyGenericError "<: with a non-subset-type")

    | Subout (t, s) as orig_term ->
	let s' = annotateProperSet cntxt s (string_of_term orig_term) in
	let (t', ty) = annotateTerm cntxt t in
	  (match hnfSet cntxt ty with
              Subset ((_ ,Some ty'), _) -> 
		if (subSet cntxt ty' s') then
		  (Subout (t', s'), s')
		else
		  tyGenericError("Subset mismatch :<")
	    | _ -> tyGenericError("Subset mismatch :<"))

    | prp -> tyGenericError ("Proposition " ^ 
				string_of_term prp ^ 
				" found where a term was expected")
    in ann)


(* A propositional function, i.e., 0 or more arguments followed by a logical proposition *)

and annotatePropFn cntxt = function
      Lambda (bnd,p) ->
        let    ((nm,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
        in let (p', ty2, pk) = annotatePropFn cntxt' p
	in let resultTy = 
	  if (NameSet.mem nm (fnSet ty2)) then
	    Exp(Some nm, ty1, ty2)
	  else
	    Exp(None, ty1, ty2)
        in (Lambda(bnd',p'), resultTy, pk)
    | p -> 
	let (p', pk) = annotateProp cntxt p
	in (p', mkPropSet pk, pk)
	  

and annotateKind cntxt = function
    (KindSet | KindProp _) as k -> k
  | KindArrow (nopt, st, knd) as k ->
      let st' = annotateProperSet cntxt st (string_of_kind k)
      in let cntxt' = 
	(match nopt with
	    None -> cntxt
	  | Some nm -> insertVar cntxt nm st')
      in let knd' = annotateKind cntxt' knd
      in KindArrow(nopt, st', knd')

and annotateTheoryElem cntxt = function
    Abstract_set(stnm, knd) -> 
      let knd' = annotateKind cntxt knd
      in
	(insertSet cntxt stnm knd', 
	 Abstract_set(stnm, knd'), 
	 SetSpec(stnm, knd', None))

  | Let_set(stnm, None, st) -> 
      let (st',knd) = annotateSet cntxt st
      in (insertTydef cntxt stnm knd st', 
	 Let_set(stnm, Some knd, st'), 
	 SetSpec(stnm, knd, Some st'))

  | Let_set(stnm, Some knd, st) -> 
      let knd' = annotateKind cntxt knd
      in let (st',knd'') = annotateSet cntxt st
      in if (subKind cntxt knd'' knd') then
	  (insertTydef cntxt stnm knd' st', 
	  Let_set(stnm, Some knd', st'), 
	  SetSpec(stnm, knd', Some st'))
	else
          tyGenericError ("Definition doesn't match constraint for " ^ 
			     stnm)
	  

  | Value(nm,st) ->
      let ((_,Some st'), cntxt') = annotateBinding cntxt (nm, Some st)
      in (cntxt', Value(nm,st'), TermSpec(nm,st'))

  | Let_term(bnd, trm) ->
      let   (trm', ty1) = annotateTerm cntxt trm
      in let ((nm,Some ty2) as bnd', cntxt') = 
	annotateBindingWithCheckedDefault cntxt ty1 bnd
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
	OtherSpec)

  | Comment cmmnt->
      (cntxt, Comment cmmnt, OtherSpec)

  | Predicate (nm, stblty, st) ->
      let (st1,knd1) = annotateSet cntxt st
	(* If the user explicitly says "stable predicate" or that it's
           an equivalence, then we assume this to be true, even if the
           given type is "... -> Prop" *)
      in let (st2,stblty') = (match (stblty,knd1) with
	  (Unstable, KindProp stb) -> 
	    (st1, joinPropKind Unstable stb)
	| (Stable, KindProp stb) -> 
	    (makeStable st1, joinPropKind Stable stb)
        | (Equivalence, KindProp stb) -> 
	    (makeEquivalence cntxt nm st, joinPropKind Equivalence stb)
        | _ -> tyGenericError 
	    ("The predicate" ^ (string_of_name nm) ^
                " has type " ^ (string_of_set st1) ^
                " which is not the type of a predicate"))
      in let cntxt' = insertVar cntxt nm st2 in
	   (cntxt', Predicate (nm, stblty', st2), TermSpec(nm, st2))

  | Let_predicate ((n,_) as bnd, stab, p) ->
      let (bnd', _) = annotateBinding cntxt bnd
      in let (p', ty', stab') = annotatePropFn cntxt p
      in let recorded_ty = 
	   (match bnd' with
	       (_, Some ty'') -> 
		 if subSet cntxt ty' ty'' then
		   (* XXX We could store ty' instead of ty'' if we wanted
		      to be more permissive (e.g., treating a stable predicate
		      as stable regardless of the user's annotation) *)
		   ty''
		 else
		   failwith ("Could not verify that " ^ 
				(string_of_name n) ^ " has type " ^ 
				(string_of_set ty''))
	     | _ -> ty')
      in let cntxt' = insertVar cntxt n recorded_ty
      in 
	   (cntxt', 
	   Let_predicate (bnd', stab, p'),
	   TermSpec(n, recorded_ty))

  | Model (mdlnm, thry) ->
      let ( thry', summary ) = annotateTheory cntxt thry
      in let cntxt' = insertModel cntxt mdlnm summary
      in 
           ( cntxt', 
	   Model ( mdlnm, thry' ), 
	   ModelSpec ( mdlnm, summary ) )

  | _ -> raise Impossible

and annotateTheoryElems cntxt = function
    [] -> ([], [])

  | Implicit(strs, s)::rest ->    (** Eliminated during inference *)
      let    s' = annotateProperSet cntxt s 
              (string_of_theory_element (Implicit(strs,s))) 
      in let cntxt' = insertImplicits cntxt strs s'
      in let (rest_defs,rest_specs) = annotateTheoryElems cntxt' rest
      in (rest_defs, rest_specs)

  | thryelm::rest ->
      let (cntxt',def,spec) = annotateTheoryElem cntxt thryelm in
      let (rest_defs,rest_specs) = annotateTheoryElems cntxt' rest
      in (def::rest_defs, spec::rest_specs)

and annotateModelBindings cntxt = function
    [] -> [], cntxt
  | (m, th) :: bnd ->
      let (th', summary) = annotateTheory cntxt th in
      let (bnd', cntxt') = annotateModelBindings cntxt bnd in
	((m, th') :: bnd', (insertModel cntxt' m summary))

and annotateTheory cntxt = function
    Theory elems ->
      let ( elems', items ) = annotateTheoryElems cntxt elems
      in  ( Theory elems', Summary_Struct (Theory elems', items ) )

  | TheoryName str -> (match peekTheory cntxt str with
        Some summary -> (TheoryName str, summary)
      | None -> tyGenericError ("Unknown theory: " ^ str))

  | TheoryFunctor ( arg, thry ) ->
      let ( [(mdlnm, _) as arg'], cntxt' ) = 
        annotateModelBindings cntxt [arg] in
      let (thry', summary) = annotateTheory cntxt' thry in 
        ( TheoryFunctor ( arg', thry'), 
        Summary_Functor ( arg', summary) )

  | TheoryApp (thry, mdl) as main_thry -> 
      let (thry', summary_thry) = annotateTheory cntxt thry in
      let (mdl', summary_mdl, sub) = annotateModel cntxt mdl in
	begin
          match summary_thry with
              Summary_Struct ( _ , _ ) -> 
		tyGenericError 
		  ( "Application of non-parameterized theory in:\n  " ^
		      string_of_theory main_thry )
            | Summary_Functor ( ( arg, argthry ), summary_result ) -> 
                (* XXX  substTheory isn't capture avoiding!!! 
                *)
		if ( etaEquivTheories argthry 
		       ( substTheory sub (summaryToTheory summary_mdl) ) )then
                  let sub = insertModelvar emptysubst arg mdl'
                  in ( TheoryApp ( thry', mdl' ),
		     substSummary sub summary_result )
		else
		  tyGenericError 
		    ( "Incompatible model argument in:\n  " ^ 
			string_of_theory main_thry ^ "\nExpected: " ^
			string_of_theory argthry ^ "\nFound   : " ^ 
			string_of_theory ( substTheory sub (summaryToTheory summary_mdl) ) )
	end

and annotateToplevel cntxt = function
    Theorydef (str, thry) ->
      let (thry', summary') =  annotateTheory cntxt thry
      in let summary'' = selfify ( TheoryName str ) summary'
      in (Theorydef (str, thry'), 
         insertTheory cntxt str summary'')

  |  TopComment cmmnt ->
       (TopComment cmmnt, cntxt)

  |  TopModel (mdlnm, thry) ->
       let (thry', summary) = annotateTheory cntxt thry in
	 (TopModel(mdlnm, thry'),
	 insertModel cntxt mdlnm summary)

and annotateToplevels cntxt = function
    [] -> ([], cntxt)
  | td::tds -> let (td', cntxt') = annotateToplevel cntxt td
    in let (tds',cntxt'') = annotateToplevels cntxt' tds 
    in (td'::tds', cntxt'')


