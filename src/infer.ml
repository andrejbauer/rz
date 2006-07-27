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

let notProperSetError ty inty  =
	    (print_string "\nTYPE ERROR: ";
	     print_string (string_of_set ty);
	     print_string " is not a proper set in";
	     print_string (string_of_set inty);
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

(** Determines whether the given ANNOTATED "set" is a true set in
    first-order logic.
 *)
let rec isSet = function
    Empty | Unit | Bool | Set_name _ -> true

  | Product lst -> List.for_all2 (function (_, s) -> isSet s) lst
  | Sum     lst -> List.for_all (function (_, None) -> true | 
                                          (_, Some s) -> isSet s) lst
  | Subset   ((_, Some st), _) -> isSet st
  | Subset   _          -> false
  | Rz       st         -> isSet st
  | Quotient (st,_)     -> isSet st
  | Exp      (_, st1, st2) -> isSet st1 && isSet st2
  | SetApp _ -> raise Unimplemented

  | Prop       -> false
  | StableProp -> false
  | EquivProp  -> false
  | Set        -> false
  | SetLambda (_, _) -> false


(** isProp : set -> bool

    Determines whether the given ANNOTATED "set" classifies
    either a proposition or in general (despite the name) a predicate.

    This cannot just be defined as the negation of isSet; a pair
    containing, say, a boolean and a proposition is neither a proper
    set nor a proper logical entity.
*)
and isProp = function
    Empty | Unit | Bool | Set_name _ | Product _
  | Sum _ | Subset _ | Rz _ | Quotient _ | Set | SetLambda _ -> false

  | Prop       -> true
  | StableProp -> true
  | EquivProp  -> true

  | Exp (_, s, t) -> isSet s && isProp t

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


(** makeBinaryCurried: set -> set

    Forces the type of a binary relation (curried or uncurried)
    into curried form.
 *)
let makeBinaryCurried = function
    Exp ( s1, Exp ( s2, ( ( Prop | StableProp | EquivProp ) as p ) ) )
  | Exp ( Product [s1; s2], ( (Prop | StableProp | EquivProp ) as p) ) ->
      Exp ( s1, Exp ( s2, p ) )
  | _ -> failwith "Invalid type of infix binary relation"

(** makeProp: name -> set -> set -> set

    makeProp nm st prp is called for a relation with the name nm;
    st is the set declared for the relation; prp is the set corresponding
    to the sort of relation being defined (e.g., Prop or StableProp).
 
    If st is a proper set, then st must be the domain of the relation.
    Otherwise, if st classifies propositions, then this must describe
    the relation in toto.
 *)
let rec makeProp nm st prp =
  if isSet st then
    Exp (st, prp)
  else if isProp st then
    st
  else
    tyGenericError ("Invalid type for predicate " ^ (string_of_name nm))

(** makeStable : set -> set

    Translates a set classifying a relation into the corresponding
    set classifying a stable relation.
 *)
let rec makeStable = function
    Prop | StableProp -> StableProp
  | EquivProp -> EquivProp
  | Exp (s, t) -> Exp (s, makeStable t)
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
  | SetSpec   of set_name * set option        (** Set and its definition *)
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
  | SetSpec ( stnm, stopt ) :: rest -> 
      let stopt' = substSetOption sub stopt
      in let this' = SetSpec ( stnm, stopt' )
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
  | SetSpec  ( stnm , _ ) -> addSetToSubst   sub stnm  whereami
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


(* peekSet' : theory_summary_item list -> set_name -> bool.

   Given the contents of a theory and a desired set name, determine
   whether a set of that name exists (with or without a definition).

   This code is simpler than peekTydef and peekTypeof below.  We are just
   returning a boolean, so there's no need to maintain the substitution.

   This function takes just the items, rather than a whole context,
   because this helper function is also used to search inside models,
   which have no implicit or theory components.
 *)
let rec peekSet' items desired_stnm =
      (* let _ = print_string ("looking for " ^ desired_stnm ^ "\n")
      in *) 
  let rec loop = function                (* loop over the items *)
      []                               -> false
    | SetSpec ( this_stnm, _ ) :: rest -> this_stnm = desired_stnm || loop rest
    | _ ::rest                         -> loop rest
  in loop items
   
(* peekSet : cntxt -> set_name -> bool.

   Like peekSet', but takes the whole context rather than just the
   items.
 *)    
let peekSet cntxt desired_stnm =  peekSet' cntxt.items desired_stnm


(** peekTydef' : Syntax.subst -> items -> model -> set_name -> set option

    Given the items from a context and a desired set name, determine
    whether a set of that name exists (with or without a definition).

    An initial substitution is passed in.  This is updated (using the
    list of model_names, to tell us what model we are inside) as we enter
    the scope of more module components, and finally applied to the
    type being found (so that the type makes sense outside the enclosing 
    modules).

 *)
let rec peekTydef' subst0 items whereami desired_stnm = 
  let rec loop substitution = function
      [] -> None
    | SetSpec (stnm, sopt) :: rest -> 
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
let insertSet   cntxt stnm = 
  if peekSet cntxt stnm then
    tyGenericError ("Shadowing of set name: " ^  stnm)
  else
    {cntxt with items = SetSpec(stnm, None) :: cntxt.items }
  
(** Takes the context and adds a new set of the given name, with the
  given set as its definition *)
let insertTydef cntxt stnm st =
  if peekSet cntxt stnm then
    tyGenericError ("Shadowing of set name: " ^  stnm)
  else
    {cntxt with items = SetSpec(stnm, Some st) :: cntxt.items }

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
               in ( ModelApp (mdl1', mdl2'), summary12, sub )
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
   let rec cmp s1 s2 = 
      (** Short circuting for (we hope) the common case *)
      (s1 = s2)
      (** Head-normalize the two sets *)
      || let    s1' = hnfSet cntxt s1
         in let s2' = hnfSet cntxt s2

         in (s1' = s2') 
            || match (s1',s2') with
                 ( Empty, Empty ) -> true       (** Redundant *)

               | ( Unit, Unit )   -> true       (** Redundant *) 

	       | ( Bool, Bool )   -> true       (** Bool <> Sum() for now *)

               | ( Set_name (mdlopt1, nm1), Set_name (mdlopt2, nm2) )  -> 
                    (** Neither has a definition *)
                    eqModelOpt cntxt mdlopt1 mdlopt2 
                    && (nm1 = nm2) 

 	       | ( Product ss1, Product ss2 ) -> 
                    cmps (ss1,ss2)

               | ( Sum lsos1, Sum lsos2 )     -> 
	            subSum do_subset cntxt (lsos1, lsos2) 
                    && (do_subset || subSum false cntxt (lsos2, lsos1))

               | ( Exp( st3, st4 ), Exp( st5, st6 ) )   -> 
                    eqSet cntxt st5 st3 
                    && cmp st4 st6

	       | ( Subset( (nm1,_) as b1, p1 ), Subset( (nm2,_) as b2, p2 ) )->
                    cmpbnd(b1,b2)
	            (** Alpha-vary the propositions so that they're using the
                        same (fresh) variable name *)
                    && let trm = Var(None, N(Syntax.freshNameString(), Word))
                       in let sub1 = insertTermvar emptysubst nm1 trm
         	       in let sub2 = insertTermvar emptysubst nm2 trm
	               in let p1' = subst sub1 p1
	               in let p2' = subst sub2 p2
	               in 
                          eqProp cntxt p1' p2'  

               | ( Quotient ( st3, eqvlnce3 ), Quotient ( st4, eqvlnce4 ) ) -> 
                    (** Quotient is invariant *)
                    eqSet cntxt st3 st4  
                    && eqTerm cntxt eqvlnce3 eqvlnce4

               | ( Rz st3, Rz st4 ) -> 
                    (** RZ seems like it should be invariant *)
                    eqSet cntxt st3 st4  

               | ( ( Prop | StableProp | EquivProp ), _ ) -> 
                    raise Impossible (** Shouldn't occur without HOL *)

               | ( _, ( Prop | StableProp | EquivProp ) ) -> 
                    raise Impossible (** Shouldn't occur without HOL *)

               | (_,_) -> false

      and cmps = function
          ([], []) -> true
	| (s1::s1s, s2::s2s) -> cmp s1 s2 && cmps(s1s,s2s)
        | (_,_) -> false

      and cmpbnd = function
	  (* Since we're not verifying equivalence of propositions,
	     we don't have to worry about the bound variable *)
          ((_, None),    (_,None)   ) -> true
        | ((_, Some s1), (_,Some s2)) -> cmp s1 s2
        | ( _,           _          ) -> false

     and subSum do_subset cntxt = function
          ( [], _ ) -> true
       | ((l1,None   )::s1s, s2s) ->
	     (try (let None = (List.assoc l1 s2s)
                   in subSum do_subset cntxt (s1s, s2s))
	      with _ -> false)
       | ((l1,Some s1)::s1s, s2s) -> 
	     (try (let Some s2 = (List.assoc l1 s2s)
                   in eqSet' do_subset cntxt s1 s2  && 
                      subSum do_subset cntxt (s1s,s2s))
	      with _ -> false)

      in cmp


and eqProp ctx prp1 prp2 = (prp1 = prp2)  (* XXX: Should allow alpha-equiv
                                                  and set-equiv *)

and eqTerm ctx trm1 trm2 = (trm1 = trm2)  (* XXX: Should allow alpha-equiv
                                                  and set-equiv *)

and eqModelOpt ctx mdlopt1 mdlopt2 = (mdlopt1 = mdlopt2)

and eqSet cntxt st1 st2 = eqSet' false cntxt st1 st2

and subSet cntxt st1 st2 = eqSet' true cntxt st1 st2

(* coerce: cntxt -> term -> set -> set -> trm option
     coerce trm st1 st2 coerces trm from the set st1 to the set st2
       using subin and subout.
     Preconditions: trm is in st1 and all arguments are fully-annotated.
     Returns:  None if trm cannot be turned into a value in set st2.
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
            let rec loop = function
                ([], [], []) -> Some []
              | ([], _, _)   -> None
              | (trm::trms, st1::sts1, st2::sts2) ->
                  (match (coerce cntxt trm st1 st2, loop(trms,sts1,sts2)) with
                     (Some trm', Some trms') -> Some (trm'::trms')
                   | _ -> None )
            in (match (loop (trms, sts1, sts2)) with
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
	      try
		let None = List.assoc l1 s2s
		in joinSums(s1s, s2s)
              with _ -> tyGenericError ("Disagreement as to whether " ^ l1 ^
                         " stands alone or tags a value")
	    else (l1,None) :: joinSums(s1s, s2s))
        | ((l1,Some s1)::s1s, s2s) ->
	    (if (List.mem_assoc l1 s2s) then
	      try
		let Some s2 = List.assoc l1 s2s
		in if eqSet cntxt s1 s2 then
		      joinSums(s1s, s2s)
		else
		    tyGenericError ("Disagreement as to whether " ^ l1 ^
                                    " tags a value or stands alone")
              with _ -> tyGenericError("Disagreement on what type of value " ^ 
                                        l1 ^ " should tag")
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

(** Given a list of kinds, check that they're proper-Set *)
let allSets ks =
	List.for_all (function k -> k = Set) ks

let rec annotateProduct cntxt nss = 
    (let rec ann cntxt = function
           [] -> []
         | (nopt, s) :: rest ->     
                let s' = annotateProperSet cntxt s (Product nss)
                in let cntxt' = match nopt with
                         None -> cntxt
                       | Some n -> insertVar cntxt n s'
                     in s' :: ann cntxt' rest
     in    (Product (ann cntxt nss), Set) )

let rec annotateSum cntxt lsos ->
    (let rec ann lbls_used = function
           [] -> []

         | (l, sopt) :: rest ->
             if (not (List.mem l lbls_used)) then
               (match sopt with
                   None -> (l, sopt) 
                 | Some s -> let s' = annotateProperSet cntxt s (Sum lsos)
                             in (l, Some s')
                ) :: 
               ann (l :: lbls_used rest) rest
             else
                tyGenericError
                    ("Duplicate label" ^
                     (string_of_label l) ^
                     "in the sum" ^
                     (string_of_sum (Sum lsos)))
            
     in ( Sum (ann [] lsos), Set ) )

let annotateExp cntxt = function
    (Exp(nopt,s1,s2)) as s ->
        let  s1' = annotateProperSet cntxt s1 s
      in let cntxt' = match nopt with
                            None -> None
                          | Some n -> insertVar cntxt n s1'
      in let s2' = annotateProperSet cntxt' s2 s
      in ( Exp(nopt,s1',s2'), Set )
    | _ -> raise Impossible
    
let annotateProperSet cntxt s in_s =
    let (s', k) = annotateSet cntxt s
    in if (k = Set) then 
          s'
       else 
          notProperSetError s in_s    
    
(** Given a contxt and a set, return the annotated version of the set.

    Raises an informitive error if the set is not well-formed.
*)
let rec annotateSet cntxt = 
    (let rec ann orig_set = 
        match orig_set with
          Product nss -> annotateProduct nss

        | Sum lsos   -> annotateSum lsos

        | (Exp _) -> annotateExp orig_set

        | Subset(bnd, p) -> 
             let (bnd',cntxt') = annotateBinding cntxt bnd
             in let (p',_) = annotateProp cntxt' p
             in ( Subset(bnd', p'), Set )

        | SetApp(st, trm) ->
              let (st', k_st') = ann st'
             in let (trm', st_trm') -> 
             in match k_st' with
                  KindArrow(st_k_st', k_k_st') ->
                    if (eqSet cntxt st_trm' st_k_st') then
                       (* Need to do some substitutions, but Syntax's substitution
                          functions aren't capture-avoiding! *)
                       raise Unimplemented
                    else
                       tyGenericError
                       (Term ^ (string_of_term trm) ^ 
                        "is not a valid argument to " ^
                        (string_of_set st))
                | _ -> tyGenericError
                       ((string_of_set st) ^ 
                        "does not take arguments; not even" ^
                        (string_of_term trm)) 

        | Quotient(st, trm) ->
        let    st' = annotateProperSet cntxt st orig_set
        in
         (match equivalenceAt cntxt trm with
          None -> tyGenericError 
            ("Not an stable equivalence relation: " ^ 
             string_of_term trm)
        | Some (domain_st, trm') -> 
            if (eqSet cntxt st' domain_st) then
              (Quotient(st', trm'), Set)
            else
              tyGenericError
            ("Wrong domain for equivalence relation in " ^
             string_of_set (Quotient(st,trm))))
        | (Rz st) -> ( Rz(annotateProperSet cntxt st orig_set), Set )
        | Set_name (None, stnm) ->
             (if (peekSet cntxt stnm) then
                orig_set
              else tyGenericError ("Set not found: " ^ stnm))
    | Set_name (Some mdl, stnm) -> 
        let (mdl', summary, _) = annotateModel cntxt mdl
        in (match summary with
              Summary_Struct(_, items) -> 
            if (peekSet' items stnm) then
              Set_name(Some mdl', stnm)
            else
              tyGenericError ( "Unknown component " ^ 
                       string_of_set orig_set )
              | _ -> tyGenericError 
                   "Set projection from parameterized model")
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
            in let ty3 = try (joinSet cntxt ty1 ty2) with
                     TypeError -> tyGenericError 
                   ("Cannot compare " ^ string_of_term t1 ^ " and "
                  ^ string_of_term t2 ^ " for equality")
                          
            in
          Equal(Some ty3, t1', t2'), Stable

        | Equal (Some s, t1, t2) ->
            let    ty = annotateSet cntxt s
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

and annotateBindingWithCheckedDefault cntxt default_st = function
    (x, None) -> annotateBindingWithDefault cntxt default_st (x, None)
  | (x, Some s2) -> let s2' = annotateSet cntxt s2 in
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

     | Constraint(t,s) ->
         let (t',ty) = ann t  in
         let s'      = annotateSet cntxt s  in
         begin
       match (coerce cntxt t' ty s') with
             Some trm'' -> (Constraint(trm'',s'), s')
           | None       -> tyMismatchError t s' ty 
     end
    
     | Star -> (Star, Unit)

     | Tuple ts ->
         let (ts', tys) = List.split (List.map ann ts)
         in (Tuple ts', Product tys)

     | Proj (n, t) -> 
         let    (trm', tuplety) = ann t
         in let (trm'', hnfty) = coerceFromSubset cntxt trm' tuplety
         in let tys = (match hnfty with
                      Product tys -> tys
                   | _ -> tyWrongSortError t " tuple" tuplety)
         in if (n >= 0 && n < List.length tys) then
              ((Proj(n,trm''), List.nth tys n))
           else
              tyGenericError ("Projection " ^ string_of_int n ^ 
                  " out of bounds")
     | App (t1, t2) ->
        let (t1', ty1) = ann t1 in
        let (t2', ty2) = ann t2 in
        let (t1'',ty3,ty4) = (match (coerceFromSubset cntxt t1' ty1) with
                          (t1'', Exp(ty3,ty4)) -> (t1'',ty3,ty4)
                        | _ -> tyWrongSortError t1 " function" ty1)
        in
          ( match (coerce cntxt t2' ty2 ty3) with
              Some trm2'' ->  (App (t1'', trm2''), ty4)
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

     | RzChoose (bnd, t1, t2, body_ty_opt) ->
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
             | Some body_ty -> if (eqSet cntxt' (annotateSet cntxt body_ty) ty2 ) then
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

     | Choose (bnd, r, t1, t2, body_ty_opt) ->
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
             | Some body_ty -> if (eqSet cntxt' (annotateSet cntxt body_ty) 
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

     | Let (bnd, t1, t2, Some st) ->
         let    (t1', ty1) = ann t1
         in let (bnd',cntxt') = annotateBindingWithCheckedDefault cntxt ty1 bnd
         in let (t2', ty2) = annotateTerm cntxt' t2
     in let st' = annotateSet cntxt st
         in if (subSet cntxt' ty2 st') then
             (Let(bnd',t1',t2',Some st'), st')
       else
             tyGenericError ("Inferred let-body type does not match annotation")

     | Lambda (bnd,t) ->
         let    ((_,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
         in let (t', ty2) = annotateTerm cntxt' t
         in (Lambda(bnd',t'), Exp(ty1, ty2))

     | The (bnd,t) ->
         let    ((_,Some ty1) as bnd', cntxt') = annotateBinding cntxt bnd
         in let (t', ty2) = annotateTerm cntxt' t
         in (The(bnd',t'), ty1)

     | Subin (t, s) ->
     let s' = annotateSet cntxt s in
     let (t', ty) = annotateTerm cntxt t in
       (match hnfSet cntxt s' with
         Subset ((_,Some ty'), _) -> 
           if (subSet cntxt ty ty') then
         (Subin (t', s'), s')
           else
         tyMismatchError t ty' ty
       | _ -> tyGenericError "<: with a non-subset-type")

     | Subout (t, s) ->
     let s' = annotateSet cntxt s in
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

  | Let_term(bnd, None, trm) ->
      let   (trm', ty1) = annotateTerm cntxt trm
      in let ((nm,Some ty2) as bnd', cntxt') = 
      annotateBindingWithCheckedDefault cntxt ty1 bnd
      in if (subSet cntxt ty1 ty2) then
          (cntxt', Let_term(bnd',None,trm'), TermSpec(nm,ty2))
      else
        tyGenericError ("Definition doesn't match constraint for " ^ 
            string_of_bnd bnd)
      
  | Let_term(bnd, Some args, trm) ->
       let    (args', cntxt') = annotateBindings cntxt args
       in let (trm', ty1) = annotateTerm cntxt' trm
       in let ty1' = List.fold_right (fun (_, Some s) t -> Exp (s, t)) args' ty1
       in let ((nm, Some ty2) as bnd', cntxt'') = 
         annotateBindingWithCheckedDefault cntxt (ty1') bnd
       in if (subSet cntxt ty1' ty2) then
         (cntxt'', Let_term(bnd', Some args', trm'), TermSpec(nm, ty2))
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
      (* XXX Predicates must be on proper sets *)
      let st' = annotateSet cntxt st in
      let st1 = makeProp nm st' (mkKind stblty) in
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
       (* XXX We could return stab' instead of stab if we wanted
              to be more permissive (e.g., treating a stable predicate
          as stable regardless of the user's annotation) *)
       Let_predicate (n, stab, bnds', p'),
       TermSpec(n, ty))
    else
      failwith ("Could not determine that " ^ 
            (string_of_name n) ^ " is stable")

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


