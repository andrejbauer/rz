(*******************************************************************)
(** {1 Type Reconstruction and Checking}                           *)
(**                                                                *)
(** For now we assume that                                         *)
(** all bound variables are annotated, either when declared        *)
(** or through a prior "implicit" statement.                       *)
(*******************************************************************)

module S = Syntax
module L = Logic
open Syntax 
open Name

exception Unimplemented
exception Impossible

(************************)
(** {2 Error Reporting} *)
(************************)

exception TypeError

let type_error_header = "\n-------------------------------\nTYPE ERROR:\n"
let type_error_footer = "\n-------------------------------\n\n"

let tyGenericError msg = 
  (print_string (type_error_header ^ msg ^ type_error_footer);
   raise TypeError)


let tyUnboundError nm =
  tyGenericError
    ("Unbound name " ^ string_of_name nm)

let notWhatsExpectedError expr expected =
  tyGenericError
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected")

let notWhatsExpectedInError expr expected context_expr =
  tyGenericError
    (S.string_of_expr expr ^ " found where a "
      ^ expected ^ " was expected, in " ^ S.string_of_expr context_expr)

let noHigherOrderLogicError expr =
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires higher-order-logic")

let noPolymorphismError expr =
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires polymorphism")

let noPropositionsAsTypesError expr = 
   tyGenericError
     ("The input " ^ S.string_of_expr expr ^ " requires polymorphism")

let noTypeInferenceInError nm expr =
  tyGenericError
     ("The bound variable " ^ string_of_name nm ^ " in " ^
      S.string_of_expr expr ^ " is not annotated explicitly or implicitly.")

let wrongTypeError expr hastype expectedsort context_expr =
  tyGenericError
    ("The term " ^ string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ " in " ^ string_of_expr context_expr ^ 
      ", but it's actually has type " ^ L.string_of_set hastype)

let wrongPropTypeError expr hasPT expectedsort context_expr =
  tyGenericError
    ("The term " ^ string_of_expr expr ^ " is used as if it were a "
      ^ expectedsort ^ " in " ^ string_of_expr context_expr ^ 
      ", but it's actually has type " ^ L.string_of_proptype hasPT)

let wrongKindError expr hasK expectedsort context_expr =
  tyGenericError
    ("The set " ^ string_of_expr expr ^ "\nis used as if had a "
      ^ expectedsort ^ " kind in " ^ string_of_expr context_expr ^ 
      ", but it's actually has kind " ^ L.string_of_kind hasK)

let tyMismatchError expr expectedTy foundTy context_expr =
  tyGenericError
    ("The term " ^ string_of_expr expr ^ " was expected to have type " ^
	L.string_of_set expectedTy ^ " instead of type " ^ 
	L.string_of_set foundTy ^ " in\n" ^ string_of_expr context_expr)

let propTypeMismatchError expr expectedTy foundTy context_expr =
  tyGenericError
    ("The proposition " ^ string_of_expr expr ^ " was expected to have type " ^
	L.string_of_proptype expectedTy ^ " instead of type " ^ 
	L.string_of_proptype foundTy ^ " in\n" ^ string_of_expr context_expr)

let kindMismatchError expr expectedK foundK context_expr =
  tyGenericError
    ("The set " ^ string_of_expr expr ^ " was expected to have kind " ^
	L.string_of_kind expectedK ^ " instead of kind " ^ 
	L.string_of_kind foundK ^ " in " ^ string_of_expr context_expr)

let notEquivalenceOnError expr expectedDomExpr =
  tyGenericError
    ("The relation " ^ string_of_expr expr ^ 
	" is not an equivalence relation on " ^ 
	string_of_expr expectedDomExpr)

let cantElimError context_expr =
  tyGenericError 
    ("Inferred type of " ^ string_of_expr context_expr ^ 
	"refers to a locally-bound variable; " ^ 
	"maybe a constraint on the body would help?")

let tyJoinError ty1 ty2 =
   tyGenericError
     ("the types " ^ L.string_of_set ty1 ^ " and " ^
	 L.string_of_set ty2 ^ " are incompatible")
	
let componentNotFoundError nm expr =
  tyGenericError
    ("Cannot project " ^ string_of_name nm ^ " in " ^ string_of_expr expr)
      
(*****************************************)
(** {2 Typechecking/Type Reconstruction} *)
(*****************************************)


(******************)
(** { 3 Contexts} *)
(******************)


type inferResult =
    ResPropType of L.proptype
  | ResKind     of L.setkind
  | ResSet      of L.set         * L.setkind
  | ResTerm     of L.term        * L.set
  | ResProp     of L.proposition * L.proptype
  | ResModel    of L.model       * L.theory 
  | ResTheory   of L.theory

type ctx_member =
    CtxProp   of L.proposition option * L.proptype
  | CtxSet    of L.set option         * L.setkind
  | CtxTerm   of                        L.set
  | CtxModel  of L.theory
  | CtxTheory of L.theory
  | CtxUnbound

type implicit_info =
      ImpTermvar of L.set
    | ImpUnknown


type context = {bindings : (name * ctx_member) list;
		implicits : (name * implicit_info) list;
	        renaming : name NameMap.t}

let emptyContext = {bindings = []; implicits = [];
		    renaming = NameMap.empty}

let lookupImplicit cntxt nm = 
  try (List.assoc nm cntxt.implicits) with
      Not_found -> ImpUnknown

let rec insertImplicits cntxt names ty = 
  {cntxt with
    implicits = ( List.map (fun nm -> (nm, ImpTermvar ty)) names )
                  @ cntxt.implicits}

let lookupId cntxt nm =
  try (List.assoc nm cntxt.bindings) with
      Not_found -> CtxUnbound

(* These functions ought to detect and complain about shadowing.
   In most cases, the system will already have renamed bound variables
   before this point.  For module labels we can't rename, and so we
   may have to just give up here with an error.
*)
let insertTermVariable cntxt nm ty =
  { cntxt with bindings =  (nm, CtxTerm ty) :: cntxt.bindings }

let insertSetVariable cntxt nm knd stopt =
  { cntxt with bindings =  (nm, CtxSet (stopt,knd)) :: cntxt.bindings }

let insertPropVariable cntxt nm pt prpopt =
  { cntxt with bindings =  (nm, CtxProp (prpopt,pt)) :: cntxt.bindings }

let insertModelVariable cntxt nm thry =
  { cntxt with bindings =  (nm, CtxModel thry) :: cntxt.bindings }

let insertTheoryVariable cntxt nm thry =
  { cntxt with bindings =  (nm, CtxTheory thry) :: cntxt.bindings }

let renameBoundVar cntxt nm =
  let rec findUnusedName nm =
    match (lookupId cntxt nm) with
	CtxUnbound -> nm
      | _ -> findUnusedName (nextName nm)
  in let nm' = findUnusedName nm
  in 
       if (nm = nm') then
	 (cntxt, nm)
       else
	 begin
	   print_endline 
	     ("WARNING:  Shadowing of " ^ string_of_name nm ^ 
		 "detected.");
	   ({cntxt with renaming = NameMap.add nm nm' cntxt.renaming}, nm')
	 end

let applyContextSubst cntxt nm = 
  try  NameMap.find nm cntxt.renaming  with
      Not_found -> nm



let rec searchElems cntxt nm' surrounding_expr mdl = 
  let rec loop subst = function
    [] -> componentNotFoundError nm' surrounding_expr
    | L.Set (nm, knd) :: rest -> 
	if (nm = nm') then
	  CtxSet(None, L.substKind subst knd)  (* or Some mdl.nm? *)
	else 
	  loop (L.insertSetvar subst nm (L.Basic(L.SLN(Some mdl, nm)))) rest
    | L.Let_set (nm, knd, st) :: rest -> 
	if (nm = nm') then
	  CtxSet(Some (L.substSet subst st), L.substKind subst knd)
	else 
	  loop (L.insertSetvar subst nm (L.Basic(L.SLN(Some mdl, nm)))) rest
    | L.Predicate (nm, pt) :: rest -> 
	if (nm = nm') then
	  CtxProp(None, L.substProptype subst pt)
	else 
	  loop (L.insertPropvar subst nm (L.Atomic(L.LN(Some mdl, nm)))) rest
    | L.Let_predicate (nm, pt, prp) :: rest -> 
	if (nm = nm') then
	  CtxProp(Some (L.substProp subst prp), L.substProptype subst pt)
	else 
	  loop (L.insertPropvar subst nm (L.Atomic(L.LN(Some mdl, nm)))) rest
    | L.Value (nm, ty) :: rest 
    | L.Let_term (nm, ty, _) :: rest -> 
	if (nm = nm') then
	  CtxTerm (L.substSet subst ty)
	else 
	  loop (L.insertTermvar subst nm (L.Var(L.LN(Some mdl, nm)))) rest
    | L.Model (nm, thry) :: rest ->
	if (nm = nm') then
	  CtxModel (L.substTheory subst thry)
	else 
	  loop (L.insertModelvar subst nm (L.ModelProj(mdl, nm))) rest
    | L.Sentence _ :: rest -> loop subst rest
    | L.Comment _  :: rest -> loop subst rest
  in
    loop L.emptysubst 

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
*)

(*******************)
(** {3: Coercions} *)
(*******************)

let rec theoryToElems cntxt = function
    L.Theory elems -> elems
  | L.TheoryName thrynm' -> 
      begin
	match lookupId cntxt thrynm' with
	    CtxTheory thry' -> theoryToElems cntxt thry'
	  | _ -> raise Impossible
      end
  | L.TheoryFunctor _ -> raise Impossible
  | L.TheoryApp _ -> raise Unimplemented

(* cntxt -> L.model -> L.theory list *)
let rec modelToTheory cntxt = function
    L.ModelName nm ->
      begin
	match (lookupId cntxt nm) with
	    CtxModel thry -> thry
	  | _ -> raise Impossible
      end
  | L.ModelProj (mdl, nm) -> 
      begin
	let elems = theoryToElems cntxt (modelToTheory cntxt mdl)
	in
	  match searchElems cntxt nm S.False mdl elems with
	      CtxModel thry -> thry
	    | _ -> raise Impossible
      end
  | L.ModelApp _ -> raise Unimplemented 
	

(** Expand out any top-level definitions or function
    applications for a (well-formed) set 
  *)
let rec hnfSet cntxt = function
    L.Basic (L.SLN ( None, stnm )) as orig_set ->
      begin
	match (lookupId cntxt stnm) with
            CtxSet(Some st, _) -> hnfSet cntxt st
	  | CtxSet(None, _)    -> orig_set
	  | _ -> raise Impossible
      end

  | L.Basic (L.SLN ( Some mdl, nm)) as orig_set -> 
      begin
      let elems = theoryToElems cntxt (modelToTheory cntxt mdl)
      in
	match searchElems cntxt nm S.False mdl elems with
            CtxSet(Some st, _) -> hnfSet cntxt st
	  | CtxSet(None, _)    -> orig_set
	  | _ -> raise Impossible
      end

  | L.SApp(st1,trm2) -> 
      begin
	match (hnfSet cntxt st1) with
	    L.SLambda((nm,_),st1body) ->
	      let sub = L.insertTermvar L.emptysubst nm trm2
	      in
		hnfSet cntxt (L.substSet sub st1body)
	  | st1' -> L.SApp(st1', trm2)
      end

  | st -> st


let rec freshNameSubsts' nm1 nm2 subst1 subst2 = 
  let freshname = N(Syntax.freshNameString(), Word)
  in let trm = L.Var(L.LN(None, freshname))
  in let sub1 = L.insertTermvar subst1 nm1 trm
  in let sub2 = L.insertTermvar subst2 nm2 trm
  in (freshname, sub1, sub2)
    
let freshNameSubsts nm1 nm2 = 
  freshNameSubsts' nm1 nm2 L.emptysubst L.emptysubst


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
   let rec cmp (s1 : L.set) (s2 : L.set) = 
      (** Short circuting for (we hope) the common case *)
      (s1 = s2)
      (** Head-normalize the two sets *)
      || let    s1' = hnfSet cntxt s1
         in let s2' = hnfSet cntxt s2

         in (s1' = s2') 
            || (match (s1',s2') with
                 ( L.Empty, L.Empty ) -> true       (** Redundant *)

               | ( L.Unit, L.Unit )   -> true       (** Redundant *) 

               | ( L.Basic (L.SLN(mdlopt1, nm1)),
		   L.Basic (L.SLN(mdlopt2, nm2)) ) -> 
                    (** Neither has a definition *)
                    eqModelOpt cntxt mdlopt1 mdlopt2 
                    && (nm1 = nm2) 

 	       | ( L.Product ss1, L.Product ss2 ) -> 
                    cmpProducts (ss1,ss2)

               | ( L.Sum lsos1, L.Sum lsos2 )     -> 
	            subSum do_subset cntxt (lsos1, lsos2) 
                    && (do_subset || subSum false cntxt (lsos2, lsos1))


               | ( L.Exp( nm1, st3, st4 ), L.Exp ( nm2, st5, st6 ) ) ->
		   let (_, sub1, sub2) = freshNameSubsts nm1 nm2
	           in let st4' = L.substSet sub1 st4
	           in let st6' = L.substSet sub2 st6
	           in 
		    (* Domains are now compared contravariantly. *)
                    subSet cntxt st5 st3 
                    && cmp st4' st6'

	       | ( L.Subset( (nm1,_) as b1, p1 ), 
		   L.Subset( (nm2,_) as b2, p2 ) )->
                    cmpbnd(b1,b2)
	            (** Alpha-vary the propositions so that they're using the
                        same (fresh) variable name *)
                    && let (_, sub1, sub2) = freshNameSubsts nm1 nm2
	               in let p1' = L.substProp sub1 p1
	               in let p2' = L.substProp sub2 p2
	               in 
                          eqProp cntxt p1' p2'  

               | ( L.Quotient ( st3, eqvlnce3 ), 
		   L.Quotient ( st4, eqvlnce4 ) ) -> 
                    (** Quotient is invariant *)
                    eqSet cntxt st3 st4  
                    && eqProp cntxt eqvlnce3 eqvlnce4

               | ( L.SApp (st3, trm3), L.SApp (st4, trm4) ) ->
		    eqSet cntxt st3 st4
		    && eqTerm cntxt trm3 trm4

               | ( L.Rz st3, L.Rz st4 ) -> 
                    (** RZ seems like it should be invariant.  *)
		    (** XXX Is it? *)
                    eqSet cntxt st3 st4  

               | (_,_) -> false )

     and cmpbnd = function
	 (* Since we're not verifying equivalence of propositions,
	    we don't have to worry about the bound variable *)
         ((_, s1), (_, s2)) -> cmp s1 s2

      and cmpProducts' subst1 subst2 = function
          ( [] , [] ) -> true

	| ( (nm1, s1) :: s1s, (nm2, s2) :: s2s) -> 
	    let (_, subst1', subst2') = freshNameSubsts' nm1 nm2 subst1 subst2
	    in let s1' = L.substSet subst1 s1
	    in let s2' = L.substSet subst2 s2
	    in  (cmp s1' s2' && cmpProducts' subst1' subst2' (s1s,s2s) )

        | (_,_) -> false

   and cmpProducts lst = cmpProducts' L.emptysubst L.emptysubst lst

     and subSum do_subset cntxt = function
          ( [], _ ) -> true
       | ((l1,None   )::s1s, s2s) ->
	   (try
	       match (List.assoc l1 s2s) with
		   None -> subSum do_subset cntxt (s1s, s2s)
		 | _ -> false 
	     with 
		 Not_found -> false)
       | ((l1,Some s1)::s1s, s2s) -> 
	   (try
	       match (List.assoc l1 s2s) with
		   Some s2 -> eqSet' do_subset cntxt s1 s2  && 
                              subSum do_subset cntxt (s1s,s2s)
		 |  _ -> false 
	     with
		 Not_found -> false)

      in cmp


and eqPropType' do_subset cntxt = 
   let rec cmp (pt1 : L.proptype) (pt2 : L.proptype) = 
     begin
       (** Short circuting for (we hope) the common case *)
       (pt1 = pt2) ||
         match (pt1, pt2) with
           | ( L.StableProp, L.Prop ) -> true
	       
           | ( L.EquivProp st1, L.EquivProp st2) -> 
	       eqSet' do_subset cntxt st2 st1
	       
           | ( L.EquivProp st1, _ ) ->
	       begin
		 do_subset &&
		   let pt1' =
		     L.PropArrow(S.freshWildName(), st1,
				L.PropArrow(S.freshWildName(), st1, 
				           L.StableProp))
		   in
		     eqPropType' true cntxt pt1' pt2
	       end
		 
           | ( L.PropArrow( nm1, st1, pt1 ), L.PropArrow ( nm2, st2, pt2 ) ) ->
	       let (_, sub1, sub2) = freshNameSubsts nm1 nm2
	       in let pt1' = L.substProptype sub1 pt1
	       in let pt2' = L.substProptype sub2 pt2
	           in 
		    (* Domains are now compared contravariantly. *)
                    subSet cntxt st2 st1 
                    && cmp pt1' pt2'

	   | _ -> false
     end
   in cmp

and subPropType cntxt pt1 pt2 = eqPropType' true cntxt pt1 pt2

and eqPropType cntxt pt1 pt2 = eqPropType' false cntxt pt1 pt2

and eqKind' do_subset cntxt = 
   let rec cmp (k1 : L.setkind) (k2 : L.setkind) = 
     begin
       (** Short circuting for (we hope) the common case *)
       (k1 = k2) ||
         match (k1, k2) with
             ( L.KindArrow( nm1, st1, kk1 ), L.KindArrow ( nm2, st2, kk2 ) ) ->
	       let (_, sub1, sub2) = freshNameSubsts nm1 nm2
	       in let kk1' = L.substKind sub1 kk1
	       in let kk2' = L.substKind sub2 kk2
	           in 
		    (* Domains are now compared contravariantly. *)
                    subSet cntxt st2 st1 
                    && cmp kk1' kk2'

	   | _ -> false
     end
   in cmp

and subKind cntxt k1 k2 = eqKind' true cntxt k1 k2

and eqKind cntxt k1 k2 = eqKind' false cntxt k1 k2

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


(** Computes the join of the two sets s1 and s2.
    Like subtSet (and unlike Coerce), 
    join does *not* do implicit conversions *)
let joinType cntxt s1 s2 = 
   if (s1 = s2) then
      (* Short circuit *)
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
        | (L.Sum lsos1, L.Sum lsos2) -> L.Sum (joinSums (lsos1, lsos2))
        | _ -> if eqSet cntxt s1 s2 then
                  s1
       	       else
	          tyJoinError s1 s2
 

let joinTypes cntxt =
  let rec loop = function
      [] -> L.Unit
    | [s] -> s
    | s::ss -> joinType cntxt s (loop ss)
  in
    loop

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
	| ( _, L.Subset ( ( _, st1'1 ) , _ ),
               L.Subset ( ( _, st2'1 ) , _ ) ) -> 

	    (** Try an implicit out-of-subset conversion *)
           (match ( coerce cntxt ( L.Subout(trm,st1) ) st1'1 st2 ) with
              Some trm' -> Some trm'
            | None -> (** That didn't work, so try an implicit 
                          into-subset conversion *)
                      (match (coerce cntxt trm st1 st2'1) with
                        Some trm' -> Some ( L.Subin ( trm', st2 ) )
                      | None      -> None ) )

        | ( _, L.Subset( ( _, st1'1 ), _ ), _ ) -> 
	    (** Try an implicit out-of-subset conversion *)
            coerce cntxt ( L.Subout(trm,st2) ) st1'1 st2 

        | ( _, _, L.Subset( ( _, st2'1 ), _ ) ) -> 
	    (** Try an implicit into-subset conversion *)
            ( match (coerce cntxt trm st1 st2'1) with
                Some trm' -> Some ( L.Subin ( trm', st2 ))
              | None      -> None )

        | ( L.Tuple trms, L.Product sts1, L.Product sts2 ) ->
            let rec loop subst2 = function 
                ([], [], []) -> Some []
              | ([], _, _)   -> None
              | (trm::trms, (nm1, st1)::sts1, (nm2, st2)::sts2) ->
		  if (isWild nm1) then
		    let st2' = L.substSet subst2 st2
		    in let subst2' = L.insertTermvar subst2 nm2 trm
                    in (match (coerce cntxt trm st1 st2', 
			      loop subst2' (trms,sts1,sts2)) with
			(Some trm', Some trms') -> Some (trm'::trms')
                      | _ -> None )
		  else
		    (* This case shouldn't ever arise; tuples naturally
		       yield non-dependent product types.  
		       But just in case, ...*)
		    (print_string 
			("WARNING: coerce: dependent->? case for products " ^
			    " arose, surprisingly!\n");
		     None)
	      | _ -> raise Impossible
            in (match (loop L.emptysubst (trms, sts1, sts2)) with
                  Some trms' -> Some (L.Tuple trms')
                | None -> None)

        | _ -> None

let rec coerceFromSubset cntxt trm st = 
   match (hnfSet cntxt st) with
      L.Subset( ( _, st1 ), _ ) -> 
         coerceFromSubset cntxt (L.Subout(trm, st)) st1
    | st' -> (trm, st')

let noDuplicates strngs =
  let sset = List.fold_right StringSet.add strngs StringSet.empty
  in
    List.length strngs = StringSet.cardinal sset


(*********************)
(** Inference proper *)
(*********************)


(*** XXX Does not check that names are of the right form,
     e.g., that set names are lowercased non-infix. *)

let rec annotateExpr cntxt = function 
    Ident nm -> 
      begin
	let nm' = applyContextSubst cntxt nm 
	in
	  match lookupId cntxt nm' with
              CtxProp (_, pty) -> ResProp(L.Atomic(L.longname_of_name nm'),
					 pty)
	    | CtxSet  (_, knd) -> ResSet(L.Basic(L.set_longname_of_name nm'),
		 			knd)
	    | CtxTerm (ty)  -> ResTerm(L.Var(L.longname_of_name nm'),
				      ty)
	    | CtxModel  thry -> ResModel(L.ModelName(L.model_name_of_name nm),
					thry )
	    | CtxTheory thry -> (print_endline "XXX Do I need to selfify?";
				 ResTheory thry)
	    | CtxUnbound -> tyUnboundError nm
      end

  | MProj (expr1, nm2) as orig_expr ->
      begin
	match annotateModel cntxt orig_expr expr1 with
	    (mdl, L.Theory elems) ->
	      begin
		match searchElems cntxt nm2 orig_expr mdl elems with
		    CtxSet (_,knd) -> ResSet(L.Basic(L.SLN(Some mdl, nm2)), knd)
		  | CtxProp (_,pt) -> ResProp(L.Atomic(L.LN(Some mdl, nm2)), pt)
		  | CtxTerm ty -> ResTerm(L.Var(L.LN(Some mdl, nm2)), ty)
		  | CtxModel thry -> ResModel(L.ModelProj(mdl,nm2), thry)
		  | _ -> raise Impossible
	      end
	  | _ -> notWhatsExpectedInError expr1 "theory of a model" orig_expr
      end


(*
      let (mdl' as whereami, summary, subst) = annotateModel cntxt orig_expr mdl
      in
*)
(*
      in ( match summary with
            Summary_Struct ( _ , items) ->
              (match (peekTypeof' subst items (Some whereami) nm) with
		  None -> tyGenericError ("Unknown component " ^
					     string_of_term orig_trm)
		| Some st -> ( Var ( Some mdl', nm ), st ) )
          | _ -> tyGenericError 
              ( "Term projection from parameterized model in:\n  " ^ 
		  string_of_term orig_trm ) )
*)
  | App(Label label, expr2) as orig_expr ->
      let (trm2', ty2') = annotateTerm cntxt orig_expr expr2
      in 
	ResTerm ( L.Inj(label, Some trm2'),
		  L.Sum[ (label, Some ty2') ] )

  | App (expr1, expr2) as orig_expr ->
      begin
	match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
	  | (ResProp(prp1,pt1), ResTerm(trm2,ty2)) -> 
	      begin
		(* Application of a predicate to a term *)
		match pt1 with
		    L.PropArrow(nm,domty,codpt) -> 
		      begin
			(* Application of a predicate *)
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      let sub = L.insertTermvar L.emptysubst
				            nm trm2'
			      in
				ResProp( L.PApp(prp1, trm2'),
				         L.substProptype sub codpt )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end

                  | L.EquivProp(domty) ->
		      begin
			(* Partial application of an equivalence relation.
			   The result has type domty -> Stable.        *)
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      ResProp( L.PApp(prp1, trm2'),
				       L.PropArrow(S.freshWildName(),
						   domty, L.StableProp) )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end
		  | _ -> wrongPropTypeError expr1 pt1 "predicate" orig_expr
	      end

	  | (ResSet(st1,knd1), ResTerm(trm2,ty2)) ->
	      begin
		(* Application of a parameterized set to a term *)
		match knd1 with
		    L.KindArrow(nm,domty,codknd) -> 
		      begin
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      let sub = L.insertTermvar L.emptysubst nm trm2'
			      in ResSet( L.SApp(st1, trm2'),
				         L.substKind sub codknd )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end
		  | _ -> wrongKindError expr1 knd1 "arrow" orig_expr 
	      end
		
	  | (ResTerm(trm1,ty1), ResTerm(trm2,ty2)) -> 
	      begin
		(* Application of a term to a term *)
		match coerceFromSubset cntxt trm1 ty1 with
		    (trm1', L.Exp(nm,domty,codty)) ->
		      begin
			match coerce cntxt trm2 ty2 domty with
			    Some trm2' ->
			      let sub = L.insertTermvar L.emptysubst nm trm2'
			      in
				ResTerm( L.App(trm1', trm2'),
				         L.substSet sub codty )
			  | None -> tyMismatchError expr2 domty ty2 orig_expr
		      end
		  | _ -> wrongTypeError expr1 ty1 "function" orig_expr
	      end

	  | (ResModel(mdl1,thry1), ResModel(mdl2,thry2)) ->
	      begin
		(* Appliation of a functor to an argument. *)
		raise Unimplemented
	      end


	  | _ -> tyGenericError ("Invalid application " ^ 
				    S.string_of_expr orig_expr) 
      end

  | Lambda (binding1, expr2) as orig_expr ->
      begin
	let (cntxt', lbnds1) = annotateBinding cntxt orig_expr binding1
	in  
	  match annotateExpr cntxt' expr2 with
	      ResProp(prp2,pt2) ->
		(* Defining a predicate *)
		ResProp ( List.fold_right L.fPLambda   lbnds1 prp2,
			  List.fold_right L.fPropArrow lbnds1 pt2 )

	    | ResSet (st2,knd2) ->
		(* Defining a family of sets *)
		ResSet ( List.fold_right L.fSLambda   lbnds1 st2,
			 List.fold_right L.fKindArrow lbnds1 knd2 )

	    | ResTerm(trm2,ty2) -> 
		(* Defining a function term *)
		ResTerm ( List.fold_right L.fLambda lbnds1 trm2,
		  	  List.fold_right L.fExp    lbnds1 ty2 )

	    | _ -> tyGenericError("Invalid body in " ^
				     S.string_of_expr orig_expr)
      end

  | Arrow (nm, expr1, expr2) as orig_expr ->
      begin
	let (cntxt, nm) = renameBoundVar cntxt nm
        in let badDomainError() = 
	  if (isWild nm) then
	    notWhatsExpectedInError expr1 
	      "proper type or proposition" orig_expr
	  else
	    notWhatsExpectedInError expr1 
	      "proper type" orig_expr
	in
	  match annotateExpr cntxt expr1 with
	    | ResPropType _ ->
		noHigherOrderLogicError orig_expr
	    | ResKind _ ->
		noPolymorphismError orig_expr
	    | ResTerm _ | ResSet (_, L.KindArrow _) 
	    | ResModel _ | ResTheory _ 
            | ResProp (_, (L.PropArrow _ | L.EquivProp _) ) ->
		badDomainError()
	    | ResProp (prp1, (L.Prop | L.StableProp)) -> 
		if (isWild nm) then
		  begin
		    (* Typechecking an implication *)
		    let (prp2, stab2) = 
		      annotateProperProp cntxt orig_expr expr2 
		    in 
		      (* case.pdf: "Almost negative formulas [are]
			 built from any combination of 
			 /\, ->, forall, =, and those
                         bas ic predicates known to be stable, but 
			 \/ and exists are only allowed to appear 
			 on the left side of a -> ..." *) 
		      ResProp ( L.Imply(prp1, prp2),
			        stab2 )
		  end
		else
		  badDomainError()
            | ResSet (ty1, L.KindSet) ->
		begin
		  (* Typechecking a Pi *)
		  let cntxt' = insertTermVariable cntxt nm ty1
		  in match annotateExpr cntxt' expr2 with
		      ResSet(st2, knd2) -> 
			(* Typechecking a dependent type of a function *)
			ResSet ( L.Exp (nm, ty1, st2),
			         L.KindSet )

                    | ResPropType(pt2) -> 
			(* Typechecking a dependent type of a proposition *)
			ResPropType( L.PropArrow(nm, ty1, pt2) )

		    | ResKind(knd2) ->
			(* Typechecking a dependent kind of a family of sets *)
			ResKind( L.KindArrow(nm, ty1, knd2) )

		    | _ ->
			notWhatsExpectedInError expr2
			  "set, proposition-type, or kind" orig_expr
		end
      end

  | Constraint (expr1, expr2) as orig_expr ->
      begin
	match (annotateExpr cntxt expr1, annotateExpr cntxt expr2) with
	    (ResTerm(trm1,ty1), ResSet(ty2,L.KindSet)) ->
	      begin
		(* Typecheck a term constrained by a type *)
		match coerce cntxt trm1 ty1 ty2 with
		    Some trm1' -> ResTerm(trm1', ty2)
		  | _ -> tyMismatchError expr1 ty2 ty1 orig_expr
	      end

	  | (ResProp(prp1,pt1), ResPropType(pt2)) ->
	      (* Typecheck a proposition constrained by a prop. type *)
	      if (subPropType cntxt pt1 pt2) then
		ResProp( prp1, pt2 )
	      else
		propTypeMismatchError expr1 pt2 pt1 orig_expr 

	  | (ResSet(st1,knd1), ResKind(knd2)) ->
	      (* Typecheck a set constrained by a kind *)
	      if (subKind cntxt knd1 knd2) then
		ResSet(st1, knd2)
	      else
		kindMismatchError expr1 knd2 knd1 orig_expr
 
          | _ -> tyGenericError 
		 ("Incoherent constraint " ^ string_of_expr orig_expr)
      end

  | Empty -> ResSet(L.Empty, L.KindSet)

  | Unit  -> ResSet(L.Unit, L.KindSet)

  | Product sbnds  as orig_expr ->
      begin
	(* A [possibly dependent] type for a tuple. *)
	let rec loop cntxt = function
	    [] -> []
	  | (nm,expr) :: rest ->     
              let (cntxt', lbnd) = 
		annotateSimpleBinding cntxt orig_expr (nm, Some expr)
	      in 
		lbnd :: loop cntxt' rest
	in    
	  ResSet(L.Product (loop cntxt sbnds), L.KindSet) 
      end

  | Sum lsos as orig_expr ->
      begin
      (* We assume that the parser has figured out this is really a sum type
         and not a use of the term operator +. *)
	let process = function 
	    (lbl, None) -> (lbl, None)
	  | (lbl, Some expr) -> (lbl, Some (annotateType cntxt orig_expr expr))
	in
	  ResSet( L.Sum( List.map process lsos),
		  L.KindSet )
      end

  | Subset (sbnd1, expr2) as orig_expr ->
      begin
	let (cntxt', lbnd1) = annotateSimpleBinding cntxt orig_expr sbnd1
	in
	  match annotateExpr cntxt' expr2 with
	      ResProp(prp2', (L.Prop | L.StableProp)) ->
		ResSet( L.Subset(lbnd1, prp2'), L.KindSet )
	    | _ ->
		notWhatsExpectedInError expr2 "proposition" orig_expr
      end
	
  | Quotient (expr1, expr2) as orig_expr -> 
      begin
	let badRelation() =
	  notWhatsExpectedInError expr2 "equivalence relation" orig_expr
	in
	  match (annotateExpr cntxt expr1) with
	      ResSet(ty1, L.KindSet) -> 
		(* Quotient of a set *)
		begin
		  match annotateProp cntxt orig_expr expr2 with 
		      (prp2, L.EquivProp(domty2)) ->
			if (subSet cntxt ty1 domty2) then
			  ResSet( L.Quotient (ty1, prp2),
			        L.KindSet )
			else
			  notEquivalenceOnError expr2 expr1
		    | _ -> badRelation()
		end
		  
	    | ResTerm(trm1, ty1) ->
		(* Quotient [equivalence class] of a term *)
		begin
		  match annotateProp cntxt orig_expr expr2 with 
		      (prp2, L.EquivProp(domty2)) ->
			begin
			  match coerce cntxt trm1 ty1 domty2 with
			      Some trm1' -> 
				ResTerm( L.Quot (trm1', prp2),
			                 L.Quotient (domty2, prp2) )
			    | _ -> notEquivalenceOnError expr2 expr1
			end
		    | _ -> badRelation()
		end
		   
	    | _ -> 
		notWhatsExpectedInError expr1 "term or proper set" orig_expr
      end

  | Rz (expr1) as orig_expr ->
      begin
	match annotateExpr cntxt expr1 with
	    ResSet(ty1, L.KindSet) -> 
	      (* Set of realizers for this set *)
	      ResSet (L.Rz ty1, L.KindSet)

	  | ResTerm(trm1, ty1) ->
	      begin
		(* Value realized by this term(?) *)
		match coerceFromSubset cntxt trm1 ty1 with
		    (trm1', L.Rz ty1') ->
		      ResTerm( L.RzQuot trm1', ty1')
		  | _ -> wrongTypeError expr1 ty1 "realizer" orig_expr
	      end			     

	  | _ -> 
	      notWhatsExpectedInError expr1 "realizer or proper set" orig_expr
      end

  | Set -> ResKind (L.KindSet)

  | Prop -> ResPropType (L.Prop)

  | Stable -> ResPropType (L.StableProp)

  | Equiv expr as orig_expr ->
      let equiv_domain_type = annotateType cntxt orig_expr expr
      in
	ResPropType ( L.EquivProp equiv_domain_type )

  | EmptyTuple -> ResTerm ( L.EmptyTuple, L.Unit )

  | Tuple exprs as orig_expr ->
      let pairs = List.map (annotateTerm cntxt orig_expr) exprs
      in let (trms',tys') = List.split pairs
      in let addName t = (S.freshWildName(), t)
      in 
	   ResTerm( L.Tuple trms', 
		    L.Product (List.map addName tys') )

  | Proj(n1, expr2) as orig_expr ->
      begin
	let    (trm2',  ty2' ) = annotateTerm cntxt orig_expr expr2
	in let (trm2'', ty2'') = coerceFromSubset cntxt trm2' ty2'
	in
	  match ty2'' with 
	      L.Product nmtys ->
		let rec loop k subst = function
		    [] -> raise Impossible
		  | (nm,ty) :: rest ->
		      if (k = n1) then
			ResTerm ( L.Proj(n1, trm2''), 
			          L.substSet subst ty )
		      else
			loop (k+1) 
			  (L.insertTermvar subst nm (L.Proj(k,trm2''))) rest
		in let len = List.length nmtys
		in 
		     if ( (n1 < 0) || (n1 >= len) ) then
		       tyGenericError ("Projection " ^ string_of_int n1 ^ 
					  " out of bounds in " ^
				          string_of_expr orig_expr)
		     else 
		       loop 0 L.emptysubst nmtys
			 
	    | _ -> wrongTypeError expr2 ty2' "tuple"  orig_expr
      end

  | Label label -> ResTerm ( L.Inj(label, None),
			     L.Sum[(label, None)] )

  | Case (expr1, arms2) as orig_expr -> 
      begin
	(* Typecheck the term being cased on *)
	let (trm1, ty1) = annotateTerm cntxt orig_expr expr1 

        (* Typecheck each arm individually *)	  
	in let annotateArm = function
	    (lbl, None, expr3) -> 
	      (lbl, None, annotateExpr cntxt expr3, expr3)
	  | (lbl, Some sbnd, expr3) ->
	      let (cntxt', lbnd) = annotateSimpleBinding cntxt orig_expr sbnd
	      in (lbl, Some lbnd, annotateExpr cntxt' expr3, expr3)
	in let arms2' = List.map annotateArm arms2

	(* Check that there are no duplicate labels *)
	in let lbls = List.map (fun (l,_,_) -> l) arms2
	in let _ = if (noDuplicates lbls) then () else
	    tyGenericError ("There are duplicate labels in " ^ 
			       string_of_expr orig_expr)

        (* Check that the bindings match the term being cased on. *)
	in let rec createSumtype = function
	    [] -> []
	  | (lbl, None,_,_)::rest -> (lbl,None) :: createSumtype rest
	  | (lbl, Some(_,ty),_,_)::rest -> (lbl, Some ty) :: createSumtype rest
	in let armty = L.Sum (createSumtype arms2')
	in let _ = if (eqSet cntxt armty ty1) then
	              ()
	            else
	              tyMismatchError expr1 armty ty1 orig_expr

	in 
	     match arms2' with
		 (_,_,ResTerm _,_)::_ ->
		   begin
		     (* Term-level Case *)
		     let rec process = function
		         [] -> ([], [])
		       | (lbl, None, ResTerm(trm3,ty3), _)::rest -> 
			   let (arms, tys) = process rest
			   in ( (lbl,None,trm3) :: arms, ty3 :: tys )
		       | (lbl, (Some (nm,_) as bopt), ResTerm(trm3,ty3), expr3) :: rest ->
			   if (NameSet.mem nm (L.fnSet ty3)) then
			     cantElimError expr3
			   else
			     let (arms, tys) = process rest
			     in ( (lbl,bopt,trm3) :: arms, ty3 :: tys )
		       | (lbl,_,_,_)::_ -> tyGenericError 
			          ("Bad case arm " ^ string_of_label lbl ^
				      " in " ^ string_of_expr orig_expr)
		     in let (arms, tys) = process arms2'
		     in let ty = joinTypes cntxt tys
		     in 
			  ResTerm(L.Case (trm1, arms), ty)
		   end
	       | (_,_,ResProp _, _)::_ ->
		   begin
		     (* Prop-level Case *)
		     raise Unimplemented
		   end
	       | _::_ ->
		   tyGenericError 
		     ("Invalid first case in " ^ string_of_expr orig_expr)
	       | _ ->
		   tyGenericError
		     ("Case must have at least one arm in " ^ 
			 string_of_expr orig_expr)
      end

  | RzChoose(sbnd1, expr2, expr3) as orig_expr ->
      begin
	let (trm2, ty2) = annotateTerm cntxt orig_expr expr2

	in let (cntxt', ((nm1,ty1) as lbnd1)) = 
	      (* Careful with error messages...nm1 might have been renamed *)
	      annotateSimpleBindingWithDefault 
		cntxt orig_expr (L.Rz ty2) sbnd1
	in let (trm3, ty3) = annotateTerm cntxt' orig_expr expr3 
	in
	     match hnfSet cntxt ty1 with
		 L.Rz ty1' ->
		   begin
		     match  coerce cntxt trm2 ty2 ty1'  with
			 Some trm2' -> 
			   if NameSet.mem nm1 (L.fnSet ty3) then
			     cantElimError orig_expr
			   else 
			     ResTerm ( L.RzChoose (lbnd1, trm2', trm3, ty3),
				     ty3 )
		       | None -> 
			   tyMismatchError expr2 ty1' ty2 orig_expr
		   end
	       | _ -> 
		   tyGenericError 
		     ("The bound variable in the construct " ^ 
			 string_of_expr orig_expr ^ 
		         "should have a realizer type, but here it has type " ^ 
		         L.string_of_set ty1)
      end

  | Choose _ -> 
      raise Unimplemented

  | Subin(expr1, expr2) as orig_expr ->
      begin
        (* Injection into a subset; incurs an obligation *)
	let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let ty2       = annotateType cntxt orig_expr expr2
	in  
	     match (hnfSet cntxt ty2) with
		 L.Subset ((_,domty2), _) -> 
		   begin
		     match coerce cntxt trm1 ty1 domty2 with
			 Some trm1' ->
			   ResTerm ( L.Subin ( trm1', ty2 ),
				     ty2 )
		       | None ->
			   tyMismatchError expr1 domty2 ty1 orig_expr
		   end
	       | _ ->
		   notWhatsExpectedInError expr2 "subset type" orig_expr
      end

  | Subout(expr1, expr2) as orig_expr ->
      begin
	let  (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let ty2       = annotateType cntxt orig_expr expr2
	in  
	     match (hnfSet cntxt ty1) with
		 L.Subset _ -> 
		   begin
		     match coerce cntxt trm1 ty1 ty2 with
			 Some trm1' ->
			   ResTerm ( L.Subout ( trm1', ty2),
				   ty2)
		       | None -> 
			   tyGenericError
			     ("Could not coerce the subset term " ^ 
				 string_of_expr expr1 ^ " to type " ^
				 string_of_expr expr2 ^ " in " ^ 
			         string_of_expr orig_expr)
		   end
	       | _ ->
		   notWhatsExpectedInError expr1 "term in a subset" orig_expr
      end

  | Let(sbnd1, expr2, expr3) as orig_expr ->
      begin
	(* Right now, let is for terms only *)
	let (trm2, ty2) = annotateTerm cntxt orig_expr expr2

	in let (cntxt', (nm1,ty1)) = 
	  (* Careful with error messages; nm1 might have been renamed *)
	  annotateSimpleBindingWithDefault cntxt orig_expr ty2 sbnd1

          (* NB: If we ever start putting term definitions into the
             context, we'd need to do it here, since
             annotateSimpleBinding doesn't know the definition... *)
	in let (trm3, ty3) = annotateTerm cntxt' orig_expr expr3
	in 
	     begin
	       match coerce cntxt trm2 ty2 ty1 with
		   Some trm2' -> 
		     if NameSet.mem nm1 (L.fnSet ty3) then
		       cantElimError orig_expr
		     else 
		       ResTerm ( L.Let ((nm1,ty1), trm2', trm3, ty3),
		               ty3 )
		 | None -> 
		     tyMismatchError expr2 ty1 ty2 orig_expr
	     end
      end

  | The(sbnd1, expr2) as orig_expr ->
      let (cntxt', ((nm1,ty1) as lbnd1) ) = 
	(* Careful with error messages; nm1 might have been renamed *)
	annotateSimpleBinding cntxt orig_expr sbnd1
      in let (prp2,_) = annotateProperProp cntxt' orig_expr expr2
      in
	   ResTerm ( L.The (lbnd1, prp2),
		       ty1 )

  | False -> ResProp(L.False, L.StableProp)

  | True -> ResProp(L.True, L.StableProp)

  | And exprs as orig_expr ->
      begin
	let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	in let (prps, pts) = List.split pairs
	in 
	     ResProp ( L.And prps,
		       L.joinProperPropTypes pts )
      end

  | Or exprs as orig_expr ->
      begin
	let pairs = List.map (annotateProperProp cntxt orig_expr) exprs
	in let (prps, pts) = List.split pairs
	in 
	     ResProp ( L.Or prps,
		       L.Prop )
      end

  | Not expr as orig_expr ->
      let (prp, pt) = annotateProperProp cntxt orig_expr expr
      in
	ResProp ( L.Not prp, pt )

  | Iff (expr1,expr2) as orig_expr ->
      begin
	let    (prp1, pt1) = annotateProperProp cntxt orig_expr expr1
	in let (prp2, pt2) = annotateProperProp cntxt orig_expr expr2
	in 
	     ResProp ( L.Iff(prp1, prp2),
		       L.joinProperPropTypes [pt1; pt2] )
      end

  | Equal (expr1, expr2) as orig_expr ->
      begin
	let    (trm1, ty1) = annotateTerm cntxt orig_expr expr1
	in let (trm2, ty2) = annotateTerm cntxt orig_expr expr2
	in let ty = joinTypes cntxt [ty1; ty2]
	in 
	     ResProp( L.Equal(ty, trm1, trm2),
		      L.StableProp )
      end

  | Forall (bnd1, expr2) as orig_expr ->
      let (cntxt', lbnds1) = annotateBinding cntxt orig_expr bnd1
      in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
      in let forallprp = 
	List.fold_right (fun lbnd p -> L.Forall(lbnd, p)) lbnds1 prp2
      in
	   ResProp ( forallprp, stab2 )
	     
  | Exists (bnd1, expr2) as orig_expr ->
      let (cntxt', lbnds1) = annotateBinding cntxt orig_expr bnd1
      in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
      in let existsprp = 
	List.fold_right (fun lbnd p -> L.Exists(lbnd, p)) lbnds1 prp2
      in
	   ResProp ( existsprp, L.Prop )

  | Unique (bnd1, expr2) as orig_expr ->
      let (cntxt', lbnds1) = annotateBinding cntxt orig_expr bnd1
      in let (prp2, stab2) = annotateProperProp cntxt' orig_expr expr2
      in let uniqueprp = 
	List.fold_right (fun lbnd p -> L.Unique(lbnd, p)) lbnds1 prp2
      in
	   ResProp ( uniqueprp, L.Prop )
	     
and annotateTerm cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResTerm(trm, ty) -> (trm, ty)
    | _ -> notWhatsExpectedInError expr "term" surrounding_expr)
    
and annotateSet cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResSet(st, knd) -> (st, knd)
    | _ -> notWhatsExpectedInError expr "set" surrounding_expr)
    
and annotateType cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResSet(st, L.KindSet) -> st
    | _ -> notWhatsExpectedInError expr "proper type" surrounding_expr)
    
and annotateProp cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResProp(prp, pt) -> (prp, pt)
    | _ -> notWhatsExpectedInError expr "proposition" surrounding_expr)
    
and annotateProperProp cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResProp(prp, ((L.Prop | L.StableProp) as pt)) -> (prp, pt)
    | ResProp _ -> 
	notWhatsExpectedInError expr "proper proposition" surrounding_expr
    | _ -> 
	notWhatsExpectedInError expr "proposition" surrounding_expr)

and annotateKind cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResKind k -> k
    | _ -> notWhatsExpectedInError expr "kind" surrounding_expr)


and annotateProptype cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResPropType k -> k
    | _ -> notWhatsExpectedInError expr "proposition-type" surrounding_expr)
    
and annotateModel cntxt surrounding_expr expr = 
  (match annotateExpr cntxt expr with
      ResModel(mdl, thry) -> (mdl, thry)
    | _ -> notWhatsExpectedInError expr "model" surrounding_expr)


(* annotateBinding: context -> S.expr -> S.binding -> L.binding list
*)
and annotateBinding cntxt surrounding_expr binders =
  (* Loop over variable-list/type pairs *)
  let rec bLoop cntxt' = function
      []                    -> (cntxt', [])
    | ([],_)::rest          -> bLoop cntxt' rest
    | (nms, expropt)::rest ->

	(* Now loop to create this pair's bindings and extended context *)
	let rec nLoop = function 
	    [] -> (cntxt', [])
	  | n::ns -> 
	      let (cntxt'', lbnds) = nLoop ns
	      in let ty = 
		begin
		  (* Figure out the type for variable.
		     NB: Check for an Implicit declaration has to happen.
		         *before* the variable is renamed! 
                  *)
		  match expropt with
		      None -> 
			begin
			  (* No type annotation; hope the variable's Implicit *)
			  match lookupImplicit cntxt n with
			      ImpTermvar ty -> ty
			    | _ -> noTypeInferenceInError n surrounding_expr
			end
		    | Some expr -> 
			annotateType cntxt surrounding_expr expr
		end 
	      in let (cntxt'', n) = renameBoundVar cntxt'' n
	      in (insertTermVariable cntxt'' n ty, (n,ty) :: lbnds)
	in let (cntxt'', lbnds) = nLoop nms

	(* Now handle the rest of the pairs *)
	in let (cntxt_final, lbnds_rest) = bLoop cntxt'' rest

	(* Combine results *)
	in
	     (cntxt_final, lbnds @ lbnds_rest)
  in
    bLoop cntxt binders

(*
   annotateSimpleBinding : context -> S.expr -> S.binding1 -> L.binding
*)
and annotateSimpleBinding cntxt surrounding_expr (nm, expropt) =
  begin
    match annotateBinding cntxt surrounding_expr [([nm], expropt)] with
	(cntxt', [lbnd]) -> (cntxt', lbnd)
      | _ -> raise Impossible
  end

(** Like annotatebinding, but takes a (previously annotated) default set to
    be used if one is not implicitly specified in the binding or
    specified in an implicit declaration.

    Raises an error (indirectly) if the set in the binding is ill-formed
*)

and annotateSimpleBindingWithDefault cntxt surrounding_expr default_ty =
  function
      (nm, None) -> 
	begin
	  (* There's a reasonable argument to say that the default_ty
             should always be used, since it's most likely to get the
             imput to typecheck.  On the other hand, if you say that n
             ranges over integers unless otherwise specified, and you
             bind it to a boolean, an error seems likely... *)
	  let ty = 
	    match (lookupImplicit cntxt nm) with
		ImpTermvar implicit_ty -> implicit_ty
	      | _                      -> default_ty
	  in let (cntxt, nm) = renameBoundVar cntxt nm
	  in let cntxt' = insertTermVariable cntxt nm ty
	  in 
	       (cntxt',  (nm, ty) )
	end

    | (nm, Some expr) -> 
	let ty = annotateType cntxt surrounding_expr expr
	in let (cntxt, nm) = renameBoundVar cntxt nm
	in 
	  (* NB:  No checking of binding annotation vs default! *)
	  (insertTermVariable cntxt nm ty,  (nm, ty) )

(* We explicitly do _not_ rename bound variables here, as they will
   eventually become labels.  Thus, a Definition or a Value declaration
   is not permitted to shadow an earlier definition, which can only
   be an earlier top-level or theory-element definition.
*)

and annotateTheoryElem cntxt = function
    Definition(nm1, expropt2, expr3) as orig_elem -> 
      begin
	match annotateExpr cntxt expr3 with
	    ResTerm(trm3, ty3) ->
	      begin
		(* Definition of a term constant *)
		match expropt2 with
		    None       -> [ L.Let_term(nm1, ty3, trm3) ] 
		  | Some expr2 ->
		      let ty2 = annotateType cntxt (Ident nm1) expr2 
		      in 
			match (coerce cntxt trm3 ty3 ty2) with
			    Some trm3' -> [ L.Let_term(nm1, ty2, trm3') ]
			  | _ -> tyMismatchError expr3 ty2 ty3 (Ident nm1)
	      end

	  | ResSet(st3, k3) ->
	      begin
		(* Definition of a set constant *)
		match expropt2 with
		    None       -> [ L.Let_set(nm1, k3, st3) ]
		  | Some expr2 ->
		      let k2 = annotateKind cntxt (Ident nm1) expr2
		      in
			if (subKind cntxt k3 k2) then
			  [ L.Let_set(nm1, k2, st3) ]
			else
			  kindMismatchError expr3 k2 k3 (Ident nm1)
	      end

	  | ResProp(prp3, pt3) ->
	      begin
		(* Definition of a propositional constant *)
		match expropt2 with
		      None       -> [ L.Let_predicate(nm1, pt3, prp3) ]
		  | Some expr2 ->
		      let pt2 = annotateProptype cntxt (Ident nm1) expr2 
		      in
			if (subPropType cntxt pt3 pt2) then
			  [ L.Let_predicate(nm1, pt2, prp3) ]
			else
			  propTypeMismatchError expr3 pt2 pt3 (Ident nm1)
	      end

	  | ResPropType _ | ResKind _ | ResModel _ | ResTheory _ ->
	      tyGenericError 
		("Invalid right-hand-side in " ^
		    string_of_theory_element orig_elem)
      end

  | Comment c -> [L.Comment c]

  | Include _ -> raise Unimplemented

  | Implicit _ -> raise Impossible (* Implicits were already removed *)

  | Value (sentence_type, values) as orig_elem ->
      let process = function
	  (nm, ResSet(ty, L.KindSet)) -> L.Value(nm, ty)
	| (nm, ResPropType pt)        -> L.Predicate (nm, pt)
	| (nm, ResKind k)             -> L.Set(nm, k)
	| (nm, ResTheory thry)        -> L.Model(nm, thry)
        | (nm, ResProp(prp, (L.Prop | L.StableProp))) ->
	    L.Sentence(sentence_type, nm, [], [], prp)
        | (nm, (ResSet _ | ResTerm _ | ResProp _ | ResModel _)) -> 
	    tyGenericError 
	      ("Invalid classifier for " ^ string_of_name nm ^
		  " in " ^ string_of_theory_element orig_elem)
      in let rec loop = function
	      [] -> []
            | (nms,expr)::rest ->
		let res = annotateExpr cntxt expr 
		in
		  (List.map (fun nm -> process(nm, res)) nms) @ 
		    (* XXX: ought to extend the context, since in Coq
		          Parameter (a : Set) (x : a).
		       is perfectly legal.
                    *)
		    (loop rest)
      in 
	   loop values

let rec updateContextForElem cntxt = function
  | L.Set           (nm, knd)     -> insertSetVariable  cntxt nm knd None
  | L.Let_set       (nm, knd, st) -> insertSetVariable  cntxt nm knd (Some st)
  | L.Predicate     (nm, pt)      -> insertPropVariable cntxt nm pt None
  | L.Let_predicate (nm, pt, prp) -> insertPropVariable cntxt nm pt (Some prp)
  | L.Value         (nm, st)      -> insertTermVariable cntxt nm st
  | L.Let_term      (nm, st, _)   -> insertTermVariable cntxt nm st
  | L.Model         (nm, thry)    -> insertModelVariable cntxt nm thry
  | L.Sentence _  -> cntxt
  | L.Comment _   -> cntxt

let updateContextForElems cntxt elems = 
  List.fold_left updateContextForElem cntxt elems

let rec annotateTheoryElems cntxt = function
    [] -> (cntxt, [])

  | Implicit(names, st)::rest ->    (** Eliminated during inference *)
      let    ty = annotateType cntxt (S.False (*XXX*)) st 
      in let cntxt' = insertImplicits cntxt names ty
      in 
	   annotateTheoryElems cntxt' rest

  | elem :: rest ->
      let    lelems1 = annotateTheoryElem cntxt elem
      in let cntxt'  = updateContextForElems cntxt lelems1
      in let (cntxt_final, lelems2) = annotateTheoryElems cntxt' rest
      in (cntxt_final, lelems1 @ lelems2)
 
let rec annotateTheory cntxt = function
    Theory elems -> 
      let (_, lelems) = annotateTheoryElems cntxt elems
      in  L.Theory lelems 

  | TheoryName nm -> 
      begin
	match lookupId cntxt nm with
	    CtxTheory thry -> thry
	  | CtxUnbound -> tyUnboundError nm
	  | _ -> tyGenericError 
	      ("The name " ^ string_of_name nm ^ " is not a theory.")
      end

  | TheoryFunctor ((nm, sthry1), sthry2) -> 
      begin
	let thry1 = annotateTheory cntxt sthry1
	in let (cntxt, nm) = renameBoundVar cntxt nm
	in let cntxt' = insertModelVariable cntxt nm thry1
	in let thry2 = annotateTheory cntxt' sthry2
	in
	     L.TheoryFunctor ((nm, thry1), thry2)
      end

  | TheoryApp _ ->
      raise Unimplemented

let annotateToplevel cntxt = function
    TopComment c -> (cntxt, L.TopComment c)

  | Theorydef(nm, thry) ->
      let lthry = annotateTheory cntxt thry
      in (insertTheoryVariable cntxt nm lthry, 
	  L.Theorydef(nm, lthry))

  | TopModel (nm, thry) -> 
      let lthry = annotateTheory cntxt thry
      in (insertModelVariable cntxt nm lthry,
	 L.TopModel(nm, lthry))

let rec annotateToplevels cntxt = function
    [] -> (cntxt, [])
  | tl::tls -> 
      let    (cntxt',  tl' ) = annotateToplevel cntxt tl
      in let (cntxt'', tls') = annotateToplevels cntxt' tls
      in (cntxt'', tl'::tls')

