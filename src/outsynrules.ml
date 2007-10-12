open Name
open Outsyn

(***************************)
(** {2 The Typing Context} *)
(***************************)

(* We must maintain different lookup tables and renamings for each
   "flavor" of identifier because they live in distinct ML namespaces. 

   Any pass that goes through and calls these renaming functions for
   bound variables is then obligated to apply the renaming to uses
   of those variables (in the base cases) 

   Currently we don't bother keeping track of the proptypes of
   propositional variables (since it never comes up), and we 
   don't bother keeping a renaming for signature variables
   (since there are no alpha-varying binders for these in the
   syntax).

*)
type context = {termvars: ty NameMap.t;          (* Type of a term variable *)
		typevars: (ty option) NameMap.t; (* Defn (if any) of ty. var.*)
		modulvars: signat NameMap.t;     (* Signature of a mod. var  *)
		signatvars: signat NameMap.t;    (* Defn of a sig. variable *)

		termrenaming: name NameMap.t;    (* Renaming of term vars *)
		typerenaming: name NameMap.t;    (* Renaming of type vars *)
		modulrenaming: name NameMap.t;   (* Renaming of mod. vars *)
		proprenaming: name NameMap.t;    (* Renaming of prop. vars *)

	        facts: proposition list          (* A list of true props *)
               }

let emptyContext = 
  {termvars   = NameMap.empty;   
   typevars   = NameMap.empty;   
   modulvars  = NameMap.empty;  
   signatvars = NameMap.empty;

   termrenaming  = NameMap.empty;
   typerenaming  = NameMap.empty;
   modulrenaming = NameMap.empty;
   proprenaming  = NameMap.empty;

   facts = []}

(* Displays the variable bindings in the context.
   For now, does not display renamings or the list of facts 
*)
let displayRenaming map = 
  begin
    let showPair nm nm' =
      print_string ("[" ^ string_of_name nm ^ "~>" ^ string_of_name nm' ^ "]")
    in
      NameMap.iter showPair map;
      print_endline "";
  end

let displayContext ctx = 
  begin
    NameMap.iter 
      (fun nm ty -> 
	print_endline("val " ^ string_of_name nm ^ ":" ^ string_of_ty ty)) 
      ctx.termvars;
    displayRenaming ctx.termrenaming;
    NameMap.iter 
      (fun nm tyopt -> 
	print_endline("type " ^ string_of_name nm ^ 
		      (match tyopt with 
			None -> "" | 
			Some ty -> "=" ^ string_of_ty ty))) 
      ctx.typevars;
    displayRenaming ctx.typerenaming;
    NameMap.iter 
      (fun nm sg -> 
	print_endline("module " ^ string_of_name nm ^ " : " ^ 
		      string_of_signat sg)) 
      ctx.modulvars;
    displayRenaming ctx.modulrenaming;
    NameMap.iter 
      (fun nm sg -> 
	print_endline("signature " ^ string_of_name nm ^ " = " ^ 
		      string_of_signat sg)) 
      ctx.signatvars;
    print_endline "and finally, proprenaming:";
    displayRenaming ctx.proprenaming;
  end


(***************)
(** {3 Lookup} *)
(***************)

let notFound sort nm = 
  failwith ("Unbound " ^ sort ^ " variable " ^ string_of_name nm)



(* 
   lookupTermVariable   : context -> name -> ty
   lookupTypeVariable   : context -> name -> ty option
   lookupModulVariable  : context -> name -> signat
   lookupSignatVariable : context -> name -> signat
*)

let lookupTermVariable ctx nm = 
   try (NameMap.find nm ctx.termvars) with 
       Not_found -> notFound "term" nm

let lookupTypeVariable ctx nm = 
   try (NameMap.find nm ctx.typevars) with 
       Not_found -> notFound "type" nm

let lookupModulVariable ctx nm = 
   try (NameMap.find nm ctx.modulvars) with 
       Not_found -> notFound "modul" nm

let lookupSignatVariable ctx nm = 
   try (NameMap.find nm ctx.signatvars) with 
       Not_found -> notFound "signat" nm

(******************)
(** {3 Insertion} *)
(******************)

let insertTermVariable ctx nm ty =
  if NameMap.mem nm ctx.termvars then
    failwith ("Outsyn: shadowing of term variable " ^ (string_of_name nm))
  else
    { ctx with termvars = NameMap.add nm ty ctx.termvars }

let insertTypeVariable ctx nm ty =
  if NameMap.mem nm ctx.typevars then
    failwith ("Outsyn: shadowing of type variable " ^ (string_of_name nm))
  else
  { ctx with typevars = NameMap.add nm ty ctx.typevars }

let insertTypeVariables ctx nms def =
  let defs = List.map (fun _ -> def) nms
  in
     List.fold_left2 insertTypeVariable ctx nms defs

let insertPropVariable ctx _ _ = 
  (* We don't keep track of propositional variables *)
  ctx
  

(** Other insertion functions defined below (after normalization):

   insertModulVariable : context -> name -> signat -> context
   insertSignatVariable: context -> name -> signat -> context

*)

(************************************)
(** {3 Renaming of Bound Variables} *)
(************************************)

let addToRenaming map oldnm newnm =
    NameMap.add oldnm newnm map

let addListToRenaming map oldnms newnms =
  List.fold_left2 addToRenaming map oldnms newnms

(* Stolen from logicrules.ml *)
let renameBoundTermVar ctx nm =
  let nm' = refresh nm in
    ({ctx with termrenaming = addToRenaming ctx.termrenaming nm nm'}, nm')

let renameBoundTermVars ctx nms =
  let nms' = refreshList nms in
    ({ctx with termrenaming = 
        addListToRenaming ctx.termrenaming nms nms'}, nms')

let renameBoundTypeVar ctx nm =
  let nm' = refresh nm in
    ({ctx with termrenaming = addToRenaming ctx.typerenaming nm nm'}, nm')

let renameBoundTypeVars ctx nms = 
  mapWithAccum renameBoundTypeVar ctx nms

let renameBoundModulVar ctx nm =
  let nm' = refresh nm in
    ({ctx with termrenaming = addToRenaming ctx.modulrenaming nm nm'}, nm')

let renameBoundPropVar ctx nm =
  let nm' = refresh nm in
    ({ctx with proprenaming = addToRenaming ctx.proprenaming nm nm'}, nm')
  
let rec renamePattern ctx pat = 
  match pat with
    WildPat -> (ctx, pat)
  | VarPat nm -> 
      failwith "Outsynrules.renamePattern: cannot infer type for VarPat"
  | TuplePat pats ->
      let (ctx', pats') = renamePatterns ctx pats
      in (ctx', TuplePat pats)
  | ConstrPat(_, None) -> (ctx, pat)
  | ConstrPat(lbl, Some (nm,ty)) ->
      let (ctx', nm') = renameBoundTermVar ctx nm
      in let ctx'' = insertTermVariable ctx nm ty
      in (ctx'', ConstrPat(lbl, Some(nm', ty)))

and renamePatterns ctx pats = 
  mapWithAccum renamePattern ctx pats


let applyRenaming map nm = 
  if (NameMap.mem nm map) then
    NameMap.find nm map
  else
    nm

let applyTermRenaming ctx nm =
  applyRenaming ctx.termrenaming nm

let applyTypeRenaming ctx nm =
  applyRenaming ctx.typerenaming nm

let applyModulRenaming ctx nm =
  applyRenaming ctx.modulrenaming nm

let applyPropRenaming ctx nm =
  applyRenaming ctx.proprenaming nm

let applyPropRenamingLN ctx = function
    LN(None, nm) -> LN(None, applyPropRenaming ctx nm)
  | ln -> ln  (* XXX: What if we've renamed modul variables in here??? *)

      

let updateSubstForElem subst mdl = function
    Spec(nm, ValSpec _, _) -> insertTermvar subst nm (Id(LN(Some mdl, nm)))
  | Spec(nm, TySpec _, _) ->  insertTyvar subst nm (NamedTy(LN(Some mdl, nm)))
  | Spec(nm, ModulSpec _, _) -> insertModulvar subst nm (ModulProj(mdl, nm))
  | Spec(nm, SignatSpec _, _) -> subst (* No substituting for signature vars *)
  | _ -> subst

let rec findModulvarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findModulvarInElems: " ^ string_of_name nm)
    | Spec(nm', ModulSpec sg, _) :: _ when nm=nm' -> substSignat subst sg
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts

let rec findTermvarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findTermvarInElems: " ^ string_of_name nm)
    | Spec(nm', ValSpec ([],ty), _) :: _ when nm=nm' -> substTy subst ty
    | Spec(nm', ValSpec (_,ty), _) :: _ when nm=nm' -> 
	failwith ("Outsynrules.findTermvarInElems: polymorphic valspec " ^ 
	  string_of_name nm)
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts

let rec findTypevarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findTypevarInElems: " ^ string_of_name nm)
    | Spec(nm', TySpec tyopt, _) :: _ when nm=nm' -> substTyOption subst tyopt
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts

let rec findSignatvarInElems elts mdl nm =
  let rec loop subst = function
      [] -> failwith ("Outsynrules.findSignatvarInElems: " ^ string_of_name nm)
    | Spec(nm', SignatSpec sg, _) :: _ when nm=nm' -> substSignat subst sg
    | elem :: rest -> loop (updateSubstForElem subst mdl elem) rest
  in loop emptysubst elts


let rec hnfSignat ctx = function
    SignatApp(sg1,mdl2) -> 
      begin
	match hnfSignat ctx sg1 with
	    SignatFunctor((nm,_),sg1b) ->
	      let sg' = substSignat (insertModulvar emptysubst nm mdl2) sg1b
	      in hnfSignat ctx sg'
	  | _ -> failwith "Outsynrules.hnfSignat 1"
      end
  | SignatName nm -> hnfSignat ctx (lookupSignatVariable ctx nm)
  | SignatProj (mdl, nm) ->
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl) with
             Signat elts -> findSignatvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.hnfSignat 2"
       end
  | sg -> sg

and modulToSignat ctx = function
    ModulName nm        -> 
      let nm = applyModulRenaming ctx nm
      in lookupModulVariable ctx nm
  | ModulProj (mdl, nm) ->
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl) with
             Signat elts -> findModulvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.modulToSignat 1"
       end
  | ModulApp (mdl1, mdl2)  -> 
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl1) with
             SignatFunctor((nm,_),sg) -> 
	       let subst = insertModulvar emptysubst nm mdl2
	       in substSignat subst sg
	   | _ -> failwith "Outsynrules.modulToSignat 2"
       end
  | ModulStruct defs -> 
      let rec loop ctx = function
	  [] -> []
	| DefTerm(nm,ty,_) :: rest ->
	    Spec(nm, ValSpec ([], ty), []) :: 
	      loop (insertTermVariable ctx nm ty) rest
	| DefType(nm,ty) :: rest ->
	    Spec(nm, TySpec (Some ty), []) :: 
	      loop (insertTypeVariable ctx nm (Some ty)) rest
	| DefModul(nm,sg,_) :: rest ->
	    Spec(nm, ModulSpec sg, []) :: 
	      loop (insertModulVariable ctx nm sg) rest
        | DefSignat(nm,sg) :: rest ->
	    Spec(nm, SignatSpec sg, []) ::
	      loop (insertSignatVariable ctx nm sg) rest
      in Signat (loop ctx defs)


and insertModulVariable ctx nm sg =
  if NameMap.mem nm ctx.modulvars then
    failwith ("Outsyn: shadowing of modul variable " ^ (string_of_name nm))
  else
    let sg' =  hnfSignat ctx sg
    in
    { ctx with modulvars = NameMap.add nm sg' ctx.modulvars }

and insertSignatVariable ctx nm sg =
  if NameMap.mem nm ctx.signatvars then
    failwith ("Outsyn: shadowing of signat variable " ^ (string_of_name nm))
  else
    let sg' =  hnfSignat ctx sg
    in
    { ctx with signatvars = NameMap.add nm sg' ctx.signatvars }



(***********************************)
(** {2 Utility functions for types *)
(***********************************)

(** Expand out any top-level definitions for a type *)
let rec hnfTy ctx orig_ty = 
  match orig_ty with
      NamedTy (LN(None, nm)) ->
	begin
	  match lookupTypeVariable ctx nm with
	    | None -> orig_ty
	    | Some ty -> hnfTy ctx ty
	end
    | NamedTy (LN(Some mdl, nm)) ->
	begin
	  match hnfSignat ctx (modulToSignat ctx mdl) with
	    Signat elems ->
	      begin
		match findTypevarInElems elems mdl nm with
		    None -> orig_ty
		  | Some ty -> hnfTy ctx ty
	      end
	    | sg' -> (print_endline "Found unprojectable signature:";
		      print_endline (string_of_signat sg');
		      failwith "hnfTy")
	end
    | _ -> orig_ty


let rec insertTermVariableLet ctx pat ty =
  match pat with
    WildPat       -> ctx
  | VarPat nm     -> insertTermVariable ctx nm ty
  | TuplePat pats -> 
      begin
	match hnfTy ctx ty with
	  TupleTy tys ->
	    List.fold_left2 insertTermVariableLet ctx pats tys
	| _ -> failwith "Outsynrules.insertTermVariableLet 1"
      end
  | ConstrPat _ -> failwith "Outsynrules.insertTermVariableLet 2"

  

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
        | _ -> s1 (** We're assuming the input typechecks! *)



(* checkFact : ctx -> prop -> bool

   Check whether the given proposition is a logical consequence 
   of the facts we already know to be true.

   This isn't even close to being a theorem prover; it doesn't even
   check for alpha-equivalence of propositions or know about modus
   ponens.  It only checks for a very few "easy" inferences. 
*)
let rec checkFact ({facts = facts} as ctx) prp =
  List.mem prp facts ||
    (match prp with 
	And prps -> List.for_all (checkFact ctx) prps
      | Imply (prp1,prp2) -> 
	  checkFact (insertFact ctx prp1) prp2
      | Iff(prp1,prp2) ->
	  checkFact ctx (Imply(prp1,prp2)) &&
	    checkFact ctx (Imply(prp2,prp1))
      | Not(Not(prp)) ->
	  (** We are guaranteed that all propositions/assertions
	      are classically valid; the "constructive" parts have
	      already been removed. *)
	  checkFact ctx prp
      | Equal(t1,t2) ->
	  (* Don't call checkFact recursively here, or we'll
	     go into an infinite loop *)
	  List.mem (Equal(t2,t1)) facts
      | PApp(PApp (p, t1), t2) when isPerProp p ->
	  (* Ditto *)
	  List.mem (PApp(PApp(p, t2), t1)) facts
      | _ -> false)

and insertFact ({facts=facts} as ctx) prp =
  if checkFact ctx prp then
    ctx
  else
    (match prp with
	And prps -> insertFacts ctx prps
      | Not (Not prp) -> insertFact ctx prp (* Classical logic! *)
      | Iff(prp1,prp2) ->
	  insertFact (insertFact ctx (Imply(prp1,prp2))) (Imply(prp2,prp1))
      | _ -> { ctx with facts = prp::facts })

and insertFacts ctx prps =
  List.fold_left insertFact ctx prps

let rec insertPattern ctx = function
    WildPat  -> ctx
  | VarPat _ -> 
      failwith "Outsynrules.insertPattern: Can't infer type of pattern"
  | TuplePat pats -> 
      List.fold_left insertPattern ctx pats
  | ConstrPat(lbl, None) -> ctx
  | ConstrPat(lbl, Some(nm,ty)) ->
      insertTermVariable ctx nm ty

(***************************************)
(** {2: Type Reconstruction for Terms} *)
(***************************************)

(* Given a context and a well-formed term, return the type
   of that term.

   Does not actually check that the term is well-formed!
   Returned type will be correct, but need not be head-normal.
 *)
let rec typeOf ctx = function
  | Id(LN(None,nm)) -> 
      let nm = applyTermRenaming ctx nm
      in lookupTermVariable ctx nm
  | Id(LN(Some mdl, nm)) ->
       begin
	 match hnfSignat ctx (modulToSignat ctx mdl) with
             Signat elts -> findTermvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.typeOf: Id"
       end
  | EmptyTuple -> UnitTy
  | BConst _ -> BoolTy
  | Dagger     -> TopTy
  | App(trm1, _) ->
      begin
	match hnfTy ctx (typeOf ctx trm1) with
	  ArrowTy(_,ty) -> ty
	| _ -> failwith "Outsynrules.typeOf App"
      end
  | Lambda((nm,ty1),trm2) -> 
      let ctx' = insertTermVariable ctx nm ty1
      in ArrowTy(ty1, typeOf ctx' trm2)
  | Tuple trms ->
      TupleTy (List.map (typeOf ctx) trms)
  | Proj(n, trm) ->
      begin
	match (hnfTy ctx (typeOf ctx trm)) with
	  TupleTy tys -> List.nth tys n
	| _ -> failwith "Outsynrules.typeOf: Proj"
      end
  | Inj(lbl, None) -> SumTy([(lbl,None)])
  | Inj(lbl, Some trm) -> SumTy([(lbl, Some (typeOf ctx trm))])
  | Case(_, arms) ->
      begin
	let typeOfArm (pat,trm) =
	      let ctx' = insertPattern ctx pat
	      in typeOf ctx' trm
	in let armTys = List.map typeOfArm arms
	in match armTys with
	  []        -> VoidTy
	| (ty::tys) -> List.fold_left (joinTy ctx) ty tys
      end
  | Let(pat,trm1,trm2) ->
      let ctx' = insertTermVariableLet ctx pat (typeOf ctx trm1)
      in typeOf ctx' trm2
  | Obligation(bnds,_,trm) ->
      let insertTermBnd ctx (nm,ty) = insertTermVariable ctx nm ty
      in let ctx' = List.fold_left insertTermBnd ctx bnds 
      in typeOf ctx' trm
  | PolyInst (trm,tys) ->
      failwith "Outsynrules.typeOf PolyInst unimplemented"



