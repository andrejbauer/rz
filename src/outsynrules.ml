open Name
open Outsyn

(***************************)
(** {2 The Typing Context} *)
(***************************)

(* We maintain different lookup tables and renamings for each "flavor"
   of identifier because they live in distinct ML namespaces. *)

type context = {termvars: ty NameMap.t;  
		termrenaming: name NameMap.t;
		typevars: (ty option) NameMap.t;
		typerenaming: name NameMap.t;
		modulvars: signat NameMap.t;
		modulrenaming: name NameMap.t;
		proprenaming: name NameMap.t;
		signatvars: signat NameMap.t;
	        facts: proposition list}

let emptyContext = 
  {termvars = NameMap.empty;   termrenaming = NameMap.empty;
   typevars = NameMap.empty;   typerenaming = NameMap.empty;
   modulvars = NameMap.empty;  modulrenaming = NameMap.empty;
   proprenaming = NameMap.empty;
   signatvars = NameMap.empty;
   facts = []}

let displayContext cntxt = 
  (NameMap.iter (fun nm ty -> print_endline("val " ^ string_of_name nm ^ ":" ^ string_of_ty ty)) cntxt.termvars;
   NameMap.iter (fun nm tyopt -> print_endline("type " ^ string_of_name nm ^ (match tyopt with None -> "" | Some ty -> "=" ^ string_of_ty ty))) cntxt.typevars;
   NameMap.iter (fun nm sg -> print_endline("module " ^ string_of_name nm ^ " : " ^ string_of_signat sg)) cntxt.modulvars;
   NameMap.iter (fun nm sg -> print_endline("signature " ^ string_of_name nm ^ " = " ^ string_of_signat sg)) cntxt.signatvars;)


(***************)
(** {3 Lookup} *)
(***************)

let notFound sort nm = 
  failwith ("Unbound " ^ sort ^ " variable " ^ string_of_name nm)


let lookupTermVariable cntxt nm = 
   try (NameMap.find nm cntxt.termvars) with 
       Not_found -> notFound "term" nm

let lookupTypeVariable cntxt nm = 
   try (NameMap.find nm cntxt.typevars) with 
       Not_found -> notFound "type" nm

let lookupModulVariable cntxt nm = 
   try (NameMap.find nm cntxt.modulvars) with 
       Not_found -> notFound "modul" nm

let lookupSignatVariable cntxt nm = 
   try (NameMap.find nm cntxt.signatvars) with 
       Not_found -> notFound "signat" nm

let isboundTermVariable cntxt nm =
  NameMap.mem nm cntxt.termvars

(******************)
(** {3 Insertion} *)
(******************)

let insertTermVariable cntxt nm ty =
  if NameMap.mem nm cntxt.termvars then
    failwith ("Outsyn: shadowing of term variable " ^ (string_of_name nm))
  else
    { cntxt with termvars = NameMap.add nm ty cntxt.termvars }

let insertTypeVariable cntxt nm ty =
  if NameMap.mem nm cntxt.typevars then
    failwith ("Outsyn: shadowing of type variable " ^ (string_of_name nm))
  else
  { cntxt with typevars = NameMap.add nm ty cntxt.typevars }

let insertTypeVariables cntxt nms def =
  let defs = List.map (fun _ -> def) nms
  in
     List.fold_left2 insertTypeVariable cntxt nms defs

(** Other functions later *)

(************************************)
(** {3 Renaming of Bound Variables} *)
(************************************)

let addToRenaming map oldnm newnm =
(*  if (oldnm = newnm) then 
    map
  else *)
    NameMap.add oldnm newnm map

let addListToRenaming map oldnms newnms =
  List.fold_left2 addToRenaming map oldnms newnms

(* Stolen from logicrules.ml *)
let renameBoundTermVar cntxt nm =
  let nm' = refresh nm in
    ({cntxt with termrenaming = addToRenaming cntxt.termrenaming nm nm'}, nm')

let renameBoundTermVars cntxt nms =
  let nms' = refreshList nms in
    ({cntxt with termrenaming = 
        addListToRenaming cntxt.termrenaming nms nms'}, nms')

let renameBoundTypeVar cntxt nm =
  let nm' = refresh nm in
    ({cntxt with termrenaming = addToRenaming cntxt.typerenaming nm nm'}, nm')

let renameBoundTypeVars ctx nms = 
  mapWithAccum renameBoundTypeVar ctx nms

let renameBoundModulVar cntxt nm =
  let nm' = refresh nm in
    ({cntxt with termrenaming = addToRenaming cntxt.modulrenaming nm nm'}, nm')

let renameBoundPropVar cntxt nm =
  let nm' = refresh nm in
    ({cntxt with proprenaming = addToRenaming cntxt.proprenaming nm nm'}, nm')
  
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

let applyTermRenaming cntxt nm =
  applyRenaming cntxt.termrenaming nm

let applyTypeRenaming cntxt nm =
  applyRenaming cntxt.typerenaming nm

let applyModulRenaming cntxt nm =
  applyRenaming cntxt.modulrenaming nm

let applyPropRenaming cntxt nm =
  applyRenaming cntxt.proprenaming nm

let applyPropRenamingLN cntxt = function
    LN(None, nm) -> LN(None, applyPropRenaming cntxt nm)
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


let rec hnfSignat cntxt = function
    SignatApp(sg1,mdl2) -> 
      begin
	match hnfSignat cntxt sg1 with
	    SignatFunctor((nm,_),sg1b) ->
	      let sg' = substSignat (insertModulvar emptysubst nm mdl2) sg1b
	      in hnfSignat cntxt sg'
	  | _ -> failwith "Outsynrules.hnfSignat 1"
      end
  | SignatName nm -> hnfSignat cntxt (lookupSignatVariable cntxt nm)
  | SignatProj (mdl, nm) ->
       begin
	 match hnfSignat cntxt (modulToSignat cntxt mdl) with
             Signat elts -> findSignatvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.hnfSignat 2"
       end
  | sg -> sg

and modulToSignat cntxt = function
    ModulName nm        -> 
      let nm = applyModulRenaming cntxt nm
      in lookupModulVariable cntxt nm
  | ModulProj (mdl, nm) ->
       begin
	 match hnfSignat cntxt (modulToSignat cntxt mdl) with
             Signat elts -> findModulvarInElems elts mdl nm
	   | _ -> failwith "Outsynrules.modulToSignat 1"
       end
  | ModulApp (mdl1, mdl2)  -> 
       begin
	 match hnfSignat cntxt (modulToSignat cntxt mdl1) with
             SignatFunctor((nm,_),sg) -> 
	       let subst = insertModulvar emptysubst nm mdl2
	       in substSignat subst sg
	   | _ -> failwith "Outsynrules.modulToSignat 2"
       end
  | ModulStruct defs -> 
      let rec loop cntxt = function
	  [] -> []
	| DefTerm(nm,ty,_) :: rest ->
	    Spec(nm, ValSpec ([], ty), []) :: 
	      loop (insertTermVariable cntxt nm ty) rest
	| DefType(nm,ty) :: rest ->
	    Spec(nm, TySpec (Some ty), []) :: 
	      loop (insertTypeVariable cntxt nm (Some ty)) rest
	| DefModul(nm,sg,_) :: rest ->
	    Spec(nm, ModulSpec sg, []) :: 
	      loop (insertModulVariable cntxt nm sg) rest
        | DefSignat(nm,sg) :: rest ->
	    Spec(nm, SignatSpec sg, []) ::
	      loop (insertSignatVariable cntxt nm sg) rest
      in Signat (loop cntxt defs)


and insertModulVariable cntxt nm sg =
  if NameMap.mem nm cntxt.modulvars then
    failwith ("Outsyn: shadowing of modul variable " ^ (string_of_name nm))
  else
    let sg' =  hnfSignat cntxt sg
    in
    { cntxt with modulvars = NameMap.add nm sg' cntxt.modulvars }

and insertSignatVariable cntxt nm sg =
  if NameMap.mem nm cntxt.signatvars then
    failwith ("Outsyn: shadowing of signat variable " ^ (string_of_name nm))
  else
    let sg' =  hnfSignat cntxt sg
    in
    { cntxt with signatvars = NameMap.add nm sg' cntxt.signatvars }



(***********************************)
(** {2 Utility functions for types *)
(***********************************)

(** Expand out any top-level definitions for a type *)
let rec hnfTy cntxt orig_ty = 
  match orig_ty with
      NamedTy (LN(None, nm)) ->
	begin
	  match lookupTypeVariable cntxt nm with
	    | None -> orig_ty
	    | Some ty -> hnfTy cntxt ty
	end
    | NamedTy (LN(Some mdl, nm)) ->
	begin
	  match hnfSignat cntxt (modulToSignat cntxt mdl) with
	    Signat elems ->
	      begin
		match findTypevarInElems elems mdl nm with
		    None -> orig_ty
		  | Some ty -> hnfTy cntxt ty
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
      | Cor prps -> List.exists (checkFact ctx) prps
      | Imply (prp1,prp2) -> 
	  checkFact (insertFact ctx prp1) prp2 ||
	  (* Don't call checkFact recursively here, or we'll
	     go into an infinite loop *)
	  List.mem (Iff(prp1,prp2)) facts ||
	  List.mem (Iff(prp2,prp1)) facts
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
      | PApp(PApp(NamedPer(nm,args), t1), t2) ->
	  (* Ditto *)
	  List.mem (PApp(PApp(NamedPer(nm,args), t2), t1)) facts
      | _ -> false)

and insertFact ({facts=facts} as ctx) prp =
  if checkFact ctx prp then
    ctx
  else
    (match prp with
	And prps -> insertFacts ctx prps
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
  | Dagger -> TopTy
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
	  [] -> VoidTy
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



