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
		signatvars: signat NameMap.t;
	        facts: proposition list}

let emptyContext = 
  {termvars = NameMap.empty;   termrenaming = NameMap.empty;
   typevars = NameMap.empty;   typerenaming = NameMap.empty;
   modulvars = NameMap.empty;  modulrenaming = NameMap.empty;
   signatvars = NameMap.empty;
   facts = []}


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

let insertModulVariable cntxt nm ty =
  if NameMap.mem nm cntxt.modulvars then
    failwith ("Outsyn: shadowing of modul variable " ^ (string_of_name nm))
  else
  { cntxt with modulvars = NameMap.add nm ty cntxt.modulvars }

let insertSignatVariable cntxt nm ty =
  if NameMap.mem nm cntxt.signatvars then
    failwith ("Outsyn: shadowing of signat variable " ^ (string_of_name nm))
  else
  { cntxt with signatvars = NameMap.add nm ty cntxt.signatvars }

(************************************)
(** {3 Renaming of Bound Variables} *)
(************************************)

let addToRenaming map oldnm newnm =
(*  if (oldnm = newnm) then 
    map
  else *)
    NameMap.add oldnm newnm map

(* Stolen from logicrules.ml *)
let renameBoundTermVar cntxt nm =
  let nm' = refresh nm in
    ({cntxt with termrenaming = addToRenaming cntxt.termrenaming nm nm'}, nm')

let renameBoundTypeVar cntxt nm =
  let nm' = refresh nm in
    ({cntxt with termrenaming = addToRenaming cntxt.typerenaming nm nm'}, nm')

let renameBoundModulVar cntxt nm =
  let nm' = refresh nm in
    ({cntxt with termrenaming = addToRenaming cntxt.modulrenaming nm nm'}, nm')


let rec renameTermBindings cntxt = function
    [] -> (cntxt, [])
  | (nm,ty)::bnds -> 
      let (cntxt', nm') = renameBoundTermVar cntxt nm
      in let cntxt'' = insertTermVariable cntxt' nm' ty
      in let (cntxt''', bnds') = renameTermBindings cntxt'' bnds
      in (cntxt''', (nm',ty)::bnds')


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



let rec hnfSignat cntxt = function
    SignatApp(sg1,mdl2) -> 
      begin
	match hnfSignat cntxt sg1 with
	    SignatFunctor((nm,_),sg1b) ->
	      let sg' = substSignat (insertModulvar emptysubst nm mdl2) sg1b
	      in hnfSignat cntxt sg'
	  | _ -> failwith "Outsynrules.hnfSignat"
      end
  | SignatName nm -> hnfSignat cntxt (lookupSignatVariable cntxt nm)
  | sg -> sg
      

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
	failwith ("Outsynrules.findTermvarInelems: polymorphic valspec " ^ 
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


let rec modulToSignat cntxt = function
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
	    | _ -> failwith "hnfTy"
	end
    | _ -> orig_ty


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
