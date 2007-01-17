(** Intelligent renaming for outsyn. *)

open Name
open Outsyn

let emptyRen = (NameMap.empty, StringSet.empty)

let forbid nm (ren, bad) =
  match nm with
      N (str,_) -> (ren, StringSet.add str bad)
    | G _ -> (ren, bad)

let rec forbidFromSignat ctx = function
    SignatName nm -> forbid nm ctx
  | SignatProj (_, _) -> ctx
  | Signat lst -> List.fold_left forbidFromSignatElem ctx lst
  | SignatFunctor ((nm, sgnt1), sgnt2) ->
      forbidFromSignat (forbidFromSignat ctx sgnt1) sgnt2
  | SignatApp (sgnt, mdl) -> forbidFromModul (forbidFromSignat ctx sgnt) mdl

and forbidFromSignatElem ctx = function
    Spec (nm, ModulSpec sgnt, _)
  | Spec (nm, SignatSpec sgnt, _) ->
      forbid nm (forbidFromSignat ctx sgnt)
  | Spec _ | Comment _ | Assertion _ -> ctx

and forbidFromModul ctx = function
    ModulName nm -> forbid nm ctx
  | ModulProj (mdl, _) -> forbidFromModul ctx mdl
  | ModulApp (mdl1, mdl2) -> forbidFromModul (forbidFromModul ctx mdl1) mdl2
  | ModulStruct lst -> List.fold_left forbidFromModuldef ctx lst

and forbidFromModuldef ctx = function
    DefType _ | DefTerm _ -> ctx
  | DefModul (nm, sgnt, mdl) ->
      forbid nm (forbidFromModul (forbidFromSignat ctx sgnt) mdl)
  | DefSignat (nm, sgnt) ->
      forbid nm (forbidFromSignat ctx sgnt)

let renList f ctx lst =
  let lst, ctx =
    List.fold_left
      (fun (ts, ct) t -> let t, ct = f ct t in t::ts, ct)
      ([], ctx)
      lst
  in
    List.rev lst, ctx

let renList' f ctx lst = List.rev (List.fold_left (fun ts t -> f ctx t :: ts) [] lst)

let rec renName (ren, bad) nm =
  let bn = rename bad nm in
    N bn, (NameMap.add nm bn ren, StringSet.add (fst bn) bad)

and renNameList ctx nms = renList renName ctx nms
    
and renBinding ctx (nm, ty) =
  let ty = renTy ctx ty in
  let nm, ctx = renName ctx nm in
    (nm, ty), ctx

and renBindingList ctx bndg = renList renBinding ctx bndg

and renPBinding ctx (nm, pt) =
  let pt = renPt ctx pt in
  let nm, ctx = renName ctx nm in
    (nm, pt), ctx

and renPBindingList ctx pbnds = renList renPBinding ctx pbnds

and renBindingOpt ctx = function
    None -> None, ctx
  | Some bnd ->
      let bnd, ctx = renBinding ctx bnd in
	Some bnd, ctx

and renPat ctx pat = 
  match pat with
    WildPat -> (pat, ctx)
  | VarPat nm -> 
      let nm, ctx = renName ctx nm in
      (VarPat nm, ctx)
  | TuplePat pats -> 
      let pats', ctx = renList renPat ctx pats in
      TuplePat pats', ctx
  | ConstrPat (_, None) -> (pat, ctx)
  | ConstrPat (lb, Some bnd) ->
      let bnd, ctx = renBinding ctx bnd in
      ConstrPat(lb, Some bnd), ctx

and renPt ctx = function
    Prop -> Prop
  | PropArrow(ty, pt) -> PropArrow(renTy ctx ty, renPt ctx pt)

and renLN ctx = function
    LN (Some mdl, nm) ->
      let mdl = renModul ctx mdl in
	LN (Some mdl, nm)
  | LN (None, nm) ->
      begin
	try
	  LN (None, N (NameMap.find nm (fst ctx)))
	with Not_found -> LN (None, nm)
      end

and renTerm ctx = function
    (EmptyTuple | Dagger | Inj (_, None)) as t -> t
      
  | Id ln -> Id (renLN ctx ln)

  | App (t1, t2) -> App (renTerm ctx t1, renTerm ctx t2)

  | Lambda (bnd, t) ->
      let bnd, ctx = renBinding ctx bnd in
	Lambda (bnd, renTerm ctx t)

  | Tuple lst -> Tuple (renTermList ctx lst)

  | Proj (k, t) -> Proj (k, renTerm ctx t)

  | Inj (lb, Some t) -> Inj (lb, Some (renTerm ctx t))
      
  | Case (t, lst) ->
      let renArm ct (pat, t) =
	let pat, ct = renPat ct pat in
	(pat, renTerm ct t)
      in
      Case (renTerm ctx t,
	    renList' renArm ctx lst)
	
  | Let (pat, t1, t2) ->
      let t1 = renTerm ctx t1 in
      let pat, ctx = renPat ctx pat in
	Let (pat, t1, renTerm ctx t2)
	  
  | Obligation (bnds, p, t) ->
      let bnds, ctx = renBindingList ctx bnds in
      let p = renProp ctx p in
	Obligation (bnds, p, renTerm ctx t)
	  
  | PolyInst (trm, tys) -> PolyInst (renTerm ctx trm, renTyList ctx tys)

and renTermList ctx lst = renList' renTerm ctx lst

and renTy ctx = function
    NamedTy ln -> NamedTy (renLN ctx ln)

  | (UnitTy | VoidTy | TopTy) as ty -> ty

  | SumTy lst ->
      SumTy (renList'
	      (fun ct -> function
		  (lb, None) -> (lb, None)
		| (lb, Some ty) -> (lb, Some (renTy ct ty)))
	      ctx
	      lst)

  | TupleTy lst -> TupleTy (renTyList ctx lst)

  | ArrowTy (ty1, ty2) -> ArrowTy (renTy ctx ty1, renTy ctx ty2)

  | PolyTy(nms, ty) ->
      let nms, ctx = renNameList ctx nms in
	PolyTy (nms, renTy ctx ty)

and renTyList ctx lst = renList' renTy ctx lst

and renTyOpt ctx = function
    None -> None
  | Some ty -> Some (renTy ctx ty)

and renSimpleTy ctx = function
  | SNamedTy ln -> SNamedTy (renLN ctx ln)
  | (SUnitTy | SVoidTy | STopTy) as sty -> sty
  | STupleTy lst -> STupleTy (renSimpleTyList ctx lst)
  | SArrowTy (sty1, sty2) -> SArrowTy (renSimpleTy ctx sty1, renSimpleTy ctx sty2)

and renSimpleTyList ctx lst = renList' renSimpleTy ctx lst

and renProp ctx = function
    (True | False) as p -> p

  | SimpleSupport sty -> SimpleSupport (renSimpleTy ctx sty)

  | SimplePer sty -> SimplePer (renSimpleTy ctx sty)

  | BasicProp ln -> BasicProp (renLN ctx ln)

  | Equal (t1, t2) -> Equal (renTerm ctx t1, renTerm ctx t2)

  | And ps -> And (renPropList ctx ps)

  | Imply (p1, p2) -> Imply (renProp ctx p1, renProp ctx p2)

  | Iff (p1, p2) -> Iff (renProp ctx p1, renProp ctx p2)

  | Not p -> Not (renProp ctx p)

  | Forall (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
	Forall (bnd, renProp ctx p)

  | ForallSupport ((nm, sty), p) ->
      let sty = renSimpleTy ctx sty in
      let nm, ctx = renName ctx nm in
	ForallSupport ((nm, sty), renProp ctx p)

  | PApp (p, t) -> PApp (renProp ctx p, renTerm ctx t)

  | PLambda (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
	PLambda (bnd, renProp ctx p)

  | PObligation (bnds, p1, p2) ->
      let bnds, ctx = renBindingList ctx bnds in
	PObligation (bnds, renProp ctx p1, renProp ctx p2)

  | PCase (t, lst) ->
      let renPArm ct (pat, p) =
	let pat, ct = renPat ct pat in
	(pat, renProp ct p)
      in
      PCase (renTerm ctx t,
	     renList' renPArm ctx lst)

  | PLet (pat, t, p) ->
      let t = renTerm ctx t in
      let pat, ctx = renPat ctx pat in
	PLet (pat, t, renProp ctx p)

and renPropList ctx lst = renList' renProp ctx lst

and renModest ctx {ty=ty; tot=p; per=q} =
  {ty = renTy ctx ty; tot = renProp ctx p; per = renProp ctx q}

and renAssertion ctx asn =
  let ctx = forbid (mk_word asn.alabel) ctx in
  let atyvars, ctx = renNameList ctx asn.atyvars in
  let apbnds, ctx = renPBindingList ctx asn.apbnds in
  let ctx = List.fold_left
    (fun ctx ->
       function
	   Annot_NoOpt -> ctx
	 | Annot_Declare n -> forbid n ctx)
    ctx
    asn.aannots
  in
  {alabel = asn.alabel;
   atyvars = atyvars;
   apbnds  = apbnds;
   aannots = asn.aannots;
   aprop = renProp ctx asn.aprop}, ctx

and renAssertionList ctx lst = renList renAssertion ctx lst

and renSpec ctx = function
    ValSpec (nms,ty) ->
      let nms, ctx = renNameList ctx nms in
	ValSpec (nms, renTy ctx ty)

  | ModulSpec sgnt -> ModulSpec (renSignat ctx sgnt)

  | TySpec tyopt -> TySpec (renTyOpt ctx tyopt)

  | SignatSpec sgnt -> SignatSpec (renSignat ctx sgnt)

  | PropSpec pt -> PropSpec (renPt ctx pt)

and renSignatElement ctx = function
    Spec (nm, spc, lst) ->
      let spc = renSpec ctx spc in
      let ctx = forbid nm ctx in
      let lst, ctx = renAssertionList ctx lst in
	Spec (nm, spc, lst), ctx

  | Assertion a ->
      let a, ctx = renAssertion ctx a in
	Assertion a, ctx

  | Comment _ as c -> c, ctx

and renSignatElementList ctx lst = renList renSignatElement ctx lst

and renSignat ctx = function
    SignatName nm -> SignatName nm

  | SignatProj (mdl, nm) -> SignatProj (renModul ctx mdl, nm)

  | Signat lst -> Signat (fst (renSignatElementList ctx lst))

  | SignatFunctor ((nm, sgnt1), sgnt2) ->
      let sgnt1 = renSignat ctx sgnt1 in
      let nm, ctx = renName (forbidFromSignat ctx sgnt2) nm in
      let sgnt2 = renSignat ctx sgnt2 in
	SignatFunctor ((nm, sgnt1), sgnt2)

  | SignatApp (sgnt, mdl) -> SignatApp (renSignat ctx sgnt, renModul ctx mdl)

and renModul ctx = function
    ModulName nm ->
      begin try
	ModulName (N (NameMap.find nm (fst ctx)))
      with
	  Not_found -> ModulName nm
      end

  | ModulProj (mdl, nm) -> ModulProj (renModul ctx mdl, nm)

  | ModulApp (mdl1, mdl2) -> ModulApp (renModul ctx mdl1, renModul ctx mdl2)

  | ModulStruct lst -> ModulStruct (fst (renModuldefList ctx lst))

and renModuldef ctx = function
    DefType (nm, ty) ->
      DefType (nm, renTy ctx ty), forbid nm ctx

  | DefTerm (nm, ty, t) ->
      DefTerm (nm, renTy ctx ty, renTerm ctx t), forbid nm ctx

  | DefModul (nm, sgnt, mdl) ->
      DefModul (nm, renSignat ctx sgnt, renModul ctx mdl),
      forbid nm ctx

  | DefSignat (nm, sgnt) ->
      DefSignat (nm, renSignat ctx sgnt), forbid nm ctx

and renModuldefList ctx lst = renList renModuldef ctx lst
    
