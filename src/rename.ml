(** Intelligent renaming for outsyn. *)

open Name
open Outsyn

let emptyRen = (NameMap.empty, StringSet.empty)

let forbid nm (ren, bad) =
  match nm with
      N (str,_) -> (ren, StringSet.add str bad)
    | G _ -> failwith "Rename.forbid: cannot forbid gensymed names."

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

let renList' f ctx lst = List.fold_left (fun ts t -> f ctx t :: ts) [] lst

let rec renName (ren, bad) nm =
  let bn = rename bad nm in
    N bn, (NameMap.add nm bn ren, StringSet.add (fst bn) bad)

and renNameList ctx nms = renList renName ctx nms
    
and renBinding ctx (nm, ty) =
  let ty = renTy ctx ty in
  let nm, ctx = renName ctx nm in
    (nm, ty), ctx

and renBindingList ctx bndg = renList renBinding ctx bndg

and renMBinding ctx (nm, ms) =
  let ms = renModest ctx ms in
  let nm, ctx = renName ctx nm in
    (nm, ms), ctx

and renMBindingList ctx bndg = renList renMBinding ctx bndg

and renBindingOpt ctx = function
    None -> None, ctx
  | Some bnd ->
      let bnd, ctx = renBinding ctx bnd in
	Some bnd, ctx

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
      Case (renTerm ctx t,
	   renList'
	     (fun ct -> function
		 (lb, None, t) -> (lb, None, renTerm ct t)
	       | (lb, Some bnd, t) ->
		   let bnd, ct = renBinding ct bnd in
		     (lb, Some bnd, renTerm ct t))
	     ctx
	     lst)

  | Let (nm, t1, t2) ->
      let t1 = renTerm ctx t1 in
      let nm, ctx = renName ctx nm in
	Let (nm, t1, renTerm ctx t2)
	  
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

and renProp ctx = function
    (True | False) as p -> p

  | NamedTotal (ln, lst) -> NamedTotal (renLN ctx ln, renTermList ctx lst)

  | NamedPer (ln, lst) -> NamedPer (renLN ctx ln, renTermList ctx lst)
      
  | NamedProp (ln, t, lst) -> NamedProp (renLN ctx ln, renTerm ctx t, renTermList ctx lst)

  | Equal (t1, t2) -> Equal (renTerm ctx t1, renTerm ctx t2)

  | And ps -> And (renPropList ctx ps)

  | Cor ps -> Cor (renPropList ctx ps)

  | Imply (p1, p2) -> Imply (renProp ctx p1, renProp ctx p2)

  | Iff (p1, p2) -> Iff (renProp ctx p1, renProp ctx p2)

  | Not p -> Not (renProp ctx p)

  | Forall (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
	Forall (bnd, renProp ctx p)

  | ForallTotal ((nm, ln), p) ->
      let ln = renLN ctx ln in
      let nm, ctx = renName ctx nm in
	ForallTotal ((nm, ln), renProp ctx p)

  | Cexists (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
	Cexists (bnd, renProp ctx p)

  | PApp (p, t) -> PApp (renProp ctx p, renTerm ctx t)

  | PMApp (p, t) -> PMApp (renProp ctx p, renTerm ctx t)

  | PLambda (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
	PLambda (bnd, renProp ctx p)

  | PMLambda ((nm, ms), p) ->
      let ms = renModest ctx ms in
      let nm, ctx = renName ctx nm in
	PMLambda ((nm, ms), renProp ctx p)

  | PObligation (bnds, p1, p2) ->
      let bnds, ctx = renBindingList ctx bnds in
	PObligation (bnds, renProp ctx p1, renProp ctx p2)

  | PCase (t1, t2, lst) ->
      PCase (
	  renTerm ctx t1,
	  renTerm ctx t2,
	  renList'
	    (fun ct (lb, b1, b2, p) ->
	      let b1, ct = renBindingOpt ct b1 in
	      let b2, ct = renBindingOpt ct b2 in
		(lb, b1, b2, renProp ct p))
	    ctx
	    lst
      )

  | PLet (nm, t, p) ->
      let t = renTerm ctx t in
      let nm, ctx = renName ctx nm in
	PLet (nm, t, renProp ctx p)

and renPropList ctx lst = renList' renProp ctx lst

and renModest ctx {ty=ty; tot=p; per=q} =
  {ty = renTy ctx ty; tot = renProp ctx p; per = renProp ctx q}

and renAssertion ctx (str, annots, p) =
  let ctx = forbid (mk_word str) ctx in
    (str, annots, renProp ctx p), ctx

and renAssertionList ctx lst = renList renAssertion ctx lst

and renSpec ctx = function
    ValSpec (nms,ty) ->
      let nms, ctx = renNameList ctx nms in
	ValSpec (nms, renTy ctx ty)

  | ModulSpec sgnt -> ModulSpec (renSignat ctx sgnt)

  | TySpec tyopt -> TySpec (renTyOpt ctx tyopt)

  | SignatSpec sgnt -> SignatSpec (renSignat ctx sgnt)

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
    
