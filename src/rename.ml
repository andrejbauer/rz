(** Intelligent renaming for outsyn. *)

open Name
open Outsyn

let emptyRen = (NameMap.empty, StringSet.empty)

let forbid nm (ren, bad) =
  match nm with
      N (str,_) -> (ren, StringSet.add str bad)
    | G _ -> failwith "Rename.forbid: cannot forbid gensymed names."

let free nm (ren, bad) =
  try
    let bn = NameMap.find nm ren in
      (NameMap.remove nm ren, StringSet.remove (fst bn) bad)
  with
      Not_found -> (ren, bad)

let renList f ctx lst =
  let lst, ctx =
    List.fold_left
      (fun (ts, ct) t -> let t, ct = f ct t in t::ts, ct)
      ([], ctx)
      lst
  in
    List.rev lst, ctx

let rec renName (ren, bad) nm =
  let bn = rename bad nm in
    N bn, (NameMap.add nm bn ren, StringSet.add (fst bn) bad)

and renNameList ctx nms = renList renName ctx nms
    
and renBinding ctx (nm, ty) =
  let ty, ctx = renTy ctx ty in
  let nm, ctx = renName ctx nm in
    (nm, ty), ctx
      
and renBindingList ctx bndg = renList renBinding ctx bndg

and renBindingOpt ctx = function
    None -> None, ctx
  | Some bnd ->
      let bnd, ctx = renBinding ctx bnd in
	Some bnd, ctx

and renLN ctx = function
    LN (Some mdl, nm) ->
      let mdl, ctx = renModul ctx mdl in
	LN (Some mdl, nm), ctx
  | LN (None, nm) ->
      begin try
	LN (None, N (NameMap.find nm (fst ctx))), ctx
      with
	  Not_found ->
	    let nm, ctx = renName ctx nm in
	      LN (None, nm), ctx
      end


and renTerm ((ren, bad) as ctx) = function
    (EmptyTuple | Dagger | Inj (_, None)) as t -> t, ctx

  | Id ln ->
      let ln, ctx = renLN ctx ln in
	Id ln, ctx

  | App (t1, t2) ->
      let t1, ctx = renTerm ctx t1 in
      let t2, ctx = renTerm ctx t2 in
	App (t1, t2), ctx

  | Lambda (bnd, t) ->
      let bnd, ctx = renBinding ctx bnd in
      let t, ctx = renTerm ctx t in
	Lambda (bnd, t), free (fst bnd) ctx

  | Tuple lst ->
      let lst, ctx = renTermList ctx lst in
	Tuple lst, ctx

  | Proj (k, t) ->
      let t, ctx = renTerm ctx t in
	Proj (k, t), ctx

  | Inj (lb, Some t) ->
      let t, ctx = renTerm ctx t in
	Inj (lb, Some t), ctx
  
  | Case (t, lst) ->
      let t, ctx = renTerm ctx t in
      let lst, ctx =
	List.fold_left
	  (fun (ts,ct) arm ->
	     match arm with
		 (lb, None, t) ->
		   let t, ct = renTerm ct t in
		     (lb, None, t)::ts, ct
	       | (lb, Some bnd, t) ->
		   let bnd, ct = renBinding ct bnd in
		   let t, ct = renTerm ct t in
		     (lb, Some bnd, t)::ts, free (fst bnd) ct)
	  ([], ctx)
	  lst
      in
	Case (t, lst), ctx

  | Let (nm, t1, t2) ->
      let t1, ctx = renTerm ctx t1 in
      let nm, ctx = renName ctx nm in
      let t2, ctx = renTerm ctx t2 in
	Let (nm, t1, t2), free nm ctx

  | Obligation (bnds, p, t) ->
      let bnds, ctx = renBindingList ctx bnds in
      let p, ctx = renProp ctx p in
      let t, ctx = renTerm ctx t in
	(Obligation (bnds, p, t),
        List.fold_left (fun ct (nm,_) -> free nm ct) ctx bnds)

  | PolyInst (trm, tys) ->
      let trm, ctx = renTerm ctx trm in
      let tys, ctx = renTyList ctx tys in
	PolyInst(trm, tys), ctx

and renTermList ctx lst = renList renTerm ctx lst

and renTy ctx = function
    NamedTy ln ->
      let ln, ctx = renLN ctx ln in
	NamedTy ln, ctx
  | (UnitTy | VoidTy | TopTy) as ty -> ty, ctx
  | SumTy lst ->
      let lst, ctx =
	renList (fun ctx -> function
		     (lb, None) -> (lb, None), ctx
		   | (lb, Some ty) ->
		       let ty, ctx = renTy ctx ty in
			 (lb, Some ty), ctx
		) ctx lst in
	SumTy lst, ctx
  | TupleTy lst ->
      let lst, ctx = renList renTy ctx lst in
	TupleTy lst, ctx
  | ArrowTy (ty1, ty2) ->
      let ty1, ctx = renTy ctx ty1 in
      let ty2, ctx = renTy ctx ty2 in
	ArrowTy (ty1, ty2), ctx
  | PolyTy(nms, ty) ->
      let nms, ctx = renNameList ctx nms in
      let ty, ctx = renTy ctx ty in
	PolyTy(nms, ty), ctx

and renTyList ctx lst = renList renTy ctx lst

and renTyOpt ctx = function
    None -> None, ctx
  | Some ty ->
      let ty, ctx = renTy ctx ty in
	Some ty, ctx

and renProp ctx = function
    (True | False) as p -> p, ctx

  | IsPer (nm, lst) ->
      let ctx = forbid nm ctx in
      let lst, ctx = renTermList ctx lst in
	IsPer (nm, lst), ctx

  | IsPredicate (nm, ty, lst) ->
      let ty, ctx = renTyOpt ctx ty in
      let ctx = forbid nm ctx in
      let lst, ctx =
	List.fold_left
	  (fun (bs, ct) (nm, ms) ->
	     let nm, ct = renName ct nm in
	     let ms, ct = renModest ct ms in
	       ((nm,ms)::bs, ct)
	  )
	  ([], ctx)
	  lst
      in
	IsPredicate (nm, ty, lst), ctx

  | IsEquiv (p, ms) ->
      let p, ctx = renProp ctx p in
      let ms, ctx = renModest ctx ms in
	IsEquiv (p, ms), ctx

  | NamedTotal (ln, lst) ->
      let ln, ctx = renLN ctx ln in
      let lst, ctx = renTermList ctx lst in
	NamedTotal (ln, lst), ctx

  | NamedPer (ln, lst) ->
      let ln, ctx = renLN ctx ln in
      let lst, ctx = renTermList ctx lst in
	NamedPer (ln, lst), ctx
      
  | NamedProp (ln, t, lst) ->
      let ln, ctx = renLN ctx ln in
      let t, ctx = renTerm ctx t in
      let lst, ctx = renTermList ctx lst in
	NamedProp (ln, t, lst), ctx

  | Equal (t1, t2) ->
      let t1, ctx = renTerm ctx t1 in
      let t2, ctx = renTerm ctx t2 in
	Equal (t1, t2), ctx

  | And ps ->
      let ps, ctx = renPropList ctx ps in
	And ps, ctx

  | Cor ps ->
      let ps, ctx = renPropList ctx ps in
	Cor ps, ctx

  | Imply (p1, p2) ->
      let p1, ctx = renProp ctx p1 in
      let p2, ctx = renProp ctx p2 in
	Imply (p1, p2), ctx

  | Iff (p1, p2) ->
      let p1, ctx = renProp ctx p1 in
      let p2, ctx = renProp ctx p2 in
	Iff (p1, p2), ctx

  | Not p ->
      let p, ctx = renProp ctx p in
	Not p, ctx

  | Forall (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
      let p, ctx = renProp ctx p in
	Forall (bnd, p), free (fst bnd) ctx

  | ForallTotal ((nm, ln), p) ->
      let ln, ctx = renLN ctx ln in
      let nm, ctx = renName ctx nm in
      let p, ctx = renProp ctx p in
	ForallTotal ((nm, ln), p), free nm ctx

  | Cexists (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
      let p, ctx = renProp ctx p in
	Cexists (bnd, p), free (fst bnd) ctx

  | PApp (p, t) ->
      let p, ctx = renProp ctx p in
      let t, ctx = renTerm ctx t in
	PApp (p, t), ctx

  | PMApp (p, t) ->
      let p, ctx = renProp ctx p in
      let t, ctx = renTerm ctx t in
	PMApp (p, t), ctx

  | PLambda (bnd, p) ->
      let bnd, ctx = renBinding ctx bnd in
      let p, ctx = renProp ctx p in
	PLambda (bnd, p), free (fst bnd) ctx

  | PMLambda ((nm, ms), p) ->
      let ms, ctx = renModest ctx ms in
      let nm, ctx = renName ctx nm in
      let p, ctx = renProp ctx p in
	PMLambda ((nm, ms), p), free nm ctx

  | PObligation (bnds, p1, p2) ->
      let bnds, ctx = renBindingList ctx bnds in
      let p1, ctx = renProp ctx p1 in
      let p2, ctx = renProp ctx p2 in
	(PObligation (bnds, p1, p2),
	List.fold_left (fun ct (nm,_) -> free nm ct) ctx bnds)

  | PCase (t1, t2, lst) ->
      let t1, ctx = renTerm ctx t1 in
      let t2, ctx = renTerm ctx t2 in
      let lst, ctx =
	renList
	  (fun ct (lb, b1, b2, p) ->
	     let b1, ct = renBindingOpt ct b1 in
	     let b2, ct = renBindingOpt ct b2 in
	     let p, ct = renProp ct p in
	     let ct = (match b1 with None -> ct | Some (nm, _) -> free nm ct) in
	     let ct = (match b2 with None -> ct | Some (nm, _) -> free nm ct) in
	       ((lb, b1, b2, p), ct)
	  )
	  ctx lst
      in
	PCase (t1, t2, lst), ctx

  | PLet (nm, t, p) ->
      let t, ctx = renTerm ctx t in
      let nm, ctx = renName ctx nm in
      let p, ctx = renProp ctx p in
	PLet (nm, t, p), free nm ctx

and renPropList ctx lst = renList renProp ctx lst

and renModest ctx {ty=ty; tot=p; per=q} =
  let p, ctx = renProp ctx p in
  let q, ctx = renProp ctx q in
    {ty=ty; tot=p; per=q}, ctx

and renAssertion ctx (str, p) =
  let ctx = forbid (mk_word str) ctx in
  let p, _ = renProp ctx p in
    (str, p), ctx

and renAssertionList ctx lst = renList renAssertion ctx lst

and renSpec ctx = function
    ValSpec (nms,ty) ->
      let nms, ctx = renNameList ctx nms in
      let ty, ctx = renTy ctx ty in
	ValSpec (nms, ty), ctx
  | ModulSpec sgnt ->
      let sgnt, ctx = renSignat ctx sgnt in
	ModulSpec sgnt, ctx
  | TySpec tyopt ->
      let tyopt, ctx = renTyOpt ctx tyopt in
	TySpec tyopt, ctx
  | SignatSpec sgnt ->
      let sgnt, ctx = renSignat ctx sgnt in
	SignatSpec sgnt, ctx

and renSignatElement ctx = function
    Spec (nm, spc, lst) ->
      let spc, ctx = renSpec ctx spc in
      let ctx = forbid nm ctx in
      let lst, ctx = renAssertionList ctx lst in
	Spec (nm, spc, lst), ctx
  | Assertion a ->
      let a, ctx = renAssertion ctx a in
	Assertion a, ctx
  | Comment _ as c -> c, ctx

and renSignatElementList ctx lst = renList renSignatElement ctx lst

and renSignat ctx = function
    SignatName nm -> SignatName nm, forbid nm ctx
  | SignatProj (mdl, nm) ->
      let mdl, ctx = renModul ctx mdl in
	SignatProj (mdl, nm), ctx
  | Signat lst ->
      let lst, ctx = renSignatElementList ctx lst in
	Signat lst, ctx
  | SignatFunctor ((nm, sgnt1), sgnt2) ->
      let sgnt1, ctx = renSignat ctx sgnt1 in
      let nm, ctx = renName ctx nm in
      let sgnt2, ctx = renSignat ctx sgnt2 in
	SignatFunctor ((nm, sgnt1), sgnt2), ctx
  | SignatApp (sgnt, mdl) ->
      let sgnt, ctx = renSignat ctx sgnt in
      let mdl, ctx' = renModul ctx mdl in
	SignatApp (sgnt, mdl), ctx

and renModul ctx = function
    ModulName nm ->
      begin try
	ModulName (N (NameMap.find nm (fst ctx))), ctx
      with
	  Not_found ->
	    let nm, ctx = renName ctx nm in
	      ModulName nm, ctx
      end
  | ModulProj (mdl, nm) ->
      let mdl, ctx = renModul ctx mdl in
	ModulProj (mdl, nm), ctx
  | ModulApp (mdl1, mdl2) ->
      let mdl1, ctx = renModul ctx mdl1 in
      let mdl2, ctx = renModul ctx mdl2 in
	ModulApp (mdl1, mdl2), ctx
  | ModulStruct lst ->
      let lst, ctx = renModuldefList ctx lst in
	ModulStruct lst, ctx

and renModuldef ctx = function
    DefType (nm, ty) -> 
      let ty, ctx = renTy ctx ty in
	DefType (nm, ty), forbid nm ctx
  | DefTerm (nm, ty, t) ->
      let ty, ctx = renTy ctx ty in
      let ctx = forbid nm ctx in
      let t, ctx = renTerm ctx t in
	DefTerm (nm, ty, t), ctx
  | DefModul (nm, sgnt, mdl) ->
      let ctx = forbid nm ctx in
      let sgnt, ctx = renSignat ctx sgnt in
      let mdl, ctx = renModul ctx mdl in
	DefModul (nm, sgnt, mdl), ctx
  | DefSignat (nm, sgnt) ->
      let ctx = forbid nm ctx in
      let sgnt, ctx = renSignat ctx sgnt in
	DefSignat (nm, sgnt), ctx

and renModuldefList ctx lst = renList renModuldef ctx lst
    
