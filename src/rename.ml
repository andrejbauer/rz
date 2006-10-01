(** Intelligent renaming for outsyn. *)

open Name
open Outsyn

let emptyRen = (NameMap.empty, NameSet.empty)

let forbid nm (ren, bad) = (ren, NameSet.add nm bad)

let insert nm1 nm2 (ren, bad) = (NameMap.add nm1 nm2 ren, NameSet.add nm2 bad)

let renBound (ren, bad) nm =
  let nm' = newRename bad nm in
    nm', (NameMap.add nm nm' ren, NameSet.add nm' bad)

let renBoundModul (ren,bad) nm =
  let nm' = newRename bad nm in
    nm', (NameMap.add nm nm' ren, NameSet.add nm' bad)
    
let renLN ctx = function
    LN (Some _, _) as ln -> ln, ctx
  | LN (None, nm) ->
      begin try
	LN (None, NameMap.find nm (fst ctx)), ctx
      with
	  Not_found ->
	    let nm, ctx = renBound ctx nm in
	      LN (None, nm), ctx
      end

let renBinding ctx (nm, ty) =
  let nm, ctx = renBound ctx nm in
    (nm, ty), ctx
      
let renBindingOpt ctx = function
    None -> None, ctx
  | Some bnd ->
      let bnd, ctx = renBinding ctx bnd in
	Some bnd, ctx

and renList f ctx lst =
  let lst, ctx =
    List.fold_right
      (fun t (ts, ct) -> let t, ct = f ct t in t::ts, ct)
      lst
      ([], ctx)
  in
    lst, ctx

let rec renTerm ((ren, bad) as ctx) = function
    (EmptyTuple | Dagger | Inj (_, None)) as t -> t, ctx

  | Id ln ->
      let ln, ctx = renLN ctx ln in
	Id ln, ctx

  | App (t1, t2) ->
      let t1, ctx = renTerm ctx t1 in
      let t2, ctx = renTerm ctx t2 in
	App (t1, t2), ctx

  | Lambda ((nm, ty), t) ->
      let nm, ctx = renBound ctx nm in
      let t, ctx = renTerm ctx t in
	Lambda ((nm, ty), t), ctx

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
	       | (lb, Some (nm, ty), t) ->
		   let nm, ct = renBound ct nm in
		   let t, ct = renTerm ct t in
		     (lb, Some (nm, ty), t)::ts, ct)
	  ([], ctx)
	  lst
      in
	Case (t, lst), ctx

  | Let (nm, t1, t2) ->
      let t1, ctx = renTerm ctx t1 in
      let nm, ctx = renBound ctx nm in
      let t2, ctx = renTerm ctx t2 in
	Let (nm, t1, t2), ctx

  | Obligation (bnds, p, t) ->
      let bnds, ctx =
	List.fold_left
	  (fun (bs, ct) (nm,ty) -> let nm, ct = renBound ct nm in ((nm,ty)::bs, ct))
	  ([], ctx)
	  bnds
      in
      let p, ctx = renProp ctx p in
      let t, ctx = renTerm ctx t in
	Obligation (bnds, p, t), ctx

and renTermList ctx lst = renList renTerm ctx lst

and renProp ctx = function
    (True | False) as p -> p, ctx

  | IsPer (tynm, lst) ->
      let ctx = forbid tynm ctx in
      let lst, ctx = renTermList ctx lst in
	IsPer (tynm, lst), ctx

  | IsPredicate (nm, ty, lst) ->
      let ctx = forbid nm ctx in
      let lst, ctx =
	List.fold_left
	  (fun (bs, ct) (nm, ms) ->
	     let nm, ct = renBound ct nm in
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

  | Forall ((nm,ty), p) ->
      let nm, ctx = renBound ctx nm in
      let p, ctx = renProp ctx p in
	Forall ((nm,ty), p), ctx

  | ForallTotal ((nm, ln), p) ->
      let ln, ctx = renLN ctx ln in
      let nm, ctx = renBound ctx nm in
      let p, ctx = renProp ctx p in
	ForallTotal ((nm, ln), p), ctx

  | Cexists ((nm,ty), p) ->
      let nm, ctx = renBound ctx nm in
      let p, ctx = renProp ctx p in
	Cexists ((nm,ty), p), ctx

  | PApp (p, t) ->
      let p, ctx = renProp ctx p in
      let t, ctx = renTerm ctx t in
	PApp (p, t), ctx

  | PMApp (p, t) ->
      let p, ctx = renProp ctx p in
      let t, ctx = renTerm ctx t in
	PMApp (p, t), ctx

  | PLambda ((nm, ty), p) ->
      let nm, ctx = renBound ctx nm in
      let p, ctx = renProp ctx p in
	PLambda ((nm, ty), p), ctx

  | PMLambda ((nm, ms), p) ->
      let ms, ctx = renModest ctx ms in
      let nm, ctx = renBound ctx nm in
      let p, ctx = renProp ctx p in
	PMLambda ((nm, ms), p), ctx

  | PObligation (bnds, p1, p2) ->
      let bnds, ctx =
	List.fold_left
	  (fun (bs,ct) (nm,ty) -> let nm, ct = renBound ct nm in ((nm,ty)::bs, ct))
	  ([], ctx)
	  bnds
      in
      let p1, ctx = renProp ctx p1 in
      let p2, ctx = renProp ctx p2 in
	PObligation (bnds, p1, p2), ctx

  | PCase (t1, t2, lst) ->
      let t1, ctx = renTerm ctx t1 in
      let t2, ctx = renTerm ctx t2 in
      let lst, ctx =
	List.fold_left
	  (fun (bs,ct) (lb, b1, b2, p) ->
	     let b1, ct = renBindingOpt ct b1 in
	     let b2, ct = renBindingOpt ct b2 in
	     let p, ct = renProp ct p in
	       ((lb, b1, b2, p)::bs, ct)
	  )
	  ([], ctx)
	  lst
      in
	PCase (t1, t2, lst), ctx

  | PLet (nm, t, p) ->
      let t, ctx = renTerm ctx t in
      let nm, ctx = renBound ctx nm in
      let p, ctx = renProp ctx p in
	PLet (nm, t, p), ctx

and renPropList ctx lst = renList renProp ctx lst

and renModest ctx {ty=ty; tot=p; per=q} =
  let p, ctx = renProp ctx p in
  let q, ctx = renProp ctx q in
    {ty=ty; tot=p; per=q}, ctx

let renAssertion ctx (str, p) =
  let p, _ = renProp ctx p in
    (str, p), ctx

let renAssertionList = renList renAssertion

let rec renSpec ctx = function
    ValSpec _ as s -> s, ctx
  | ModulSpec sgnt ->
      let sgnt, ctx = renSignat ctx sgnt in
	ModulSpec sgnt, ctx
  | TySpec _ as s -> s, ctx
  | SignatSpec sgnt ->
      let sgnt, ctx = renSignat ctx sgnt in
	SignatSpec sgnt, ctx

and renSignatElement ctx = function
    Spec (nm, spc, lst) ->
      let ctx = forbid nm ctx in
      let spc, _ = renSpec ctx spc in
      let lst, _ = renAssertionList ctx lst in
	Spec (nm, spc, lst), ctx
  | Assertion a ->
      let a, _ = renAssertion ctx a in
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
      let nm, ctx = renBoundModul ctx nm in
      let sgnt2, ctx = renSignat ctx sgnt2 in
	SignatFunctor ((nm, sgnt1), sgnt2), ctx
  | SignatApp (sgnt, mdl) ->
      let sgnt, ctx = renSignat ctx sgnt in
      let mdl, ctx' = renModul ctx mdl in
	SignatApp (sgnt, mdl), ctx

and renModul ctx = function
    ModulName nm -> ModulName nm, forbid nm ctx
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
    DefType (nm, ty) -> DefType (nm, ty), forbid nm ctx
  | DefTerm (nm, ty, t) ->
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
    
