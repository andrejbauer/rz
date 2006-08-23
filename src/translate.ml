module L = Logic
open Outsyn
open Name

(* exception Unimplemented *)

(** contexts (environments)
    We're anticipating dependent contexts here so we have a single
    context with everything stuffed in it.

    A context entry is one of:
    - name bound to a type
    - definition of a set (name = set definition)
    - definition of a proposition
    - model name with its summary
    - theory name with its summary
*)

type ctxElement =
    CtxVar of name * L.set
  | CtxSet of L.set_name * L.setkind * L.set option
  | CtxProp of name * L.proptype
  | CtxModel of L.model_name * theorySummary
  | CtxTheory of L.theory_name * theorySummary

and theorySummary = 
    Ctx of ctxElement list
  | CtxParam of L.model_name * signat * theorySummary

let emptyCtx = []

let name_of_ctx_entry = function
    CtxVar (nm, _) -> nm
  | CtxSet (nm, _, _) -> nm
  | CtxProp (nm, _) -> nm
  | CtxModel (nm, _) -> nm
  | CtxTheory (nm, _) -> nm

let occursCtx ctx nm = List.exists (fun e -> nm = name_of_ctx_entry e) ctx

let insertTermvar        n s   ctx = CtxVar(n,s) :: ctx
let insertAbstractSetvar n knd ctx = CtxSet(n,knd,None) :: ctx
let insertSetvar       n knd s ctx = CtxSet(n,knd,Some s) :: ctx
let insertPropvar        n stb ctx = CtxProp(n,stb) :: ctx
let insertModelvar       n thr ctx = CtxModel(n,thr) :: ctx
let addTheory            n thr ctx = CtxTheory(n,thr) :: ctx

let insertBinding bind ctx =
  List.fold_left (fun ctx (n,s) -> insertTermvar n s ctx) ctx bind

let getBind n ctx =
  let rec find = function
      [] -> raise Not_found
    | CtxVar (m,s) :: ctx' -> if n = m then s else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx
    
let getSet n ctx =
  let rec find = function
      [] -> raise Not_found
    | CtxSet(m,_,Some s) :: ctx' -> if n = m then s else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx
    
let getProp n ctx =
  let rec find = function
      [] -> failwith ("No such proposition " ^ (string_of_name n))
    | CtxProp (m,stb) :: ctx' -> if n = m then stb else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx

let getTheory n ctx =
  let rec find = function
      [] -> (failwith ("No such theory " ^ string_of_name n))
    | CtxTheory (m,thr) :: ctx' -> if n = m then thr else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx

let rec getModel n ctx =
  let rec find = function
      [] -> raise Not_found
    | CtxModel(m,thr) :: ctx' -> if n = m then thr else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx

let rec translateModel = function
    L.ModelName nm -> ModulName nm
  | L.ModelProj (mdl, nm) -> ModulProj (translateModel mdl, nm)
  | L.ModelApp (mdl1, mdl2) -> ModulApp (translateModel mdl1, translateModel mdl2)

let translateLN = function
    L.LN (None, nm) -> LN (None, nm)
  | L.LN (Some mdl, nm) -> LN (Some (translateModel mdl), nm)

let rec substMCtx m mdl = function
    [] -> []
  | CtxVar (nm,st) :: lst -> CtxVar (nm, L.substMSet m mdl st) :: (substMCtx m mdl lst)
  | CtxSet (stnm, knd, stopt) :: lst ->
      CtxSet (stnm, L.substMSetkind m mdl knd, L.substMSetOption m mdl stopt) :: (substMCtx m mdl lst)
  | (CtxProp _ as el) :: lst -> el :: (substMCtx m mdl lst)
  | CtxModel (nm, summary) :: lst ->
      CtxModel (nm, substMSummary m mdl summary) :: (if nm = m then lst else substMCtx m mdl lst)
  | CtxTheory _ :: _ -> failwith "substMCtx: cannot have a theory inside a theory"

and substMSummary m mdl = function
    Ctx elems -> Ctx (substMCtx m mdl elems)
  | (CtxParam (m', sgnt, summary)) as s ->
      if m = m' then
	s
      else CtxParam (m',
		     substSignat (insertModulvar emptysubst m (translateModel mdl)) sgnt,
		     substMSummary m mdl summary)

let rec normalizeModel ctx = function
    L.ModelName n -> getModel n ctx
  | L.ModelProj (mdl, n) ->
      (match normalizeModel ctx mdl with
	   Ctx elems -> getModel n elems
	 | CtxParam _ -> failwith "normalizeModel: cannot project from a functor")
  | L.ModelApp (mdl1, mdl2) ->
      (match normalizeModel ctx mdl1 with
	   Ctx _ -> failwith "normalizeModel: cannot apply a non-parametrized model"
	 | CtxParam (m, _, smmry) -> substMSummary m mdl2 smmry)

let rec getLong getter ctx ln =
  let rec find = function
      L.LN(None, nm) -> getter nm ctx
    | L.LN(Some mdl, nm) ->
	(match normalizeModel ctx mdl with
	     Ctx elems -> getter nm elems
	   | CtxParam _ -> failwith "getLong: cannot project from a functor")
  in 
    find ln

let rec getLongSet ctx ln =
  let rec find = function
      L.SLN(None, nm) -> getSet nm ctx
    | L.SLN(Some mdl, nm) ->
	(match normalizeModel ctx mdl with
	     Ctx elems -> getSet nm elems
	   | CtxParam _ -> failwith "getLong: cannot project from a functor")
  in 
    find ln


(** *** *)

let rec toSubset ctx = function
    L.Subset ((x,s), p) -> ((x, s), p)
  | L.Basic ln -> toSubset ctx (getLongSet ctx ln)
  | _ -> failwith "not a subset"

(** translation functions *)

let any = wildName

let mk s = N(s, Word)

let fresh good ?(bad=[]) ctx = freshName good bad (occursCtx ctx)
let fresh2 g1 g2 ?(bad=[]) ctx = freshName2 g2 g2 bad (occursCtx ctx)
let fresh3 g1 g2 g3 ?(bad=[]) ctx = freshName3 g1 g2 g3 bad (occursCtx ctx)
let fresh4 g1 g2 g3 g4 ?(bad=[]) ctx = freshName4 g1 g2 g3 g4 bad (occursCtx ctx)
let freshList gs ?(bad=[]) ctx = freshNameList gs bad (occursCtx ctx)

let sbp ctx ?(bad=[]) lst =
  substProp ~occ:(fun nm -> List.mem nm bad || occursCtx ctx nm) (termsSubst lst)

let sbt ctx lst = substTerm ~occ:(occursCtx ctx) (termsSubst lst)

let pApp ctx p t = match p with
    PLambda ((n,_), q) -> sbp ctx [(n,t)] q
  | NamedTotal _ | NamedPer _ | NamedProp _ | PApp _ | PMApp _ | PObligation _ -> PApp (p, t)
  | PMLambda _ | True | False | IsPer _ | IsPredicate _ | IsEquiv _ | Equal _ | And _
  | Cor _ | Imply _ | Iff _ | Not _ | Forall _ | ForallTotal _ | Cexists _ ->
      failwith "bad propositional application"

let pMApp ctx p t = match p with
    PMLambda ((n,_), q) -> sbp ctx [(n,t)] q
  | NamedTotal _ | NamedPer _ | NamedProp _ | PApp _ | PMApp _ | PObligation _ -> PMApp (p, t)
  | PLambda _ | True | False | IsPer _ | IsPredicate _ | IsEquiv _ | Equal _ | And _
  | Cor _ | Imply _ | Iff _ | Not _ | Forall _ | ForallTotal _ | Cexists _ ->
      failwith "bad propositional application"

let nest_forall = List.fold_right (fun b p -> Forall (b, p))

let makeTot (x, t) p = PLambda ((x,t), p)

let makePer (x, y, t) p = PLambda ((x,t), PLambda ((y,t), p))

let makeProp (x, t) p = (t, PLambda ((x,t), p))

let rec translateSet (ctx : ctxElement list) = function
    L.Empty -> 
      { ty  = VoidTy;
	tot = makeTot (any(), VoidTy) False;
	per = makePer (any(), any(), VoidTy) False;
      }

  | L.Unit ->
      let x = fresh [mk "x"] ctx in
      { ty  = UnitTy;
	tot = makeTot (x, UnitTy) (Equal (id x, EmptyTuple));
	per = makePer (any(), any(), UnitTy) True;
      }

  | L.Basic sln ->
      let s' = translateSLN sln in
	{ ty  = NamedTy s';
	  tot = NamedTotal s';
	  per = NamedPer s'
	}

  | L.Product lst ->
      let us = snd
	(List.fold_left 
	   (fun (ctx, us) (nm, st) -> (insertTermvar nm st ctx, (translateSet ctx st) :: us))
	   (ctx, [])
	   lst) in
      let v = TupleTy (List.map (fun u -> u.ty) us) in
	{
	  ty = v;
	  tot = (
	    let t = fresh [mk "t"; mk "u"; mk "v"] ctx in
	      makeTot (t, v)
		(And (let k = ref 0 in
			List.map
			  (fun u -> let q = pApp ctx u.tot (Proj (!k, id t)) in incr k ; q)
			  us
		))
	  );
	  per = (
	      let t, u = fresh2 [mk "t"; mk "u"; mk "v"] [mk "u"; mk "v"; mk "w"] ctx in
		makePer (t, u, v) (And (
		    let k = ref 0 in
		      List.map
			(fun u -> let q = pApp ctx (pApp ctx u.per (Proj (!k, id t))) (Proj (!k, id t)) in incr k; q)
			us
		))
	  )
	}

  | L.Exp (nm, s, t) ->
      let {ty=u; per=p} = translateSet ctx s in
      let {ty=v; per=q} = translateSet (insertTermvar nm s ctx) t in
      let w = ArrowTy (u, v) in
      let z, z', f, g =
	fresh4
	  [mk "x"; mk "y"; mk "z"]
	  [mk "x'"; mk "y'"; mk "z'"]
	  [mk "f"; mk "g"; mk "h"]
	  [mk "g"; mk "h"; mk "k"] ~bad:[nm] ctx
      in
	{ ty = w;
	  tot = makeTot (f, w)
	    (Forall ((z, u),
		    Forall ((z', u),
			   Imply (
			       pApp ctx (pApp ctx p (id z)) (id z'),
			       pApp ctx (pApp ctx (pMApp ctx q (id z)) (App (id f, id z))) (App (id f, id z'))
			   ))));
	  per = makePer (f, g, w)
	    (Forall ((z, u),
		    Forall ((z', u),
			   Imply (
			       pApp ctx (pApp ctx p (id z)) (id z'),
			       pApp ctx (pApp ctx (pMApp ctx q (id z)) (App (id f, id z))) (App (id g, id z'))
			   ))))
	}


  | L.Subset ((n, s), phi) ->
      let {ty=u; tot=p; per=q} = translateSet ctx s in
      let (v,r) = translateProp (insertTermvar n s ctx) phi in
      let w = TupleTy [u; v] in
	{
	  ty = w;
	  tot = (
	    let k = fresh [mk "k"; mk "j"; mk "x"] ctx in
	      makeTot (k,w)
	      (And [pApp ctx p (Proj (0, id k));
		    pApp ctx (sbp ctx [(n, Proj (0, id k))] r) (id k)]
	      ));
	  per = (
	    let y, y'  = fresh2 [mk "x"; mk "y"; mk "w"] [mk "x'"; mk "y'"; mk "w'"] ctx in
	      makePer (y, y', w) (pApp ctx (pApp ctx q (Proj (0, id y))) (Proj (0, id y'))))
	}

  | L.Quotient (s, e) ->
      let {ty=t; tot=p; per=q} = translateSet ctx s in
      let _, r = translateProp ctx e in
	{ ty = t;
	  tot = p;
	  per = (
	    let x, x' = fresh2 [mk "x"] [mk "y"] ctx in
	      makePer (x, x', t) (pApp ctx (pApp ctx (pApp ctx r (id x)) (id x')) Dagger)
	  )
	}


  | L.Sum lst -> 
      let lst' = List.map (function
			       (lb, None) -> (lb, None)
			     | (lb, Some s) -> (lb, Some (translateSet ctx s)))
		   lst
      in
      let t = SumTy (List.map (function
				    (lb, None) -> (lb, None)
				  | (lb, Some {ty=u}) -> (lb, Some u)
			       ) lst')
      in
      let x, y, y' = fresh3
	[mk "w"; mk "t"; mk "u"; mk "p"]
	[mk "v"; mk "u"; mk "s"; mk "p"]
	[mk "w"; mk "t"; mk "r"; mk "q"] ctx
      in
	{
	  ty = t;
	  tot = makeTot (x, t)
	    (Cor (List.map
		   (function
		       (lb, None) -> Equal (id x, Inj (lb, None))
		     | (lb, Some {ty=u; tot=p}) ->
			 let x' = fresh [x] ~bad:[x] ctx in
			   Cexists ((x', u), And [Equal (id x, Inj (lb, Some (id x'))); pApp ctx p (id x')]))
		   lst')
	    );
	  per = makePer (y, y', t)
	    (Cor (List.map
		   (function
		       (lb, None) -> And [Equal (id y,  Inj (lb, None)); Equal (id y', Inj (lb, None))]
		     | (lb, Some {ty=u; per=q}) ->
			 let w, w' =  fresh2 [y] [y'] ~bad:[y;y'] ctx in
			   Cexists ((w,u),
		           Cexists ((w',u),
				    And [Equal (id y, Inj (lb, Some (id w)));
					 Equal (id y', Inj (lb, Some (id w')));
					 pApp ctx (pApp ctx q (id w)) (id w')])))
		   lst')
	  )
	}

  | L.Rz s ->
      let {ty=t; tot=p} = translateSet ctx s in
	{
	  ty = t;
	  tot = p;
	  per = 
	    let x, x' = fresh2 [mk "x"; mk "y"] [mk "x'"; mk "y'"] ctx in
	      makePer (x, x',t) (Equal (id x, id x'));
	}

  | L.SApp (s, t) ->
      let {ty=v; tot=p; per=q} = translateSet ctx s in
      let t' = translateTerm ctx t in
	{
	  ty = v;
	  tot = pMApp ctx p t';
	  per = pMApp ctx q t';
	}

  | L.SLambda ((n, s), t) ->
       let u = translateSet ctx s in
       let {ty=v; tot=p; per=q} = translateSet (insertTermvar n s ctx) t in
       {
	 ty = v;
	 tot = PMLambda ((n, u), p);
	 per = PMLambda ((n, u), q)
       }


and translateTerm ctx = function
    L.Var ln -> Id (translateLN ln)

  | L.EmptyTuple -> EmptyTuple

  | L.Tuple lst -> Tuple (List.map (translateTerm ctx) lst)

  | L.Proj (k, t) -> Proj (k, translateTerm ctx t)

  | L.App (u, v) -> App (translateTerm ctx u, translateTerm ctx v)

  | L.Lambda ((n, s), t) -> Lambda ((n, (translateSet ctx s).ty), translateTerm ctx t)

  | L.The ((n, s), phi) ->
      let {per=p; ty=t} = translateSet ctx s in
      let (v,q) = translateProp (insertTermvar n s ctx) phi in
      let n', z = fresh2 [n] [mk "z"] ~bad:[n] ctx in
	Obligation ((n, t), True,
		   Obligation ((z,v),
			      And [pApp ctx q (id z);
				   Forall ((n',t),
					  Imply (pApp ctx (sbp ctx [(n, id n')] q) (id z),
						pApp ctx (pApp ctx p (id n)) (id n')))],
			      id n
		    ))

  | L.Inj (lb, None) -> Inj (lb, None)

  | L.Inj (lb, Some t) -> Inj (lb, Some (translateTerm ctx t))

  | L.Case (t1, lst) ->
      Case (translateTerm ctx t1, List.map
	       (function
		    (lb, Some (n, s), t) ->
		      let ctx' = insertTermvar n s ctx in
			(lb, Some (n, (translateSet ctx' s).ty), translateTerm ctx' t)
                  | (lb, None, t) ->
                      (lb, None, translateTerm (insertTermvar (any()) L.Unit ctx) t)
	       )
               lst
	    )
  | L.RzQuot t -> translateTerm ctx t

  | L.RzChoose ((n, st1), t, u, st2) ->
      let {ty=ty1; per=p1} = translateSet ctx st1 in
      let {per=p2} = translateSet ctx st2 in
      let n' = fresh [n] ~bad:[n] ctx in
      let v = translateTerm (insertTermvar n st1 ctx) u in
      let v' = sbt ctx [(n, id n')] v in
	Let (n, translateTerm ctx t,
	     Obligation ((any(), TopTy),
			 Forall ((n', ty1),
				 Imply (pApp ctx (pApp ctx p1 (id n)) (id n'),
					pApp ctx (pApp ctx p2 v) v')),
			 v))

  | L.Quot (t, _) -> translateTerm ctx t

  | L.Choose ((n, st1), r, t, u, st2) ->
      let {ty=ty1; per=p1} = translateSet ctx st1 in
      let {per=p2} = translateSet ctx st2 in
      let _, q = translateProp ctx r in
      let n' = fresh [n] ~bad:[n] ctx in
      let v = translateTerm (insertTermvar n st1 ctx) u in
      let v' = sbt ctx [(n, id n')] v in
	Let (n, translateTerm ctx t,
	     Obligation ((any(), TopTy),
			 Forall ((n', ty1), Imply (
				   pApp ctx (pApp ctx (pApp ctx q (id n)) (id n')) Dagger,
				   pApp ctx (pApp ctx p2 v) v')),
			 v))

  | L.Let ((n, s), u, v, _) ->
      Let (n, translateTerm ctx u, translateTerm (insertTermvar n s ctx) v)

  | L.Subin (t, sb) ->
      let ((x, s), p) = toSubset ctx sb in
      let (ty, p') = translateProp (insertTermvar x s ctx) p in
      let t' = translateTerm ctx t in
      let y = fresh [mk "x"; mk "y"; mk "v"; mk "u"; mk "t"] ctx in
	Obligation ((y, ty), pApp ctx (pApp ctx p' t') (id y), Tuple [t'; id y])

  | L.Subout (t, _) -> Proj (0, translateTerm ctx t)
			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * name * Outsyn.negative *)
and translateProp ctx = function
    L.False -> makeProp (any(), TopTy) False

  | L.True -> makeProp (any(), TopTy) True

  | L.Atomic ln ->
      let ty =
	(if L.is_stable (getLong getProp ctx ln)
	  then TopTy
	  else NamedTy (translateSLN (L.sln_of_ln ln)))
      in
	(ty, NamedProp (translateLN ln))

  | L.And lst ->
      let lst' = List.map (translateProp ctx) lst in
      let t = fresh [mk "t"; mk "p"; mk "u"; mk "q"; mk "r"] ctx in
	makeProp (t, TupleTy (List.map fst lst'))
	  (And (let k = ref 0 in
		  List.map
		    (fun (_, p) -> let q = pApp ctx p (Proj (!k, id t)) in incr k ; q)
		    lst'))

  | L.Imply (p, q) ->
      let (t, p') = translateProp ctx p in
      let (u, q') = translateProp ctx q in
      let x, f = fresh2 [mk "x"; mk "y"; mk "z"] [mk "f"; mk "g"; mk "h"; mk "p"; mk "q"] ctx in
	makeProp (f, ArrowTy (t, u))
	  (Forall ((x, t),
		  Imply (pApp ctx p' (id x), pApp ctx q' (App (id f, id x)))))

  | L.Iff (p, q) -> 
      let (t, p') = translateProp ctx p in
      let (u, q') = translateProp ctx q in
      let x, y, f = fresh3
	[mk "x"; mk "y"; mk "z"]
	[mk "y"; mk "z"; mk "x"]
	[mk "f"; mk "g"; mk "h"; mk "p"; mk "q"] ctx
      in
	makeProp (f, TupleTy [ArrowTy (t, u); ArrowTy (u, t)])
	  (And [
	      Forall ((x, t), Imply (pApp ctx p' (id x), pApp ctx q' (App (Proj (0, id f), id x))));
	      Forall ((y, t), Imply (pApp ctx q' (id y), pApp ctx p' (App (Proj (1, id f), id y))))
	  ])
	  
  | L.Or lst ->
      let rec make_labels i j =
	if i >= j then [] else ("or" ^ (string_of_int i)) :: (make_labels (i+1) j)
      in
      let lst' = List.map (translateProp ctx) lst in
      let lbs = make_labels 0 (List.length lst) in
      let u = fresh [mk "u"; mk "v"; mk "w"; mk "r"] ctx in
      let ty = SumTy (List.map2 (fun lb (t,_) -> (lb, Some t)) lbs lst') in
	makeProp (u, ty)
	 (Cor (
	   List.map2
		(fun lb (t,p) ->
		   let x = fresh [mk "x"; mk "y"] ~bad:[u] ctx in
		     Cexists ((x,t), And [Equal(id u, Inj (lb, Some (id x))); pApp ctx p (id x)]))
		lbs lst'
	 ))

  | L.Forall ((n, s), p) ->
      let {ty=t; tot=q} = translateSet ctx s in
      let (u, p') = translateProp (insertTermvar n s ctx) p in
      let f = fresh [mk "f"; mk "g"; mk "h"; mk "l"] ctx in
	makeProp (f, ArrowTy (t, u))
	  (Forall ((n, t), Imply (pApp ctx q (id n), pApp ctx p' (App (id f, id n)))))

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=q} = translateSet ctx s in
      let (u, p') = translateProp (insertTermvar n s ctx) p in
      let w = fresh [mk "w"; mk "u"; mk "p"; mk "t"] ctx
      in
	makeProp (w, TupleTy [t; u])
	 (And [pApp ctx q (Proj (0, id w));
	       pApp ctx (sbp ctx [(n, Proj (0, id w))] p') (Proj (1, id w))])

  | L.Unique ((n, s), p) -> 
      let {ty=t; tot=q; per=pr} = translateSet ctx s in
      let (u, p') = translateProp (insertTermvar n s ctx) p in
      let w, w' = fresh2 [mk "w"; mk "u"; mk "p"; mk "t"] [mk "u"; mk "p"; mk "t"] ctx in
	makeProp (w, TupleTy [t; u])
	 (And [
	     pApp ctx q (Proj (0, id w));
	     pApp ctx (sbp ctx [(n, Proj (0, id w))] p') (Proj (1, id w));
	     Forall ((w', TupleTy [t; u]),
		    Imply (And [pApp ctx q (Proj (0, id w'));
				pApp ctx (sbp ctx [(n, Proj (0, id w'))] p') (Proj (1, id w;))],
			  pApp ctx (pApp ctx pr (Proj (0, id w))) (Proj (0, id w'))))
	 ])

  | L.Not p ->
      let (t, p') = translateProp ctx p in
      let r = fresh [mk "r"; mk "u"; mk "t"] ctx in
	makeProp (any(), TopTy) (Forall ((r, t), Not (pApp ctx p' (id r))))

  | L.Equal (s, t, u) ->
      let {per=p} = translateSet ctx s in
      let t' = translateTerm ctx t in
      let u' = translateTerm ctx u in
	makeProp (any(), TopTy) (pApp ctx (pApp ctx p t') u')

  | L.PLambda ((n, s), p) ->
      let (ty1, p') = translateProp (insertTermvar n s ctx) p in
      let u = translateSet ctx s in
	(ty1, PMLambda ((n, u), p'))

  | L.PApp (p, t) -> 
      let (ty, q) = translateProp ctx p in
	(ty, PApp (q, translateTerm ctx t))

  | L.EquivCoerce (s, p) ->
      let t = translateSet ctx s in
      let (_, r) = translateProp ctx p in
      let x, y = fresh2 [mk "x"; mk "y"] [mk "y"; mk "z"] ctx in
      let q = PLambda ((x, t.ty),
		      PLambda ((y, t.ty),
			      pApp ctx (pApp ctx (pApp ctx r (id x)) (id y)) Dagger))
      in
	(TopTy, PObligation (IsEquiv (t, q), r))

and translateBinding ctx bind =
  List.map (fun (n, s) -> n, (translateSet ctx s).ty) bind

and translateProptype ctx n = function
    L.Prop ->
      (match n with
	  None -> failwith "invalid proptype translation"
	| Some n -> NamedTy (tln_of_tyname n))
  | L.StableProp -> TopTy
  | L.EquivProp s ->
      let {ty=t} = translateSet ctx s in
	ArrowTy (t, ArrowTy (t, TopTy))
  | L.PropArrow (m, s, pt) ->
      let {ty=t} = translateSet ctx s in
	ArrowTy (t, translateProptype (insertTermvar m s ctx) n pt)

and bindings_of_proptype ctx = function
    L.Prop | L.StableProp | L.EquivProp _ -> []
  | L.PropArrow (m, s, pt) ->
      let n = fresh [(if isWild m then mk "x" else m)] ctx in
      let {ty=t} = translateSet ctx s in
	(n,t) :: (bindings_of_proptype (insertTermvar m s ctx) pt)

and translateTheoryElements ctx = function
    [] -> [], emptyCtx
  | L.Set (n, knd) :: rest -> 
      let sgnt, smmry = translateTheoryElements (insertAbstractSetvar n knd ctx) rest in
	(TySpec (n, None, [("per_" ^ string_of_name n, IsPer n)])) :: sgnt,
	(insertAbstractSetvar n knd smmry)

  | L.Let_set (n, knd, s) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertSetvar n knd s ctx) rest in	
	(let {ty=t; tot=p; per=q} = translateSet ctx s in
	   TySpec (n, Some t,
		    [(string_of_name n ^ "_def_total",
		      let x = fresh [mk "x"; mk "y"] ctx in
			Forall((x,t), Iff (PApp (NamedTotal (tln_of_tyname n), id x), p)));
		     (string_of_name n ^ "_def_per",
		      let y, y' = fresh2 [mk "y"; mk "z"; mk "w"] [mk "y"; mk "z"; mk "w"] ctx in
			Forall ((y,t),
			       Forall ((y',t),
				      Iff (PApp (PApp (NamedPer (tln_of_tyname n), id y), id y'), q))))]
	)) :: sgnt,
	insertSetvar n knd s smmry

  | L.Predicate (n, pt) :: rest -> begin
      let sgnt, smmry = translateTheoryElements (insertPropvar n pt ctx) rest in
	(if L.is_stable pt then
	    AssertionSpec ("predicate_" ^ (string_of_name n), IsPredicate (n, translateProptype ctx None pt))
	  else
	    TySpec (L.typename_of_name n,
		   None,
		   [("predicate_" ^ (string_of_name n),
		    IsPredicate (n, translateProptype ctx (Some (L.typename_of_name n)) pt))])
	) :: sgnt,
      insertPropvar n pt smmry
    end

  | L.Let_predicate (n, pt, p) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertPropvar n pt ctx) rest in
	(let (ty, p') = translateProp ctx p in
	let binds = bindings_of_proptype ctx pt in
	let r = fresh [mk "r"; mk "q"] ~bad:(List.map fst binds) ctx in
	  TySpec (L.typename_of_name n, Some ty,
            [((string_of_name n) ^ "_def",
	     nest_forall binds
	       (Forall ((r, ty),
		       Iff (
			   PApp (List.fold_left (fun p (y,_) -> PApp (p, id y))
				  (NamedProp (ln_of_name n)) binds, id r),
			   pApp ctx (List.fold_left (fun p (y,_) -> pApp ctx p (id y)) p' binds) (id r)
		       )
		 ))
	    )])
	) :: sgnt,
      insertPropvar n pt smmry

  | L.Let_term (n, s, t) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertTermvar n s ctx) rest in
	(let {ty=u; per=q} = translateSet ctx s in
	 let t' = translateTerm ctx t in
	   ValSpec (n, u, [((string_of_name n) ^ "_def", pApp ctx (pApp ctx q (id n)) t')])
	) :: sgnt,
	insertTermvar n s smmry

  | L.Value (n, s) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertTermvar n s ctx) rest in
       (let {ty=t; tot=p} = translateSet ctx s in
	  ValSpec (n, t, [((string_of_name n) ^ "_total", pApp ctx p (id n))])
       ) :: sgnt,
       insertTermvar n s smmry

  | L.Comment cmmnt :: rest ->
      let sgnt, smmry = translateTheoryElements ctx rest in
	(Comment cmmnt) :: sgnt, smmry

  | L.Sentence (nm, mdlbind, prp) :: rest ->
      let sgnt, smmry = translateTheoryElements ctx rest in
	begin
	  let strctbind, ctx' = translateModelBinding ctx mdlbind in
	  let (typ, prp') = translateProp ctx' prp in
	  let elem =
	    ValSpec (nm, typ, [(string_of_name nm, pApp ctx' prp' (id nm))])
	  in
	    if mdlbind = [] then
	      elem
	    else
	      let fnctr =
		List.fold_right (fun bnd sgnt -> SignatFunctor (bnd,sgnt)) strctbind (Signat [elem])
	      in
		ModulSpec (capitalize_name nm, fnctr)
	end :: sgnt,
	smmry

  | L.Model (mdlnm, thr) :: rest ->
      let sgnt, smmry = translateTheory ctx thr in
      let sgnt', smmry' = translateTheoryElements (insertModelvar mdlnm smmry ctx) rest in
	ModulSpec (mdlnm, sgnt) :: sgnt',
	(insertModelvar mdlnm smmry smmry')


and translateSLN = function
    L.SLN (None, nm) -> TLN (None, nm)
  | L.SLN (Some mdl, nm) -> TLN (Some (translateModel mdl), nm)

and translateModelBinding ctx = function
    [] -> [], ctx
  | (m, th) :: rest ->
      let signat, smmry = translateTheory ctx th in
      let signats, ctx' = translateModelBinding (insertModelvar m smmry ctx) rest in
	(m, signat) :: signats, ctx'

and translateTheory ctx = function
    L.Theory body ->
      let sgnt, smmry = translateTheoryElements ctx body in
	Signat sgnt, Ctx smmry
  | L.TheoryName id -> SignatName id, getTheory id ctx
  | L.TheoryLambda ((nm, thr1), thr2)
  | L.TheoryArrow ((nm,thr1),thr2) ->
      let sgnt1, smmry1 = translateTheory ctx thr1 in
      let sgnt2, smmry2 = translateTheory (insertModelvar nm smmry1 ctx) thr2 in
	SignatFunctor ((nm, sgnt1), sgnt2), CtxParam (nm, sgnt2, smmry2)
  | L.TheoryApp (thr, mdl) ->
      let sgnt, smmry = translateTheory ctx thr in
      let modul = translateModel mdl in
	(match smmry with
	     Ctx _ -> failwith "translateTheory: cannot apply a non-parametrized theory"
	   | CtxParam (m, sgnt', smmry') ->
	       SignatApp (sgnt, modul, substSignat (insertModulvar emptysubst m modul) sgnt'),
	       substMSummary m mdl smmry')
		 
let attachSignat s (ss, ctx) = s::ss, ctx

let rec translateToplevel ctx = function
  | [] -> [], ctx
  | L.Theorydef (n, thr) :: rest -> 
      let sgnt, smmry = translateTheory ctx thr in
	attachSignat (Signatdef (n, sgnt)) (translateToplevel (addTheory n smmry ctx) rest)
  | L.TopComment cmmnt :: rest ->
      attachSignat (TopComment cmmnt) (translateToplevel ctx rest)
  | L.TopModel (mdlnm, thry) :: rest ->
      let sgnt, smmry = translateTheory ctx thry in
	attachSignat (TopModul (mdlnm, sgnt)) (translateToplevel (insertModelvar mdlnm smmry ctx) rest)
