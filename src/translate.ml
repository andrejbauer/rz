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
  | L.Basic (ln, _) -> toSubset ctx (getLongSet ctx ln)
  | _ -> failwith "not a subset"

(** translation functions *)

let any = wildName

let mk s = N(s, Word)

let fresh good ?(bad=[]) ctx = freshName good bad (occursCtx ctx)
let fresh2 g1 g2 ?(bad=[]) ctx = freshName2 g1 g2 bad (occursCtx ctx)
let fresh3 g1 g2 g3 ?(bad=[]) ctx = freshName3 g1 g2 g3 bad (occursCtx ctx)
let fresh4 g1 g2 g3 g4 ?(bad=[]) ctx = freshName4 g1 g2 g3 g4 bad (occursCtx ctx)
let freshList gs ?(bad=[]) ctx = freshNameList gs bad (occursCtx ctx)

let sbp nm t p = PLet (nm, t, p)
let sbt nm t u = Let (nm, t, u)

let rec map3 f lst1 lst2 lst3 =
  match lst1, lst2, lst3 with
      [], [], [] -> []
    | x::xs, y::ys, z::zs -> (f x y z) :: (map3 f xs ys zs)
    | _ -> failwith "map3"

let pApp p t = match p with
    PLambda ((n, _), q) -> sbp n t q
  | NamedTotal _ | NamedPer _ | NamedProp _ | PApp _ | PMApp _ | PObligation _ | PLet _ -> PApp (p, t)
  | PMLambda _ | True | False | IsPer _ | IsPredicate _ | IsEquiv _ | Equal _ | And _
  | Cor _ | Imply _ | Iff _ | Not _ | Forall _ | ForallTotal _ | Cexists _ | PCase _ ->
      failwith ("bad propositional application 1 on "  ^ string_of_proposition p ^ " :: " ^ string_of_term t)

let pMApp p t = match p with
    PMLambda ((n, _), q) -> sbp n t q
  | IsPer _ | NamedTotal _ | NamedPer _ | NamedProp _ | PApp _ | PMApp _ | PObligation _ | PLet _ ->
      PMApp (p, t)
  | PLambda _ -> failwith ("bad propositional application on " ^ string_of_proposition p)
  | True | False | IsPredicate _ | IsEquiv _ | Equal _ | And _
  | Cor _ | Imply _ | Iff _ | Not _   | Forall _ | ForallTotal _ | Cexists _ | PCase _ ->
      failwith ("bad propositional application 2 on " ^ string_of_proposition p ^ " :: " ^ string_of_term t)

let forall_tot (x, s) p = Forall ((x, s.ty), Imply (pApp s.tot (id x), p))

let nest_forall ctx = List.fold_right forall_tot

let nest_forall_ty ctx =
  List.fold_right (fun (y, {ty=t}) p -> Forall ((y,t), p))

let nest_lambda ctx =
  List.fold_right (fun b p -> PMLambda (b, p))

let makeTot (x, t) p = PLambda ((x,t), p)

let makePer (x, y, t) p = PLambda ((x,t), PLambda ((y,t), p))

let makeProp (x, t) p = (t, PLambda ((x,t), p))

let isPredicate ctx n ty binds =
  let xs = List.map fst binds in
  let r = fresh [mk "r"; mk "u"] ~bad:xs ctx in
  let ys = Name.freshNameList (List.map (fun n -> [n]) xs) (r::xs) (occursCtx ctx) in
    And [
	nest_forall_ty ctx binds
	  (Forall ((r, ty), Imply (NamedProp (n, id r, List.map id xs),
				  And (List.map (fun (x,s) -> pApp s.tot (id x)) binds))));
	nest_forall ctx binds
	  (nest_forall ctx (List.map2 (fun (_,s) y -> (y,s)) binds ys)
	    (Forall ((r, ty),
		   Imply (And (List.map2 (fun (x,s) y -> pApp (pApp s.per (id x)) (id y)) binds ys),
			 Imply (NamedProp (n, id r, List.map id xs),
			       NamedProp (n, id r, List.map id ys))))))]

let isEquiv ctx p s =
  let q u v = pApp (pMApp (pMApp p (id u)) (id v)) Dagger in
  let x, y, z =
    fresh3
      [mk "x"; mk "y"; mk "z"; mk "u"]
      [mk "x"; mk "y"; mk "z"; mk "u"]
      [mk "x"; mk "y"; mk "z"; mk "u"] ctx
  in
    And [
	forall_tot (x, s) (q x x);
	forall_tot (x, s) (forall_tot (y, s) (Imply (q x y, q y x)));
	forall_tot (x, s) (forall_tot (y, s) (forall_tot (z, s) (Imply (And [q x y; q y z], q x z))))
    ]

let isPer ctx p ty =
  let q u v = pApp (pApp p (id u)) (id v) in
  let x, y, z =
    fresh3
      [mk "x"; mk "y"; mk "z"; mk "u"]
      [mk "x"; mk "y"; mk "z"; mk "u"]
      [mk "x"; mk "y"; mk "z"; mk "u"] ctx
  in
    And [
	Forall ((x, ty), Forall ((y, ty), Imply (q x y, q y x)));
	Forall ((x, ty), Forall ((y, ty), (Forall ((z, ty), (Imply (And [q x y; q y z], q x z))))))
    ]

(** Main translation functions *)

let rec translateSet (ctx : ctxElement list) = function
    L.Empty -> 
      { ty  = VoidTy;
	tot = makeTot (any(), VoidTy) False;
	per = makePer (any(), any(), VoidTy) False;
      }

  | L.Unit ->
      let x, y = fresh2 [mk "x"; mk "y"; mk "u"] [mk "y"; mk "z"; mk "v"] ctx in
      { ty  = UnitTy;
	tot = makeTot (x, UnitTy) (Equal (id x, EmptyTuple));
	per = makePer (x, y, UnitTy) (Equal (id x, id y));
      }

  | L.Basic (sln, knd) ->
      let nm = translateSLN sln in
      let binds = bindings_of_setkind ctx knd in
	{ ty  = NamedTy nm;
	  tot = nest_lambda ctx binds (NamedTotal (nm, List.map (fun (y,_) -> id y) binds));
	  per = nest_lambda ctx binds (NamedPer (nm, List.map (fun (y,_) -> id y) binds));
	}

  | L.Product lst ->
      let _, nms, ws =
	List.fold_left
	  (fun (ctx, nms, ws) (nm,st) -> (insertTermvar nm st ctx, nm::nms, (translateSet ctx st)::ws))
	  (ctx, [], [])
	  lst
      in
      let n = List.length ws - 1 in
      let nms = List.rev nms in
      let ws = List.rev ws in
      let v = TupleTy (List.map (fun w -> w.ty) ws) in
	{
	  ty = v;
	  tot = (
	    let t = fresh [mk "t"; mk "u"; mk "v"] ~bad:nms ctx in
	      makeTot
		(t, v)
		(fst (List.fold_right
		       (fun nm (p,k) -> PLet (nm, Proj (k, id t), p), k-1)
		       nms
		       (And (List.map2 (fun nm w -> pApp w.tot (id nm)) nms ws), n)
		))
	  );
	  per = (
	      let t, u = fresh2 [mk "t"; mk "u"; mk "v"] [mk "u"; mk "v"; mk "w"] ~bad:nms ctx in
	      let nms' = Name.freshNameList (List.map (fun n -> [n]) nms) (t::u::nms) (occursCtx ctx) in
		makePer (t, u, v) 
		  (fst (List.fold_right (fun nm (p,k) -> PLet (nm, Proj (k, id t), p), k-1) nms
			 (
			   (fst (List.fold_right (fun nm (p,k) -> PLet (nm, Proj (k, id u), p), k-1) nms'
				  (And (map3 (fun nm nm' w -> pApp (pApp w.per (id nm)) (id nm')) nms nms' ws), n))
			   ), n)
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
	  [mk "x"; mk "y"; mk "z"]
	  [mk "f"; mk "g"; mk "h"]
	  [mk "g"; mk "h"; mk "k"] ~bad:[nm] ctx
      in
	{ ty = w;
	  tot = makeTot (f, w)
	    (Forall ((z, u),
		    Forall ((z', u),
			   Imply (
			       pApp (pApp p (id z)) (id z'),
			       pApp (pApp (sbp nm (id z) q) (App (id f, id z))) (App (id f, id z'))
			   ))));
	  per = makePer (f, g, w)
	    (Forall ((z, u),
		    Forall ((z', u),
			   Imply (
			       pApp (pApp p (id z)) (id z'),
			       pApp (pApp (sbp nm (id z) q) (App (id f, id z))) (App (id g, id z'))
			   ))))
	}


  | L.Subset ((n, s), phi) ->
      let {ty=u; tot=p; per=q} = translateSet ctx s in
      let (v,r) = translateProp (insertTermvar n s ctx) phi in
      let w = TupleTy [u; v] in
	{
	  ty = w;
	  tot = (
	    let k = fresh [mk "k"; mk "j"; mk "r"] ctx in
	      makeTot (k,w)
	      (And [pApp p (Proj (0, id k));
		    pApp (sbp n (Proj (0, id k)) r) (Proj (1, id k))]
	      ));
	  per = (
	    let y, y'  = fresh2 [mk "x"; mk "y"; mk "w"] [mk "x'"; mk "y'"; mk "w'"] ctx in
	      makePer (y, y', w) (And [
		  pApp (sbp n (Proj (0, id y )) r) (Proj (1, id y ));
		  pApp (sbp n (Proj (0, id y')) r) (Proj (1, id y'));
		  pApp (pApp q (Proj (0, id y))) (Proj (0, id y'))
	      ])
	  )
	}

  | L.Quotient (s, e) ->
      let {ty=t; tot=p; per=q} = translateSet ctx s in
      let ty, r = translateProp ctx e in
	{ ty = t;
	  tot = p;
	  per = (
	    let x, x' = fresh2 [mk "x"; mk "e"; mk "q"] [mk "y"; mk "e"; mk "q"] ctx in
	      makePer (x, x', t) (pApp (pMApp (pMApp r (id x)) (id x')) (dagger_of_ty ty))
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
			   Cexists ((x', u), And [Equal (id x, Inj (lb, Some (id x'))); pApp p (id x')]))
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
					 pApp (pApp q (id w)) (id w')])))
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
	  tot = pMApp p t';
	  per = pMApp q t';
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
      let {ty=t; tot=p1; per=p2} = translateSet ctx s in
      let (v,q) = translateProp (insertTermvar n s ctx) phi in
      let n', z, z' = fresh3 [n] [mk "x"; mk "y"; mk "z"] [mk "x"; mk "y"; mk "z"] ~bad:[n] ctx in
	Obligation ([(n, t); (z,v)], 
		   And [pApp p1 (id n);
			pApp q (id z);
			Forall ((n',t),
			       Imply (pApp p1 (id n'),
				     Forall ((z',v),
					    Imply (pApp (sbp n (id n') q) (id z'),
						  pApp (pApp p2 (id n)) (id n')))))],
		   Tuple [id n; id z]
		   )

  | L.Inj (lb, None) -> Inj (lb, None)

  | L.Inj (lb, Some t) -> Inj (lb, Some (translateTerm ctx t))

  | L.Case (t1, _, lst, _) ->
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
      let v' = sbt n (id n') v in
	Let (n, translateTerm ctx t,
	     Obligation ([],
			 Forall ((n', ty1),
				 Imply (pApp (pApp p1 (id n)) (id n'),
					pApp (pApp p2 v) v')),
			 v))

  | L.Quot (t, _) -> translateTerm ctx t

  | L.Choose ((n, st1), r, t, u, st2) ->
      let {ty=ty1; per=p1} = translateSet ctx st1 in
      let {per=p2} = translateSet ctx st2 in
      let ty2, q = translateProp ctx r in
      let n' = fresh [n] ~bad:[n] ctx in
      let v = translateTerm (insertTermvar n st1 ctx) u in
      let v' = sbt n (id n') v in
	Let (n, translateTerm ctx t,
	     Obligation ([],
			 Forall ((n', ty1), Imply (
				   pApp (pMApp (pMApp q (id n)) (id n')) (dagger_of_ty ty2),
				   pApp (pApp p2 v) v')),
			 v))

  | L.Let ((n, s), u, v, _) ->
      Let (n, translateTerm ctx u, translateTerm (insertTermvar n s ctx) v)

  | L.Subin (t, sb) ->
      let ((x, s), p) = toSubset ctx sb in
      let (ty, p') = translateProp (insertTermvar x s ctx) p in
      let t' = translateTerm ctx t in
      let y = fresh [mk "x"; mk "y"; mk "v"; mk "u"; mk "t"] ~bad:((fvTerm t')) ctx in
	Tuple[t'; Obligation ([(y, ty)], pApp (sbp x t' p') (id y), id y)]

  | L.Subout (t, _) -> Proj (0, translateTerm ctx t)

  | L.Assure (None, p, t, _) ->
      let (ty, p') = translateProp ctx p in
	Obligation ([], pApp p' (dagger_of_ty ty), translateTerm ctx t)

  | L.Assure (Some (n, s), p, t, _) ->
      let {ty=ty2; tot=q} = translateSet ctx s in
      let ctx' = insertTermvar n s ctx in
      let (ty1, p') = translateProp ctx' p in
	Obligation ([(n, ty2)],
		   And [pApp q (id n); pApp p' (dagger_of_ty ty1)],
		   translateTerm ctx' t)

			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * name * Outsyn.negative *)
and translateProp ctx = function
    L.False -> makeProp (any(), TopTy) False

  | L.True -> makeProp (any(), TopTy) True

  | L.Atomic (ln, pt) ->
      let ty =
	(if L.is_stable (getLong getProp ctx ln)
	  then TopTy
	  else NamedTy (translateSLN (L.sln_of_ln ln)))
      in
      let r = fresh [mk "r"; mk "u"; mk "t"; mk "w"] ctx in
      let binds = bindings_of_proptype ctx pt in
	(ty, nest_lambda ctx binds
	  (PLambda ((r, ty), NamedProp (translateLN ln, id r, List.map (fun (y,_) -> id y) binds))))

  | L.And lst ->
      let lst' = List.map (translateProp ctx) lst in
      let t = fresh [mk "t"; mk "p"; mk "u"; mk "q"; mk "r"] ctx in
	makeProp (t, TupleTy (List.map fst lst'))
	  (And (let k = ref 0 in
		  List.map
		    (fun (_, p) -> let q = pApp p (Proj (!k, id t)) in incr k ; q)
		    lst'))

  | L.Imply (p, q) ->
      let (t, p') = translateProp ctx p in
      let (u, q') = translateProp ctx q in
      let x, f = fresh2 [mk "x"; mk "y"; mk "z"] [mk "f"; mk "g"; mk "h"; mk "p"; mk "q"] ctx in
	makeProp (f, ArrowTy (t, u))
	  (Forall ((x, t),
		  Imply (pApp p' (id x), pApp q' (App (id f, id x)))))

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
	      Forall ((x, t), Imply (pApp p' (id x), pApp q' (App (Proj (0, id f), id x))));
	      Forall ((y, t), Imply (pApp q' (id y), pApp p' (App (Proj (1, id f), id y))))
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
		     Cexists ((x,t), And [Equal(id u, Inj (lb, Some (id x))); pApp p (id x)]))
		lbs lst'
	 ))

  | L.Forall ((n, s), p) ->
      let {ty=t; tot=q} = translateSet ctx s in
      let (u, p') = translateProp (insertTermvar n s ctx) p in
      let f = fresh [mk "f"; mk "g"; mk "h"; mk "l"] ~bad:[n] ctx in
	makeProp (f, ArrowTy (t, u))
	  (Forall ((n, t), Imply (pApp q (id n), pApp p' (App (id f, id n)))))

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=q} = translateSet ctx s in
      let (u, p') = translateProp (insertTermvar n s ctx) p in
      let w = fresh [mk "w"; mk "u"; mk "p"; mk "t"] ~bad:[n] ctx
      in
	makeProp (w, TupleTy [t; u])
	 (And [pApp q (Proj (0, id w));
	       pApp (sbp n (Proj (0, id w)) p') (Proj (1, id w))])

  | L.Unique ((n, s), p) -> 
      let {ty=t; tot=q; per=pr} = translateSet ctx s in
      let (u, p') = translateProp (insertTermvar n s ctx) p in
      let w, w' = fresh2 [mk "w"; mk "u"; mk "p"; mk "t"] [mk "u"; mk "p"; mk "t"] ~bad:[n] ctx in
	makeProp (w, TupleTy [t; u])
	 (And [
	     pApp q (Proj (0, id w));
	     pApp (sbp n (Proj (0, id w)) p') (Proj (1, id w));
	     Forall ((w', TupleTy [t; u]),
		    Imply (And [pApp q (Proj (0, id w'));
				pApp (sbp n (Proj (0, id w')) p') (Proj (1, id w;))],
			  pApp (pApp pr (Proj (0, id w))) (Proj (0, id w'))))
	 ])

  | L.Not p ->
      let (t, p') = translateProp ctx p in
      let r = fresh [mk "r"; mk "u"; mk "t"] ctx in
	makeProp (any(), TopTy) (Forall ((r, t), Not (pApp p' (id r))))

  | L.Equal (s, t, u) ->
      let {per=p} = translateSet ctx s in
      let t' = translateTerm ctx t in
      let u' = translateTerm ctx u in
	makeProp (any(), TopTy) (pApp (pApp p t') u')

  | L.PLambda ((n, s), p) ->
      let (ty1, p') = translateProp (insertTermvar n s ctx) p in
      let u = translateSet ctx s in
	(ty1, PMLambda ((n, u), p'))

  | L.PApp (p, t) -> 
      let (ty, q) = translateProp ctx p in
	(ty, pMApp q (translateTerm ctx t))

  | L.IsEquiv (p, s) ->
      let (_, p') = translateProp ctx p in
      let s' = translateSet ctx s in
	makeProp (any(), TopTy) (isEquiv ctx p' s')


  | L.PCase (t, _, lst) ->
      let tys, arms = List.fold_left
	(fun (tys, arms) -> function
	    (lb, Some (n, s), p) ->
	      let {ty=ty2; tot=q} = translateSet ctx s in
	      let (ty1, p') = translateProp (insertTermvar n s ctx) p in
	      let x = fresh [mk "r"; mk "q"; mk "s"] ~bad:[n] ctx in
		(lb, Some ty1)::tys, (lb, Some (x, ty1), Some (n, ty2),
				     And [pApp q (id n); pApp p' (id x)])::arms
          | (lb, None, p) ->
	      let (ty1, p') = translateProp ctx p in
	      let x = fresh [mk "r"; mk "q"; mk "s"] ctx in
		(lb, Some ty1)::tys, (lb, Some (x, ty1), None, pApp p' (id x))::arms
	)
	([], [])
        lst
      in
      let r = fresh [mk "r"; mk "u"] ctx in
	makeProp (r, SumTy tys) (PCase (id r, translateTerm ctx t, arms))

  | L.PAssure (None, p, q) ->
      let (ty1, p') = translateProp ctx p in
      let (ty2, q') = translateProp ctx q in
	ty2, PObligation ([], pApp p' (dagger_of_ty ty1), q')

  | L.PAssure (Some (n, s), p, q) ->
      let {ty=ty2; tot=r} = translateSet ctx s in
      let ctx' = insertTermvar n s ctx in
      let (ty1, p') = translateProp ctx' p in
      let (ty3, q') = translateProp ctx q in
	ty3, PObligation ([(n, ty2)], And [pApp r (id n); pApp p' (dagger_of_ty ty1)], q')

  | L.PLet ((n,s), t, p) ->
      let ty, q = translateProp (insertTermvar n s ctx) p in
	ty, PLet (n, translateTerm ctx t, q)
      

and translateBinding ctx bind =
  List.map (fun (n, s) -> n, (translateSet ctx s).ty) bind

and bindings_of_proptype ctx = function
    L.Prop | L.StableProp -> []
  | L.EquivProp s ->
      let x, y = fresh2 [mk "x"; mk "y"; mk "z"] [mk "y"; mk "z"; mk "w"] ctx in
      let ms = translateSet ctx s in
	[(x, ms); (y, ms)]
  | L.PropArrow (m, s, pt) ->
      let m' = if isWild m then fresh [mk "x"; mk "y"; mk "z"; mk "w"] ctx else m in
	(m', translateSet ctx s) :: (bindings_of_proptype (insertTermvar m' s ctx) pt)

and equiv_bindings_of_proptype ctx = function
    L.Prop | L.StableProp -> failwith "Translate.equiv_bindings_of_proptype: not an equivalence"
  | L.EquivProp s -> [], [], translateSet ctx s
  | L.PropArrow (m, s, pt) ->
      let m' =
	if isWild m then
	  fresh [mk "x"; mk "y"; mk "z"; mk "w"] ctx
	else
	  m
      in
      let bnd1, bnd2, t = equiv_bindings_of_proptype (insertTermvar m' s ctx) pt in
	(m', translateSet ctx s) :: bnd1, (m',s) :: bnd2, t

and bindings_of_setkind ctx = function
    L.KindSet -> []
  | L.KindArrow (m, s, knd) ->
      let m' = if isWild m then fresh [mk "x"; mk "y"; mk "z"] ctx else m in
	(m', translateSet ctx s) :: (bindings_of_setkind (insertTermvar m' s ctx) knd)

and translateTheoryElements ctx = function
    [] -> [], emptyCtx
  | L.Declaration(n, L.DeclSet (None, knd)) :: rest -> 
      let sgnt, smmry = translateTheoryElements (insertAbstractSetvar n knd ctx) rest in
	(Spec (n, TySpec None, [("per_" ^ string_of_name n,
			   (let binds = bindings_of_setkind ctx knd in
			      nest_forall ctx binds
				(IsPer (n, (List.map (fun (y,_) -> id y) binds)))
			   ))])) :: sgnt,
	(insertAbstractSetvar n knd smmry)

  | L.Declaration(n, L.DeclSet(Some s, knd)) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertSetvar n knd s ctx) rest in	
	(let {ty=t; tot=p; per=q} = translateSet ctx s in
	let binds = bindings_of_setkind ctx knd in
	let ys = List.map fst binds in
	let idys = List.map id ys in
	let x = fresh [mk "x"; mk "y"] ~bad:ys ctx in
	let y, y' = fresh2 [mk "y"; mk "z"; mk "w"] [mk "y"; mk "z"; mk "w"] ~bad:ys ctx in
	  Spec (n, TySpec (Some t),
            [(string_of_name n ^ "_def_total",
	      nest_forall ctx binds
		(Forall((x,t),
			Iff (PApp (NamedTotal (ln_of_name n, idys), id x),
			     pApp (List.fold_left (pMApp) p idys) (id x)))));
	     (string_of_name n ^ "_def_per",
	     nest_forall ctx binds
	       (Forall ((y,t),
                       Forall ((y',t),
			      Iff (PApp (PApp (NamedPer (ln_of_name n, idys), id y), id y'),
				  pApp (pApp (List.fold_left (pMApp) q idys) (id y)) (id y'))))))]
	)) :: sgnt,
	insertSetvar n knd s smmry

  | L.Declaration(n, L.DeclProp(None, pt)) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertPropvar n pt ctx) rest in
      let binds = bindings_of_proptype ctx pt in
      let spec =
	isPredicate
	  ctx (ln_of_name n)
	  (if L.is_stable pt then TopTy else NamedTy (ln_of_name n))
	  binds
      in
	(if L.is_stable pt then
	   Assertion ("predicate_" ^ (string_of_name n), spec)
	 else
	   (Spec (L.typename_of_name n,
		    TySpec None,
		    [("predicate_" ^ (string_of_name n), spec)]))
	) :: (if L.is_equiv pt then
	    [Assertion    ("equiv_" ^ (string_of_name n),
			    let bnds1, bnds2, s' = equiv_bindings_of_proptype ctx pt in
			    let ctx' = insertBinding bnds2 ctx in
			    let xs = List.map fst bnds1 in
			    let x, y = fresh2 [mk "x"; mk "y"; mk "z"] [mk "x"; mk "y"; mk "z"] ~bad:xs ctx in
			    let p =
			      PMLambda ((x,s'),
                              PMLambda ((y,s'),
       			      PLambda ((any(), TopTy), 
                                NamedProp (ln_of_name n, Dagger, (List.map id xs) @ [id x; id y]))))
			    in
			      nest_forall ctx bnds1 (isEquiv ctx' p s')
	    )]
	  else []
	) @ sgnt,
      insertPropvar n pt smmry

  | L.Declaration(n, L.DeclProp(Some p, pt)) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertPropvar n pt ctx) rest in
	(let (ty, p') = translateProp ctx p in
	let binds = bindings_of_proptype ctx pt in
	let ys = List.map fst binds in
	let idys = List.map id ys in
	let r = fresh [mk "r"; mk "q"] ~bad:ys ctx in
	  Spec (
	    L.typename_of_name n,
	    TySpec (Some ty),
            [((string_of_name n) ^ "_def",
	     nest_forall ctx binds
	       (Forall ((r, ty),
		  Iff (
		      NamedProp (ln_of_name n, id r, idys),
		      pApp (List.fold_left pMApp p' idys) (id r)
		  )))
	    )])
	) :: sgnt,
      insertPropvar n pt smmry

  | L.Declaration(n, L.DeclTerm(Some t, s)) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertTermvar n s ctx) rest in
	(let {ty=u; per=q} = translateSet ctx s in
	 let t' = translateTerm ctx t in
	   Spec(n, ValSpec u, [((string_of_name n) ^ "_def", pApp (pApp q (id n)) t')])
	) :: sgnt,
	insertTermvar n s smmry

  | L.Declaration(n, L.DeclTerm(None, s)) :: rest ->
      let sgnt, smmry = translateTheoryElements (insertTermvar n s ctx) rest in
       (let {ty=t; tot=p} = translateSet ctx s in
	  Spec (n, ValSpec t, [((string_of_name n) ^ "_total", pApp p (id n))])
       ) :: sgnt,
       insertTermvar n s smmry

  | L.Comment cmmnt :: rest ->
      let sgnt, smmry = translateTheoryElements ctx rest in
	(Comment cmmnt) :: sgnt, smmry

  | L.Declaration(nm, L.DeclSentence (mdlbind, prp)) :: rest ->
      let sgnt, smmry = translateTheoryElements ctx rest in
	begin
	  let strctbind, ctx' = translateModelBinding ctx mdlbind in
	  let (typ, prp') = translateProp ctx' prp in
	  let elem =
	    Spec (nm, ValSpec typ, [(string_of_name nm, pApp prp' (id nm))])
	  in
	    if mdlbind = [] then
	      elem
	    else
	      let fnctr =
		List.fold_right (fun bnd sgnt -> SignatFunctor (bnd,sgnt)) strctbind (Signat [elem])
	      in
		Spec(capitalize_name nm, ModulSpec fnctr, [])
	end :: sgnt,
	smmry

  | L.Declaration(mdlnm, L.DeclModel (thr)) :: rest ->
      let sgnt, smmry = translateTheory ctx thr in
      let sgnt', smmry' = translateTheoryElements (insertModelvar mdlnm smmry ctx) rest in
	Spec (mdlnm, ModulSpec sgnt, []) :: sgnt',
	(insertModelvar mdlnm smmry smmry')

  | L.Declaration(n, L.DeclTheory (thr,_)) :: rest ->
     let sgnt, smmry = translateTheory ctx thr in
     let sgnt', smmry' = translateTheoryElements (addTheory n smmry ctx) rest in
       Spec(n, SignatSpec sgnt, []) :: sgnt',
       addTheory n smmry smmry'

and translateSLN = function
    L.SLN (None, nm) -> LN (None, nm)
  | L.SLN (Some mdl, nm) -> LN (Some (translateModel mdl), nm)

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

let translateToplevel = translateTheoryElements
