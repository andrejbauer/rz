module L = Logic
open Outsyn
open Name

let rec translateModel = function
    L.ModelName nm -> ModulName nm
  | L.ModelProj (mdl, nm) -> ModulProj (translateModel mdl, nm)
  | L.ModelApp (mdl1, mdl2) -> ModulApp (translateModel mdl1, translateModel mdl2)
  | L.ModelOf _ -> failwith "Translate.translateModel: unimplemented"

let translateLN = function
    L.LN (None, nm) -> LN (None, nm)
  | L.LN (Some mdl, nm) -> LN (Some (translateModel mdl), nm)

let any = wildName

let mk s = s

(* Pick a suitable name of a given set *)
let rec good = function
    VoidTy -> [mk "v"; mk "w"; mk "u"]
  | UnitTy -> [mk "u"; mk "v"; mk "w"]
  | TopTy -> [mk "dagger"]
  | NamedTy _ -> [mk "x"; mk "y"; mk "z"; mk "w"; mk "t"]
  | SumTy _ -> [mk "i"; mk "j"; mk "k"; mk "m"]
  | TupleTy (ArrowTy _ as ty :: _) -> good ty
  | TupleTy _ -> [mk "p"; mk "q"; mk "t"; mk "u"]
  | ArrowTy (ArrowTy (ArrowTy _, _), _) -> [mk "alpha"; mk "beta"; mk "gamma"; mk "delta"]
  | ArrowTy (ArrowTy (_, _), _) -> [mk "phi"; mk "psi"; mk "xi"; mk "zeta"]
  | ArrowTy _ -> [mk "f"; mk "g"; mk "h"; mk "r"]
  | PolyTy _ -> failwith "Translate.good:  unexpected PolyTy"

let rec goodRz = [mk "a"; mk "b"; mk "c"; mk "d"]

let fresh ty = freshName (good ty)
let fresh2 ty = fresh ty, fresh ty
let fresh3 ty = fresh ty, fresh ty, fresh ty
let fresh4 ty = fresh ty, fresh ty, fresh ty, fresh ty

let freshRz = freshName goodRz
let freshList tys = List.map fresh tys

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

let nest_forall = List.fold_right forall_tot

let nest_forall_ty = List.fold_right (fun (y, {ty=t}) p -> Forall ((y,t), p))

let nest_lambda = List.fold_right (fun b p -> PMLambda (b, p))

let makeTot (x, t) p = PLambda ((x,t), p)

let makePer (x, y, t) p = PLambda ((x,t), PLambda ((y,t), p))

let makeProp (x, t) p = (t, PLambda ((x,t), p))

let isPredicate n ty binds =
  let xs = List.map fst binds in
  let r = freshRz in
  let ys = freshList (List.map (fun (_,{ty=t}) -> t) binds) in
    And [
	nest_forall_ty binds
	  (Forall ((r, ty), Imply (NamedProp (n, id r, List.map id xs),
				  And (List.map (fun (x,s) -> pApp s.tot (id x)) binds))));
	nest_forall binds
	  (nest_forall (List.map2 (fun (_,s) y -> (y,s)) binds ys)
	    (Forall ((r, ty),
		   Imply (And (List.map2 (fun (x,s) y -> pApp (pApp s.per (id x)) (id y)) binds ys),
			 Imply (NamedProp (n, id r, List.map id xs),
			       NamedProp (n, id r, List.map id ys))))))]

let isEquiv p s =
  let q u v = pApp (pMApp (pMApp p (id u)) (id v)) Dagger in
  let x, y, z = fresh3 s.ty in
    And [
	forall_tot (x, s) (q x x);
	forall_tot (x, s) (forall_tot (y, s) (Imply (q x y, q y x)));
	forall_tot (x, s) (forall_tot (y, s) (forall_tot (z, s) (Imply (And [q x y; q y z], q x z))))
    ]

(** Main translation functions *)

let rec translateSet = function
    L.Empty -> 
      { ty  = VoidTy;
	tot = makeTot (any(), VoidTy) False;
	per = makePer (any(), any(), VoidTy) False;
      }

  | L.Unit ->
      let x, y = fresh2 UnitTy in
      { ty  = UnitTy;
	tot = makeTot (x, UnitTy) (Equal (id x, EmptyTuple));
	per = makePer (x, y, UnitTy) (Equal (id x, id y));
      }

  | L.Basic (sln, knd) ->
      let nm = translateSLN sln in
      let binds = bindings_of_setkind knd in
	{ ty  = NamedTy nm;
	  tot = nest_lambda binds (NamedTotal (nm, List.map (fun (y,_) -> id y) binds));
	  per = nest_lambda binds (NamedPer (nm, List.map (fun (y,_) -> id y) binds));
	}

  | L.Product lst ->
      let nms, ws =
	List.fold_left
	  (fun (nms, ws) (nm,st) -> (nm::nms, (translateSet st)::ws))
	  ([], [])
	  lst
      in
      let n = List.length ws - 1 in
      let nms = List.rev nms in
      let ws = List.rev ws in
      let v = TupleTy (List.map (fun w -> w.ty) ws) in
	{
	  ty = v;
	  tot = (
	    let t = fresh v in
	      makeTot
		(t, v)
		(fst (List.fold_right
		       (fun nm (p,k) -> PLet (nm, Proj (k, id t), p), k-1)
		       nms
		       (And (List.map2 (fun nm w -> pApp w.tot (id nm)) nms ws), n)
		))
	  );
	  per = (
	      let t, u = fresh2 v in
	      let nms' = List.map refresh nms in
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
      let {ty=u; per=p} = translateSet s in
      let {ty=v; per=q} = translateSet t in
      let w = ArrowTy (u, v) in
      let z, z' = fresh2 u in
      let f, g = fresh2 w in
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
      let {ty=u; tot=p; per=q} = translateSet s in
      let (v,r) = translateProp phi in
      let w = TupleTy [u; v] in
	{
	  ty = w;
	  tot = (
	    let k = fresh u in
	      makeTot (k,w)
	      (And [pApp p (Proj (0, id k));
		    pApp (sbp n (Proj (0, id k)) r) (Proj (1, id k))]
	      ));
	  per = (
	    let y, y'  = fresh2 u in
	      makePer (y, y', w) (And [
		  pApp (sbp n (Proj (0, id y )) r) (Proj (1, id y ));
		  pApp (sbp n (Proj (0, id y')) r) (Proj (1, id y'));
		  pApp (pApp q (Proj (0, id y))) (Proj (0, id y'))
	      ])
	  )
	}

  | L.Quotient (s, e) ->
      let {ty=t; tot=p; per=q} = translateSet s in
      let ty, r = translateProp e in
	{ ty = t;
	  tot = p;
	  per = (
	    let x, x' = fresh2 t in
	      makePer (x, x', t) (pApp (pMApp (pMApp r (id x)) (id x')) (dagger_of_ty ty))
	  )
	}


  | L.Sum lst -> 
      let lst' = List.map (function
			       (lb, None) -> (lb, None)
			     | (lb, Some s) -> (lb, Some (translateSet s)))
		   lst
      in
      let t = SumTy (List.map (function
				    (lb, None) -> (lb, None)
				  | (lb, Some {ty=u}) -> (lb, Some u)
			       ) lst')
      in
      let x, y, y' = fresh3 t in
	{
	  ty = t;
	  tot = makeTot (x, t)
	    (Cor (List.map
		   (function
		       (lb, None) -> Equal (id x, Inj (lb, None))
		     | (lb, Some {ty=u; tot=p}) ->
			 let x' = refresh x in
			   Cexists ((x', u), And [Equal (id x, Inj (lb, Some (id x'))); pApp p (id x')]))
		   lst')
	    );
	  per = makePer (y, y', t)
	    (Cor (List.map
		   (function
		       (lb, None) -> And [Equal (id y,  Inj (lb, None)); Equal (id y', Inj (lb, None))]
		     | (lb, Some {ty=u; per=q}) ->
			 let w = refresh y in
			 let w' = refresh y' in
			   Cexists ((w,u),
		           Cexists ((w',u),
				    And [Equal (id y, Inj (lb, Some (id w)));
					 Equal (id y', Inj (lb, Some (id w')));
					 pApp (pApp q (id w)) (id w')])))
		   lst')
	  )
	}

  | L.Rz s ->
      let {ty=t; tot=p} = translateSet s in
	{
	  ty = t;
	  tot = p;
	  per = 
	    let x, x' = freshRz, freshRz in
	      makePer (x, x',t) (Equal (id x, id x'));
	}

  | L.SApp (s, t) ->
      let {ty=v; tot=p; per=q} = translateSet s in
      let t' = translateTerm t in
	{
	  ty = v;
	  tot = pMApp p t';
	  per = pMApp q t';
	}

  | L.SLambda ((n, s), t) ->
       let u = translateSet s in
       let {ty=v; tot=p; per=q} = translateSet t in
       {
	 ty = v;
	 tot = PMLambda ((n, u), p);
	 per = PMLambda ((n, u), q)
       }

and translateTerm = function
    L.Var ln -> Id (translateLN ln)

  | L.EmptyTuple -> EmptyTuple

  | L.Tuple lst -> Tuple (List.map translateTerm lst)

  | L.Proj (k, t) -> Proj (k, translateTerm t)

  | L.App (u, v) -> App (translateTerm u, translateTerm v)

  | L.Lambda ((n, s), t) -> Lambda ((n, (translateSet s).ty), translateTerm t)

  | L.The ((n, s), phi) ->
      let {ty=t; tot=p1; per=p2} = translateSet s in
      let (v,q) = translateProp phi in
      let n' = refresh n in
      let z, z' = freshRz, freshRz in
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

  | L.Inj (lb, Some t) -> Inj (lb, Some (translateTerm t))

  | L.Case (t1, _, lst, _) ->
      Case (translateTerm t1, List.map
	       (function
		    (lb, Some (n, s), t) ->
		      (lb, Some (n, (translateSet s).ty), translateTerm t)
                  | (lb, None, t) ->
                      (lb, None, translateTerm t)
	       )
               lst
	    )
  | L.RzQuot t -> translateTerm t

  | L.RzChoose ((n, st1), t, u, st2) ->
      let {ty=ty1; per=p1} = translateSet st1 in
      let {per=p2} = translateSet st2 in
      let n' = refresh n in
      let v = translateTerm u in
      let v' = sbt n (id n') v in
	Let (n, translateTerm t,
	     Obligation ([],
			 Forall ((n', ty1),
				 Imply (pApp (pApp p1 (id n)) (id n'),
					pApp (pApp p2 v) v')),
			 v))

  | L.Quot (t, _) -> translateTerm t

  | L.Choose ((n, st1), r, t, u, st2) ->
      let {ty=ty1; per=p1} = translateSet st1 in
      let {per=p2} = translateSet st2 in
      let ty2, q = translateProp r in
      let n' = refresh n in
      let v = translateTerm u in
      let v' = sbt n (id n') v in
	Let (n, translateTerm t,
	     Obligation ([],
			 Forall ((n', ty1), Imply (
				   pApp (pMApp (pMApp q (id n)) (id n')) (dagger_of_ty ty2),
				   pApp (pApp p2 v) v')),
			 v))

  | L.Let ((n, s), u, v, _) ->
      Let (n, translateTerm u, translateTerm v)

  | L.Subin (t, (x, s), p) ->
      let (ty, p') = translateProp p in
      let t' = translateTerm t in
      let y = freshRz in
	Tuple[t'; Obligation ([(y, ty)], pApp (sbp x t' p') (id y), id y)]

  | L.Subout (t, _) -> Proj (0, translateTerm t)

  | L.Assure (None, p, t, _) ->
      let (ty, p') = translateProp p in
	Obligation ([], pApp p' (dagger_of_ty ty), translateTerm t)

  | L.Assure (Some (n, s), p, t, _) ->
      let {ty=ty2; tot=q} = translateSet s in
      let (ty1, p') = translateProp p in
	Obligation ([(n, ty2)],
		   And [pApp q (id n); pApp p' (dagger_of_ty ty1)],
		   translateTerm t)

			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * name * Outsyn.negative *)
and translateProp = function
    L.False -> makeProp (any(), TopTy) False

  | L.True -> makeProp (any(), TopTy) True

  | L.Atomic (ln, pt) ->
      let ty =
	(if L.is_stable pt
	  then TopTy
	  else NamedTy (translateSLN (L.sln_of_ln ln)))
      in
      let r = freshRz in
      let binds = bindings_of_proptype pt in
	(ty, nest_lambda binds
	  (PLambda ((r, ty), NamedProp (translateLN ln, id r, List.map (fun (y,_) -> id y) binds))))

  | L.And lst ->
      let lst' = List.map (translateProp) lst in
      let ty = TupleTy (List.map fst lst') in
      let t = fresh ty in
	makeProp (t, ty)
	  (And (let k = ref 0 in
		  List.map
		    (fun (_, p) -> let q = pApp p (Proj (!k, id t)) in incr k ; q)
		    lst'))

  | L.Imply (p, q) ->
      let (t, p') = translateProp p in
      let (u, q') = translateProp q in
      let ty = ArrowTy (t, u) in
      let x = fresh t in
      let f = fresh ty in
	makeProp (f, ty)
	  (Forall ((x, t),
		  Imply (pApp p' (id x), pApp q' (App (id f, id x)))))

  | L.Iff (p, q) -> 
      let (t, p') = translateProp p in
      let (u, q') = translateProp q in
      let x = fresh t in
      let y = fresh u in
      let f = fresh (ArrowTy (t,u)) in
	makeProp (f, TupleTy [ArrowTy (t, u); ArrowTy (u, t)])
	  (And [
	      Forall ((x, t), Imply (pApp p' (id x), pApp q' (App (Proj (0, id f), id x))));
	      Forall ((y, u), Imply (pApp q' (id y), pApp p' (App (Proj (1, id f), id y))))
	  ])
	  
  | L.Or lst ->
      let rec make_labels i j =
	if i >= j then [] else ("or" ^ (string_of_int i)) :: (make_labels (i+1) j)
      in
      let lst' = List.map translateProp lst in
      let lbs = make_labels 0 (List.length lst) in
      let ty = SumTy (List.map2 (fun lb (t,_) -> (lb, Some t)) lbs lst') in
      let u = fresh ty in
	makeProp (u, ty)
	 (Cor (
	   List.map2
		(fun lb (t,p) ->
		   let x = fresh t in
		     Cexists ((x,t), And [Equal(id u, Inj (lb, Some (id x))); pApp p (id x)]))
		lbs lst'
	 ))

  | L.Forall ((n, s), p) ->
      let {ty=t; tot=q} = translateSet s in
      let (u, p') = translateProp p in
      let ty = ArrowTy (t, u) in
      let f = fresh ty in
	makeProp (f, ty)
	  (Forall ((n, t), Imply (pApp q (id n), pApp p' (App (id f, id n)))))

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=q} = translateSet s in
      let (u, p') = translateProp p in
      let ty = TupleTy [t; u] in
      let w = fresh ty in
	makeProp (w, ty)
	 (And [pApp q (Proj (0, id w));
	       pApp (sbp n (Proj (0, id w)) p') (Proj (1, id w))])

  | L.Unique ((n, s), p) -> 
      let {ty=t; tot=q; per=pr} = translateSet s in
      let (u, p') = translateProp p in
      let ty = TupleTy [t; u] in
      let w, w' = fresh2 ty in
	makeProp (w, ty)
	 (And [
	     pApp q (Proj (0, id w));
	     pApp (sbp n (Proj (0, id w)) p') (Proj (1, id w));
	     Forall ((w', ty),
		    Imply (And [pApp q (Proj (0, id w'));
				pApp (sbp n (Proj (0, id w')) p') (Proj (1, id w;))],
			  pApp (pApp pr (Proj (0, id w))) (Proj (0, id w'))))
	 ])

  | L.Not p ->
      let (t, p') = translateProp p in
      let r = fresh t in
	makeProp (any(), TopTy) (Forall ((r, t), Not (pApp p' (id r))))

  | L.Equal (s, t, u) ->
      let {per=p} = translateSet s in
      let t' = translateTerm t in
      let u' = translateTerm u in
	makeProp (any(), TopTy) (pApp (pApp p t') u')

  | L.PLambda ((n, s), p) ->
      let (ty1, p') = translateProp p in
      let u = translateSet s in
	(ty1, PMLambda ((n, u), p'))

  | L.PApp (p, t) -> 
      let (ty, q) = translateProp p in
	(ty, pMApp q (translateTerm t))

  | L.IsEquiv (p, s) ->
      let (_, p') = translateProp p in
      let s' = translateSet s in
	makeProp (any(), TopTy) (isEquiv p' s')


  | L.PCase (t, _, lst) ->
      let tys, arms = List.fold_left
	(fun (tys, arms) -> function
	    (lb, Some (n, s), p) ->
	      let {ty=ty2; tot=q} = translateSet s in
	      let (ty1, p') = translateProp p in
	      let x = fresh ty1 in
		(lb, Some ty1)::tys, (lb, Some (x, ty1), Some (n, ty2),
				     And [pApp q (id n); pApp p' (id x)])::arms
          | (lb, None, p) ->
	      let (ty1, p') = translateProp p in
	      let x = fresh ty1 in
		(lb, Some ty1)::tys, (lb, Some (x, ty1), None, pApp p' (id x))::arms
	)
	([], [])
        lst
      in
      let r = fresh (SumTy tys) in
	makeProp (r, SumTy tys) (PCase (id r, translateTerm t, arms))

  | L.PAssure (None, p, q) ->
      let (ty1, p') = translateProp p in
      let (ty2, q') = translateProp q in
	ty2, PObligation ([], pApp p' (dagger_of_ty ty1), q')

  | L.PAssure (Some (n, s), p, q) ->
      let {ty=ty2; tot=r} = translateSet s in
      let (ty1, p') = translateProp p in
      let (ty3, q') = translateProp q in
	ty3, PObligation ([(n, ty2)], And [pApp r (id n); pApp p' (dagger_of_ty ty1)], q')

  | L.PLet ((n,s), t, p) ->
      let ty, q = translateProp p in
	ty, PLet (n, translateTerm t, q)
      

and bindings_of_proptype = function
    L.Prop | L.StableProp -> []
  | L.EquivProp s ->
      let ms = translateSet s in
      let x, y = fresh2 ms.ty in
	[(x, ms); (y, ms)]
  | L.PropArrow (m, s, pt) ->
      let s' = translateSet s in
      let m' = (if isWild m then fresh s'.ty else refresh m) in
	(m', s') :: (bindings_of_proptype pt)

and equiv_bindings_of_proptype = function
    L.Prop | L.StableProp -> failwith "Translate.equiv_bindings_of_proptype: not an equivalence"
  | L.EquivProp s -> [], [], translateSet s
  | L.PropArrow (m, s, pt) ->
      let s' = translateSet s in
      let m' = (if isWild m then fresh s'.ty else refresh m) in
      let bnd1, bnd2, t = equiv_bindings_of_proptype pt in
	(m', s') :: bnd1, (m',s) :: bnd2, t

and bindings_of_setkind = function
    L.KindSet -> []
  | L.KindArrow (m, s, knd) ->
      let s' = translateSet s in
      let m' = (if isWild m then fresh s'.ty else refresh m) in
	(m', s') :: (bindings_of_setkind knd)

and translateTheoryElement = function
  | L.Declaration(n, L.DeclSet (None, knd)) -> 
      [Spec (n,
	   TySpec None,
	   [("per_" ^ string_of_name n,
	    (let binds = bindings_of_setkind knd in
	       nest_forall binds
		 (IsPer (n, (List.map (fun (y,_) -> id y) binds)))
	    ))])]

  | L.Declaration(n, L.DeclSet(Some s, knd)) ->
      let {ty=t; tot=p; per=q} = translateSet s in
      let binds = bindings_of_setkind knd in
      let ys = List.map fst binds in
      let idys = List.map id ys in
      let x = fresh t in
      let y, y' = fresh2 t in
	[Spec (n, TySpec (Some t),
             [(string_of_name n ^ "_def_total",
	      nest_forall binds
		(Forall((x,t),
		       Iff (PApp (NamedTotal (ln_of_name n, idys), id x),
			   pApp (List.fold_left (pMApp) p idys) (id x)))));
	      (string_of_name n ^ "_def_per",
	      nest_forall binds
		(Forall ((y,t),
			Forall ((y',t),
			       Iff (PApp (PApp (NamedPer (ln_of_name n, idys), id y), id y'),
				   pApp (pApp (List.fold_left (pMApp) q idys) (id y)) (id y'))))))]
	)]

  | L.Declaration(n, L.DeclProp(None, pt)) ->
      let binds = bindings_of_proptype pt in
      let spec =
	isPredicate
	  (ln_of_name n)
	  (if L.is_stable pt then TopTy else NamedTy (ln_of_name (L.typename_of_name n)))
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
			    let bnds1, bnds2, s' = equiv_bindings_of_proptype pt in
			    let xs = List.map fst bnds1 in
			    let x, y = fresh2 s'.ty in
			    let p =
			      PMLambda ((x,s'),
                              PMLambda ((y,s'),
       			      PLambda ((any(), TopTy), 
                                NamedProp (ln_of_name n, Dagger, (List.map id xs) @ [id x; id y]))))
			    in
			      nest_forall bnds1 (isEquiv p s')
	    )]
	  else []
	)

  | L.Declaration(n, L.DeclProp(Some p, pt)) ->
      let (ty, p') = translateProp p in
      let binds = bindings_of_proptype pt in
      let ys = List.map fst binds in
      let idys = List.map id ys in
      let r = freshRz in
	[Spec (
	    L.typename_of_name n,
	    TySpec (Some ty),
            [((string_of_name n) ^ "_def",
	     nest_forall binds
	       (Forall ((r, ty),
		       Iff (
			   NamedProp (ln_of_name n, id r, idys),
			   pApp (List.fold_left pMApp p' idys) (id r)
		       )))
	    )])]

  | L.Declaration(n, L.DeclTerm(Some t, s)) ->
      let {ty=u; per=q} = translateSet s in
      let t' = translateTerm t in
	[ Spec(n, ValSpec ([],u), [((string_of_name n) ^ "_def", pApp (pApp q (id n)) t')]) ]

  | L.Declaration(n, L.DeclTerm(None, s)) ->
      let {ty=t; tot=p} = translateSet s in
	[ Spec (n, ValSpec ([],t), [((string_of_name n) ^ "_total", pApp p (id n))]) ]

  | L.Comment cmmnt ->
	[ Comment cmmnt ]

  | L.Declaration(nm, L.DeclSentence (mdlbind, prp)) ->
      [
	let strctbind = translateModelBinding mdlbind in
	let (typ, prp') = translateProp prp in
	let elem =
	  Spec (nm, ValSpec ([],typ), [(string_of_name nm, pApp prp' (id nm))])
	in
	  if mdlbind = [] then
	    elem
	  else
	    let fnctr =
	      List.fold_right (fun bnd sgnt -> SignatFunctor (bnd,sgnt)) strctbind (Signat [elem])
	    in
	      Spec(capitalize_name nm, ModulSpec fnctr, [])
      ]


  | L.Declaration(mdlnm, L.DeclModel (thr)) ->
      [ Spec (mdlnm, ModulSpec (translateTheory thr), []) ]

  | L.Declaration(n, L.DeclTheory (thr,_)) ->
      [ Spec(n, SignatSpec (translateTheory thr), []) ]

and translateSLN = function
    L.SLN (None, nm) -> LN (None, L.typename_of_name nm)
  | L.SLN (Some mdl, nm) -> LN (Some (translateModel mdl), L.typename_of_name nm)

and translateTheoryElements thy =
  List.fold_right (fun e elts -> translateTheoryElement e @ elts) thy []

and translateModelBinding bnd =
  List.map (fun (m, thry) -> (m, translateTheory thry)) bnd

and translateTheory = function
    L.Theory body -> Signat (translateTheoryElements body)
  | L.TheoryName id -> SignatName id
  | L.TheoryLambda ((nm, thr1), thr2)
  | L.TheoryArrow ((nm,thr1),thr2) ->
      SignatFunctor ((nm, translateTheory thr1), translateTheory thr2)
  | L.TheoryApp (thr, mdl) -> SignatApp (translateTheory thr, translateModel mdl)
  | L.TheoryProj(mdl, nm) -> SignatProj(translateModel mdl, nm)
		 
let translateToplevel = translateTheoryElements
