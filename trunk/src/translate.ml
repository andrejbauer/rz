module L = Logic
module S = Syntax
open Outsyn 

exception Unimplemented

(** contexts (environments)
    We're anticipating dependent contexts here so we have a single
    context with everything stuffed in it.

    A context entry is one of:
    - name bound to a type (can be bound to a kind SET or PROP)
    - definition of a term (name = term)
    - definition of a set (name = set definition)
    - definition of a proposition
*)

type ctxElement =
    CtxBind of L.name * L.set
  | CtxSet of L.set_name * L.set
  | CtxProp of L.name * S.propKind
  | CtxModel of L.model_name * theorySummary
  | CtxTheory of L.theory_name * theorySummary

and theorySummary = 
    Ctx of ctxElement list
  | CtxParam of L.model_name * signat * theorySummary

let emptyCtx = []

let occursCtx ctx str =
  List.exists
    (function
	 CtxBind (Syntax.N(nm,_), _) -> nm = str
       | CtxSet (nm, _) -> nm = str
       | CtxProp (Syntax.N(nm,_), _) -> nm = str
       | CtxModel (nm, _) -> nm = str
       | CtxTheory (nm, _) -> nm = str
    ) ctx

let addBind  n s ctx = CtxBind(n,s) :: ctx
let addSet   n s ctx = CtxSet(n,s) :: ctx
let addProp  n stb ctx = CtxProp(n,stb) :: ctx
let addModel n thr ctx = CtxModel(n,thr) :: ctx
let addTheory n thr ctx = CtxTheory(n,thr) :: ctx

let addBinding bind ctx =
  List.fold_left (fun ctx (n,s) -> addBind n s ctx) ctx bind

let getBind n ctx =
  let rec find = function
      [] -> raise Not_found
    | CtxBind (m,s) :: ctx' -> if n = m then s else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx
    
let getSet n ctx =
  let rec find = function
      [] -> raise Not_found
    | CtxSet(m,s) :: ctx' -> if n = m then s else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx
    
let getProp n ctx =
  let rec find = function
      [] -> failwith ("No such proposition " ^ (L.string_of_name n))
    | CtxProp (m,stb) :: ctx' -> if n = m then stb else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx

let getTheory n ctx =
  let rec find = function
      [] -> (failwith ("No such theory " ^ n))
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
  | CtxBind (nm,st) :: lst -> CtxBind (nm, L.substMSet m mdl st) :: (substMCtx m mdl lst)
  | CtxSet (stnm,st) :: lst -> CtxSet (stnm, L.substMSet m mdl st) :: (substMCtx m mdl lst)
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

let any = mk_word "_"

(** translation functions *)

let fresh good bad ctx = freshName good bad ~occ:(occursCtx ctx) emptysubst

let sbp ctx ?(bad=[]) lst =
  substProp ~occ:(fun str -> List.exists (fun (Syntax.N(nm,_)) -> nm = str) bad ||
		    occursCtx ctx str) (termsSubst lst)

let sbt ctx lst = substTerm ~occ:(occursCtx ctx) (termsSubst lst)

let rec translateSet (ctx : ctxElement list) = function
    L.Empty -> 
      { ty = VoidTy;
	tot = (any, False);
	per = (any, any, False)
      }
  | L.Unit ->
      let x = fresh [mk_word "x"] [] ctx in
      { ty = UnitTy;
	tot = (x, Equal (id x, Star));
	per = (any, any, True)
      }
  | L.Bool ->
      let x = fresh [mk_word "x"; mk_word "u"] [] ctx in
      let y = fresh [mk_word "y"; mk_word "v"] [x] ctx in
	{ ty = NamedTy (tln_of_tyname "bool");
	  tot = (x, (Cor [Equal (id x, mk_id "true");
                          Equal (id x, mk_id "false")]));
	  per = (x, y, Equal (id x, id y))
      }
  | L.Basic sln ->
      let s' = translateSLN sln in
      let x = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "a"] [] ctx in
      let y = fresh [mk_word "y"; mk_word "v"; mk_word "b"] [x] ctx in
	{ ty = NamedTy s';
	  tot = (x, NamedTotal (s', id x));
	  per = (x, y, NamedPer (s', id x, id y))
	}
  | L.Product lst ->
      let us = List.map (translateSet ctx) lst in
	{
	  ty = TupleTy (List.map (fun u -> u.ty) us);
	  tot = (
	    let t = fresh [mk_word "t"; mk_word "u"; mk_word "v"] [] ctx in
	      (t, And (
		 let k = ref 0 in
		   List.map (fun {tot=(x,p)} ->
			       let q = sbp ctx ~bad:[t] [x, (Proj (!k, id t))] p in
				 incr k ; q) us
	       )
	      )
	  );
	  per = (
	    let t = fresh [mk_word "t"; mk_word "u"; mk_word "v"] [] ctx in
	    let u = fresh [mk_word "u"; mk_word "v"; mk_word "w"] [t] ctx in
	      (t, u, And (
		 let k = ref 0 in
		   List.map (fun {per=(x,y,p)} ->
			       let q = sbp ctx ~bad:[t;u]
					 [(x, Proj (!k, id t)); (y, Proj (!k, id u))] p in
				 incr k; q
			    ) us
	       )
	      )
	  )
	}
  | L.Exp (s, t) ->
      let {ty=u; per=(x,x',p)} = translateSet ctx s in
      let {ty=v; per=(y,y',q)} = translateSet ctx t in
      let z = fresh [x] [] ctx in
      let z' = fresh [x'] [z] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"] [z;z'] ctx in
      let g = fresh [mk_word "g"; mk_word "h"; mk_word "k"] [f;z;z'] ctx in
	{ ty = ArrowTy (u, v);
	  tot = (
	      (f,
	       Forall ((z, u),
	       Forall ((z', u),
	         Imply (sbp ctx ~bad:[z;z';f] [(x, id z); (x', id z')] p,
			sbp ctx ~bad:[z;z';f] [(y, App (id f, id z)); (y', App (id f, id z'))] q)
		      ))
	      )
	  );
	  per = (
	      (f, g,
	       Forall ((z,u),
               Forall ((z',u),
                 Imply (sbp ctx ~bad:[z;z';f;g] [(x, id z); (x', id z')] p,
			sbp ctx ~bad:[z;z';f;g] [(y, App (id f, id x)); (y', App (id g, id x'))] q)
		      ))
	      )
	  )
	}

  | L.Subset ((n, s), phi) ->
      let {ty=u; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
      let (v,z,r) = translateProp (addBind n s ctx) phi in
	{
	  ty = TupleTy [u; v];
	  tot = (
	    let k = fresh [mk_word "k"; mk_word "j"; mk_word "x"] [] ctx in
	      (k,
	       And [sbp ctx ~bad:[k] [(x, Proj (0, id k))] p;
		    sbp ctx ~bad:[k] [(n, Proj (0, id k)); (z, Proj (1, id k))] r]
	      )
	  );
	  per = (
	    let w  = fresh [y; mk_word "w"] [] ctx in
	    let w' = fresh [y'; mk_word "w'"] [w] ctx in
	      (w, w', sbp ctx ~bad:[w;w'] [(y, Proj (0, id w)); (y', Proj (0, id w'))] q)
	  )
	}
  | L.Quotient (s, r) ->
      let {ty=u; tot=(w,p); per=(z,z',q)} = translateSet ctx s in
	{ ty = u;
	  tot = (w, p);
	  per = (
	    let u = fresh [z] [] ctx in
	    let u' = fresh [z'] [u] ctx in
	      u, u', NamedProp (translateLN r, Dagger, [Tuple [id u; id u']])
	  )
	}

  | L.Sum lst -> 
      let lst' = List.map (function
			       (lb, None) -> (lb, None)
			     | (lb, Some s) -> (lb, Some (translateSet ctx s)))
		   lst
      in
      let x = fresh [mk_word "w"; mk_word "t"; mk_word "u"; mk_word "p"] [] ctx in
      let y = fresh [mk_word "v"; mk_word "u"; mk_word "s"; mk_word "p"] [] ctx in
      let y' = fresh [mk_word "w"; mk_word "t"; mk_word "r"; mk_word "q"] [y] ctx in
	{
	  ty = SumTy (List.map (function
				    (lb, None) -> (lb, None)
				  | (lb, Some {ty=u}) -> (lb, Some u)
			       ) lst');
	  tot = (
	    x,
	    Cor (List.map (
		   function
		       (lb, None) -> Equal (id x, Inj (lb, None))
		     | (lb, Some {ty=u; tot=(x',p)}) ->
			 let x'' = fresh [x'] [x] ctx in
			   Cexists ((x'', u),
				   And [Equal (id x, Inj (lb, Some (id x'')));
					sbp ctx ~bad:[x;x''] [(x', id x'')] p]))
		   lst')
	  );
	  per = (
	    y, y',
	    Cor (List.map (
		   function
		       (lb, None) -> And [Equal (id y,  Inj (lb, None));
					  Equal (id y', Inj (lb, None))]
		     | (lb, Some {ty=u; per=(z,z',q)}) ->
			 let w =  fresh [z] [y;y'] ctx in
			 let w' = fresh [z'] [w;y;y'] ctx in
			   Cexists ((w,u),
		           Cexists ((w',u),
				    And [Equal (id y, Inj (lb, Some (id w)));
					 Equal (id y', Inj (lb, Some (id w')));
					 sbp ctx ~bad:[y;y';w;w'] [(z, id w); (z', id w')] q])))
		   lst')
	  )
	}

  | L.Rz s ->
      let {ty=t; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
	{
	  ty = t;
	  tot = (x, p);
	  per = (y, y', Equal (id y, id y'));
	}

  | L.PROP | L.STABLE | L.EQUIV -> failwith "Cannot translate higher-order logic"

and translateTerm ctx = function
    L.Var ln -> Id (translateLN ln)

  | L.Star -> Star

  | L.Tuple lst -> Tuple (List.map (translateTerm ctx) lst)

  | L.Proj (k, t) -> Proj (k, translateTerm ctx t)

  | L.App (u, v) -> App (translateTerm ctx u, translateTerm ctx v)

  | L.Lambda ((n, s), t) -> Lambda ((n, (translateSet ctx s).ty), translateTerm ctx t)

  | L.The ((n, s), phi) ->
      let {per=(x,y,p); ty=t} = translateSet ctx s in
      let (v,z,q) = translateProp ctx phi in
      let n' = fresh [n] [n] ctx in
      let z' = fresh [z] [n;n'] ctx in
	Obligation ((n, t), True,
		    Obligation ((z',v),
				And [sbp ctx ~bad:[z'] [(z, id z')] q;
				     Forall ((n',t),
					     Imply (sbp ctx ~bad:[z';n'] [(n, id n'); (z, id z')] q,
						    sbp ctx ~bad:[z';n'] [(x, id n); (y, id n')] p))], id n)
		   )

  | L.Inj (lb, None) -> Inj (lb, None)

  | L.Inj (lb, Some t) -> Inj (lb, Some (translateTerm ctx t))

  | L.Case (t1, lst) ->
      Case (translateTerm ctx t1, List.map
	       (function
		    (lb, Some (n, s), t) ->
		      let ctx' = addBind n s ctx in
			(lb, Some (n, (translateSet ctx' s).ty), translateTerm ctx' t)
                  | (lb, None, t) ->
                      (lb, None, translateTerm (addBind any L.Unit ctx) t)
	       )
               lst
	    )
  | L.RzQuot t -> translateTerm ctx t

  | L.RzChoose ((n, st1), t, u, st2) ->
      let {ty=ty1; per=(x1,y1,p1)} = translateSet ctx st1 in
      let {per=(x2,y2,p2)} = translateSet ctx st2 in
      let n' = fresh [n] [n] ctx in
      let v = translateTerm (addBind n st1 ctx) u in
      let v' = sbt ctx [(n, id n')] v in
	Let (n, translateTerm ctx t,
	     Obligation ((any, TopTy),
			 Forall ((n', ty1), Imply (
				   sbp ctx ~bad:[n'] [(x1, id n); (y1, id n')] p1, 
				   sbp ctx ~bad:[n'] [(x2, v); (y2, v')] p2)),
			 v))

  | L.Quot (t, _) -> translateTerm ctx t

  | L.Choose ((n, st1), r, t, u, st2) ->
      let {ty=ty1; per=(x1,y1,p1)} = translateSet ctx st1 in
      let {per=(x2,y2,p2)} = translateSet ctx st2 in
      let n' = fresh [n] [n] ctx in
      let v = translateTerm (addBind n st1 ctx) u in
      let v' = sbt ctx [(n, id n')] v in
	Let (n, translateTerm ctx t,
	     Obligation ((any, TopTy),
			 Forall ((n', ty1), Imply (
				   NamedProp(translateLN r, Dagger, [Tuple [id n; id n']]),
				   sbp ctx ~bad:[n'] [(x2, v); (y2, v')] p2)),
			 v))

  | L.Let ((n, s), u, v, _) ->
      Let (n, translateTerm ctx u, translateTerm (addBind n s ctx) v)

  | L.Subin (t, sb) ->
      let ((x, s), p) = toSubset ctx sb in
      let (ty, y, p') = translateProp (addBind x s ctx) p in
      let t' = translateTerm ctx t in
      let y' = fresh [y; mk_word "v"; mk_word "u"; mk_word "t"] [] ctx in
	Obligation ((y', ty), sbp ctx ~bad:[y'] [(y, id y'); (x,t')] p', Tuple [t'; id y'])
  | L.Subout (t, _) -> Proj (0, translateTerm ctx t)

			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
and translateProp ctx = function
    L.False -> (TopTy, any, False)

  | L.True -> (TopTy, any, True)

  | L.Atomic (ln, trms) ->
      let r = fresh [mk_word "r"; mk_word "q"; mk_word "s"] [] ctx in
      let ty = (match getLong getProp ctx ln with
		    S.Unstable -> NamedTy (translateSLN (L.sln_of_ln ln))
		  | S.Stable | S.Equivalence -> TopTy)
      in
	(ty, r, NamedProp (translateLN ln, id r, List.map (translateTerm ctx) trms))

  | L.And lst ->
      let lst' = List.map (translateProp ctx) lst in
      let t =
	fresh [mk_word "t"; mk_word "p"; mk_word "u"; mk_word "q"; mk_word "r"] [] ctx in
	(TupleTy (List.map (fun (s,_,_) -> s) lst'), t,
	 And (let k = ref 0 in
		List.map (fun (_, x, p) ->
			    let q = sbp ctx ~bad:[t] [(x, Proj (!k, id t))] p in incr k ; q)
		  lst')
	)

  | L.Imply (p, q) ->
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; mk_word "x"; mk_word "y"; mk_word "z"] [] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x'] ctx in
	(ArrowTy (t, u),
	 f,
	 Forall ((x', t), Imply (sbp ctx ~bad:[x';f] [(x, id x')] p',
				 sbp ctx ~bad:[x';f] [(y, App (id f, id x'))] q')))

  | L.Iff (p, q) -> 
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; mk_word "x"; mk_word "y"; mk_word "z"] [] ctx in
      let y' = fresh [y; mk_word "y"; mk_word "z"; mk_word "x"] [x'] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x';y'] ctx in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f,
	 And [
	   Forall ((x', t), Imply (sbp ctx ~bad:[x';f] [(x, id x')] p',
				   sbp ctx ~bad:[x';f] [(y, App (Proj (0, id f), id x))] q'));
	   Forall ((y', u), Imply (sbp ctx ~bad:[y';f] [(y, id y')] q',
				   sbp ctx ~bad:[y';f] [(x, App (Proj (1, id f), id y))] p'))
	 ]
	)

  | L.Or lst ->
      let rec make_labels i j =
	if i >= j then [] else ("or" ^ (string_of_int i)) :: (make_labels (i+1) j)
      in
      let lst' = List.map (translateProp ctx) lst in
      let lbs = make_labels 0 (List.length lst) in
      let u = fresh [mk_word "u"; mk_word "v"; mk_word "w"; mk_word "r"] [] ctx
      in
	(SumTy (List.map2 (fun lb (t,_,_) -> (lb, Some t)) lbs lst'),
	 u,
	 Cor (
	   List.map2
		(fun lb (t,x,p) ->
		   let x' = fresh [x] [u] ctx in
		     Cexists ((x',t), And [Equal(id u, Inj (lb, Some (id x')));
					   sbp ctx ~bad:[x';u] [(x, id x')] p]))
		lbs lst'
	 ))

  | L.Forall ((n, s), p) ->
      let {ty=t; tot=(x,q)} = translateSet ctx s in
      let (u, y, p') = translateProp (addBind n s ctx) p in
      let x' = fresh [n] [] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "l"] [x'] ctx
      in
	(ArrowTy (t, u),
	 f,
	 Forall ((x',t), Imply (sbp ctx ~bad:[x';f] [(x, id x')] q,
				sbp ctx ~bad:[x';f] [(n, id x'); (y, App (id f, id x'))] p'))
	)

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=(x,q)} = translateSet ctx s in
      let (u, y, p') = translateProp (addBind n s ctx) p in
      let w = fresh [mk_word "w"; mk_word "u"; mk_word "p"; mk_word "t"] [] ctx
      in
	(TupleTy [t; u], w,
	 And [
	   sbp ctx ~bad:[w] [(x, Proj (0, id w))] q;
	   sbp ctx ~bad:[w] [(n, Proj (0, id w)); (y, Proj (1, id w))] p'
	 ])

  | L.Unique ((n, s), p) -> 
      let {ty=t; tot=(x,q); per=(z,z',pr)} = translateSet ctx s in
      let (u, y, p') = translateProp (addBind n s ctx) p in
      let w = fresh [mk_word "w"; mk_word "u"; mk_word "p"; mk_word "t"] [] ctx in
      let w' = fresh [mk_word "u"; mk_word "p"; mk_word "t"] [w] ctx in
	(TupleTy [t; u], w,
	 And [
	   sbp ctx ~bad:[w] [(x, Proj (0, id w))] q;
	   sbp ctx ~bad:[w] [(n, Proj (0, id w)); (y, Proj (1, id w))] p';
	   Forall ((w', TupleTy [t; u]),
		   Imply (
		     sbp ctx ~bad:[w;w'] [(x, Proj (0, id w'))] q,
		     Imply (
		       sbp ctx ~bad:[w;w'] [(n, Proj (0, id w')); (y, Proj (1, id w'))] p',
		       sbp ctx ~bad:[w;w'] [(z,Proj(0, id w)); (z',Proj(0,id w'))] pr
		     )
		   )
		  )
	 ])

  | L.Not p ->
      let (t, n, p') = translateProp ctx p in
	(TopTy, any, Forall ((n, t), Not p'))

  | L.Equal (s, t, u) ->
      let {per=(x,y,p)} = translateSet ctx s in
      let t' = translateTerm ctx t in
      let u' = translateTerm ctx u in
	(TopTy, any, sbp ctx [(x,t'); (y,u')] p)

and translateBinding ctx bind =
  List.map (fun (n, s) -> n, (translateSet ctx s).ty) bind

and translateTheoryElements ctx = function
    [] -> [], emptyCtx
  | L.Set n :: rest -> 
      let sgnt, smmry = translateTheoryElements (addSet n L.SET ctx) rest in
	(TySpec (n, None, [("per_" ^ n, [], IsPer n)])) :: sgnt,
	(addSet n L.SET smmry)

  | L.Let_set (n, s) :: rest ->
      let sgnt, smmry = translateTheoryElements (addSet n s ctx) rest in	
	(let {ty=t; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
	   TySpec (n, Some t,
		    [(n ^ "_def_total", [(x,t)], Iff (NamedTotal (tln_of_tyname n, id x), p));
		     (n ^ "_def_per", [(y,t); (y',t)],
		      Iff (NamedPer (tln_of_tyname n, id y, id y'), q))])
	) :: sgnt,
	addSet n s smmry

  | L.Predicate (n, stab, s) :: rest -> begin
      let sgnt, smmry = translateTheoryElements (addProp n stab ctx) rest in
	(match stab with
	     S.Unstable ->
	       TySpec (L.typename_of_name n,
		       None,
		       [("predicate_" ^ (S.string_of_name n), [], IsPredicate n)]
		      )
	   | S.Stable | S.Equivalence ->
	     AssertionSpec ("predicate_" ^ (S.string_of_name n), [], IsPredicate n)
	) :: sgnt,
	addProp n stab smmry
    end

  | L.Let_predicate (n, stab, bind, p) :: rest ->
      let sgnt, smmry = translateTheoryElements (addProp n stab ctx) rest in
	(let bind' = translateBinding ctx bind in
	 let ctx' = addBinding bind ctx in
	 let (ty, r, p') = translateProp ctx' p in
	 let r' = fresh [r] (List.map fst bind) ctx in
	   TySpec (L.typename_of_name n, Some ty,
		   [((S.string_of_name n) ^ "_def",
		     (r',ty) :: bind',
		     Iff (NamedProp (ln_of_name n, id r', List.map (fun (y,_) -> id y) bind),
			  sbp ctx ~bad:[r'] ([(r, id r')]) p'))])
	) :: sgnt,
	addProp n stab smmry

  | L.Let_term (n, s, None, t) :: rest ->
      let sgnt, smmry = translateTheoryElements (addBind n s ctx) rest in
	(let {ty=u; per=(y,y',q)} = translateSet ctx s in
	 let t' = translateTerm ctx t in
	   ValSpec (n, u, [((S.string_of_name n) ^ "_def", [],
			sbp ctx [(y, id n); (y', t')] q)])
	) :: sgnt,
	addBind n s smmry

  | L.Let_term (n, s, Some args, t) :: rest ->
      let sgnt, smmry = translateTheoryElements (addBind n s ctx) rest in
	(let {ty=u; per=(y,y',q)} = translateSet ctx s in
	 let t' = translateTerm (addBinding args ctx) t in
	   ValSpec (n, u, [((S.string_of_name n) ^ "_def", [], 
			    sbp ctx [(y, (id n));
				     (y', nested_lambda (translateBinding ctx args) t')] q)])
	) :: sgnt,
	addBind n s smmry

  | L.Value (n, s) :: rest ->
      let sgnt, smmry = translateTheoryElements (addBind n s ctx) rest in
       (let {ty=t; tot=(x,p)} = translateSet ctx s in
	  ValSpec (n, t, [((S.string_of_name n) ^ "_total", [],
		      sbp ctx [(x, id n)] p)])
       ) :: sgnt,
       addBind n s smmry

  | L.Comment cmmnt :: rest ->
      let sgnt, smmry = translateTheoryElements ctx rest in
	(Comment cmmnt) :: sgnt, smmry

  | L.Sentence (_, nm, mdlbind, valbnd, prp) :: rest ->
      let sgnt, smmry = translateTheoryElements ctx rest in
	begin
	  let strctbind, ctx' = translateModelBinding ctx mdlbind in
	  let ctx'' = addBinding valbnd ctx' in
	  let bnd = translateBinding ctx' valbnd in
	  let (typ, x, prp') = translateProp ctx'' prp in
	  let typ' = List.fold_right (fun (_,t) a -> ArrowTy (t, a)) bnd typ in
	  let app = List.fold_left (fun a (n,_) -> App (a, id n)) (id nm) bnd in
	  let elem =
	    ValSpec (nm, typ', [(string_of_name nm, bnd, sbp ctx'' [(x, app)] prp')])
	  in
	    if mdlbind = [] then
	      elem
	    else
	      let fnctr =
		List.fold_right (fun bnd sgnt -> SignatFunctor (bnd,sgnt)) strctbind (Signat [elem])
	      in
		ModulSpec (String.capitalize (string_of_name nm), fnctr)
	end :: sgnt,
	smmry

  | L.Model (mdlnm, thr) :: rest ->
      let sgnt, smmry = translateTheory ctx thr in
      let sgnt', smmry' = translateTheoryElements (addModel mdlnm smmry ctx) rest in
	ModulSpec (mdlnm, sgnt) :: sgnt',
	(addModel mdlnm smmry smmry')


and translateSLN = function
    L.SLN (None, nm) -> TLN (None, nm)
  | L.SLN (Some mdl, nm) -> TLN (Some (translateModel mdl), nm)

and translateModelBinding ctx = function
    [] -> [], ctx
  | (m, th) :: rest ->
      let signat, smmry = translateTheory ctx th in
      let signats, ctx' = translateModelBinding (addModel m smmry ctx) rest in
	(m, signat) :: signats, ctx'

and translateTheory ctx = function
    L.Theory body ->
      let sgnt, smmry = translateTheoryElements ctx body in
	Signat sgnt, Ctx smmry
  | L.TheoryName id -> SignatName id, getTheory id ctx
  | L.TheoryFunctor ((nm,thr1),thr2) ->
      let sgnt1, smmry1 = translateTheory ctx thr1 in
      let sgnt2, smmry2 = translateTheory (addModel nm smmry1 ctx) thr2 in
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
	attachSignat (TopModul (mdlnm, sgnt)) (translateToplevel (addModel mdlnm smmry ctx) rest)
