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
    CtxBind of L.set
  | CtxTerm of L.term
  | CtxSet of L.set
  | CtxProp of Syntax.propKind * (L.binding list * L.proposition) option
  | CtxModel of context
  | CtxTheory of L.model_binding list * L.theory

and context = (L.name * ctxElement) list

let emptyCtx : context = []

let addBind  (n : L.name) s ctx = (n, CtxBind s) :: ctx
let addTerm  (n : L.name) t ctx = (n, CtxTerm t) :: ctx
let addSet   (n : L.name) s ctx = (n,  CtxSet s) :: ctx
let addProp  (n : L.name) (stb,x) ctx = (n, CtxProp (stb,x)) :: ctx
let addModel n thry ctx = (Syntax.N(n,Syntax.Word), CtxModel thry) :: ctx
let addTheory n args th ctx =
  (Syntax.N(n,Syntax.Word), CtxTheory (args, th)) :: ctx

let addBinding bind ctx =
  List.fold_left (fun ctx (n,s) -> addBind n s ctx) ctx bind

let getBind n ctx =
  let rec find = function
      [] -> raise Not_found
    | (m, CtxBind s) :: ctx' -> if n = m then s else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx
    
let getTerm n ctx =
  let rec find = function
      [] -> raise Not_found
    | (m, CtxTerm t) :: ctx' -> if n = m then t else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx
    
let getSet n ctx =
  let rec find = function
      [] -> raise Not_found
    | (m, CtxSet s) :: ctx' -> if n = m then s else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx
    
let getProp n ctx =
  let rec find = function
      [] -> raise Not_found
    | (m, CtxProp (stb, x)) :: ctx' -> if n = m then (stb,x) else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx

let getModel n ctx =
  let rec find = function
      [] -> raise Not_found
    | (Syntax.N(m,_), CtxModel thr) :: ctx' -> if n = m then thr else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx

let getTheory n ctx =
  let rec find = function
      [] -> (failwith ("No such theory " ^ n))
    | (Syntax.N(m,_), CtxTheory (args, th)) :: ctx' ->
	if n = m then (args, th) else find ctx'
    | (Syntax.N(m,_), _) :: ctx' ->
	find ctx'
  in
    find ctx

let rec getLong getter ctx = function
    (L.LN(str, [], namesort) as lname) -> getter (Syntax.N(str,namesort)) ctx
  | (L.LN(str, lab::labs, namesort) as lname) ->
      let ctx' = getModel str ctx
      in getLong getter ctx' (L.LN(lab, labs, namesort))


(** *** *)

let rec toSubset ctx = function
    L.Subset ((x,s), p) -> ((x, s), p)
  | L.Basic b -> toSubset ctx (getLong getSet ctx b)
  | _ -> failwith "not a subset"

let any = mk_word "_"

(*
let make_type_name _ = function
    (n, Syntax.Word) -> n
  | ("<", _) -> "lt"
  | (">", _) -> "gt"
  | ("<=", _) -> "leq"
  | (">=", _) -> "geq"
  | ("=", _) -> "eq"
  | ("<>", _) -> "neq"
  | (s, _) -> s
*)

(** translation functions *)

let toLN = Logic.ln_of_name
let toId nm = Id (toLN nm)
let ln_of_string = Logic.ln_of_string

let rec translateSet (ctx : context) = function
    L.Empty -> 
      { ty = VoidTy;
	tot = (any, False);
	per = (any, any, False)
      }
  | L.Unit ->
      let x = fresh [mk_word "x"] [] ctx in
      { ty = UnitTy;
	tot = (x, Equal (toId x, Star));
	per = (any, any, True)
      }
  | L.Bool ->
      let x = fresh [mk_word "x"; mk_word "u"] [] ctx in
      let y = fresh [mk_word "y"; mk_word "v"] [x] ctx in
	{ ty = NamedTy (mk_longword "bool");
	  tot = (x, (Cor [Equal (toId x, mk_id "true");
                          Equal (toId x, mk_id "false")]));
	  per = (x, y, Equal (toId x, toId y))
      }
  | L.Basic s ->
      let x = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "a"] [] ctx in
      let y = fresh [mk_word "y"; mk_word "v"; mk_word "b"] [x] ctx in
	{ ty = NamedTy s;
	  tot = (x, NamedTotal (s, toId x));
	  per = (x, y, NamedPer (s, toId x, toId y))
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
			       let q = substProp ctx [(x, Proj (!k, toId t))] p in
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
			       let q = substProp ctx [(x, Proj (!k, toId t)); (y, Proj (!k, toId u))] p in
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
	         Imply (substProp ctx [(x, toId z); (x', toId z')] p,
			substProp ctx [(y, App (toId f, toId x)); (y', App (toId f, toId x'))] q)
		      ))
	      )
	  );
	  per = (
	      (f, g,
	       Forall ((z,u),
               Forall ((z',u),
                 Imply (substProp ctx [(x, toId z); (x', toId z')] p,
			substProp ctx [(y, App (toId f, toId x)); (y', App (toId g, toId x'))] q)
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
	       And [substProp ctx [(x, Proj (0, toId k))] p;
		    substProp ctx [(n, Proj (0, toId k)); (z, Proj (1, toId k))] r]
	      )
	  );
	  per = (
	    let w  = fresh [y; mk_word "w"] [] ctx in
	    let w' = fresh [y'; mk_word "w'"] [w] ctx in
	      (w, w', substProp ctx [(y, Proj (0, toId w)); (y', Proj (0, toId w'))] q)
	  )
	}
  | L.Quotient (s, r) ->
      let {ty=u; tot=(w,p); per=(z,z',q)} = translateSet ctx s in
	{ ty = u;
	  tot = (w, p);
	  per = (
	    let u = fresh [z] [] ctx in
	    let u' = fresh [z'] [u] ctx in
	      u, u', NamedProp (r, Dagger, [Tuple [toId u; toId u']])
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
		       (lb, None) -> Equal (toId x, Inj (lb, None))
		     | (lb, Some {ty=u; tot=(x',p)}) ->
			 let x'' = fresh [x'] [x] ctx in
			   Cexists ((x'', u),
				   And [Equal (toId x, Inj (lb, Some (toId x'')));
					substProp ctx [(x', toId x'')] p]))
		   lst')
	  );
	  per = (
	    y, y',
	    Cor (List.map (
		   function
		       (lb, None) -> And [Equal (toId y, Inj (lb, None));
					  Equal (toId y, Inj (lb, None))]
		     | (lb, Some {ty=u; per=(z,z',q)}) ->
			 let w =  fresh [z] [y;y'] ctx in
			 let w' = fresh [z'] [w;y;y'] ctx in
			   Cexists ((w,u),
		           Cexists ((w',u),
				    And [Equal (toId y, Inj (lb, Some (toId w)));
					 Equal (toId y', Inj (lb, Some (toId w')));
					 substProp ctx [(z, toId w); (z', toId w')] q])))
		   lst')
	  )
	}

  | L.Rz s ->
      let {ty=t; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
	{
	  ty = t;
	  tot = (x, p);
	  per = (y, y', Equal (toId y, toId y'));
	}

  | L.PROP | L.STABLE | L.EQUIV -> failwith "Cannot translate higher-order logic"

and translateTerm ctx = function
    L.Var n -> Id n

  | L.Star -> Star

  | L.Tuple lst -> Tuple (List.map (translateTerm ctx) lst)

  | L.Proj (k, t) -> Proj (k, translateTerm ctx t)

  | L.App (u, v) -> App (translateTerm ctx u, translateTerm ctx v)

  | L.Lambda ((n, s), t) -> Lambda ((n, (translateSet ctx s).ty), translateTerm ctx t)

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
      let v = translateTerm (addTerm n t ctx) u in
      let v' = substTerm ctx [(n, toId n')] v in
	Let (n, translateTerm ctx t,
	     Obligation ((any, TopTy),
			 Forall ((n', ty1), Imply (
				   substProp ctx [(x1, toId n); (y1, toId n')] p1, 
				   substProp ctx [(x2, v); (y2, v')] p2)),
			 v))

  | L.Quot (t, _) -> translateTerm ctx t

  | L.Choose ((n, st1), r, t, u, st2) ->
      let {ty=ty1; per=(x1,y1,p1)} = translateSet ctx st1 in
      let {per=(x2,y2,p2)} = translateSet ctx st2 in
      let n' = fresh [n] [n] ctx in
      let v = translateTerm (addTerm n t ctx) u in
      let v' = substTerm ctx [(n, toId n')] v in
	Let (n, translateTerm ctx t,
	     Obligation ((any, TopTy),
			 Forall ((n', ty1), Imply (
				   substProp ctx [(x1, toId n); (y1, toId n')] p1, 
				   substProp ctx [(x2, v); (y2, v')] p2)),
			 v))

  | L.Let ((n, s), u, v, _) ->
      Let (n, translateTerm ctx u, translateTerm (addTerm n u ctx) v)

  | L.Subin (t, sb) ->
      let ((x, s), p) = toSubset ctx sb in
      let (ty, y, p') = translateProp (addBind x s ctx) p in
      let t' = translateTerm ctx t in
      let y' = fresh [y; mk_word "v"; mk_word "u"; mk_word "t"] [] ctx in
	Obligation ((y', ty), substProp ctx [(y, toId y'); (x,t')] p', Tuple [t'; toId y'])
  | L.Subout (t, _) -> Proj (0, translateTerm ctx t)

			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
and translateProp ctx = function
    L.False -> (TopTy, any, False)

  | L.True -> (TopTy, any, True)

  | L.Atomic (n, trms) ->
      let r = fresh [mk_word "r"; mk_word "q"; mk_word "s"] [] ctx in
      let ty = (match fst (getLong getProp ctx n) with
		    Syntax.Unstable -> NamedTy n
		  | Syntax.Stable | Syntax.Equivalence -> TopTy)
      in
	(ty, r, NamedProp (n, toId r, List.map (translateTerm ctx) trms))

  | L.And lst ->
      let lst' = List.map (translateProp ctx) lst in
      let t =
	fresh [mk_word "t"; mk_word "p"; mk_word "u"; mk_word "q"; mk_word "r"] [] ctx in
	(TupleTy (List.map (fun (s,_,_) -> s) lst'), t,
	 And (let k = ref 0 in
		List.map (fun (_, x, p) ->
			    let q = substProp ctx [(x, Proj (!k, toId t))] p in incr k ; q)
		  lst')
	)

  | L.Imply (p, q) ->
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; mk_word "x"; mk_word "y"; mk_word "z"] [] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x'] ctx in
	(ArrowTy (t, u),
	 f,
	 Forall ((x', t), Imply (substProp ctx [(x, toId x')] p',
				 substProp ctx [(y, App (toId f, toId x'))] q')))

  | L.Iff (p, q) -> 
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; mk_word "x"; mk_word "y"; mk_word "z"] [] ctx in
      let y' = fresh [y; mk_word "y"; mk_word "z"; mk_word "x"] [x'] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x';y'] ctx in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f,
	 And [
	   Forall ((x', t), Imply (substProp ctx [(x, toId x')] p',
				   substProp ctx [(y, App (Proj (0, toId f), toId x))] q'));
	   Forall ((y', u), Imply (substProp ctx [(y, toId y')] q',
				   substProp ctx [(x, App (Proj (1, toId f), toId y))] p'))
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
		     Cexists ((x',t), And [Equal(toId u, Inj (lb, Some (toId x')));
					   substProp ctx [(x, toId x')] p]))
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
	 Forall ((x',t), Imply (substProp ctx [(x, toId x')] q,
				substProp ctx [(n, toId x'); (y, App (toId f, toId x'))] p'))
	)

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=(x,q)} = translateSet ctx s in
      let (u, y, p') = translateProp (addBind n s ctx) p in
      let w = fresh [mk_word "w"; mk_word "u"; mk_word "p"; mk_word "t"] [] ctx
      in
	(TupleTy [t; u], w,
	 And [
	   substProp ctx [(x, Proj (0, toId w))] q;
	   substProp ctx [(n, Proj (0, toId w)); (y, Proj (1, toId w))] p'
	 ])

  | L.Not p ->
      let (t, n, p') = translateProp ctx p in
	(TopTy, any, Forall ((n, t), Not p'))

  | L.Equal (s, t, u) ->
      let {per=(x,y,p)} = translateSet ctx s in
      let t' = translateTerm ctx t in
      let u' = translateTerm ctx u in
	(TopTy, any, substProp ctx [(x,t'); (y,u')] p)

and translateBinding ctx bind =
  List.map (fun (n, s) -> n, (translateSet ctx s).ty) bind

and translateTheoryElement ctx = function
    L.Set n -> 
      [TySpec (n, None, [("per_" ^ n, [], IsPer n)])],
      addBind (Syntax.N(n, Syntax.Word)) L.SET ctx

  | L.Let_set (n, s) ->
      (let {ty=t; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
	[TySpec (n, Some t,
	 [(n ^ "_def_total", [(x,t)], Iff (NamedTotal (ln_of_string n, toId x), p));
	  (n ^ "_def_per", [(y,t); (y',t)], Iff (NamedPer (ln_of_string n, toId y, toId y'), q))])
	]
      ),
      addSet (Syntax.N(n, Syntax.Word)) s ctx

  | L.Predicate (n, stab, s) -> begin
      let rec domain = function
	| L.Exp (s, t) -> s :: (domain t)
	| L.PROP | L.STABLE | L.EQUIV -> []
	| _ -> failwith "Internal error: invalid domain of a predicate"
      in
      let ty = (if stab = Syntax.Stable or stab = Syntax.Equivalence then
		  TopTy else
		    NamedTy (toLN n))
      in
	[TySpec (Syntax.string_of_name n, None,
		 if stab = Syntax.Stable or stab = Syntax.Equivalence then
		   []
		 else
		   [("predicate_" ^ (Syntax.string_of_name n), [], IsPredicate n)])],
	addProp n (stab, None) ctx
    end

  | L.Let_predicate (n, stab, bind, p) ->
      let bind' = translateBinding ctx bind in
      let ctx' = addBinding bind ctx in
      let (ty, r, p') = translateProp ctx' p in
      let r' = fresh [r] (List.map fst bind) ctx in
	[TySpec (Syntax.string_of_name n, Some ty,
	 [((Syntax.string_of_name n) ^ "_def",
	   (r',ty) :: bind',
	   Iff (NamedProp (toLN n, toId r', List.map (fun (y,_) -> toId y) bind),
		substProp ctx ([(r, toId r')]) p'))])]
	,
	addProp n (stab, Some (bind, p)) ctx

  | L.Let_term (n, s, t) ->
      let {ty=u; per=(y,y',q)} = translateSet ctx s in
      let t' = translateTerm ctx t in
      [ValSpec (n, u, [((Syntax.string_of_name n) ^ "_def", [], 
			substProp ctx [(y, toId n); (y', t')] q)])
      ],
      addTerm n t (addBind n s ctx)

  | L.Value (n, s) ->
      let {ty=t; tot=(x,p)} = translateSet ctx s in
      [ValSpec (n, t, [((Syntax.string_of_name n) ^ "_total", [],
		      substProp ctx [(x, toId n)] p)])],
      addBind n s ctx

  | L.Comment cmmnt -> ([Comment cmmnt], ctx)

  | L.Sentence (_, nm, mdlbind, valbnd, prp) ->
      begin
	let strctbind, ctx' = translateModelBinding ctx mdlbind in
	let ctx'' = addBinding valbnd ctx' in
	let bnd = translateBinding ctx' valbnd in
	let (typ, x, prp') = translateProp ctx'' prp in
	let typ' = List.fold_right (fun (_,t) a -> ArrowTy (t, a)) bnd typ in
	let app = List.fold_left (fun a (n,_) -> App (a, toId n)) (toId nm) bnd in
	let elems =
	  [ ValSpec (nm, typ', [(Syntax.string_of_name nm, bnd, 
				substProp ctx'' [(x, app)] prp')]) ]
	in
	  if mdlbind = [] then
	    elems
	  else
	    [ StructureSpec (String.capitalize (Syntax.string_of_name nm), strctbind, Signat elems) ]
      end, ctx

and translateModelBinding ctx = function
    [] -> [], ctx
  | (m, th) :: rest ->
      let th', ctx' = translateTheory ctx th in
      let rest', ctx'' = translateModelBinding ctx rest in
	(m, th') :: rest', (addModel m ctx' ctx'')

and translateTheoryBody ctx = function
    [] -> [], emptyCtx
  | elem::elems ->
      let es, ctx' = translateTheoryElement ctx elem in
      let th, ctx'' = translateTheoryBody ctx' elems in
	(es @ th), ctx''

and translateTheory ctx = function
    L.Theory body -> 
      let body', ctx' = translateTheoryBody ctx body in
	Signat body', ctx'
  | L.TheoryID id -> SignatID id, ctx

(*
and processModelBinding ctx = function
    [] -> [], emptyCtx
  | (m, th) :: rest ->
      let th', ctx' = processTheory ctx th in
      let rest', ctx'' = processModelBinding ctx rest in
	(m, th') :: rest', (addModel m ctx' ctx'')

and processTheory ctx = function
    L.Theory body -> 
      let body', ctx' = translateTheoryBody ctx body in
	body', ctx'
  | L.TheoryID id -> 
      let args, body = getTheory id ctx in
	if args <> [] then
	  failwith "Cannot accept functors as arguments to sentences"
	else
	  let body', ctx' = processTheory ctx body in
	    body', ctx'
*)

let translateToplevel ctx = function
    (L.Theorydef (n, args, th)) -> 
      let args', ctx' = translateModelBinding ctx args in
	(Signatdef (n, args', fst (translateTheory ctx' th)),  
	 addTheory n args th ctx)
  | (L.TopComment cmmnt) -> (TopComment cmmnt,  ctx)
  | (L.TopModel (mdlnm, thry)) ->
      let (thry',ctx') = translateTheory ctx thry
      in (TopModule(mdlnm,thry'),  ctx')
      

let rec translateToplevels ctx = function
    [] -> ([], ctx)
  | thr :: ths ->
      let (signat,ctx') = translateToplevel ctx thr in
      let (signats,ctx'') = translateToplevels ctx' ths in
	(signat :: signats, ctx'')

