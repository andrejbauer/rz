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

let empty = []

let addBind n s ctx = (n, CtxBind s) :: ctx
let addTerm n t ctx = (n, CtxTerm t) :: ctx
let addSet  n s ctx = (n,  CtxSet s) :: ctx
let addProp n (stb,x) ctx = (n, CtxProp (stb,x)) :: ctx

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

(** *** *)

let rec toSubset ctx = function
    L.Subset ((x,s), p) -> ((x, s), p)
  | L.Basic b -> toSubset ctx (getSet b ctx)
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

let rec translateSet ctx = function
    L.Empty -> 
      { ty = VoidTy;
	tot = (any, False);
	per = (any, any, False)
      }
  | L.Unit ->
      let x = fresh [mk_word "x"] [] ctx in
      { ty = UnitTy;
	tot = (x, Equal (Id x, Star));
	per = (any, any, True)
      }
  | L.Bool ->
      let x = fresh [mk_word "x"; mk_word "u"] [] ctx in
      let y = fresh [mk_word "y"; mk_word "v"] [x] ctx in
	{ ty = NamedTy (mk_word "bool");
	  tot = (x, (Cor [Equal (Id x, mk_id "true");
                          Equal (Id x, mk_id "false")]));
	  per = (x, y, Equal (Id x, Id y))
      }
  | L.Basic s ->
      let x = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "a"] [] ctx in
      let y = fresh [mk_word "y"; mk_word "v"; mk_word "b"] [x] ctx in
	{ ty = NamedTy s;
	  tot = (x, NamedTotal (s, Id x));
	  per = (x, y, NamedPer (s, Id x, Id y))
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
			       let q = substProp ctx [(x, Proj (!k, Id t))] p in
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
			       let q = substProp ctx [(x, Proj (!k, Id t)); (y, Proj (!k, Id u))] p in
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
	         Imply (substProp ctx [(x, Id z); (x', Id z')] p,
			substProp ctx [(y, App (Id f, Id x)); (y', App (Id f, Id x'))] q)
		      ))
	      )
	  );
	  per = (
	      (f, g,
	       Forall ((z,u),
               Forall ((z',u),
                 Imply (substProp ctx [(x, Id z); (x', Id z')] p,
			substProp ctx [(y, App (Id f, Id x)); (y', App (Id g, Id x'))] q)
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
	       And [substProp ctx [(x, Proj (0, Id k))] p;
		    substProp ctx [(n, Proj (0, Id k)); (z, Proj (1, Id k))] r]
	      )
	  );
	  per = (
	    let w  = fresh [y; mk_word "w"] [] ctx in
	    let w' = fresh [y'; mk_word "w'"] [w] ctx in
	      (w, w', substProp ctx [(y, Proj (0, Id w)); (y', Proj (0, Id w'))] q)
	  )
	}
  | L.Quotient (s, r) ->
      let {ty=u; tot=(w,p); per=(z,z',q)} = translateSet ctx s in
	{ ty = u;
	  tot = (w, p);
	  per = (
	    let u = fresh [z] [] ctx in
	    let u' = fresh [z'] [u] ctx in
	      u, u', NamedProp (r, Dagger, Tuple [Id u; Id u'])
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
		       (lb, None) -> Equal (Id x, Inj (lb, None))
		     | (lb, Some {ty=u; tot=(x',p)}) ->
			 let x'' = fresh [x'] [x] ctx in
			   Cexists ((x'', u),
				   And [Equal (Id x, Inj (lb, Some (Id x'')));
					substProp ctx [(x', Id x'')] p]))
		   lst')
	  );
	  per = (
	    y, y',
	    Cor (List.map (
		   function
		       (lb, None) -> And [Equal (Id y, Inj (lb, None));
					  Equal (Id y, Inj (lb, None))]
		     | (lb, Some {ty=u; per=(z,z',q)}) ->
			 let w =  fresh [z] [y;y'] ctx in
			 let w' = fresh [z'] [w;y;y'] ctx in
			   Cexists ((w,u),
		           Cexists ((w',u),
				    And [Equal (Id y, Inj (lb, Some (Id w)));
					 Equal (Id y', Inj (lb, Some (Id w')));
					 substProp ctx [(z, Id w); (z', Id w')] q])))
		   lst')
	  )
	}

  | L.Rz s ->
      let {ty=t; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
	{
	  ty = t;
	  tot = (x, p);
	  per = (y, y', Equal (Id y, Id y'));
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

  | L.RzChoose ((n, s), t, u) ->
      Let (n, translateTerm ctx t, translateTerm (addTerm n t ctx) u)

  | L.Quot (t, _) -> translateTerm ctx t

  | L.Choose ((n, s), r, t, u) ->
      Let (n, translateTerm ctx t, translateTerm (addTerm n t ctx) u)

  | L.Let ((n, s), u, v) ->
      Let (n, translateTerm ctx u, translateTerm (addTerm n u ctx) v)

  | L.Subin (t, sb) ->
      let ((x, s), p) = toSubset ctx sb in
      let (ty, y, p') = translateProp (addBind x s ctx) p in
      let t' = translateTerm ctx t in
      let y' = fresh [y; mk_word "v"; mk_word "u"; mk_word "t"] [] ctx in
	Tuple [t'; Obligation ((y', ty), substProp ctx [(y, Id y'); (x,t')] p')]
  | L.Subout (t, _) -> Proj (0, translateTerm ctx t)

			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
and translateProp ctx = function
    L.False -> (TopTy, any, False)

  | L.True -> (TopTy, any, True)

  | L.Atomic (n, t) ->
      let r = fresh [mk_word "r"; mk_word "q"; mk_word "s"] [] ctx in
      let ty = (match fst (getProp n ctx) with
		    Syntax.Unstable -> NamedTy n
		  | Syntax.Stable | Syntax.Equivalence -> TopTy)
      in
	(ty, r, NamedProp (n, Id r, translateTerm ctx t))

  | L.And lst ->
      let lst' = List.map (translateProp ctx) lst in
      let t =
	fresh [mk_word "t"; mk_word "p"; mk_word "u"; mk_word "q"; mk_word "r"] [] ctx in
	(TupleTy (List.map (fun (s,_,_) -> s) lst'), t,
	 And (let k = ref 0 in
		List.map (fun (_, x, p) ->
			    let q = substProp ctx [(x, Proj (!k, Id t))] p in incr k ; q)
		  lst')
	)

  | L.Imply (p, q) ->
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; mk_word "x"; mk_word "y"; mk_word "z"] [] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x'] ctx in
	(ArrowTy (t, u),
	 f,
	 Forall ((x', t), Imply (substProp ctx [(x, Id x')] p',
				 substProp ctx [(y, App (Id f, Id x'))] q')))

  | L.Iff (p, q) -> 
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; mk_word "x"; mk_word "y"; mk_word "z"] [] ctx in
      let y' = fresh [y; mk_word "y"; mk_word "z"; mk_word "x"] [x'] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x';y'] ctx in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f,
	 And [
	   Forall ((x', t), Imply (substProp ctx [(x, Id x')] p',
				   substProp ctx [(y, App (Proj (0, Id f), Id x))] q'));
	   Forall ((y', u), Imply (substProp ctx [(y, Id y')] q',
				   substProp ctx [(x, App (Proj (1, Id f), Id y))] p'))
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
		     Cexists ((x',t), And [Equal(Id u, Inj (lb, Some (Id x')));
					   substProp ctx [(x, Id x')] p]))
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
	 Forall ((x',t), Imply (substProp ctx [(x, Id x')] q,
				substProp ctx [(n, Id x'); (y, App (Id f, Id x'))] p'))
	)

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=(x,q)} = translateSet ctx s in
      let (u, y, p') = translateProp (addBind n s ctx) p in
      let w = fresh [mk_word "w"; mk_word "u"; mk_word "p"; mk_word "t"] [] ctx
      in
	(TupleTy [t; u], w,
	 And [
	   substProp ctx [(x, Proj (0, Id w))] q;
	   substProp ctx [(n, Proj (0, Id w)); (y, Proj (1, Id w))] p'
	 ])

  | L.Not p ->
      let (t, n, p') = translateProp ctx p in
	(TopTy, any, Forall ((n, t), Not p'))

  | L.Equal (s, t, u) ->
      let {per=(x,y,p)} = translateSet ctx s in
      let t' = translateTerm ctx t in
      let u' = translateTerm ctx u in
	(TopTy, any, substProp ctx [(x,t'); (y,u')] p)

let translateBinding ctx bind =
  List.map (fun (n, s) -> n, (translateSet ctx s).ty) bind

let rec domain = function
  | L.Exp (s, t) -> s :: (domain t)
  | L.PROP | L.STABLE | L.EQUIV -> []
  | _ -> failwith "Internal error: invalid domain of a predicate"

let translateTheoryElement ctx = function
    L.Set n -> 
      [TySpec (n, None);
       (let x = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "v"] [] ctx in
	  AssertionSpec ([(x, NamedTy n)],
			 Imply (NamedPer (n, Id x, Id x), NamedTotal (n, Id x))));
       (let x = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "v"] [] ctx in
	let x' = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "v"] [x] ctx in
	  AssertionSpec ([(x, NamedTy n); (x', NamedTy n)],
			 Imply (NamedPer (n, Id x, Id x'), NamedPer (n, Id x', Id x))));
       (let x = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "v"] [] ctx in
	let x' = fresh [mk_word "x"; mk_word "y"; mk_word "u"; mk_word "v"] [x] ctx in
	let x''= fresh [mk_word "x"; mk_word "y"; mk_word "z"; mk_word "v"] [x;x'] ctx in
	  AssertionSpec (
	    [(x, NamedTy n); (x', NamedTy n); (x'', NamedTy n)],
	    Imply (And [NamedPer (n, Id x, Id x'); NamedPer (n, Id x', Id x'')],
		   NamedPer (n, Id x, Id x''))))
      ],
      addBind n L.SET ctx

  | L.Let_set (n, s) ->
      (let {ty=t; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
	[TySpec (n, Some t);
	 AssertionSpec ([(x,t)], Iff (NamedTotal (n, Id x), p));
	 AssertionSpec ([(y,t); (y',t)], Iff (NamedPer (n, Id y, Id y'), q))
	]
      ),
      addSet n s ctx

  | L.Predicate (n, stab, s) ->
      let ty = (if stab = Syntax.Stable or stab = Syntax.Equivalence then TopTy else NamedTy n) in
	((if stab = Syntax.Stable or stab = Syntax.Equivalence then [] else [TySpec (n, None)])) @
	[(
	   let r = fresh [mk_word "r"; mk_word "s"; mk_word "t"; mk_word "p"] [n] ctx in
	   let _, bind, app, tots =
	     List.fold_left
	       (fun (bad, bind, app, tots) d ->
		  let {ty=t; tot=(x,p)} = translateSet ctx d in
		  let x' = fresh [x] bad ctx in
		    (x'::bad, (x',t)::bind, (Id x')::app, (substProp ctx [(x, Id x')] p)::tots))
	       ([r; n],[],[],[]) (domain s)
	   in
	     AssertionSpec ((r, ty)::bind, Imply (
			      NamedProp (n, Id r, tuplify app),
			      And tots
			    )));
	 (let r = fresh [mk_word "r"; mk_word "s"; mk_word "t"; mk_word "p"] [n] ctx in
	  let _, bind, app1, app2, eqs =
	    List.fold_left
	      (fun (bad, bind, app1, app2, eqs) d ->
		 let {ty=t; per=(x,y,p)} = translateSet ctx d in
		 let x' = fresh [x] bad ctx in
		 let y' = fresh [y] (x'::bad) ctx in
		   (x'::y'::bad, (x',t)::(y',t)::bind,
		    (Id x')::app1, (Id y')::app2,
		    (substProp ctx [(x, Id x'); (y, Id y')] p)::eqs))
	      ([r;n], [], [], [], []) (domain s)
	  in
	    AssertionSpec (
	      (r, ty)::bind, Imply (
		And ((NamedProp (n, Id r, tuplify app1))::eqs),
		NamedProp (n, Id r, tuplify app2)
	      )))] ,
      addProp n (stab, None) ctx

  | L.Let_predicate (n, stab, bind, p) ->
      let bind' = translateBinding ctx bind in
      let ctx' = addBinding bind ctx in
      let (ty, r, p') = translateProp ctx' p in
      let r' = fresh [r] (List.map fst bind) ctx in
	[TySpec (n, Some ty);
	 AssertionSpec (
	   (r',ty) :: bind',
	   Iff (NamedProp (n, Id r', Tuple (List.map (fun (y,_) -> Id y) bind)),
		substProp ctx ([(r, Id r')]) p'))
	],
	addProp n (stab, Some (bind, p)) ctx

  | L.Let_term (n, s, t) ->
      let {ty=u; per=(y,y',q)} = translateSet ctx s in
      let t' = translateTerm ctx t in
      [ValSpec (n, u);
       AssertionSpec([], substProp ctx [(y, Id n); (y', t')] q)
      ],
      addTerm n t (addBind n s ctx)

  | L.Value (n, s) ->
      let {ty=t; tot=(x,p)} = translateSet ctx s in
      [ValSpec (n, t);
       AssertionSpec ([], substProp ctx [(x, Id n)] p)
      ],
      addBind n s ctx

  | L.Define (n, s, t) ->
      (let {ty=ty; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
       let t' = translateTerm ctx t in
	 [ValSpec (n, ty);
	  AssertionSpec ([], substProp ctx [(x, Id n)] p);
	  AssertionSpec ([], substProp ctx [(y, Id n); (y', t')] q)
	 ]
      ),
      addBind n s ctx

  | L.Sentence (_, n, bind, p) ->
      begin
	let ctx' = List.fold_left (fun cx (x,s) -> addBind x s cx) ctx bind in
	let (ty, x, p') = translateProp ctx' p in
	let p'' = substProp ctx' [(x, App (Id n, Tuple (List.map (fun (x,_) -> Id x) bind)))] p' in
	let rec fold cx tots = function
	    [] -> [],
	      (match List.rev tots with
		   [] -> p''
		 | [q] -> Imply (q, p'')
		 | qs -> Imply (And qs, p'')
	      )
	  | (x, s) :: bs ->
	      let {ty=t; tot=(y,q)} = translateSet cx s in
	      let (cx, r) = fold (addBind x s cx) ((substProp cx [(y, Id x)] q)::tots) bs in
		((x,t)::cx), r
	in
	let (b, r) = fold ctx [] bind in 
	  [ ValSpec (n, ArrowTy (TupleTy (List.map snd b), ty));
	    AssertionSpec (b, r)
	  ]
      end,
      addProp n (Syntax.Unstable, Some (bind, p)) ctx

let rec translateTheoryBody ctx = function
    [] -> ctx, []
  | elem::elems ->
      let es, ctx' = translateTheoryElement ctx elem in
      let ctx'', th = translateTheoryBody ctx' elems in
	ctx'', (es @ th)

let translateTheory {L.t_name=name; L.t_arg=args; L.t_body=body} =
  let ctx, args' =
    (match args with
	 None -> empty, None
       | Some a ->
	   let ctx, a' = translateTheoryBody empty a in
	     ctx, Some a'
    )
  in
    { s_name = name;
      s_arg = args';
      s_body = snd (translateTheoryBody ctx body)
    }
