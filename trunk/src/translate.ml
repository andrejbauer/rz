(* random stuff, probably wrong *)

module L = Logic
module S = Syntax
open Outsyn 
open Context

(** AB
Translation functions should be (roughly):

translateSet s
  translates a set s to a pair (ty, re) where ty is a
  type and re describes the realizability relation on ty.

translateTerm t
  translates a term t of Logic.term to a value of type Outsyn.term.

translateProp phi
  translate a formula phi to (ty, s) where ty is a type
  and s tells which values of ty are realizers for phi.

I am not quite sure this is right. I need to think more.
At some point we need to separate logical formulas from terms
(they're not in syntax.ml). Also, it seems likely we need to drag
around typing contexts.

*)

exception Unimplemented

let any = mk_word "_"


let make_type_name = function
    (n, Syntax.Word) -> n
  | ("<", _) -> "lt"
  | (">", _) -> "gt"
  | ("<=", _) -> "leq"
  | (">=", _) -> "geq"
  | ("=", _) -> "eq"
  | ("=", _) -> "eq"
  | ("<>", _) -> "neq"
  | (s, _) -> s

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
	{ ty = NamedTy "bool";
	  tot = (x, (Cor [Equal (Id x, mk_id "true");
                          Equal (Id x, mk_id "false")]));
	  per = (x, y, Equal (Id x, Id y))
      }
  | L.Basic (s, _) ->
      let x = fresh [mk_word "x"; mk_word "u"] [] ctx in
      let y = fresh [mk_word "y"; mk_word "v"] [x] ctx in
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
			       let q = substProp [(x, Proj (!k, Id t))] p in incr k ; q) us
	       )
	      )
	  );
	  per = (
	    let t = fresh [mk_word "t"; mk_word "u"; mk_word "v"] [] ctx in
	    let u = fresh [mk_word "u"; mk_word "v"; mk_word "w"] [t] ctx in
	      (t, u, And (
		 let k = ref 0 in
		   List.map (fun {per=(x,y,p)} ->
			       let q = substProp [(x, Proj (!k, Id t)); (y, Proj (!k, Id u))] p in
				 incr k; q
			    ) us
	       )
	      )
	  )
	}
  | L.Exp (s, t) ->
      let {ty=u; per=(x,x',p)} = translateSet ctx s in
      let {ty=v; per=(y,y',q)} = translateSet ctx t in
	{ ty = ArrowTy (u, v);
	  tot = (
	    let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"] [x;x'] ctx in
	      (f,
	       Forall ((x, u),
	       Forall ((x', u),
	         Imply (p,
			substProp [(y, App (Id f, Id x)); (y', App (Id f, Id x'))] q)
		      ))
	      )
	  );
	  per = (
	    let z = fresh [x; mk_word "x"; mk_word "y"] [] ctx in
	    let z' = fresh [x'; mk_word "x'"; mk_word "y'"] [x] ctx in
	    let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"] [z;z'] ctx in
	    let g = fresh [mk_word "g"; mk_word "h"; mk_word "k"] [f;z;z'] ctx in
	      (f, g,
	       Forall ((z,u),
               Forall ((z',u),
                 Imply (substProp [(x, Id z); (x', Id z')] p,
			substProp [(y, App (Id f, Id x)); (y', App (Id g, Id x'))] q)
		      ))
	      )
	  )
	}

  | L.Subset ((n, s), phi) ->
      let {ty=u; tot=(x,p); per=(y,y',q)} = translateSet ctx s in
      let (v,z,r) = translateProp ctx phi in
	{
	  ty = TupleTy [u; v];
	  tot = (
	    let k = fresh [mk_word "k"; mk_word "j"; mk_word "x"] [] ctx in
	      (k,
	       And [substProp [(x, Proj (1, Id k))] p;
		    substProp [(z, Proj (2, Id k))] r]
	      )
	  );
	  per = (
	    let w  = fresh [y; mk_word "w"] [] ctx in
	    let w' = fresh [y'; mk_word "w'"] [w] ctx in
	      (w, w', substProp [(y, Proj (1, Id w)); (y', Proj (1, Id w'))] q)
	  )
	}

  | L.Sum _ -> failwith "Translation of sums not implemented"

  | L.RZ _ -> failwith "Translation of RZ not implemented"

(* remaining cases:
  | Sum of (label * set option) list
  | RZ of set
  | Quotient, if we add this to Logic
*)

and translateTerm ctx = function
    L.Var n -> Id n

  | L.Star -> Star

  | L.Tuple lst -> Tuple (List.map (translateTerm ctx) lst)

  | L.Proj (k, t) -> Proj (k, translateTerm ctx t)

  | L.App (u, v) -> App (translateTerm ctx u, translateTerm ctx v)

  | L.Lambda ((n, s), t) -> Lambda ((n, (translateSet ctx s).ty), translateTerm ctx t)

  | L.Inj (lb, t) -> Inj (lb, translateTerm ctx t)

  | L.Case (t1, lst) ->
      Cases (translateTerm ctx t1, List.map
	       (function
		    (lb, Some (n, s), t) ->
		      let ctx' = addCtx n s ctx in
			(lb, (n, (translateSet ctx' s).ty), translateTerm ctx' t)
                  | (lb, None, t) ->
                      (lb, (any, UnitTy), translateTerm (addCtx any L.Unit ctx) t)
	       )
               lst
	    )

  | L.Let ((n, s), u, v) ->
      Let (n, translateTerm ctx u, translateTerm (addCtx n s ctx) v)

  | L.Subin (t, sb) ->
      let ((x, s), p) = L.toSubset ctx sb in
      let (ty, y, p') = translateProp (addCtx x s ctx) p in
      let t' = translateTerm ctx t in
      let y' = fresh [y; mk_word "v"; mk_word "u"; mk_word "t"] [] ctx in
	Tuple [t'; Obligation ((y', ty), substProp [(y, Id y'); (x,t')] p')]
  | L.Subout (t, _) -> Proj (1, translateTerm ctx t)

			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
and translateProp ctx = function
    L.False -> (VoidTy, any, False)

  | L.True -> (UnitTy, any, True)

  | L.Atomic (n, t) ->
      let r = fresh [mk_word "r"; mk_word "q"; mk_word "s"] [] ctx in
      let n' = make_type_name ctx n in
	(NamedTy n', r, NamedProp (n', Id r, translateTerm t))

  | L.And lst ->
      let lst' = List.map (translateProp ctx) lst in
      let t = fresh [mk_word "t"; mk_word "p"; mk_word "u"; mk_word "q"; mk_word "r"] ctx in
	(TupleTy (List.map (fun (s,_,_) -> s) lst'), t,
	 And (let k = ref 0 in
		List.map (fun (_, x, p) ->
			    let q = substProp [(x, Proj (!k, Id t))] p in incr k ; q)
		  lst')
	)

  | L.Imply (p, q) ->
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; "x"; "y"; "z"] [] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x'] ctx in
	(ArrowTy (t, u),
	 f,
	 Forall ((x', t), Imply (substProp [(x,x')] p',
				 substProp [(y, App (Id f, Id x'))] q')))

  | L.Iff (p, q) -> 
      let (t, x, p') = translateProp ctx p in
      let (u, y, q') = translateProp ctx q in
      let x' = fresh [x; "x"; "y"; "z"] [] ctx in
      let y' = fresh [y; "y"; "z"; "x"] [x'] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"] [x';y'] ctx in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f,
	 And [
	   Forall ((x', t), Imply (substProp [(x,x')] p',
				   substProp [(y, App (Proj (0, Id f), Id x))] q'));
	   Forall ((y', u), Imply (substProp [(y,y')] q',
				   substProp [(x, App (Proj (1, Id f), Id y))] p'))
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
	(SumTy (List.map2 (fun lb (t,_,_) -> (lb, t)) lbs lst'),
	 u,
	 And (
	   List.map2
		(fun lb (t,x,p) ->
		   let x' = fresh [x] [u] ctx in
		     Forall ((x',t), Imply (Equal(Id u, Inj (lb, Id x')), substProp [(x,x')] p)))
		lbs lst'
	 ))

  | L.Forall ((n, s), p) ->
      let {ty=t; tot=(x,q)} = translateSet ctx s in
      let (u, y, p') = translateProp (ctxAdd n s ctx) p in
      let x' = fresh [x] ctx in
      let f = fresh [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "l"] [x'] ctx
      in
	(ArrowTy (t, u),
	 f,
	 Forall ((x',t), Imply (substProp [(x,x')] q,
				substProp [(n,x'); (y, App (Id f, Id x'))] p'))
	)

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=(x,q)} = translateSet s in
      let (u, y, p') = translateProp ctx p in
      let w = find_name [mk_word "w"; mk_word "u"; mk_word "p"; mk_word "t"] (List.map fst ctx)
      in
	(TupleTy [t; u], w,
	 And [
	   substProp [(x, Proj (1, Id w))] q;
	   substProp [(n, Proj (1, Id w)); (y, Proj (2, Id w))] p'
	 ])

  | L.Not p ->
      let (t, n, p') = translateProp ctx p in
	(UnitTy, any, Forall ((n, t), Not p'))

  | L.Equal (s, t, u) ->
      let {per=(x,y',p)} = translateSet ctx s in
      let t' = translateTerm ctx t in
      let u' = translateTerm ctx u in
	(UnitTy, any, substProp [(x,t'); (y,u')] p)

let translateBinding (n, s) = (n, (translateSet s).ty)

let translateTheoryElement = function
    L.Set n -> TySpec (n, None)
  | L.Let_set (n, s) -> TySpec (n, Some (translateSet s))
  | L.Predicate (n, _, s) -> TySpec (make_type_name n, None)
  | L.Let_predicate (n, bind, p) -> raise Unimplemented
  | L.Let_term (n, s, t) -> raise Unimplemented
  | L.Value (n, s) -> ValSpec (n, translateSet s, None)
  | L.Define (n, s, t) -> ValSpec (n, translateSet s, Some (translateTerm t))
  | L.Sentence (_, n, bind, p) ->
      SentenceSpec (n, List.map translateBinding bind, translateProp [] p)

let translateTheory {L.t_name=name; L.t_arg=args; L.t_body=body} =
  { s_name = name;
    s_arg = (match args with
		 None -> None
	       | Some a -> Some (List.map translateTheoryElement a));
    s_body = List.map translateTheoryElement body
  }
