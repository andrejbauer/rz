(* random stuff, probably wrong *)

module L = Logic
module S = Syntax
open Outsyn 
open Context

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
  | CtxProp of L.binding list * L.proposition

let empty = []

let addBind n s ctx = (n, CtxBind s) :: ctx
let addTerm n t ctx = (n, CtxTerm t) :: ctx
let addSet  n s ctx = (n,  CtxSet s) :: ctx
let addProp n (b,p) ctx = (n, CtxProp (b,p)) :: ctx

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
    | (m, CtxProp (b,p)) :: ctx' -> if n = m then (b,p) else find ctx'
    | _ :: ctx' -> find ctx'
  in
    find ctx

let rec toSubset ctx = function
    L.Subset ((x,s), p) -> ((x, s), p)
  | L.Basic b -> toSubset ctx (getSet b ctx)
  | _ -> failwith "not a subset"


(** *** *)

let any = mk_word "_"

let make_type_name _ = function
    (n, Syntax.Word) -> n
  | ("<", _) -> "lt"
  | (">", _) -> "gt"
  | ("<=", _) -> "leq"
  | (">=", _) -> "geq"
  | ("=", _) -> "eq"
  | ("<>", _) -> "neq"
  | (s, _) -> s

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
      let (v,z,r) = translateProp ctx phi in
	{
	  ty = TupleTy [u; v];
	  tot = (
	    let k = fresh [mk_word "k"; mk_word "j"; mk_word "x"] [] ctx in
	      (k,
	       And [substProp ctx [(x, Proj (1, Id k))] p;
		    substProp ctx [(z, Proj (2, Id k))] r]
	      )
	  );
	  per = (
	    let w  = fresh [y; mk_word "w"] [] ctx in
	    let w' = fresh [y'; mk_word "w'"] [w] ctx in
	      (w, w', substProp ctx [(y, Proj (1, Id w)); (y', Proj (1, Id w'))] q)
	  )
	}

  | L.Sum _ -> failwith "Translation of sums not implemented"

  | L.Rz _ -> failwith "Translation of RZ not implemented"

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
		      let ctx' = addBind n s ctx in
			(lb, (n, (translateSet ctx' s).ty), translateTerm ctx' t)
                  | (lb, None, t) ->
                      (lb, (any, UnitTy), translateTerm (addBind any L.Unit ctx) t)
	       )
               lst
	    )

  | L.Let ((n, s), u, v) ->
      Let (n, translateTerm ctx u, translateTerm (addTerm n u ctx) v)

  | L.Subin (t, sb) ->
      let ((x, s), p) = toSubset ctx sb in
      let (ty, y, p') = translateProp (addBind x s ctx) p in
      let t' = translateTerm ctx t in
      let y' = fresh [y; mk_word "v"; mk_word "u"; mk_word "t"] [] ctx in
	Tuple [t'; Obligation ((y', ty), substProp ctx [(y, Id y'); (x,t')] p')]
  | L.Subout (t, _) -> Proj (1, translateTerm ctx t)

			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
and translateProp ctx = function
    L.False -> (VoidTy, any, False)

  | L.True -> (UnitTy, any, True)

  | L.Atomic (n, t) ->
      let r = fresh [mk_word "r"; mk_word "q"; mk_word "s"] [] ctx in
      let n' = make_type_name ctx n in
	(NamedTy n', r, NamedProp (n', Id r, translateTerm ctx t))

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
	(SumTy (List.map2 (fun lb (t,_,_) -> (lb, t)) lbs lst'),
	 u,
	 And (
	   List.map2
		(fun lb (t,x,p) ->
		   let x' = fresh [x] [u] ctx in
		     Forall ((x',t), Imply (Equal(Id u, Inj (lb, Id x')), substProp ctx [(x, Id x')] p)))
		lbs lst'
	 ))

  | L.Forall ((n, s), p) ->
      let {ty=t; tot=(x,q)} = translateSet ctx s in
      let (u, y, p') = translateProp (addBind n s ctx) p in
      let x' = fresh [x] [] ctx in
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
	   substProp ctx [(x, Proj (1, Id w))] q;
	   substProp ctx [(n, Proj (1, Id w)); (y, Proj (2, Id w))] p'
	 ])

  | L.Not p ->
      let (t, n, p') = translateProp ctx p in
	(UnitTy, any, Forall ((n, t), Not p'))

  | L.Equal (s, t, u) ->
      let {per=(x,y,p)} = translateSet ctx s in
      let t' = translateTerm ctx t in
      let u' = translateTerm ctx u in
	(UnitTy, any, substProp ctx [(x,t'); (y,u')] p)

let translateBinding ctx (n, s) = (n, (translateSet ctx s).ty)

let translateTheoryElement ctx = function
    L.Set n -> 
      TySpec (fst n, None),
      addBind n L.SET ctx

  | L.Let_set (n, s) ->
      TySpec (fst n, Some (translateSet ctx s)),
      addSet n s ctx

  | L.Predicate (n, _, s) ->
      TySpec (make_type_name ctx n, None),
      addBind n (L.Exp (s, L.PROP)) ctx

  | L.Let_predicate (n, bind, p) ->
      failwith "predicate definitions not implemented"

  | L.Let_term (n, s, t) -> raise Unimplemented

  | L.Value (n, s) ->
      ValSpec (n, translateSet ctx s, None),
      addBind n s ctx

  | L.Define (n, s, t) ->
      ValSpec (n, translateSet ctx s, Some (translateTerm ctx t)),
      addTerm n t ctx

  | L.Sentence (_, n, bind, p) ->
	SentenceSpec (n, List.map (translateBinding ctx) bind,
		      translateProp (addBinding bind ctx) p),
	addProp n (bind, p) ctx

let rec translateTheoryBody ctx = function
    [] -> ctx, []
  | elem::elems ->
      let e, ctx' = translateTheoryElement ctx elem in
      let ctx'', th = translateTheoryBody ctx' elems in
	ctx'', (e :: th)

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
