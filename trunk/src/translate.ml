(* random stuff, probably wrong *)

module L = Logic
module S = Syntax
open Outsyn 

(** AB
Translation functions should be (roughly):

translateSet s
  translates a set s to a pair (ty, re) where ty is a
  type and re describes the realizability relation on ty.

translateTerm t
  translates a term t of Logic.term to a value of type Outsyn.term.

translateProposition phi
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
  | ("<>", _) -> "neq"
  | (s, _) -> s

let rec translateSet = function
    L.Empty -> 
      { ty = VoidTy;
	tot = (any, False);
	per = (any, any, False)
      }
  | L.Unit ->
      { ty = UnitTy;
	tot = (mk_word "x", Equal (mk_id "x", Star));
	per = (any, any, True)
      }
  | L.Bool ->
      { ty = NamedTy "bool";
	tot = (mk_word "x", (Cor [Equal (mk_id "x", mk_id "true");
                          Equal (mk_id "x", mk_id "false")]));
	per = (mk_word "x", mk_word "y", Equal (mk_id "x", mk_id "y"))
      }
  | L.Basic s ->
      { ty = NamedTy s;
	tot = (mk_word "x", NamedTotal (s, mk_id "x"));
	per = (mk_word "x", mk_word "y", NamedPer (s, mk_id "x", mk_id "y"))
      }
  | L.Product lst ->
      let us = List.map translateSet lst in
	{
	  ty = TupleTy (List.map (fun u -> u.ty) us);
	  tot = (
	    let t = mk_word "t" in
	      (t, And (
		 let k = ref 0 in
		   List.map (fun {tot=(x,p)} ->
			       let q = subst_proposition [(x, Proj (!k, Id t))] p in incr k ; q) us
	       )
	      )
	  );
	  per = (
	    let t = mk_word "t" in
	    let u = mk_word "u" in
	      (t, u, And (
		 let k = ref 0 in
		   List.map (fun {per=(x,y,p)} ->
			       let q = subst_proposition [(x, Proj (!k, Id t)); (y, Proj (!k, Id u))] p in
				 incr k; q
			    ) us
	       )
	      )
	  )
	}
  | L.Exp (s, t) ->
      let {ty=u; per=(x,x',p)} = translateSet s in
      let {ty=v; per=(y,y',q)} = translateSet t in
	{ ty = ArrowTy (u, v);
	  tot = (
	    let f = find_name [mk_word "f"; mk_word "g"; mk_word "h"] [x;x'] in
	      (f,
	       Forall ((x, u),
	       Forall ((x', u),
	         Imply (p,
			subst_proposition [(y, App (Id f, Id x)); (y', App (Id f, Id x'))] q)
		      ))
	      )
	  );
	  per = (
	    let f = find_name [mk_word "f"; mk_word "g"; mk_word "h"] [x; x'] in
	    let g = find_name [mk_word "f"; mk_word "g"; mk_word "h"] [x; x'; f] in
	      (f, g,
	       Forall ((x, u),
               Forall ((x', u),
                 Imply (p,
			subst_proposition [(y, App (Id f, Id x)); (y', App (Id g, Id x'))] q)
		      ))
	      )
	  )
	}

  | L.Subset ((n, s), phi) ->
      let {ty=u; tot=(x,p); per=(y,y',q)} = translateSet s in
      let (v,z,r) = translateProposition [] phi in
	{
	  ty = TupleTy [u; v];
	  tot = (
	    let k = find_name [mk_word "k"; mk_word "j"; mk_word "x"] [] in
	      (k,
	       And [subst_proposition [(x, Proj (1, Id k))] p;
		    subst_proposition [(z, Proj (2, Id k))] r]
	      )
	  );
	  per = (
	    let w  = find_name [y; y'; mk_word "w"] [] in
	    let w' = find_name [w; y; y'; mk_word "w"] [] in
	      (w, w', subst_proposition [(y, Proj (1, Id w)); (y', Proj (1, Id w'))] q)
	  )
	}

(* remaining cases:
  | Sum of (label * set option) list
  | RZ of set
  | Quotient, if we add this to Logic
*)

and translateTerm = function
    L.Var n -> Id n
  | L.Star -> Star
  | L.Tuple lst -> Tuple (List.map translateTerm lst)
  | L.Proj (k, t) -> Proj (k, translateTerm t)
  | L.App (u, v) -> App (translateTerm u, translateTerm v)
  | L.Lambda ((n, s), t) -> Lambda ((n, (translateSet s).ty), translateTerm t)
  | L.Inj (lb, t) -> Inj (lb, translateTerm t)
  | L.Case (t1, lst) -> Cases (translateTerm t1, 
                               List.map (function 
                                            (lb, Some (n, s), t) -> 
                                               (lb, (n, (translateSet s).ty),
                                                translateTerm t)
                                          | (lb, None, t) ->
                                               (lb, (any, UnitTy), 
                                                translateTerm t))
                                        lst)
  | L.Let ((n,_), u, v) -> Let (n, translateTerm u, translateTerm v)
  | L.Subin (t, _) -> Tuple [translateTerm t; Questionmark]
  | L.Subout (t, _) -> Proj (1, translateTerm t)
			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
and translateProposition ctx = function
    L.False -> (VoidTy, any, False)

  | L.True -> (UnitTy, any, True)

  | L.Atomic (n, t) ->
      let r = find_name [mk_word "r"; mk_word "q"; mk_word "s"] (List.map fst ctx)
      in
	(NamedTy (make_type_name n), r, NamedProp (make_type_name n, Id r, translateTerm t))

  | L.And lst ->
      let lst' = List.map (translateProposition ctx) lst in
      let t = find_name
		[mk_word "t"; mk_word "p"; mk_word "u"; mk_word "q"; mk_word "r"]
		(List.map fst ctx) in
	(TupleTy (List.map (fun (s,_,_) -> s) lst'), t,
	 And (let k = ref 0 in
		List.map (fun (_, x, p) ->
			    let q = subst_proposition [(x, Proj (!k, Id t))] p in
			      incr k ; q)
		  lst'))

  | L.Imply (p, q) ->
      let (t, x, p') = translateProposition ctx p in
      let (u, y, q') = translateProposition ctx q in
      let f = find_name [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"]
		(x :: (List.map fst ctx)) in
	(ArrowTy (t, u), f, Forall ((x, t), Imply (p', subst_proposition [(y, App (Id f, Id x))] q')))

  | L.Iff (p, q) -> 
      let (t, x, p') = translateProposition ctx p in
      let (u, y, q') = translateProposition ctx q in
      let f = find_name
		[mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"; mk_word "r"]
		(x :: y :: (List.map fst ctx))
      in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f, And [
	   Forall ((x, t), Imply (p', subst_proposition [(y, App (Proj (0, Id f), Id x))] q'));
	   Forall ((y, u), Imply (q', subst_proposition [(x, App (Proj (1, Id f), Id y))] p'))])

  | L.Or lst ->
      let rec make_labels i j =
	if i >= j then [] else ("or" ^ (string_of_int i)) :: (make_labels (i+1) j)
      in
      let lst' = List.map (translateProposition ctx) lst in
      let lbs = make_labels 0 (List.length lst) in
      let u = find_name
		[mk_word "u"; mk_word "v"; mk_word "w"; mk_word "r"]
		((List.map (fun (_,x,_) -> x) lst') @ (List.map fst ctx))
      in
	(SumTy (List.map2 (fun lb (s,_,_) -> (lb, s)) lbs lst'), u,
	 And (
	   List.map2
		(fun lb (t,y,p) -> Forall ((y,t), Imply (Equal(Id u, Inj (lb, Id y)), p)))
		lbs lst'
	 ))

  | L.Forall ((n, s), p) ->
      let {ty=t; tot=(x,q)} = translateSet s in
      let (u, y, p') = translateProposition ctx p in
      let f = find_name [mk_word "f"; mk_word "g"; mk_word "h"; mk_word "l"] (List.map fst ctx)
      in
	(ArrowTy (t, u), f,
	 Forall ((x,t), Imply (q, subst_proposition [(y, App (Id f, Id x))] p'))
	)

  | L.Exists ((n, s), p) -> 
      let {ty=t; tot=(x,q)} = translateSet s in
      let (u, y, p') = translateProposition ctx p in
      let w = find_name [mk_word "w"; mk_word "u"; mk_word "p"; mk_word "t"] (List.map fst ctx)
      in
	(TupleTy [t; u], w,
	 And [
	   subst_proposition [(x, Proj (1, Id w))] q;
	   subst_proposition [(n, Proj (1, Id w)); (y, Proj (2, Id w))] p'
	 ])

  | L.Not p ->
      let (t, n, p') = translateProposition ctx p in
	(UnitTy, any, Forall ((n, t), Not p'))

  | L.Equal (s, t, u) -> (UnitTy, any, Equal (translateTerm t, translateTerm u))

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
      SentenceSpec (n, List.map translateBinding bind, translateProposition [] p)

let translateTheory {L.t_name=name; L.t_arg=args; L.t_body=body} =
  { s_name = name;
    s_arg = (match args with
		 None -> None
	       | Some a -> Some (List.map translateTheoryElement a));
    s_body = List.map translateTheoryElement body
  }
