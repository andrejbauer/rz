(* random stuff, probably wrong *)

module L = Logic

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

let rec translateSet = function
    L.Empty -> 
      { ty = VoidTy;
	tot = ("_", False);
	per = ("_", "_", False)
      }
  | L.Unit | L.InvisibleUnit ->
      { ty = UnitTy;
	tot = ("x", Equal (Ident "x", Star));
	per = ("x", "y", True)
      }
  | L.Bool ->
      { ty = NamedTy "bool";
	tot = ("x", (Cor [Equal (Ident "x", "true"), Equal (Ident "x", "false")]));
	per = ("x", "y", Equal (Ident "x", Ident "y"))
      }
  | L.Basic s ->
      { ty = NamedTy s;
	tot = ("x", Total ("s", Ident "x"));
	per = ("x", "y", Per ("s", Ident "x", Ident "y"))
      }
  | L.Product lst ->
      let us = List.map translateSet lst in
	{
	  ty = TupleTy (List.map (fun u -> u.ty) us);
	  tot = (
	    let t = "t" in
	      (t, And (
		 let k = ref 0 in
		   List.map (fun {tot=(x,p)} ->
			       let q = subst [(x, Proj (!k, Ident t))] p in incr k ; q) us
	       )
	      )
	  );
	  per = (
	    let t = "t" in
	    let u = "u" in
	      (t, u, And (
		 let k = ref 0 in
		   List.map (fun {per=(x,y,p)} ->
			       let q = subst [(x, Proj (!k, Ident t)), (y, Proj (!k, Ident u))] p in
				 incr k; q
			    ) us
	       )
	      )
	  )
	}
  | L.Exp (s, t) ->
      let u = translateSet s in
      let v = translateSet t in
	{ ty = ArrowTy (u.ty, v.ty);
	  tot = (
	    let x = fst u.tot in
	    let y = fst v.tot in
	    let f = find_name ["f"; "g"; "h"] [x; y] in
	      (f, Forall (x, u.ty, Imply (snd u.tot, subst [y, (App (f, x))] (snd v.tot)))
	      )
	  );
	  per = (
	    let x1, x2 = fst u.per in
	    let y1, y2 = fst v.per in
	    let f = find_name ["f"; "g"; "h"] [x1; x2] in
	    let g = find_name ["f"; "g"; "h"] [x1; x2; f] in
	      (f, g, (Forall (x1, u.ty,
				Forall (x2, u.ty,
					Imply (snd u.per, subst [(y1, App (f, x1)); (y2, App (g, x2))] (snd v.per))
				))))
	  )
	}
(* remaining cases:
  | Sum of (label * set) list
  | Subset of binding * proposition
  | RZ of set
*)

let rec translateTerm = function
    L.Var n -> Ident n
  | L.Star -> Star
  | L.Tuple lst -> Tuple (List.map translateTerm lst)
  | L.Proj (k, t) -> Proj (k, translateTerm t)
  | L.App (u, v) -> App (translateTerm u, translateTerm v)
  | L.Lambda ((n, s), t) -> Lambda (n, translateSet s, translateTerm t)
  | L.Inj (lb, t) -> Inj (lb, translateTerm t)
  | L.Case (t, lst) -> Cases (translateTerm t, List.map (fun (lb, (n, s), t) -> (lb, n, (translateSet s).ty, translateTerm)) lst)
  | L.Let (n, u, v) -> Let (n, translateTerm u, translateTerm v)
			     
let rec translateProposition ctx = function
    L.False -> (VoidyTy, "_", False)
  | L.True -> (UnitTy, "_", True)
  | L.Atomic (n, t) -> (NamedTy n, translateTerm t, )
  | L.And lst ->
      let lst' = List.map (translateProposition ctx) lst in
      let t = find_name ["t"; "p"; "u"; "q"; "r"] (List.map fst ctx) in
	(TupleTy (List.map fst lst'), t,
	 And (let k = ref 0 in
		List.map (fun (_, x, p) -> let q = subst [(x, Proj (!k, t))] p in incr k ; q) lst))
  | L.Imply (p, q) ->
      let (t, x, p') = translateProposition ctx p in
      let (u, y, q') = translateProposition ctx q in
      let f = find_name ["f"; "g"; "h"; "p"; "q"] (x :: (List.map fst ctx)) in
	(ArrowTy (t, u), f, Forall (x, t, Imply (p, subst [(y, App (f, x))] q)))
  | L.Iff (p, q) -> 
      let (t, x, p') = translateProposition ctx p in
      let (u, y, q') = translateProposition ctx q in
      let f = find_name ["f"; "g"; "h"; "p"; "q"; "r"] (x :: y :: (List.map fst ctx)) in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f, And (
	   Forall (x, t, Imply (p, subst [(y, App (Proj (0, f), x))] q)),
	   Forall (y, u, Imply (q, subst [(x, App (Proj (1, f), y))] p))
	 ))

  | L.Or of proposition list

  | L.Forall ((n, s), p) ->
      let s' = translateSet s in
      let n' = find_name [n] (List.map fst ctx) in
	Forall (n', s', p) (*AB: this line unfinished *)

  | L.Exists ((n, s), p) ->

  | L.Not p ->

  | L.Equal (s, t, u) ->
