(* random stuff, probably wrong *)

module L = Logic

open Outsyn 


(** AB
Translation functions should be (roughly):

translateSet s
  translates a set s to a pair (ty, re) where ty is a
  type and re describes the realizability relation on ty.

translateTerm t
  translates a term t to (ty, u) where u is a value of
  type ty.

translatePred phi
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
	  
      



let rec extractTy = function
    L.True -> O.unitTy
  | L.False -> O.voidTy
  | L.Equal(_, _, _) -> O.unitTy
  | L.And ts -> O.TupleTy (map extractTy ts)
  | L.Imply(t1,t2) -> O.ArrowTy(extractTy t1, extractTy t2)
  | L.Or ts -> O.SumTy   (map extractTy ts)
  | L.Exists((name, Some set), t) -> O.TupleTy [xSet set; extractTy t]
  | L.All((name, Some set), t) -> O.ArrowTy(xSet set; extractTy t)
      
and rec xElement = function
    L.Set (name, None) -> O.TySpec(name, None)
  | L.Set (name, Some set) -> O.TySpec(name, Some (xSet set))
  | L.Predicate (name, stability, set) -> 
      
and rec xSet = function
    L.Empty -> O.NamedTy "void"
  | L.Unit  -> O.unitTy
  | L.Bool  -> O.NamedTy "bool"
  | L.Set_name name -> O.NamedTy name
  | L.Product sets -> O.TupleTy (map xSet sets)
  | L.Sum sets -> O.SumTy (map xSet sets)
  | L.Exp (s1,s2) -> O.ArrowTy (xSet s1, xSet s2)
  | L.Subset (_, Some s), p) -> O.TupleTy (xSet s, xTerm p)
