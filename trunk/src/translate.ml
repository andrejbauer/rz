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

let rec translateSet = function
    L.Empty -> 
      { ty = VoidTy;
	tot = (any, False);
	per = (any, any, False)
      }
  | L.Unit ->
      { ty = UnitTy;
	tot = (any, Equal (mk_id "x", Star));
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
      let u = translateSet s in
      let v = translateSet t in
	{ ty = ArrowTy (u.ty, v.ty);
	  tot = (
	    let (x,uneg) = u.tot in
	    let (y,vneg) = v.tot in
	    let f = find_name [mk_word "f"; mk_word "g"; mk_word "h"] [x; y] in
	      (f, Forall (x, u.ty, Imply (uneg, subst_proposition [(y, (App (Id f, Id x)))] (vneg)))
	      )
	  );
	  per = (
	    let (x1, x2, uneg) = u.per in
	    let (y1, y2, vneg) = v.per in
	    let f = find_name [mk_word "f"; mk_word "g"; mk_word "h"] [x1; x2] in
	    let g = find_name [mk_word "f"; mk_word "g"; mk_word "h"] [x1; x2; f] in
	      (f, g, (Forall (x1, u.ty,
				Forall (x2, u.ty,
					Imply (uneg, subst_proposition [(y1, App (Id f, Id x1)); (y2, App (Id g, Id x2))] (vneg))
				)))) 
	  )

	}

(* remaining cases:
  | Sum of (label * set option) list
  | Subset of binding * proposition
  | RZ of set
  | Quotient, if we add this to Logic
*)

let rec translateTerm = function
    L.Var n -> Id n
  | L.Star -> Star
  | L.Tuple lst -> Tuple (List.map translateTerm lst)
  | L.Proj (k, t) -> Proj (k, translateTerm t)
  | L.App (u, v) -> App (translateTerm u, translateTerm v)
  | L.Lambda ((n, s), t) -> Lambda (n, translateSet s, translateTerm t)
  | L.Inj (lb, t) -> Inj (lb, translateTerm t)
  | L.Case (t1, lst) -> Cases (translateTerm t1, 
                               List.map (function 
                                            (lb, Some (n, s), t) -> 
                                               (lb, n, (translateSet s).ty, 
                                                translateTerm t)
                                          | (lb, None, t) ->
                                               (lb, any, UnitTy, 
                                                translateTerm t))
                                        lst)
  | L.Let ((n,s), u, v) -> Let (n, translateTerm u, translateTerm v)
			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
let rec translateProposition ctx = function
    L.False -> (VoidTy, any, False)
  | L.True -> (UnitTy, any, True)
  | L.Atomic (n, t) -> (NamedTy n, raise Unimplemented, raise Unimplemented)
  | L.And lst ->
      let lst' = List.map (translateProposition ctx) lst in
      let t = find_name
		[mk_word "t"; mk_word "p"; mk_word "u"; mk_word "q"; mk_word "r"]
		(List.map fst ctx) in
	(TupleTy (List.map (function(s,_,_) -> s) lst'), t,
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
	(ArrowTy (t, u), f, Forall (x, t, Imply (p', subst_proposition [(y, App (Id f, Id x))] q')))
  | L.Iff (p, q) -> 
      let (t, x, p') = translateProposition ctx p in
      let (u, y, q') = translateProposition ctx q in
      let f = find_name
		[mk_word "f"; mk_word "g"; mk_word "h"; mk_word "p"; mk_word "q"; mk_word "r"]
		(x :: y :: (List.map fst ctx))
      in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f, And [
	   Forall (x, t, Imply (p', subst_proposition [(y, App (Proj (0, Id f), Id x))] q'));
	   Forall (y, u, Imply (q', subst_proposition [(x, App (Proj (1, Id f), Id y))] p'))])

  | L.Or ps -> raise Unimplemented

  | L.Forall (((n,_), s), p) -> raise Unimplemented
(*
  need to translate p too
      let s' = translateSet s in
      let n' = find_name [n] (List.map fst ctx) in
	Forall (n', s', p)
*)

  | L.Exists (((n,_), s), p) -> raise Unimplemented

  | L.Not p -> raise Unimplemented

  | L.Equal (s, t, u) -> raise Unimplemented
