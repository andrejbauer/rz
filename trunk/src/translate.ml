(* random stuff, probably wrong *)

module L = Logic
module S = Syntax
open Outsyn 

(* 
  isNegative : Syntax.term -> bool

  Checks for a negative formula, as defined on slide 20
  (plus the fact that Not and Iff can be defined in terms
   of falsehood, and, and implication)
*)
let rec isNegative = function
      S.False         -> true
    | S.True          -> true
    | S.Equal _       -> true
    | S.Not p         -> isNegative p
    | S.Forall(_,p)   -> isNegative p
    | S.Imply (p1,p2) -> (isNegative p1) && (isNegative p2)
    | S.Iff (p1,p2)   -> (isNegative p1) && (isNegative p2)
    | S.And ps        -> List.for_all isNegative ps
    | _               -> false

      
(* Generates variable names x0, x1, ...
   For now we will hope that the user doesn't use these names too.
 *)
(*
let var_counter = ref 0
let freshVar() =
      let count = !var_counter
      in let var_counter := !var_counter + 1
      in "x" ^ string_of_int count


let makesum n = 
  let rec loop k = 
           if (k<=n) then (string_of_int k,None)::loop(k+1) else []
  in
      S.Sum(loop 1)
  end

*)

(*
let rec normalize = function
      S.Or ps -> 
        let d = freshVar()
        in let p' = S.Exists((d,Some (makesum (List.length p)),
                             And(Equal(Some Bool,
                               
  *)
          
(*
let rec extractTy = function
      S.True -> O.TupleTy []
    | S.False -> O.TupleTy [] 
    | S.Equal(_, _, _) -> O.TupleTy []
    | S.And ts -> O.TupleTy (List.map extractTy ts)
    | S.Imply(t1,t2) -> O.ArrowTy(extractTy t1, extractTy t2)
(*    | S.Or  ts -> O.SumTy   (List.map extractTy ts)  *)
    | S.Exists((name,Some set), t) -> O.TupleTy[xSet set; extractTy t]
    | S.Forall((name,Some set), t) -> O.ArrowTy(xSet set, extractTy t)

and xElement = function
      S.Set (name, None) -> O.TySpec(name, None)
    | S.Set (name, Some set) -> O.TySpec(name, Some (xSet set))
(*    | S.Predicate (name, stability, set) -> *)

and xSet = function 
      S.Empty -> O.NamedTy "void"
    | S.Unit  -> O.TupleTy []
    | S.Bool  -> O.NamedTy "bool"
    | S.Set_name name -> O.NamedTy name
    | S.Product sets -> O.TupleTy (List.map xSet sets)
    | S.Exp (s1,s2) -> O.ArrowTy (xSet s1, xSet s2)

*)





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
	tot = ("x", (Cor [Equal (Ident "x", Constant "true");
                          Equal (Ident "x", Constant "false")]));
	per = ("x", "y", Equal (Ident "x", Ident "y"))
      }
  | L.Basic s ->
      { ty = NamedTy s;
	tot = ("x", NamedTotal (s, Ident "x"));
	per = ("x", "y", NamedPer (s, Ident "x", Ident "y"))
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
			       let q = subst_negative [(x, Proj (!k, Ident t))] p in incr k ; q) us
	       )
	      )
	  );
	  per = (
	    let t = "t" in
	    let u = "u" in
	      (t, u, And (
		 let k = ref 0 in
		   List.map (fun {per=(x,y,p)} ->
			       let q = subst_negative [(x, Proj (!k, Ident t)); (y, Proj (!k, Ident u))] p in
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
	    let f = find_name ["f"; "g"; "h"] [x; y] in
	      (f, Forall (x, u.ty, Imply (uneg, subst_negative [(y, (App (Ident f, Ident x)))] (vneg)))
	      )
	  );
	  per = (
	    let (x1, x2, uneg) = u.per in
	    let (y1, y2, vneg) = v.per in
	    let f = find_name ["f"; "g"; "h"] [x1; x2] in
	    let g = find_name ["f"; "g"; "h"] [x1; x2; f] in
	      (f, g, (Forall (x1, u.ty,
				Forall (x2, u.ty,
					Imply (uneg, subst_negative [(y1, App (Ident f, Ident x1)); (y2, App (Ident g, Ident x2))] (vneg))
				)))) 
	  )

	}

(* remaining cases:
  | Sum of (label * set) list
  | Subset of binding * proposition
  | RZ of set
  | Quotient, if we add this to Logic
*)

let rec translateTerm = function
    L.Var (n,_) -> Ident n
  | L.Star -> Star
  | L.Tuple lst -> Tuple (List.map translateTerm lst)
  | L.Proj (k, t) -> Proj (k, translateTerm t)
  | L.App (u, v) -> App (translateTerm u, translateTerm v)
  | L.Lambda (((n,_), s), t) -> Lambda (n, translateSet s, translateTerm t)
  | L.Inj (lb, t) -> Inj (lb, translateTerm t)
  | L.Case (t1, lst) -> Cases (translateTerm t1, List.map (fun (lb, ((n,_), s), t) -> (lb, n, (translateSet s).ty, translateTerm t)) lst)
  | L.Let (((n,_),s), u, v) -> Let (n, translateTerm u, translateTerm v)
			     
(* (string * ty) list -> L.proposition -> Outsyn.ty * string * Outsyn.negative *)
let rec translateProposition ctx = function
    L.False -> (VoidTy, "_", False)
  | L.True -> (UnitTy, "_", True)
  | L.Atomic ((n,_), t) -> (NamedTy n, raise Unimplemented, raise Unimplemented)
  | L.And lst ->
      let lst' = List.map (translateProposition ctx) lst in
      let t = find_name ["t"; "p"; "u"; "q"; "r"] (List.map fst ctx) in
	(TupleTy (List.map (function(s,_,_) -> s) lst'), t,
	 And (let k = ref 0 in
		List.map (fun (_, x, p) -> let q = subst_negative [(x, Proj (!k, Ident t))] p in incr k ; q) lst'))
  | L.Imply (p, q) ->
      let (t, x, p') = translateProposition ctx p in
      let (u, y, q') = translateProposition ctx q in
      let f = find_name ["f"; "g"; "h"; "p"; "q"] (x :: (List.map fst ctx)) in
	(ArrowTy (t, u), f, Forall (x, t, Imply (p', subst_negative [(y, App (Ident f, Ident x))] q')))
  | L.Iff (p, q) -> 
      let (t, x, p') = translateProposition ctx p in
      let (u, y, q') = translateProposition ctx q in
      let f = find_name ["f"; "g"; "h"; "p"; "q"; "r"] (x :: y :: (List.map fst ctx)) in
	(TupleTy [ArrowTy (t, u); ArrowTy (u, t)],
	 f, And [
	   Forall (x, t, Imply (p', subst_negative [(y, App (Proj (0, Ident f), Ident x))] q'));
	   Forall (y, u, Imply (q', subst_negative [(x, App (Proj (1, Ident f), Ident y))] p'))])

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
