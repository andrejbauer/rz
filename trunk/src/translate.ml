(* random stuff, probably wrong *)

module S = Syntax
module O = Outsyn 


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


let rec extractTy = function
    S.True -> O.unitTy
  | S.False -> O.voidTy
  | S.Equal(_, _, _) -> O.unitTy
  | S.And ts -> O.TupleTy (map extractTy ts)
  | S.Imply(t1,t2) -> O.ArrowTy(extractTy t1, extractTy t2)
  | S.Or ts -> O.SumTy   (map extractTy ts)
  | S.Exists((name, Some set), t) -> O.TupleTy [xSet set; extractTy t]
  | S.All((name, Some set), t) -> O.ArrowTy(xSet set; extractTy t)
      
and rec xElement = function
    S.Set (name, None) -> O.TySpec(name, None)
  | S.Set (name, Some set) -> O.TySpec(name, Some (xSet set))
  | S.Predicate (name, stability, set) -> 
      
and rec xSet = function
    S.Empty -> O.NamedTy "void"
  | S.Unit  -> O.unitTy
  | S.Bool  -> O.NamedTy "bool"
  | S.Set_name name -> O.NamedTy name
  | S.Product sets -> O.TupleTy (map xSet sets)
  | S.Sum sets -> O.SumTy (map xSet sets)
  | S.Exp (s1,s2) -> O.ArrowTy (xSet s1, xSet s2)
  | S.Subset (_, Some s), p) -> O.TupleTy (xSet s, xTerm p)
