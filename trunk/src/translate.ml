(* random stuff, probably wrong *)

module S = Syntax
module O = Outsyn 

let rec extractTy = function
      S.True -> O.TupleTy []
    | S.False -> O.TupleTy []           (* Why not void? *)
    | S.Equal(_, _, _) -> O.TupleTy []
    | S.And ts -> O.TupleTy (map extractTy ts)
    | S.Imply(t1,t2) -> O.ArrowTy(extractTy t1, extractTy t2)
(*    | S.Or  ts -> O.SumTy   (map extractTy ts)  *)
    | S.Exists((name,Some set), t) -> O.TupleTy[xSet set, extractTy t]
    | S.All((name,Some set), t) -> O.ArrowTy(xSet set, extractTy t)

and rec xElement = function
      S.Set (name, None) -> O.TySpec(name, None)
    | S.Set (name, Some set) -> O.TySpec(name, Some (xSet set))
    | S.Predicate (name, stability, set) -> 

and rec xSet = function 
      S.Empty -> O.NamedTy "void"
    | S.Unit  -> O.TupleTy []
    | S.Bool  -> O.NamedTy "bool"
    | S.Set_name name -> O.NamedTy name
    | S.Product sets -> O.TupleTy (map xSet sets)
    | S.Exp (s1,s2) -> O.ArrowTy (xSet s1, xSet s2)
