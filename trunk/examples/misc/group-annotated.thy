(* Version of Group.thy where all the variables
   and all the equality comparisons are explicitly 
   annotated with types; for testing purposes until
   some sort of type inference is implemented.
*)

theory GroupAnnotated =
thy
  set g  
  const e : g
  const ( * ) : g -> g -> g
  const i : g -> g

  axiom useless (x : g) = (x = x in g)

  axiom unit (x : g) =
  begin
    (e * x = x in g) and (x * e = x in g)
  end

  axiom assoc (x : g) (y : g) (z : g) =

    ((x * y) * z = x * (y * z)   in   g)

  axiom inverse (x : g) =
  begin
    ((x * i(x)) =  e  in g)
    and (i(x) * x = e  in g)
  end
end