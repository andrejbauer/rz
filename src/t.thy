theory T := thy
       Parameter s : Set.
       Parameter t : s -> Set.

       
       Implicit Type y : s.

       Parameter (a b : s->s) (c : s).
       Axiom m : forall (x : s), exists (y:s), True /\ True \/ True /\ True.

       Definition n := the y, y = y.
       Definition u := t n.

       Definition q : Set := s -> s.
(*       Definition (d : q) := a. *)
         Definition d : q := a.
end

Module Type U.

   Parameter s : Set.
   Definition t := s.

   Parameter n : [x : s] * s .

End U.

theory Iteration :=
thy
  Parameter (a : Set).
  Parameter (x:a).
  Parameter s : a -> a.
end

theory DenseLinearOrder :=
thy
  Parameter s : Set.
  Parameter (<) : s -> s -> Prop.

  Implicit Type x y z : s.

  Axiom irreflexive : 
        forall (x : s), not (x < x).

  Axiom transitive:
        forall x y z, x < y /\ y < z -> x < z.

  Axiom assymetric:
        forall x y, not (x < y /\ y < x).

  Axiom linear:
        forall x y z, x < y -> x < z \/ z < y.

  Axiom dense:
        forall x y, x < y -> exists z, x < z /\ z < y.

end
