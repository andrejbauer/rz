theory T := thy
       Parameter s : Set.

       Parameter t : s -> Set.
       Definition www : (s -> Set) := t.

       Parameter u : s -> (s -> Set).
       Definition wwww : (s -> s -> Set) := u.

       Implicit Type y : s.

       Parameter (a b : s->s) (c d : s).
       Axiom m : forall (x : s), exists (y:s), True /\ True \/ True /\ True.

       Definition n := the y, y = y.
       Definition uu := t n.

       Definition q : Set := s -> s.
       Definition dd : q := a.

       Parameter yy : [x:s] * [y : t x] * s.
       Parameter zz : [x:s] -> [y : t x] -> s.
       Parameter ww : [x:s] -> [y:s] -> u x y.

       Definition yy0 := yy.0.
       Definition yy1 := yy.1.
       Definition yy2 := yy.2.

       Definition wwcd := ww c d.
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

theory Sums :=
thy

	Parameter s : Set.

	Parameter a b c : s.

        Definition sum : Set := [`yes : s + `no : unit + `maybe].

	Definition tmp1  := `yes a.
	Definition tmp2 : sum := tmp1.
	
	Definition d  := match tmp2 with
   `yes (q : s) => (q, ( ))
   | `no (r : unit) => (c, r)
   | `maybe => (a, ())
  end.

	Definition e : s := d.0.

end