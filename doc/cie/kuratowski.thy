Definition Semilattice :=
thy
  Parameter s : Set.
  Parameter zero : s.
  Parameter join : s -> s -> s.

  Implicit Type x y z : s.

  Axiom commutative : forall x y,   join x y = join y x.
  Axiom associative : forall x y z, join (join x y) z = join x (join y z).
  Axiom idempotent  : forall x,     join x x = x.
  Axiom bottom      : forall x,     join x zero = x.
end.


Definition Kuratowski (A : thy 
                              Parameter a : Set. 
                           end) :=
thy
  include Semilattice.

  Parameter singleton : A.a -> s.

  Definition fin := s.
  Definition emptyset := zero.
  Definition union := join.

  Axiom initial :
    forall S : Semilattice, forall f : A.a -> S.s,
    exists1 g : fin -> S.s, 
      g emptyset = S.zero /\
        (forall x : A.a, f x = g (singleton x))/\
        (forall u v : fin, g (union u v) = S.join (g u) (g v)).

end.
