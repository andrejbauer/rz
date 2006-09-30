Definition Preorder := thy
  Parameter s : Set.
  Parameter leq : s -> s -> Prop.

  Implicit Type x y z : s.

  Axiom reflexive:  forall x, leq x x.

  Axiom transitive:  forall x y z, leq x y /\ leq y z -> leq x z.
end.

Definition Order := thy
  include Preorder.

  Implicit Type x y: s.

  Axiom antisymmetric:  forall x y, (leq x y /\ leq y x) -> (x=y).
end.

Definition Semilattice := thy
  include Order.

  Parameter join:  s -> s -> s.

  Implicit Type x y z : s.

  Axiom join1: forall x y, leq x (join x y).
  Axiom join2: forall x y, leq y (join x y).
  Axiom join3: forall x y z, leq x z /\ leq y z -> leq (join x y) z.

  Parameter lemma: forall x y, leq x y <-> ( y = join x y).
end.

