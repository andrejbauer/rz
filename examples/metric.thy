Definition Metric (R : Real) :=
thy
  Parameter s : Set.
  Parameter d : s -> s -> R.real.

  Axiom nonnegative:
    forall x : s, R.leq R.zero (d x x).

  Axiom strict:
    forall x y : s, d x y = R.zero <-> x = y.

  Axiom symmetric:
    forall x y : s, d x y = d y x.

  Axiom triangle_inequality:
    forall x y z : s,
      R.leq (d x z) (R.add (d x y) (d y z)).
end.