Require Number.
Require Sets.

Definition Space := 
thy
  Parameter t : Set.
end.

Definition Metric :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (U : Space) =>
thy
  Definition s := U.t.
  Parameter d : s -> s -> R.real.

  Implicit Type x y z : s.

  Axiom nonnegative:
    forall x, R.leq R.zero (d x x).

  Axiom strict:
    forall x y, d x y = R.zero <-> x = y.

  Axiom symmetric:
    forall x y, d x y = d y x.

  Axiom triangle_inequality:
    forall x y z,
      R.leq (d x z) (R.add (d x y) (d y z)).

  Definition cauchy (a : I.nat -> s) :=
    forall k : I.nat,
      R.leq (d (a (I.add1 k)) (a k)) (R.ratio I.one (I.pow I.two k)).

  Definition limit (a : I.nat -> s) x :=
    forall epsilon : R.positiveReal,
      exists k : I.nat,
        forall m n : I.nat,
          I.leq k m /\ I.leq k n -> R.lt (d (a m) (a n)) epsilon.

  Definition ball (x : s) (r : R.real) := {y : s | R.lt (d x y) r}.
end.

Definition CompleteMetric :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (U : Space) =>
thy
  include Metric I R U.

  Axiom complete:
    forall (a : I.nat -> s), cauchy a -> exists x : s, limit a x.
end.

Definition CompactMetric :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (U : Space) => 
thy
  include CompleteMetric I R U.

  Parameter FinitePointSets : Sets.Finite(U).

  Definition net (epsilon : R.positiveReal) (u : FinitePointSets.t) :=
    forall x : s, exists y : FinitePointSets.carrier u, R.lt (d x y) epsilon.

  Axiom totally_bounded:
    forall epsilon : R.positiveReal, exists u : FinitePointSets.t,
	 net epsilon u.

end.