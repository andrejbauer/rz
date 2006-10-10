Require Number.
Require Sets.

Definition Metric :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (U : Sets.Space) =>
thy
  Definition s := U.s.
  Parameter dist : s -> s -> R.real.

  Implicit Type x y z : s.

  Axiom nonnegative:
    forall x, R.leq R.zero (dist x x).

  Axiom strict:
    forall x y, dist x y = R.zero <-> x = y.

  Axiom symmetric:
    forall x y, dist x y = dist y x.

  Axiom triangle_inequality:
    forall x y z,
      R.leq (dist x z) (R.add (dist x y) (dist y z)).

  Definition cauchy (a : I.nat -> s) :=
    forall k : I.nat,
      R.leq (dist (a (I.add1 k)) (a k)) (R.ratio I.one (I.pow I.two k)).

  Definition limit (a : I.nat -> s) x :=
    forall epsilon : R.positiveReal,
      exists k : I.nat,
        forall m n : I.nat,
          I.leq k m /\ I.leq k n -> R.lt (dist (a m) (a n)) epsilon.

  Definition ball (x : s) (r : R.real) := {y : s | R.lt (dist x y) r}.
end.

Definition CompleteMetric :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (U : Sets.Space) =>
thy
  include Metric I R U.

  Axiom complete:
    forall (a : I.nat -> s), cauchy a -> exists x : s, limit a x.
end.

Definition CompactMetric :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (U : Sets.Space) => 
thy
  include CompleteMetric I R U.

  Parameter FiniteSets : Sets.Finite(U).

  Definition net (epsilon : R.positiveReal) (u : FiniteSets.s) :=
    forall x : s, exists y : FiniteSets.carrier u, R.lt (dist x y) epsilon.

  Axiom totally_bounded:
    forall epsilon : R.positiveReal, exists u : FiniteSets.s,
	 net epsilon u.
end.

Definition CompleteSeparableMetric :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (U : Sets.Space) =>
thy
  include CompleteMetric I R U.

  Parameter CountableSets : Sets.Countable I U.

  Parameter denseSet : CountableSets.s.

  Axiom separable:
    forall epsilon : R.positiveReal,
    forall x : s,
    exists y : CountableSets.carrier denseSet,
      R.lt (dist x y) epsilon.
end.
