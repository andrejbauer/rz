Require Sets.
Require Number.
Require Algebra.
Require Metric.

(** Real vector space *)

Definition VectorSpace :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
  Algebra.LeftModule R.

(** Normed space *)

Definition Norm :=
fun (I : Number.Integer) =>
fun (R : Number.Real(I)) =>
fun (V : VectorSpace I R) =>
thy
  Parameter norm : V.s -> R.real.

  Axiom norm_nonnegative:
    forall x : V.s, R.leq R.zero (norm x).

  Axiom norm_homogeneous:
    forall x : V.s, forall a : R.real, norm (V.act a x) = R.mul (R.abs a) (norm x).

  Axiom norm_triangle:
    forall x y : V.s, R.leq (norm (V.add x y)) (R.add (norm x) (norm y)).
end.

(** Banach space. *)

Definition BanachSpace :=
fun (I : Number.Integer) =>
fun (R : Number.Real I) =>
fun (V : VectorSpace I R) =>
thy
  include Norm I R V.

  include Metric.CompleteMetric I R V.

  Axiom dist_from_norm:
    forall x y : V.s, dist x y = norm (V.sub x y).
end.