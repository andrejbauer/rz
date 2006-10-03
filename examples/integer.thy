(** The ring of integers. *)

Parameter t : Set.

(* Ring structure *)

Parameter zero: t.

Parameter one: t.

Parameter add: t -> t -> t.

Parameter neg: t -> t.

Parameter mul: t -> t -> t.

Implicit Type x y z : t.

Axiom non_trivial:
  not (zero = one).

Axiom add_associative:
  forall x y z, add x (add y z) = add (add x y) z.

Axiom zero_add_neutral:
  forall x, add zero x = x.

Axiom neg_add_inverse:
  forall x, add x (neg x) = zero.

Axiom add_commutative:
  forall x y, add x y = add y x.

Axiom mul_associative:
  forall x y z, mul x (mul y z) = mul (mul x y) z.

Axiom one_mul_neutral:
  forall x, mul one x = x.

Axiom mul_commutative:
  forall x y, mul x y = mul y x.

Axiom distributivity:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).

(* Decidable order *)

Parameter lt : t -> t -> Stable.

Definition gt x y := lt y x.

Definition leq x y := not (gt x y).

Definition geq x y := not (lt x y).

Axiom lt_reflexive:
  forall x, lt x x.

Axiom lt_transitive:
  forall x y z, lt x y /\ lt y z -> lt x z.

Axiom lt_antisymmetric:
  forall x y, lt x y /\ lt y x -> x = y.

Axiom lt_dichotomy:
  forall x y, lt x y \/ x = y \/ lt y x.

Definition positive x := lt zero x.

Axiom one_positive:
  positive one.

Axiom order_add:
  forall x y z, lt x y -> lt (add x z) (add y z).

Axiom order_mul:
  forall x y z, lt x y -> positive z -> lt (mul x z) (mul x z).

