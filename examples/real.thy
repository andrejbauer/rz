Require Algebra.
Require Integer.

(* Real numbers. *)


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

(* Field structure. *)

Parameter inv : {x | not (x = zero)} -> t.

Axiom field:
  forall x, (not (x = zero)) -> mul x (inv x) = one.

(* Linear order. *)

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

Axiom lt_linear:
  forall x y z, lt x y -> lt x z \/ lt z y.

Definition positive x := lt zero x.

Axiom one_positive:
  positive one.

Axiom order_add:
  forall x y z, lt x y -> lt (add x z) (add y z).

Axiom order_mul:
  forall x y z, lt x y -> positive z -> lt (mul x z) (mul x z).

Axiom order_inv:
  forall x, positive x -> positive (inv x).

(* Archimedean property. *)

Parameter of_integer : Integer.t -> t.

Definition foo := Integer.zero.

(*Axiom integer_embedding:
  of_integer Integer.zero = zero /\
  of_integer Integer.one = one /\
  (forall i j : Integer.t, of_integer (Integer.add i j) = add (of_integer i) (of_integer j)) /\	
  (forall i j : Integer.t, of_integer (Integer.mul i j) = mul (of_integer i) (of_integer j)).*)