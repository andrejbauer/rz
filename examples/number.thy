(* ***** INTEGERS ***** *)

Definition Integer :=
thy
(** The ring of integers. *)

Parameter integer: Set.

Implicit Type x y z : integer.

(* Ring structure *)

Parameter zero: integer.

Parameter one: integer.

Parameter add: integer -> integer -> integer.

Definition add1 x := add x one.

Definition two := add one one.

Parameter neg: integer -> integer.

Parameter mul: integer-> integer-> integer.

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

Parameter lt : integer-> integer-> Stable.

Definition gt x y := lt y x.

Definition leq x y := not (gt x y).

Definition geq x y := not (lt x y).

Definition nat := {k : integer| leq zero k}.

Axiom lt_reflexive:
  forall x, lt x x.

Axiom lt_transitive:
  forall x y z, lt x y /\ lt y z -> lt x z.

Axiom lt_antisymmetric:
  forall x y, lt x y /\ lt y x -> x = y.

Axiom lt_dichotomy:
  forall x y, lt x y \/ x = y \/ lt y x.

Definition positive x := lt zero x.

Definition positiveInteger := { x | positive x}.

Axiom one_positive:
  positive one.

Axiom order_add:
  forall x y z, lt x y -> lt (add x z) (add y z).

Axiom order_mul:
  forall x y z, lt x y -> positive z -> lt (mul x z) (mul x z).

(* Powers *)

Parameter pow : integer-> nat -> integer.

Axiom pow_power:
  (forall x : integer, pow x zero = one) /\
  (forall x : integer, forall n : nat, pow x (add n one) = mul x (pow x n)).

end. (* Integer *)




(* ***** REALS ***** *)

Definition Real (I : Integer) :=
thy
(* Real numbers. *)

Parameter real : Set.

Definition t := real.  (* By convention, we always have the type t *)

Implicit Type x y z : real.

(* Ring structure *)

Parameter zero: real.

Parameter one: real.

Parameter add: real -> real -> real.

Parameter neg: real -> real.

Definition sub x y := add x (neg y).

Parameter mul: real -> real -> real.

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

Parameter inv : {x | not (x = zero)} -> real.

Definition div (x : real) (y : {x | not (x = zero)}) := mul x (inv y).

Axiom field:
  forall x, (not (x = zero)) -> mul x (inv x) = one.

(* Linear order. *)

Parameter lt : real -> real -> Stable.

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

Definition positiveReal := {x | positive x}.

Axiom one_positive:
  positive one.

Axiom order_add:
  forall x y z, lt x y -> lt (add x z) (add y z).

Axiom order_mul:
  forall x y z, lt x y -> positive z -> lt (mul x z) (mul x z).

Axiom order_inv:
  forall x, positive x -> positive (inv x).

(* Lattice *)

Parameter max : real -> real -> real.

Parameter min : real -> real -> real.

Axiom max_is_max:
  forall x y z, leq (max x y) z <-> leq x z /\ leq y z.

Axiom min_is_min:
  forall x y z, leq z (min x y) <-> leq z x /\ leq z y.

Definition abs x := max x (neg x).

(* Archimedean property. *)

Parameter of_integer : I.integer -> real.

Definition ratio (p : I.integer) (q : {k : I.integer | not (k = I.zero)}) :=
  div (of_integer p) (of_integer q).

Axiom integer_embedding:
  of_integer I.zero = zero /\
  of_integer I.one = one /\
  (forall i j : I.integer, of_integer (I.add i j) = add (of_integer i) (of_integer j)) /\	
  (forall i j : I.integer, of_integer (I.mul i j) = mul (of_integer i) (of_integer j)).

Axiom archimedean:
  forall x : real,
  forall n : I.positiveInteger,
  exists m : I.integer,
    lt (ratio m n) x /\ lt x (ratio (I.add m I.two) n).

(* Cauchy completeness. *)

Definition cauchy (a : I.nat -> real) :=
  forall k : I.nat, leq (abs (sub (a (I.add1 k)) (a k))) (ratio I.one (I.pow I.two k)).

Definition limit (a : I.nat -> real) x :=
  forall epsilon : positiveReal,
  exists k : I.nat,
  forall m n : I.nat,
    I.leq k m /\ I.leq k n -> lt (abs (sub (a m) (a n))) epsilon.

Axiom complete_field:
  forall (a : I.nat -> real), cauchy a -> exists x : real, limit a x.

end.
