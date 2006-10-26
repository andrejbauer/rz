Require Algebra.

(* ***** INTEGERS ***** *)

Definition Integer :=
thy
  include Algebra.CommutativeRingWithUnit.

  Definition integer := s.

  Implicit Type x y z : integer.

  Definition add1 x := add x one.

  Definition two := add one one.

  Axiom non_trivial:
    not (zero = one).

  Axiom initial:
    forall R : Algebra.Ring,
      forall u : R.s,
        exists1 h : integer -> R.s,
          h zero = R.zero /\
          h one = u /\
          forall x y, (h (add x y) = R.add (h x) (h y)) /\
          forall x y, (h (mul x y) = R.mul (h x) (h y)).

  (* Decidable order *)

  Parameter compare : integer -> integer -> [`less + `equal + `greater].

  Definition lt x y := (compare x y = `less).

  Definition gt x y := (compare x y = `greater).

  Definition eq x y := (compare x y = `equal).

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
include Algebra.CommutativeField.

Definition real := s.

Implicit Type x y z : real.

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
  forall m : I.nat,
    I.leq k m -> lt (abs (sub (a m) x)) epsilon.

Axiom complete_field:
  forall (a : I.nat -> real), cauchy a -> exists x : real, limit a x.

end.
