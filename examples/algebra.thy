(** In this example we attempt to describe the basic algebraic
  structures in a modular way. We do so by first defining suitable
  signatures and parametrized theories, then combine them together in
  various ways to get the usual algebraic structures.
*)


(** An algebraic structure without any operations is just a set. *)
Definition SimpleSet :=
thy
  Parameter s : Set.
end.

Definition Magma :=
thy
  Parameter s : Set.
  Parameter mul : s -> s -> s.
end.

Definition CommutativeMagma :=
thy
  Parameter s : Set.
  Parameter add : s -> s -> s.

  Axiom commutative:
    forall x y : s, add x y = add y x.
end.

(** A semigroup is an associative magma. *)
Definition Semigroup :=
thy
  include Magma.

  Axiom mul_associative:
    forall x y z : s, mul (mul x y) z = mul x (mul y z).
end.


Definition CommutativeSemigroup :=
thy
  include CommutativeMagma.

  Axiom add_associative:
    forall x y z : s, add x (add y z) = add x (add y z).
end.


(** A monoid is a semigroup with unit. *)
Definition Monoid :=
thy
  include Semigroup.

  Parameter one : s.

  Axiom one_neutral:
    forall x : s, mul x one = x /\ mul one x = x.
end.


Definition CommutativeMonoid :=
thy
  include CommutativeSemigroup.

  Parameter zero : s.

  Axiom zero_neutral:
    forall x : s, add x zero = x /\ add zero x = x.
end.


(** A group is a monoid with inverses. *)
Definition Group :=
thy
  include Monoid.

  Parameter inv : s -> s.

  Axiom inv_inverse:
    forall x : s, mul x (inv x) = one /\ mul (inv x) x = one.
end.


(** Commutative groups are written additively. *)
Definition CommutativeGroup :=
thy
  include CommutativeMonoid.

  Parameter neg : s -> s.

  Axiom neg_inverse:
    forall x : s, add x (neg x) = zero /\ add (neg x) x = zero.
end.


(** We now combine semigroups and commutative groups to get rings. *)
Definition Ring :=
thy
  include CommutativeGroup.

  # It's a pity we cannot just "include Semiroup",
  # we can't because s would get shadowed.

  Parameter mul : s -> s -> s.

  Axiom mul_associative:
    forall x y z : s, mul (mul x y) z = mul x (mul y z).

  Axiom add_mul_distribute:
    forall x y z : s,
      mul x (add y z) = add (mul x y) (mul x z) /\
      mul (add x y) z = add (mul x z) (mul y z).
end.

Definition RingWithUnit :=
thy
  include CommutativeGroup.

  # It's a pity we cannot just "include Semiroup",
  # we can't because s would get shadowed.

  Parameter one : s.

  Parameter mul : s -> s -> s.

  Axiom one_mul_neutral:
    forall x : s, mul one x = x /\ mul x one = x.

  Axiom mul_associative:
    forall x y z : s, mul (mul x y) z = mul x (mul y z).

  Axiom add_mul_distribute:
    forall x y z : s,
      mul x (add y z) = add (mul x y) (mul x z) /\
      mul (add x y) z = add (mul x z) (mul y z).
end.

Definition CommutativeRingWithUnit :=
thy
  include CommutativeGroup.

  Parameter one : s.

  Parameter mul : s -> s -> s.

  Axiom one_mul_neutral:
    forall x : s, mul one x = x /\ mul x one = x.

  Axiom mul_associative:
    forall x y z : s, mul (mul x y) z = mul x (mul y z).

  Axiom mul_commutative:
    forall x y : s, mul x y = mul y x.

  Axiom add_mul_distribute:
    forall x y z : s,
      mul x (add y z) = add (mul x y) (mul x z) /\
      mul (add x y) z = add (mul x z) (mul y z).
end.

Definition RingHomSig := [S : Ring] -> [R : Ring] ->
thy
  Definition homomorphism (f : S.s -> R.s) :=
    f S.zero = R.zero /\
    (forall x : S.s, f (S.neg x) = R.neg (f x)) /\
    (forall x y : S.s, f (S.add x y) = R.add (f x) (f y)).

  Definition s := {f : S.s -> R.s | homomorphism(f)}.
end.

Parameter RingHom : RingHomSig.
