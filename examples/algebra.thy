(** In this example we attempt to describe the basic algebraic
  structures in a modular way. We do so by first defining suitable
  signatures and parametrized theories, then combine them together in
  various ways to get the usual algebraic structures.
*)


(** An algebraic structure without any operations is just a set. *)
theory SimpleSet :=
thy
  Parameter s : Set.
end

theory Magma :=
thy
  Parameter s : Set.
  Parameter mul : s -> s -> s.
end

theory CommutativeMagma :=
thy
  Parameter s : Set.
  Parameter add : s -> s -> s.

  Axiom commutative:
    forall x y : s, add x y = add y x.
end

(** A semigroup is an associative magma. *)
theory Semigroup :=
thy
  include Magma.

  Axiom mul_associative:
    forall x y z : s, mul (mul x y) z = mul x (mul y z).
end


theory CommutativeSemigroup :=
thy
  include CommutativeMagma.

  Axiom add_associative:
    forall x y z : s, add x (add y z) = add x (add y z).
end


(** A monoid is a semigroup with unit. *)
theory Monoid :=
thy
  include Semigroup.

  Parameter one : s.

  Axiom one_neutral:
    forall x : s, mul x one = x /\ mul one x = x.
end


theory CommutativeMonoid :=
thy
  include CommutativeSemigroup.

  Parameter zero : s.

  Axiom zero_neutral:
    forall x : s, add x zero = x /\ add zero x = x.
end


(** A group is a monoid with inverses. *)
theory Group :=
thy
  include Monoid.

  Parameter inv : s -> s.

  Axiom inv_inverse:
    forall x : s, mul x (inv x) = one /\ mul (inv x) x = one.
end


(** Commutative groups are written additively. *)
theory CommutativeGroup :=
thy
  include CommutativeMonoid.

  Parameter neg : s -> s.

  Axiom neg_inverse:
    forall x : s, add x (neg x) = zero /\ add (neg x) x = zero.
end


(** We now combine semigroups and commutative groups to get rings. *)
theory Ring :=
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
end

theory RingWithUnit :=
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
end