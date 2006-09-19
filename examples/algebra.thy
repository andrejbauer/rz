(** Basic algebraic structures. *)

(** An algebraic structure without any operations is just a set. *)
theory Primodial :=
thy
  Parameter s : Set.
end

(** Magma is the structure with a single binary operation. *)
theory Magma :=
thy
  include Primodial.
  Parameter mul : s -> s -> s.
end

(** A semigroup is an associative magma. *)
theory Semigroup :=
thy
  include Magma.

  Axiom mul_associative:
    forall x y z : s, mul (mul x y) z = mul x (mul y z).
end

(** A monoid is a semigroup with unit. *)
theory Monoid :=
thy
  include Semigroup.

  Parameter one : s.

  Axiom one_neutral:
    forall x : s, mul x one = x /\ mul one x = x.
end

(** A group is monoid with inverses. *)
theory Group :=
thy
  include Monoid.

  Parameter inv : s -> s.

  Axiom inv_inverse:
    forall x : s, mul x (inv x) = one /\ mul (inv x) x = one.
end
