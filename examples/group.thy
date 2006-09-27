(** We investigate how one might implement finitely presented monoids. *)

theory Monoid :=
thy
  Parameter s : Set.
  Parameter one : s.
  Parameter mul : s -> s -> s.

  Axiom one_neutral:
    forall x : s, mul x one = x /\ mul one x = x.

  Axiom mul_associative:
    forall x y z : s, mul x (mul y z) = mul (mul x y) z.
end