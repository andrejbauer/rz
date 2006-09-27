Definition FiniteSets (S : thy Parameter s : Set. end) :=
thy
  Parameter s : Set.
  Parameter empt : s.
  Parameter add : S.s -> s -> s.
  Parameter elt : S.s -> s -> Stable.

  Definition carrier (u : s) := {x : S.s | elt x u}.

  Axiom elt_empt: forall x : S.s, not (elt x empt).

  Axiom add_commutative:
    forall x y : S.s, forall u : s,
      add x (add y u) = add y (add x u).

  Axiom add_idempotent:
    forall x : S.s, forall u : s,
      add x u = add x (add x u).

  Axiom elt_add1:
    forall x : S.s, forall u : s, elt x (add x u).

  Axiom elt_add2:
    forall x : S.s, forall u : s,
      elt x u -> exists v : s, (v = add x u /\ not (elt x v)).
end.

Definition Monoid :=
thy
  Parameter s : Set.
  Parameter one : s.
  Parameter mul : s -> s -> s.
end.

Definition FGMonoid :=
thy
  Parameter M : Monoid.
end.