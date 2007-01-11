Definition K(A : thy Parameter a : Set. end) :=
thy
  Parameter s : Set.
  Parameter emptySet : s.
  Parameter add : A.a -> s -> s.
  Implicit Type x y : A.a.
  Implicit Type u : s.
  Definition fin u := {x : A.a | u = add x u}.
  Axiom emptySet_empty: forall x, not (emptySet = add x emptySet).
  Axiom add_idem: forall x u, add x (add x u) = add x u.
  Axiom add_comm: forall x y u, add x (add y u) = add y (add x u).
  Axiom induction:
    forall P : thy Parameter p : s -> Prop. end,
      P.p emptySet -> (forall x u, P.p u -> P.p (add x u)) -> forall u, P.p u.
end.