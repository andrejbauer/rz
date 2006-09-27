(** The theory of Kuratowski-style finite sets. *)

Definition Kuratowski (S : thy Parameter s : Set. end) :=
thy
  Parameter s : Set.
  Parameter elt : S.s -> s -> Prop.
  Parameter emptyset : s.
  Parameter add : S.s -> s -> s.

  Axiom emptyest_is_empty:
     forall x : S.s, not (elt x emptyset).

  Axiom kuratowski_closure:
    forall x : S.s, forall u : s,
      elt x u <-> exists v : s, (u = add x v /\ not (elt x v)).
end.

Definition Finset (S : thy Parameter s : Set. end) :=
thy
   Parameter K : Kuratowski(S).
end.