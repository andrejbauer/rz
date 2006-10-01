(** The theory of Kuratowski-style finite sets. *)

Require List.

Definition Make (S : thy Parameter s : Set. end) :=
thy
   include List.Make(S).

   Axiom cons_commutative:
     forall x y : S.s, forall u : list, cons x (cons y u) = cons y (cons x u).
end.

