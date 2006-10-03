(** The theory of Kuratowski-style finite sets. *)

Require List.

Definition Make (S : thy Parameter t : Set. end) :=
thy
   include List.Make(S).

   Axiom cons_commutative:
     forall x y : S.t, forall u : t, cons x (cons y u) = cons y (cons x u).
end.

