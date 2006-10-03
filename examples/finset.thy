(** The theory of Kuratowski-style finite sets. *)

Require Multiset.

Definition Make(S : thy Parameter t : Set. end) :=
thy
   include Multiset.Make(S).

   Axiom cons_idempotent:
     forall x : S.t, forall u : t, cons x (cons x u) = cons x u.
end.

