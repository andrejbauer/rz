(** The theory of Kuratowski-style finite sets. *)

Require Multiset.

Definition Make(S : thy Parameter s : Set. end) :=
thy
   include Multiset.Make(S).

   Axiom cons_idempotent:
     forall x : S.s, forall u : list, cons x (cons x u) = cons x u.
end.
