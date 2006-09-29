(** The theory of Kuratowski-style finite sets. *)

Definition Finset (S : thy Parameter s : Set. end) :=
thy
   include Multiset.Make(S).

   Axiom cons_idempotent:
     forall x : S.s, cons x (cons x u) = cons x u.
end.