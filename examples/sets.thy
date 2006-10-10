(* ***** Lists ***** *)

Definition List(S : thy Parameter t : Set. end) :=
thy
  Parameter t : Set.
  Parameter nil : t.
  Parameter cons : S.t -> t -> t.

  (* Induction principle for ts gives us "fold". *)
  Axiom induction:
    forall M : thy Parameter p : t -> Prop. end,
      M.p nil ->
      (forall x : S.t, forall lst : t, (M.p lst -> M.p (cons x lst))) ->
      (forall lst : t, M.p lst).
end.

(* ***** Finite sets ***** *)

Definition Finite(S : thy Parameter t : Set. end) :=
thy
   Parameter t : Set.
   Parameter elm : S.t -> t -> Prop.

   Definition carrier (u : t) := {x : S.t | elm x u}.

   Parameter emptySet : t.   
   Parameter add : S.t -> t -> t.

   Axiom elm_emptySet:
     forall x : S.t, not (elm x emptySet).

   Axiom elm_add:
     forall x : S.t, forall u : t,
       (elm x u <-> u = add x u).

   Axiom add_idempotent:
     forall x : S.t, forall u : t, add x (add x u) = add x u.

   Axiom add_commutative:
     forall x y : S.t, forall u : t, add x (add y u) = add y (add x u).

   Axiom induction:
     forall M : thy Parameter p : t -> Prop. end,
     M.p emptySet ->
     (forall x : S.t, forall u : t, (M.p u -> M.p (add x u))) ->
     (forall u : t, M.p u).
end.

(* ***** Multisets ***** *)
Require Number.

Definition Multi (I : Number.Integer) (S : thy Parameter t : Set. end) :=
thy
   Parameter t : Set.
   Parameter count : S.t -> t -> I.integer.

   Definition carrier (u : t) := {p : S.t * I.integer | count (p.0) u = p.1}.

   Parameter emptySet : t.   
   Parameter add : S.t -> t -> t.

   Axiom count_emptySet:
     forall x : S.t, count x emptySet = I.zero.

   Axiom count_add:
     forall x : S.t, forall u : t,
       count x (add x u) = I.add1 (count x u).

   Axiom add_commutative:
     forall x y : S.t, forall u : t, add x (add y u) = add y (add x u).

   Axiom induction:
     forall M : thy Parameter p : t -> Prop. end,
     M.p emptySet ->
     (forall x : S.t, forall u : t, (M.p u -> M.p (add x u))) ->
     (forall u : t, M.p u).
end.
