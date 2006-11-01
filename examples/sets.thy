Definition Space := 
thy
  Parameter s : Set.
end.

(* ***** Lists ***** *)

Definition List(S : Space) :=
thy
  Parameter s : Set.
  Parameter nil : s.
  Parameter cons : S.s -> s -> s.

  (* Induction principle for ts gives us "fold". *)
  Axiom induction:
    forall M : thy Parameter p : s -> Prop. end,
      M.p nil ->
      (forall x : S.s, forall lst : s, (M.p lst -> M.p (cons x lst))) ->
      (forall lst : s, M.p lst).
end.

Parameter ListMaker : [S : Space] -> List S.


Definition Hyperspace(S : Space) :=
thy
  Parameter s : Set.
  Parameter elm : S.s -> s -> Prop.
  Definition carrier (u : s) := {x : S.s | elm x u}.
end.

(* ***** Finite sets ***** *)

Definition Finite(S : Space) :=
thy
   include Hyperspace(S).

   Parameter emptySet : s.   
   Parameter add : S.s -> s -> s.

   Axiom elm_emptySet:
     forall x : S.s, not (elm x emptySet).

   Axiom elm_add:
     forall x : S.s, forall u : s,
       (elm x u <-> u = add x u).

   Axiom add_idempotent:
     forall x : S.s, forall u : s, add x (add x u) = add x u.

   Axiom add_commutative:
     forall x y : S.s, forall u : s, add x (add y u) = add y (add x u).

   Axiom induction:
     forall M : thy Parameter p : s -> Prop. end,
     M.p emptySet ->
     (forall x : S.s, forall u : s, (M.p u -> M.p (add x u))) ->
     (forall u : s, M.p u).
end.

(* ***** Multisets ***** *)
Require Number.

Definition Multi (I : Number.Integer) (S : Space) :=
thy
   Parameter s : Set.
   Parameter count : S.s -> s -> I.integer.

   Definition carrier (u : s) := {p : S.s * I.integer | count (p.0) u = p.1}.

   Parameter emptySet : s.   
   Parameter add : S.s -> s -> s.

   Axiom count_emptySet:
     forall x : S.s, count x emptySet = I.zero.

   Axiom count_add:
     forall x : S.s, forall u : s,
       count x (add x u) = I.add1 (count x u).

   Axiom add_commutative:
     forall x y : S.s, forall u : s, add x (add y u) = add y (add x u).

   Axiom induction:
     forall M : thy Parameter p : s -> Prop. end,
     M.p emptySet ->
     (forall x : S.s, forall u : s, (M.p u -> M.p (add x u))) ->
     (forall u : s, M.p u).
end.

(* ***** Countable sets ***** *)

Definition Countable :=
fun (I : Number.Integer) =>
fun (S : Space) =>
thy
   include Hyperspace(S).

   Parameter emptySet : s.
   Parameter add : S.s -> s -> s.

   Axiom emptySet_empty:
     forall x : S.s, not (elm x emptySet).

   Axiom elm_add:
     forall x : S.s, forall u : s, (elm x u <-> u = add x u).

   Axiom add_idempotent:
     forall x : S.s, forall u : s,
       add x (add x u) = add x u.

   Axiom add_commutative:
     forall x y : S.s, forall u : s,
       add x (add y u) = add y (add x u).

   Axiom countable:
     forall u : s, exists e : I.nat -> [`skip + `enum : S.s],
       forall x : carrier u, exists n : I.nat, `enum (x :< S.s) = e n.
end.