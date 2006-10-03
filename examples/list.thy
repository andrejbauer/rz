(** Finite lists *)

Definition Make(S : thy Parameter t : Set. end) :=
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