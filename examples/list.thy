(** Finite lists *)

Definition Make(S : thy Parameter s : Set. end) :=
thy
  Parameter list : Set.
  Parameter nil : list.
  Parameter cons : S.s -> list -> list.

  (* Induction principle for lists gives us "fold". *)
  Axiom induction:
    forall M : thy Parameter p : list -> Prop. end,
      M.p nil ->
      (forall x : S.s, forall lst : list, (M.p lst -> M.p (cons x lst))) ->
      (forall lst : list, M.p lst).
end.