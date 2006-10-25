Definition Signature :=
thy
  Parameter s : Set.      (* branching types *)
  Parameter t : s -> Set. (* branch labels *)
end.

Definition W(S : Signature) :=
thy
  Parameter w : Set.

  Parameter tree : [x : S.s] -> (S.t x -> w) -> w.

  Axiom induction:
    forall M : thy Parameter p : w -> Prop. end,
    (forall x : S.s, forall y : S.t x -> w, M.p (tree x y)) ->
    (forall t : w, M.p t).
end.