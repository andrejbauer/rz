Definition Signature :=
thy
  Parameter s : Set.      (* branching types *)
  Parameter t : s -> Set. (* branch labels *)
end.

Parameter W : [S : Signature] ->
thy
  Parameter w : Set.

  Parameter tree : [x : S.s] -> (S.t x -> w) -> w.

  Axiom induction:
    forall M : thy Parameter p : w -> Prop. end,
    (forall x : S.s, forall f : S.t x -> w,
       ((forall y : S.t x, M.p (f y)) -> M.p (tree x f))) ->
    forall t : w, M.p t.
end.