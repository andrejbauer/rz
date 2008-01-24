Definition Branching :=
thy
  Parameter s : Set.      (* branching types *)
  Parameter t : s -> Set. (* branch labels *)
end.

Parameter W : [B : Branching] ->
thy
  Parameter w : Set.
  Parameter tree : [x : B.s] -> (B.t x -> w) -> w.
  Axiom induction:
    forall M : thy Parameter p : w -> Prop. end,
    (forall x : B.s, forall f : B.t x -> w,
       ((forall y : B.t x, M.p (f y)) -> M.p (tree x f))) ->
    forall t : w, M.p t.
end.