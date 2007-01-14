Definition List(S : thy Parameter s : Set. end) :=
thy
  Parameter list : Set.
  Parameter nil : list.
  Parameter cons : S.s -> list -> list.
  Axiom fold:
    forall P : thy Parameter p : list -> Prop. end,
    (P.p nil) ->
    (forall x:S.s, forall u:list, P.p u -> P.p (cons x u)) ->
    forall u:list, P.p u.
end.