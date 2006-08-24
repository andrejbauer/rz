theory T :=
thy
  Parameter s : Set.

  Axiom shadow : forall x : s, exists x : s, x = x.
end
