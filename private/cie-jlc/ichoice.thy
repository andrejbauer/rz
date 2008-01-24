Parameter a b : Set.
Parameter r : a -> b -> Prop.
Axiom iac:
  (forall x : a, exists y : b, r x y) ->
  (exists c : rz a -> b, forall x : rz a, r (rz x) (c x)).