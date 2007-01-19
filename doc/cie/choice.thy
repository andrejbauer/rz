Parameter a b : Set.
Parameter r : a -> b -> Prop.
Axiom ac: (forall x : a, exists y : b, r x y) ->
          (exists c : a -> b, forall x : a, r x (c x)).