Module Type AC.
  Parameter s : Set.
  Parameter t : Set.
  Parameter r : s -> t -> Set.

  Definition ac :=
    (forall x : s, exists y : t, r x y) ->
    (exists f : s -> t, forall x : s, r x (f x)).
End AC.
