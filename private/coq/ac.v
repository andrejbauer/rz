Module Type AC.
  Parameter s : Set.
  Parameter t : Set.
  Parameter r : s -> t -> Set.

  Definition ac :=
    (forall x : s, { y : t & r x y}) ->
    {f : s -> t & forall x : s, (r x (f x))}.
End AC.

Module Type SILLINESS.
End SILLINESS.

Module AcSilly (Thing : AC) : SILLINESS.
End AcSilly.

Extraction "acSilly.ml" AcSilly.
