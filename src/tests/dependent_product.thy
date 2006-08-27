theory T := thy
  Parameter s : Set.
  Parameter t : s -> Set.
  Parameter a b : [x:s] * (t x).
  Axiom eq : a = b.
end
