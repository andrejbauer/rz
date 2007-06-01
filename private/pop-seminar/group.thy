Definition Group :=
thy
  Parameter s : Set.
  Parameter e : s.
  Parameter mul : s -> s -> s.
  Parameter inv : s -> s.
  Axiom associative:
    forall x y z : s, mul (mul x y) z = mul x (mul y z).
  Axiom neutral: forall x : s,
    mul e x = x /\ mul x e = x.
  Axiom inverse:
    forall x : s, mul (inv x) x = e /\ mul x (inv x) = e.
end.