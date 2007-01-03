Definition AbelianGroup :=
thy
  Parameter t : Set.
  Parameter zero : t.
  Parameter neg : t -> t.
  Parameter add : t * t -> t.
  Axiom zero_neutral: forall u : t, add(zero, u) = zero.
  Axiom neg_inverse: forall u : t, add(u,neg u) = zero.
  Axiom add_associative:
   forall u v w : t, add(add(u,v),w) = add(u,add(v,w)).
  Axiom abelian:
   forall u v : t, add (u,v) = add (v,u).
end.