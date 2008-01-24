Definition Order :=
thy
  Parameter s : Set.
  Parameter (<<) : s -> s -> Stable.

  Axiom reflexive : forall x:s, x << x.

  Axiom transitive : forall x y z:s, (x << y /\ y << z) -> x << z.

  Definition eq  :=  (fun x y:s => x << y /\ y << x) : Equiv(s).

end.