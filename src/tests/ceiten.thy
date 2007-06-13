(* Below is an example given by Jaap van Oosten in his "History and
Developments" [of realizability] paper. Attributed to Ceiten, it is described
as being realizable yet unprovable in intuitionistic propositional logic. *)

Parameter p1 p2 q1 q2 : Prop.

Axiom ceiten : 
  (not(p1 /\ p2) /\ (not(p1) -> q1 \/ q2) /\ (not(p2) -> q1 \/ q2)) ->
    ((not p1 -> q1) \/ (not p1 -> q2) \/ (not p2 -> q1) \/ (not p2 -> q2)).