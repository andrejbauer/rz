Module Type NEQ_AS_PROP.
  Parameter s : Set.

  Parameter neq : s -> s -> Prop.

  Parameter zero : s.
  Parameter one : s.	
  Parameter plus : s -> s -> s.
  Parameter neg : s -> s.
  Parameter times : s -> s -> s.

  Definition nonzero : s -> Prop := fun w => neq w zero.

  Definition s' := {x:s | nonzero x}.

  Parameter inv : s' -> s.

  Definition apart1 : Prop := forall x y : s, (not (neq x y)) <-> (x=y).
  Definition apart2 : Prop := forall x y : s, neq x y <-> neq y x.
  Definition apart3 : Prop := forall x y z : s, neq x y -> (neq x z \/ neq y z).
  
  Definition inverse : Prop := 
     forall x : s, forall n : neq x zero, times x (inv (exist nonzero x n)) = one /\
                                          times (inv (exist nonzero x n)) x = one.
End NEQ_AS_PROP.


Module Type NEQ_AS_SET.
  Parameter s : Set.

  Parameter neq : s -> s -> Set.

  Parameter zero : s.
  Parameter one : s.	
  Parameter plus : s -> s -> s.
  Parameter neg : s -> s.
  Parameter times : s -> s -> s.
  Parameter m : s.

  Definition nonzero : s -> Set := fun w => neq w zero.

  Definition s' := {x:s & nonzero x}.

  Parameter inv : s' -> s.

(* Wrong. 
   But how to handle equality and negation? 
 *)
  Definition apart1 := forall x y : s, (neq x y) .

(* Works because implicaton == function arrow *)
  Definition apart2 := forall x y : s, (neq x y) -> (neq y x).

(* Replace logical \/ with set + *)
  Definition apart3 := forall x y z : s, neq x y -> (neq x z + neq y z).

(* This axiom disappears in the output because I've used the equality proposition and
   logical conjunction.  But probably this isn't the "right" translation.
 *)
  Definition inverse :=
     forall x : s, forall n : neq x zero, (times x (inv (existS nonzero x n)) = one) /\
                                          (times (inv (existS nonzero x n)) x = one).
End NEQ_AS_SET.

(* XXX
     I don't know how to get coq to extract an ML signature from a Module Type, so
     instead I create dummy functors whose domain is the signature of interest,
     and which return nothing.  It's easy to generate code for functors...
 *)

Module Type NULL.
End NULL.

Module TestNeqAsProp (Thing : NEQ_AS_PROP) : NULL.
End TestNeqAsProp.

Module TestNeqAsSet (Thing : NEQ_AS_SET) : NULL.
End TestNeqAsSet.

Extraction "neqAsProp.ml" TestNeqAsProp.
Extraction "neqAsSet.ml" TestNeqAsSet.

