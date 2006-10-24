Require Number.
Require Algebra.

(** Vector space *)

Definition VectorSpace(F : Algebra.Field) := Algebra.LeftModule(F).

(** Normed space *)

Definition NormedSpace(F : Algebra.Field) :=
thy
  include VectorSpace(F).

  Parameter norm : s -> 

end.