(** Real numbers. *)

theory Integers :=
thy
  Parameter Z : Ring.

  Axiom z_initial:
    forall R : Ring, exists1 f : Z.s -> R.s, ((RingHom Z  R).homomorphism) f.
end
