Parameter real : Set.
Parameter zero one: real.
Parameter ( * ) : real -> real -> real.

Definition nonZeroReal := {x : real | not (x = zero)}.

Parameter inv : nonZeroReal -> real.

Axiom inverse: forall x : real, (not x = zero) -> x * (inv x) = one.

Definition (/) (x : real) (y : nonZeroReal) := x * (inv y).

Parameter (<) : real -> real -> Stable.

Axiom inv_positive: forall x : real, zero < x -> zero < inv x.