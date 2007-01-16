Parameter real : Set.
Parameter zero one: real.
Parameter mul : real -> real -> real.

Parameter inv : {x : real | not (x = zero)} -> real.

Axiom inverse:
  forall x : real, (not x = zero) -> mul x (inv x) = one.

Definition div (x : real) (y : {x:real|not(x=zero)}) := mul x (inv y).