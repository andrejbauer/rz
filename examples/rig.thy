
(** Construction of free rings from rigs (or semirings), as discussed on
    the ocaml mailing list. Everything here is commutative. *)

Definition Rig :=
thy
  Parameter s : Set.
  Parameter zero : s.
  Parameter add : s -> s -> s.
  Parameter mul : s -> s -> s.

  Axiom zero_neutral:
    forall x : s, add x zero = x.

  Axiom commutative_plus:
    forall x y : s, add x y = add y x.

  Axiom associative_plus:
    forall x y z : s, add x (add y z) = add (add x y) z.

  Axiom commutative_mul:
    forall x y : s, add x y = add y x.

  Axiom associative_mul:
    forall x y z : s, add x (add y z) = add (add x y) z.

  Axiom distributivity:
    forall x y z : s, mul (add x y) z = add (mul x z) (mul y z).
end.

Definition Ring :=
thy
  include Rig.

  Parameter sub : s -> s -> s.

  Axiom sub_subtraction:
    forall x y : s, add (sub x y) y = x.
end.

Parameter RigHom : [M : Rig] -> [N : Rig] ->
thy
  Definition homomorphism (f : M.s -> N.s) :=
    f M.zero = N.zero /\
    (forall x y : M.s, f (M.add x y) = N.add (f x) (f y)) /\
    (forall x y : M.s, f (M.mul x y) = N.mul (f x) (f y)).   

  Definition s := { f : M.s -> N.s | homomorphism f }.
end.

Parameter RingHom : [R : Ring] -> [T : Ring] ->
thy
  Definition homomorphism (f : R.s -> T.s) :=
    f R.zero = T.zero /\
    (forall x y : R.s, f (R.add x y) = T.add (f x) (f y)) /\
    (forall x y : R.s, f (R.mul x y) = T.mul (f x) (f y)) /\
    (forall x y : R.s, f (R.sub x y) = T.sub (f x) (f y)).   

  Definition s := { f : R.s -> T.s | homomorphism f }.
end.

Definition FreeRing (M : Rig) :=
thy
  Parameter R : Ring.

  Parameter embed : M.s -> R.s.

  Axiom lift :
    forall T : Ring, forall f : (RigHom M T).s, exists1 g : (RingHom R T).s,
      forall x : M.s, g (embed x) = f x.
end.