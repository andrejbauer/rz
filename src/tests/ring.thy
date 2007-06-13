Definition Monoid := thy
  Parameter s : Set.
  Parameter one : s.
  Parameter mul : s -> s -> s.

  Axiom associative : forall x y z : s, mul x (mul y z) = mul (mul x y) z.
  (* Plus other axioms *)
end.

Definition Group := thy
  include Monoid.

  Parameter inv : s -> s.
  
  Axiom rightinverse : forall x : s, mul x (inv x) = one.
  (* Plus other axioms *)
end.

Definition Ring := thy
  include Monoid. 
  include Group with mul -> add 
                with one -> zero
                with associative -> associative_add.
end.

  
