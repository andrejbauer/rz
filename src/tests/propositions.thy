theory P :=
thy

  Axiom tst_false : False.
  Axiom tst_true : True.
  Parameter s : Set.
  Parameter p : s -> Prop.
  Parameter p2 : s -> Stable.
  Parameter p3 : Equiv s.

  Parameter phi psi rho : Prop.
  Axiom tst_and : phi /\ psi /\ rho.
  Axiom tst_imply : phi -> psi.
  Axiom tst_iff : phi <-> psi.
  Axiom tst_or : phi \/ psi \/ rho.
  Axiom tst_forall : forall x : s, p x.
  Axiom tst_exists: exists x : s, p x.
  Axiom tst_exists1: exists1 x : s, p x.
  Axiom tst_not : not phi.

  Parameter x0 y0 : s.
  Axiom tst_equal : x0 = y0.
  Definition q := fun z : s => (z = x0 -> p z).
  Axiom tst_papp : q y0.
  
  Definition r1 := fun x y : s => (not p x /\ not p y).
  Definition r2 := r1 : Equiv s.

  Parameter w : [`foo + `bar:(s*s)].
  Axiom tst_pcase : match w with `foo => p x0 | `bar (u:s*s) => p (u.0)	 end.
end