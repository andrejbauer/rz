theory Nat =
thy
  set nat

  const f : nat -> nat
  const x : nat
  const y = f ( f ( x ) )
end

theory Real(X : Nat) =
thy
  set real
  const inject : X.nat -> real
end

theory MetaReal (A : Nat) (B : Real) (C : Real(A)) =
thy
  model RR : Real(A)
end

theory Foo =
thy
  model N : Nat
  model R : Real
  model R2 : Real(N)

  model RR2 : MetaReal(N)(R)(R2)  
  model RR3 : MetaReal(N)(R)(R(N))  
end