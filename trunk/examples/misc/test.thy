theory TestQuot =
thy
  set nat
  equivalence ( =~= ) : nat * nat

  equivalence ( =/= ) (x : nat) (y : nat) = true

  # This should not type check!
  axiom foo (x : nat) =
    (=~=) x x and
    (let y % (=~=) = x % (=~=) in y) = x % (=~=)

  # This should type check!
  #axiom bar (x : nat) =
  #  (let [y] = x in [y]) = x

end

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