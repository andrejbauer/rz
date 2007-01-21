theory TestSubset =
thy
  set s
  predicate p : s
  predicate q : {x : s with p(x) }

  axiom foo (x:s) =
    p(x) => q(x :> {y : s with p(y)})

  axiom bar (x:s) =
    p(x) => q(x)

  predicate r : s * s
  set t = { x : s with r(x,x) }

  axiom baz (x:t) = r(x,x)

end