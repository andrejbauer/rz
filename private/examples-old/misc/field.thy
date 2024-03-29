theory Field =
thy

  set s

  relation ( <> ) : s * s
  const zero : s
  const one : s
  const ( + ) : s -> s -> s
  const ( ~ ) : s -> s
  const ( * ) : s -> s -> s

  set s' = { x : s | x <> zero }

  const inv : s' -> s

  implicit x, y, z : s

  axiom apart1 x y =
    not (x <> y) <=> x = y

  axiom apart2 x y =
    x <> y => y <> x

  axiom apart3 x y z =
    x <> y => (x <> z or y <> z)

  axiom inverse x =
    x <> zero =>
      x * inv (x :> s') = one and inv (x :> s') * x = one

  axiom testing x =
    some (y : s') . (x + (y :< s) = zero => (y :< s) <> one)

end