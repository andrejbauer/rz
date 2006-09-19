theory Quotients =
thy
  set s
  stable relation (<<) : s * s

  equivalence r : s -> s -> Prop

  implicit x, y, z : s
  implicit e : s % r

  axiom reflexive x = (x << x)

  axiom transitive x y z = (x << y and y << z) => x << z

  equivalence eq x y = (x << y and y << x)

  axiom surj = all e . some x . (e = x % r)

  axiom bar (f : s -> s) (a : s) e = r a (let x % r = e in f x)

end