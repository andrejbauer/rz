theory T =
thy
  set s
  stable relation p : s * s

  implicit x : s

  axiom foo = true and all x .
    (p (x, x) and p (x, x) => p (x, x))

end