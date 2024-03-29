theory DenseLinearOrder =
thy
  set s
  relation ( < ) : s * s

  implicit x,y,z : s

  axiom irreflexive x = (not (x < x))

  axiom transitive x y z = (x < y and y < z => x < z)

  axiom asymmetric x y = not (x < y and y < x)

  axiom linear x y z = (x < y => x < z or z < y)

  axiom dense x y = x < y => some z . (x < z and z < y)
end