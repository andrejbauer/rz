# Semilattices.
# Used by kuratowski2.thr

theory Semilattice =
thy
  set s
  const zero : s
  const join : s -> s -> s
  implicit x, y, z : s
  axiom commutative x y = (join x y = join y x)
  axiom associative x y z = (join (join x y) z = join x (join y z))
  axiom idempotent x = (join x x = x)
  axiom bottom x =  (join x zero = x)
end
