# Kuratowski finite sets over a set

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


theory Kuratowski (A : thy set a end) =
thy

  set fin
  const empty : fin
  const union : fin -> fin -> fin

  const singleton : A.a -> fin

  # at this point we want to say that (s, zero, union) is a semilattice
  # and it seems like we just have to repeat the axioms

  implicit x, y, z : fin

  axiom commutative x y = (union x y = union y x)
  axiom associative x y z = (union (union x y) z = union x (union y z))
  axiom idempotent x = (union x x = x)
  axiom bottom (x : fin) =  (union x empty = x)

  # we really want unique existence, but we don't have the some1
  # quantifier yet

  axiom initial [S : Semilattice] (f : A.a -> S.s) =
    some (g : fin -> S.s) . (
      g empty = S.zero and
        all (x : A.a) . (f x = g (singleton x)) and
        all (u : fin) . all (v : fin) . (
          g (union u v) = S.join (g u) (g v)
        )
    )

end
