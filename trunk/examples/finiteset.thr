theory Semilattice =
thy
  set t
  const z : t
  const join : t -> t -> t

  implicit x,y,z : t

  relation leq(x, y) = (join x y = y)

  axiom symmetry x y =
    join x y = join y x

  axiom assoc x y z =
    join (join x y) z = join x (join y z)

  axiom id x =
    join x x = x

end

theory FiniteSubsets ( a : set ) =
thy
   theory L :  Semilattice

   const incl : a -> L.t

   axiom init (M : Semilattice) (f : a -> M.t) =
   begin
     semilattice_morphism(f) =>
     exists1 (phi : L.t -> M.t) . (
	phi L.z = M.z and
        (forall x . forall y . phi (L.join x y) = M.join (phi x) (phi y)) and
        forall (x : a) . (phi (incl x) = f a)
     )
   end
end
