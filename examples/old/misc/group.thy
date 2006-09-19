theory Group =
thy
  set g  
  const e : g
  const ( * ) : g -> g -> g
  const i : g -> g
  implicit x,y,z : g
  axiom unit x =
    e * x = x and x * e = x
  axiom associative x y z =
    (x * y) * z = x * (y * z)
  axiom inverse x =
    x * (i x) =  e and (i x) * x = e
 
  axiom root x = some y . y * y = x

  axiom generator = some y . (not (y = e) and (all x . some z . x = y * z))
end