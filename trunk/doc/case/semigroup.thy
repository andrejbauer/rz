theory SQGROUP = thy
  set s
  const e : s
  const ( * ) : s -> s -> s
  implicit x, y, z : s
  axiom unit x      =  x * e = x and e * x = x
  axiom assoc x y z =  x * (y * z) = (x * y) * z
  axiom sqrt x      =  some y . y * y = x
end
