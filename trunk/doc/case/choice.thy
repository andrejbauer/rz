theory Choice =
thy
 set a
 set b
 relation r : a * b
 axiom choice =
  (all (x:a). some (y:b) . r(x,y)) =>
  some (f:a->b) . all (x:a) . r(x,f(x))
end