theory Choice =
thy
 set a
 set b
 relation r : a * b
 axiom choice =
  (all (x:a). some (y:b) . r(x,y)) =>
  some (g:a->b) . all (x:a) . r(x,g(x))
end