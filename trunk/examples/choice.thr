theory Choice =
thy
  set a
  set b
  relation r : a * b

  implicit x : a
  implicit y : b

  axiom choice =
   (all x. some y. r (x, y)) => some (f : a -> b) . all x . r (x, f x)

  axiom intensionalChoice =
   (all x. some y. r (x, y)) => some (f : (rz a) -> b) . all (x' : rz a) . r ([x'], f x')

end
