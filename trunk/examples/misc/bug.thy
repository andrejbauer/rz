theory Real =
thy
  set r

  # if you remove "stable" from phi it works
  stable predicate phi : r

  set r' = { x : r | phi(x) }

  constant f : r' -> r'
  constant g : r -> r

  constant x : r
  constant y = g (f x)

end
