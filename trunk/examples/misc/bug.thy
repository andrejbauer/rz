theory Bug =
thy
  set s

  set v = s -> s -> s

  axiom test (f : v) (g : v) = f = g
end
