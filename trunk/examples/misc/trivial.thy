theory Trivial =
thy
 set s

 const f : rz s -> (s -> s)

 axiom foo (x : s) = all (y : s) . (y = (let [(u : rz s)] = x in f u y))

end