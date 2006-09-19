# The law of excluded middle

theory Lem =
thy
  set s
  predicate p : s

  axiom lem =
   all (x : s) . (p x or not (p x))
end