theory SetSeparation =
thy
  set v                           (* the "meta-set" of all sets *)
  relation elem : v -> v -> Prop  (* the element-hood relation *)

  const x : v
  predicate p : v

  axiom separation_x_p =
    some (y : v) . all (t : v) . (elem t y  iff  elem t x and p t)
end


theory BoundedSetSeparation =
thy
  set v
  relation elem : v -> v -> Prop

  const x : v
  set extension_x = { t : v | elem x t }

  predicate p : extension_x

  axiom separation_x_p =
    some (y : v) . all (t : v) . (elem t y  <=>  elem t x && p t)
end