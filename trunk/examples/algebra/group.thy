# Examples of theories involving groups.
#

# The simplest theory is the theory of a group
theory Group =
thy
  set g
  const e : g
  const ( * ) : g -> g -> g
  const i : g -> g

  implicit x,y,z : g

  axiom associative x y z =
    (x * y) * z = x * (y * z)

  axiom unit x =
    e * x = x and x * e = x

  axiom inverse x =
    x * (i x) =  e and (i x) * x = e
end



# Sometimes a group is axiomatized with existence
# axioms for inverse and unit
theory GroupViaExistence =
thy
  set g
  const ( * ) : g -> g -> g

  implicit x, y, z: g

  axiom associative x y z =
    (x * y) * z = x * (y * z)

  predicate is_unit (e : g) = all x . (e * x = x and x * e = x)

  axiom unit = some (e : g) . is_unit(e)


  # Now we want to show there exists exactly one unit and
  # define it. But we do not have the unique existential quantifier
  # and the description operators, so this is a big pain.

  theorem unit_unique =
    (some (e : g) . is_unit(e)) and
    (all (e : g). all (e' : g). (is_unit(e) and is_unit(e') => e = e'))
 
  const e = the (e : g) . (is_unit (e))

  # now we do a similar thing with inverses

  predicate inverses x y =
    x * y = e and y * x = e

  axiom inverse x =
    (some y . inverses x y) and
    (all y . all z . (inverses x y and inverses x z => y = z))

  const i  = lam x . the y . inverses x y
end
