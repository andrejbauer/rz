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

  axiom neutral x =
    e * x = x and x * e = x

  axiom inverse x =
    x * (i x) =  e and (i x) * x = e
end



# Sometimes a group is axiomatized with existence
# axioms for inverse and neutral
theory GroupViaExistence =
thy
  set g
  const ( * ) : g -> g -> g

  implicit x, y, z: g

  axiom associative x y z =
    (x * y) * z = x * (y * z)

  predicate is_neutral (e : g) = all x . (e * x = x and x * e = x)

  axiom neutral = some (e : g) . is_neutral(e)


  # We want to show there exists exactly one neutral and
  # define it. But we do not have the unique existential quantifier
  # and the description operators, so this is a big pain.

  theorem neutral_unique = some1 (e : g) . is_neutral e
 
  const e = the (e : g) . (is_neutral e)

  # We do a similar thing with inverses

  predicate inverses x y =
    x * y = e and y * x = e

  axiom inverse x = some1 y . inverses x y

  const i  = lam x . the y . inverses x y
end
