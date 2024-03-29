# First we need natural numbers

theory Natural =
thy
  set nat
  const zero : nat
  const succ : nat -> nat

  axiom recursion [A : thy
                         set s
                         const x : s
                         const f : s -> s
                       end] =
  some1 (g : nat -> A.s) . (
    g zero = A.x and
    all (n : nat) . (g (succ n) = A.f (g n))
  )
end


# We axiomatize the real numbers as the
# ordered Archimedean Cauchy complete field.
# We take into account validity of MP, which implies
# that apartness is the same thing as inequality.

theory Real (N : Natural) =
thy
  set r
  constant zero : r
  constant one : r
  constant ( + ) : r -> r -> r
  constant ( * ) : r -> r -> r
  constant ( - ) : r -> r -> r
  constant ( ~- ): r -> r

  set r' = { x : r | not (x = zero) }

  constant inv : r' -> r'

  ##################################################
  # Basic algebraic structure

  # (r, zero, +, ~-) is a commutative group

  implicit x, y, z : r

  axiom assoc_plus x y z =
	(x + y) + z = x + (y + z)

  axiom comm_plus x y =
	x + y = y + x

  axiom zero_plus x =
	x + zero = zero

  axiom inverse_plus x =
        x + (~- x) = zero

  # (r, zero, one, +, ~-, *) is a commutative ring with unit

  axiom assoc_mult x y z =
	(x * y) * z = x * (y * z)

  axiom comm_mult x y =
	x * y = y * x

  axiom one_mult x =
	x * one = x

  axiom distributivity x y z =
	(x + y) * z = (x * z) + (y * z)
  
  # r is a field

  axiom field x =
	not (x = zero) => x * (inv x) = one

  ##################################################
  # linear order

  # we take into account the fact that < turns out to be stable

  stable relation ( < ) : r * r

  stable relation ( <= ) x y = not (y < x)

  axiom assymetry x y =
	not (x < y and y < x)

  axiom linearity x y z =
	x < y => x < z or z < y

  axiom not_apart x y =
	not (x < y or y < x) => x = y

  axiom order_plus x y z =
	x < y => x + z < y + z

  axiom order_mult x y z =
	x < y and zero < x => x * z < y * z

  axiom order_positive x y =
	zero < x and zero < y => zero < x * y

  axiom order_inverse x =
	zero < x => zero < (inv (x :> r') :< r)
  	
  # The Archimedean axiom

  const i : N.nat -> r

  axiom i_injects =
    i N.zero = zero and
    all (n : N.nat) . (i (N.succ n) = one + i n)

  axiom archimedean x =
	zero < x => some (n : N.nat) . x < i n

  ##################################################
  # reals form a lattice

  const max : r -> r -> r
  const min : r -> r -> r

  axiom max_is_lub x y =
	x <= max x y and y <= max x y and
        all z. ((x <= z and y <= z) => max x y <= z)

  axiom min_is_glb x y =
	min x y <= x and min x y <= y and
        all z. ((z <= x and z <= y) => z <= min x y)

  const (abs : r -> r) = lam x . (max x (~- x))

  ##################################################
  # Cauchy completeness

  const halfTo : N.nat -> r

  axiom halfTo_is_what_you_think_it_is =
    halfTo N.zero = one and
    all (n : N.nat) . (halfTo (N.succ n) + halfTo (N.succ n) = halfTo n)


  axiom cauchy (a : N.nat -> r) =
  begin
    (all (n : N.nat) . (abs (a (N.succ n) - a n) < halfTo n))
    =>
    some (x : r) . all (n : N.nat) . (
      abs (x - a (N.succ n)) < halfTo n
    )
  end

end