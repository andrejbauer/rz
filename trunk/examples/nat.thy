# natural numbers

theory Nat =
thy
  set nat
  const zero : nat
  const succ : nat -> nat

  implicit n : nat

  # the existential in the following axiom should really
  # be unique existential, which we don't have right now

  axiom initial [I : thy set a
                         const x : a
                         const s : a -> a
                     end] =
    some (f : nat -> I.a) . (
      f zero = I.x and
      (all (n : nat) . f (succ n) = I.s (f n))
      and
      all (f' : nat -> I.a) . (
      (f' zero = I.x and all (n : nat) . (f' (succ n) = I.s (f' n))) =>
      f = f')
    )

  # The principle of induction shuld turn out to be equivalent to the
  # initiality axiom.


  axiom induction1 [T : thy predicate p : nat end] =
    (T.p zero and all n . (T.p n => T.p (succ n))) => all n . T.p n



  axiom induction2 [T : thy
                         predicate p : nat

                         axiom p0 = p zero
                         axiom p1 n = p (n) => p (succ n)
                       end] =
    all n . (T.p n)
end