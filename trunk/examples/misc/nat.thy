# natural numbers

theory Iteration =
thy
  set a
  const x : a
  const s : a -> a
end

theory Nat =
thy
  set nat
  const zero : nat
  const succ : nat -> nat

  axiom initial [I : thy set a
                         const x : a
                         const s : a -> a
                     end] =
    some1 (f : nat -> I.a) . (
      f zero = I.x and
      (all (n : nat) . f (succ n) = I.s (f n))
      and
      all (f' : nat -> I.a) . (
      (f' zero = I.x and all (n : nat) . (f' (succ n) = I.s (f' n))) =>
      f = f')
    )


end