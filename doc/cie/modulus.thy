Parameter nat : Set.
Parameter zero : nat.
Parameter s : nat -> nat.
Parameter (+) : nat -> nat -> nat.

Implicit Type k m n : nat.

Axiom plus_zero: forall k, k + zero = k.
Axiom plus_succ: forall k m, (s k) + m = s (k + m).

Definition (<=) k m := (not forall n, not (k + n = m)).

Axiom continuity:
forall f : (nat -> nat) -> nat, forall a : nat -> nat,
  exists k, forall b : nat -> nat,
    (forall m, m <= k -> a m = b m) -> f a = f b.
