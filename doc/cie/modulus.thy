Parameter nat : Set.
Parameter zero : nat.
Parameter s : nat -> nat.
Parameter (+) : nat -> nat -> nat.

Implicit Type k m n : nat.

Axiom plus_zero: forall k, k + zero = k.
Axiom plus_succ: forall k m, (s k) + m = s (k + m).

Definition (<=) k m := exists n, k + n = m.

Implicit Type a b : nat -> nat.

Definition eq_prefix k a b := forall m, m <= k -> a m = b m.

Axiom continuity:
  forall f : (nat -> nat) -> nat, forall a,
    exists k, forall b, eq_prefix k a b -> f a = f b.
